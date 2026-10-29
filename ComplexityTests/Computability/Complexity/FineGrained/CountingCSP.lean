/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingCSP

/-!
# Tests for bounded-arity CSP definitions, CNF compilation, counting, and subexponential decision

Concrete execution and non-vacuity checks for `CSP.toCNF`, `CSP.toCNFBounded`, `CSP.modelCountOn`,
`CSP.modelCount` (over both Boolean and finite non-Boolean domains), `CSP.exists_declaredCounter`,
`CSP.exists_modelCounter`, and `CSP.decidableInSubexpTime_KCSP`.
-/

@[expose] public section

namespace Cslib.Complexity.Tests.CountingCSP

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- Sample finite relation alphabet: 3-variable parity (`x ⊕ y ⊕ z = 1`), 2-variable NAE (`x ≠ y`),
and a 2-variable tautology (`⊤`, emitting 0 clauses). -/
abbrev SampleRel : Type := Bool × Bool

def sampleSem : SampleRel → List Bool → Bool
  | (false, false), [a, b, c] => a ^^ b ^^ c
  | (false, true), [a, b] => a != b
  | (true, _), [_, _] => true
  | _, _ => false

def encSampleRel : SampleRel ↪ List Bool :=
  encPair encBool encBool

/-- Sample CSP instance with non-contiguous variable labels (`2, 5, 9, 12`), a repeated variable
in a constraint scope (`(5, 5)`), and a tautological constraint on `(9, 12)` that emits 0 clauses
in `toCNF` while still keeping `12` in `F.vars`. -/
def sampleCSP : CSP SampleRel ℕ :=
  [((false, false), [2, 5, 9]),
   ((false, true), [2, 5]),
   ((true, false), [9, 12])]

/-- CSP with a repeated variable in an unsatisfied NAE constraint `x ≠ x`. -/
def unsatRepeatedScopeCSP : CSP SampleRel ℕ :=
  [((false, true), [4, 4])]

-- Concrete evaluations on `sampleCSP`, `unsatRepeatedScopeCSP`, and the empty CSP.
example :
    (BitString.enumList 3).length = 8 ∧
    sampleCSP.numVars = 4 ∧
    sampleCSP.distinctVars = [2, 5, 9, 12] ∧
    (sampleCSP.toCNF sampleSem).length = 6 ∧
    sampleCSP.toCNFBounded 3 sampleSem = sampleCSP.toCNF sampleSem ∧
    (sampleCSP.toCNF sampleSem).all (fun cl => decide (cl.length ≤ 3)) = true ∧
    sampleCSP.modelCount sampleSem = 4 ∧
    (sampleCSP.denseRelabel.toCNF sampleSem).modelCountOn (Finset.range sampleCSP.numVars) = 4 ∧
    (unsatRepeatedScopeCSP.toCNF sampleSem).length = 2 ∧
    unsatRepeatedScopeCSP.modelCount sampleSem = 0 ∧
    CSP.modelCount sampleSem ([] : CSP SampleRel ℕ) = 1 ∧
    CSP.modelCountOn sampleSem ([] : CSP SampleRel ℕ) (Finset.range 3) = 8 := by
  decide

-- Domain-polymorphic `CSP.modelCount` over a finite non-Boolean domain (`Fin 3`):
-- 3-coloring of a triangle `[((), [0, 1]), ((), [1, 2]), ((), [0, 2])]` has `3 * 2 * 1 = 6` models.
def neqFin3 : Unit → List (Fin 3) → Bool
  | (), [a, b] => decide (a ≠ b)
  | (), _ => false

def triangle3ColorCSP : CSP Unit ℕ :=
  [((), [10, 20]), ((), [20, 30]), ((), [10, 30])]

example :
    triangle3ColorCSP.modelCount neqFin3 = 6 ∧
    triangle3ColorCSP.denseRelabel.modelCount neqFin3 = 6 := by
  decide

-- Polynomial-time compilation check on both finite (`SampleRel`) and infinite (`Bool × List Bool`)
-- relation types.
def taggedSem (r : Bool × List Bool) (_w : List Bool) : Bool := r.1

theorem computableInPolyTime_taggedSem :
    ComputableInPolyTime (fun p : (Bool × List Bool) × List Bool => taggedSem p.1 p.2)
      (encPair (encPair encBool encBits) encBits) encBool :=
  (ComputableInPolyTime.fst encBool encBits).comp (ComputableInPolyTime.fst _ _)

example :
    ComputableInPolyTime (CSP.toCNFBounded 3 sampleSem)
      (encCSP encSampleRel encNat) encCNF ∧
    ComputableInPolyTime (CSP.toCNFBounded 3 taggedSem)
      (encCSP (encPair encBool encBits) encNat) encCNF :=
  ⟨CSP.computableInPolyTime_toCNFBounded_of_finite encSampleRel encNat 3 sampleSem,
   CSP.computableInPolyTime_toCNFBounded (encPair encBool encBits) encNat 3 taggedSem
     computableInPolyTime_taggedSem⟩

-- Non-vacuity of declared-variable exact `#CSP` counter.
example :
    ∃ (count : ℕ × CSP SampleRel ℕ → ℕ) (T S : ℕ × CSP SampleRel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary (encCSP encSampleRel encNat)) encNat T S ∧
      (∀ x, count x = if CSP.validDeclaredCSP 3 x.1 x.2 then
        x.2.modelCountOn sampleSem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encSampleRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encSampleRel encNat) x).length + 1) ^ b) :=
  CSP.exists_declaredCounter_of_finite encSampleRel 3 sampleSem

-- Non-vacuity of occurring-variable exact `#CSP` counter (general polynomial-time `sem`).
example :
    ∃ (count : CSP (Bool × List Bool) ℕ → ℕ) (T S : CSP (Bool × List Bool) ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encCSP (encPair encBool encBits) encNat) encNat T S ∧
      (∀ F : CSP (Bool × List Bool) ℕ,
        (∀ c ∈ F, c.2.length ≤ 3) → count F = F.modelCount taggedSem) ∧
      (∀ F : CSP (Bool × List Bool) ℕ,
        (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
          (((encCSP (encPair encBool encBits) encNat F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP (Bool × List Bool) ℕ,
        S F ≤ a * ((encCSP (encPair encBool encBits) encNat F).length + 1) ^ b) :=
  CSP.exists_modelCounter (encPair encBool encBits) encNat 3 taggedSem
    computableInPolyTime_taggedSem

-- Non-vacuity of subexponential decision for bounded-arity Boolean CSP.
example :
    DecidableInSubexpTime (CSP.KCSP 3 sampleSem) (encCSP encSampleRel encNat) CSP.numVars :=
  CSP.decidableInSubexpTime_KCSP_of_finite encSampleRel encNat 3 sampleSem

end Cslib.Complexity.Tests.CountingCSP
