/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.BooleanCSP

/-!
# Tests for bounded-arity Boolean `#CSP` compilation, counting, and subexponential decision

Concrete execution and non-vacuity checks for `CSP.toCNF`, `CSP.toCNFBounded`, `CSP.modelCountOn`,
`CSP.modelCount`, `CSP.exists_declaredCounter`, `CSP.exists_modelCounter`, and
`CSP.decidableInSubexpTime_KCSP`.
-/

@[expose] public section

namespace Cslib.Complexity.Tests.BooleanCSP

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

example : (enumBoolLists 3).length = 8 := by decide

-- `sampleCSP`:
-- 1. `2 ^^ 5 ^^ 9 = true` and `2 != 5` forces `2 ≠ 5` (2 choices) and `9 = false` (1 choice).
-- 2. Variable `12` appears only in the tautological constraint `((true, false), [9, 12])`, so it
--    has 2 free choices in `sampleCSP.modelCount sampleSem`, giving `2 * 1 * 2 = 4` solutions.
example : sampleCSP.numVars = 4 := by decide
example : sampleCSP.distinctVars = [2, 5, 9, 12] := by decide
example : (sampleCSP.toCNF sampleSem).length = 6 := by decide
example : sampleCSP.toCNFBounded 3 sampleSem = sampleCSP.toCNF sampleSem := by decide
example :
    (sampleCSP.toCNF sampleSem).all (fun cl => decide (cl.length ≤ 3)) = true := by
  decide
example : sampleCSP.modelCount sampleSem = 4 := by decide
example :
    (sampleCSP.denseRelabel.toCNF sampleSem).modelCountOn (Finset.range sampleCSP.numVars) = 4 := by
  decide

-- Repeated variable in scope (`x ≠ x`) is properly unsatisfiable via `forbidClause`.
example : (unsatRepeatedScopeCSP.toCNF sampleSem).length = 2 := by decide
example : unsatRepeatedScopeCSP.modelCount sampleSem = 0 := by decide

-- Empty CSP has 1 satisfying assignment on its empty variable set, and `2 ^ N` on `Finset.range N`.
example : CSP.modelCount sampleSem ([] : CSP SampleRel ℕ) = 1 := by decide
example : CSP.modelCountOn sampleSem ([] : CSP SampleRel ℕ) (Finset.range 3) = 8 := by decide

-- Polynomial-time compilation check.
example :
    ComputableInPolyTime (CSP.toCNFBounded 3 sampleSem)
      (encCSP encSampleRel encNat) encCNF :=
  CSP.computableInPolyTime_toCNFBounded encSampleRel encNat 3 sampleSem

-- Non-vacuity of declared-variable exact `#CSP` counter.
example :
    ∃ (count : ℕ × CSP SampleRel ℕ → ℕ) (T S : ℕ × CSP SampleRel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary (encCSP encSampleRel encNat)) encNat T S ∧
      (∀ x, count x = if CSP.validDeclaredCSP 3 x.1 x.2 then
        x.2.modelCountOn sampleSem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encSampleRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encSampleRel encNat) x).length + 1) ^ b) :=
  CSP.exists_declaredCounter encSampleRel 3 sampleSem

-- Non-vacuity of occurring-variable exact `#CSP` counter.
example :
    ∃ (count : CSP SampleRel ℕ → ℕ) (T S : CSP SampleRel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encCSP encSampleRel encNat) encNat T S ∧
      (∀ F : CSP SampleRel ℕ, (∀ c ∈ F, c.2.length ≤ 3) → count F = F.modelCount sampleSem) ∧
      (∀ F : CSP SampleRel ℕ,
        (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
          (((encCSP encSampleRel encNat F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP SampleRel ℕ, S F ≤ a * ((encCSP encSampleRel encNat F).length + 1) ^ b) :=
  CSP.exists_modelCounter encSampleRel encNat 3 sampleSem

-- Non-vacuity of subexponential decision for bounded-arity Boolean CSP.
example :
    DecidableInSubexpTime (CSP.KCSP 3 sampleSem) (encCSP encSampleRel encNat) CSP.numVars :=
  CSP.decidableInSubexpTime_KCSP encSampleRel encNat 3 sampleSem

end Cslib.Complexity.Tests.BooleanCSP
