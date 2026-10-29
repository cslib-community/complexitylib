/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CSP.ToBoolean
import Complexity.Computability.Complexity.FineGrained.CountingFiniteCSP

/-!
# Finite-domain CSP unit tests

This module tests the finite-domain CSP compilation pipeline and its exact model counting:
* Bit width computation and binary encoding retraction properties.
* Graph 3-coloring on the triangle graph K₃ (yielding chromatic polynomial P(K₃, 3) = 6).
* Graph 3-coloring on the path graph P₃ (yielding P(P₃, 3) = 12).
* Graph 2-coloring on K₃ (unsatisfiable, yielding 0 models).
* Exact agreement between finite-domain model count and compiled Boolean CSP model count.
* Width and variable bounds on the compiled Boolean CSP instance.
-/

open Cslib.Logic.PL
open Cslib.BitString
open Cslib.Complexity
open Turing.MultiTapeTM
open SubexponentialSAT

namespace ComplexityTests.FiniteCSP

-- Bit width computation
example : CSP.bitWidth 1 = 1 := by decide
example : CSP.bitWidth 2 = 1 := by decide
example : CSP.bitWidth 3 = 2 := by decide
example : CSP.bitWidth 4 = 2 := by decide
example : CSP.bitWidth 5 = 3 := by decide
example : CSP.bitWidth 8 = 3 := by decide

-- Binary encoding round-trips
example : lowBits 2 0 = [false, false] := by decide
example : lowBits 2 1 = [true, false] := by decide
example : lowBits 2 2 = [false, true] := by decide
example : lowBits 2 3 = [true, true] := by decide
example : lsbValue [true, false] = 1 := by decide
example : lsbValue [false, true] = 2 := by decide
example : lsbValue (lowBits 3 5) = 5 := by decide

/-- Disequality semantics over `Fin q`. -/
def semNeq (q : ℕ) : Unit → List (Fin q) → Bool
  | (), [c1, c2] => c1 != c2
  | (), _ => false

/-- Triangle graph K₃ 3-coloring CSP instance. -/
def triangleCSP : CSP Unit ℕ :=
  [((), [0, 1]), ((), [1, 2]), ((), [0, 2])]

/-- Path graph P₃ 3-coloring CSP instance. -/
def pathCSP : CSP Unit ℕ :=
  [((), [0, 1]), ((), [1, 2])]

-- Model counts directly on finite-domain CSP
example : triangleCSP.modelCountOn (semNeq 3) (Finset.range 3) = 6 := by decide
example : pathCSP.modelCountOn (semNeq 3) (Finset.range 3) = 12 := by decide
example : triangleCSP.modelCountOn (semNeq 2) (Finset.range 3) = 0 := by decide

-- Model counts on compiled Boolean CSP
example :
    (triangleCSP.toBoolean 3 3).modelCountOn (CSP.semBoolean 3 (semNeq 3))
      (Finset.range 6) = 6 := by
  decide

example :
    (pathCSP.toBoolean 3 3).modelCountOn (CSP.semBoolean 3 (semNeq 3)) (Finset.range 6) = 12 := by
  decide

example :
    (triangleCSP.toBoolean 2 3).modelCountOn (CSP.semBoolean 2 (semNeq 2))
      (Finset.range 3) = 0 := by
  decide

-- Model count equivalence theorem application
example :
    (triangleCSP.toBoolean 3 3).modelCountOn (CSP.semBoolean 3 (semNeq 3)) (Finset.range 6) =
    triangleCSP.modelCountOn (semNeq 3) (Finset.range 3) :=
  CSP.modelCountOn_toBoolean 3 3 (semNeq 3) triangleCSP (by decide)

-- Width and variable bounds
example : (triangleCSP.toBoolean 3 3).all (fun c => c.2.length ≤ 4) = true := by decide
example : (triangleCSP.toBoolean 3 3).vars.all (fun v => decide (v < 6)) = true := by decide
example : CSP.validDeclaredCSP 4 6 (triangleCSP.toBoolean 3 3) = true := by decide

-- Satisfiability and unsatisfiability checks
example : 0 < triangleCSP.modelCountOn (semNeq 3) (Finset.range 3) := by decide
example : triangleCSP.modelCountOn (semNeq 2) (Finset.range 3) = 0 := by decide

-- Satisfiability equivalence and variable count bound on compiled Boolean CSP
example :
    (triangleCSP.toBoolean 3 3).Satisfiable (CSP.semBoolean 3 (semNeq 3)) ↔
    triangleCSP.Satisfiable (semNeq 3) :=
  CSP.satisfiable_toBoolean 3 3 (semNeq 3) triangleCSP (by decide)

example : (triangleCSP.toBoolean 3 3).numVars ≤ 3 * CSP.bitWidth 3 :=
  CSP.numVars_toBoolean_le (by decide)

/-- Trivial encoding for the singleton relation alphabet `Unit`. -/
def encUnit : Unit ↪ List Bool :=
  ⟨fun _ => [], fun _ _ _ => rfl⟩

-- Polynomial-time compilation and compiled encoding length bound
example :
    ComputableInPolyTime (fun x : ℕ × CSP Unit ℕ => x.2.toBoolean 3 x.1)
      (encPair encUnary (encCSP encUnit encNat))
      (encCSP (encOption encUnit) encNat) :=
  CSP.computableInPolyTime_toBoolean encUnit 3

example :
    ComputableInPolyTime
      (fun x : ℕ × CSP Unit ℕ => (x.1 * CSP.bitWidth 3, x.2.toBoolean 3 x.1))
      (encPair encUnary (encCSP encUnit encNat))
      (encPair encUnary (encCSP (encOption encUnit) encNat)) :=
  CSP.computableInPolyTime_toBooleanDeclared encUnit 3

example :
    PolyBounded
      (fun x : ℕ × CSP Unit ℕ => (encPair encUnary (encCSP encUnit encNat) x).length)
      (fun x : ℕ × CSP Unit ℕ =>
        (encPair encUnary (encCSP (encOption encUnit) encNat)
          (x.1 * CSP.bitWidth 3, x.2.toBoolean 3 x.1)).length) :=
  CSP.polyBounded_length_toBooleanDeclared encUnit 3

-- Native declared-variable exact counting on `Fin 3` (graph 3-coloring)
example :
    ∃ (count : ℕ × CSP Unit ℕ → ℕ) (T S : ℕ × CSP Unit ℕ → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encPair encUnary (encCSP encUnit encNat)) encNat T S ∧
      (∀ x, count x = if CSP.validDeclaredCSP 2 x.1 x.2 then
        x.2.modelCountOn (semNeq 3) (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encUnit encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encUnit encNat) x).length + 1) ^ b_space) :=
  CSP.exists_declaredCounter_finiteDomain encUnit 3 2 (semNeq 3)

-- Native occurring-variable exact counting on `Fin 3`
example :
    ∃ (count : CSP Unit ℕ → ℕ) (T S : CSP Unit ℕ → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encCSP encUnit encNat) encNat T S ∧
      (∀ F : CSP Unit ℕ, (∀ c ∈ F, c.2.length ≤ 2) → count F = F.modelCount (semNeq 3)) ∧
      (∀ F : CSP Unit ℕ, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encUnit encNat F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Unit ℕ, S F ≤ a * ((encCSP encUnit encNat F).length + 1) ^ b_space) :=
  CSP.exists_modelCounter_finiteDomain encUnit encNat 3 2 (semNeq 3)

-- Subexponential-time decision for bounded-arity CSP on `Fin 3`
example : DecidableInSubexpTime (CSP.KCSP 2 (semNeq 3)) (encCSP encUnit encNat) CSP.numVars :=
  CSP.decidableInSubexpTime_finiteDomainKCSP encUnit encNat 3 2 (semNeq 3)

end ComplexityTests.FiniteCSP
