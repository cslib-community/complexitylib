/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.ThreeXOR

/-! Concrete systems for the four-clause XOR reduction, including the tight `7 / 8` boundary. -/

namespace ComplexityTests.ThreeXOR

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-- Opposite parity requirements on the same three distinct variables. -/
def inconsistent : CSP Bool ℕ := [(false, [0, 1, 2]), (true, [0, 1, 2])]

private theorem scopes_inconsistent : ∀ c ∈ inconsistent, c.2.length = 3 := by decide

/-- The compiler introduces no auxiliary variables and emits eight clauses. -/
example : (inconsistent.toCNFBounded 3 CSP.paritySem).length = 8 := by decide

/-- The two input equations always disagree, so every assignment falsifies exactly one clause. -/
theorem countUnsat_inconsistent (σ : ℕ → Bool) :
    (inconsistent.toCNFBounded 3 CSP.paritySem).countUnsat σ = 1 := by
  rw [CSP.countUnsat_toCNFBounded _ (fun c hc => (scopes_inconsistent c hc).le)]
  cases h₀ : σ 0 <;> cases h₁ : σ 1 <;> cases h₂ : σ 2 <;>
    simp [inconsistent, Constraint.eval, CSP.paritySem, h₀, h₁, h₂]

/-- This nonvacuous distinct-variable system meets the `7 / 8` boundary exactly. -/
example : (inconsistent.toCNFBounded 3 CSP.paritySem).unsatVal = 1 / 8 := by
  have hlen : (inconsistent.toCNFBounded 3 CSP.paritySem).length = 8 := by decide
  refine le_antisymm ?_ ((CNF.le_unsatVal_iff _).2 fun σ => ?_)
  · simpa [countUnsat_inconsistent, hlen] using
      (inconsistent.toCNFBounded 3 CSP.paritySem).unsatVal_le (fun _ => false)
  · rw [countUnsat_inconsistent, hlen]
    norm_num

example : (inconsistent.toCNFBounded 3 CSP.paritySem).IsExactThreeDistinct :=
  CSP.isExactThreeDistinct_toCNFBounded_parity (by decide)

/-- Repeated variables are permitted: `x ⊕ x ⊕ x = true` is satisfiable by `x = true`. -/
example : (CSP.toCNFBounded 3 CSP.paritySem [(true, [0, 0, 0])] : CNF ℕ).Satisfiable :=
  ⟨fun _ => true, by decide⟩

/-- The same repeated-variable constraint has exactly one false clause at `x = false`. -/
example : (CSP.toCNFBounded 3 CSP.paritySem [(true, [0, 0, 0])] : CNF ℕ).countUnsat
    (fun _ => false) = 1 := by decide

/-- An even-parity equation is satisfied by the zero assignment. -/
example : (CSP.toCNFBounded 3 CSP.paritySem [(false, [0, 1, 2])] : CNF ℕ).eval
    (fun _ => false) = true := by decide

/-- The empty system produces the empty formula and has value zero. -/
example : (CSP.toCNFBounded 3 CSP.paritySem ([] : CSP Bool ℕ)).unsatVal = 0 := by
  exact (CNF.unsatVal_eq_zero_iff _).2 ⟨fun _ => false, rfl⟩

/-- The total compiler retains a false nullary constraint as an empty clause. -/
example : CSP.toCNFBounded 3 CSP.paritySem [(true, ([] : List ℕ))] = [[]] := by decide

/-- A scope beyond the width guard is discarded, outside the stated three-variable domain. -/
example : CSP.toCNFBounded 3 CSP.paritySem [(true, ([0, 1, 2, 3] : List ℕ))] = [] := by decide

/-- Runtime certificates compose with a real client counting the output clauses. -/
example : ComputableInPolyTime
    (fun F : CSP Bool ℕ => (F.toCNFBounded 3 CSP.paritySem).length)
    (encCSP encBool encNat) encUnary := by
  fun_prop

end ComplexityTests.ThreeXOR
