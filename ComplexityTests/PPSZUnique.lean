/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.Unique

/-! PPSZ for isolated and unique solutions: a uniquely satisfiable 3-CNF formula, for which the
depth-two bound `2^{-(39/70) n}` beats the PPZ bound, and a 3-CNF formula with two solutions at
distance three, each of them `2`-isolated. -/

namespace ComplexityTests.PPSZUnique

open Cslib.Logic.PL Cslib.Complexity.PPSZ

/-! ### A unique solution -/

/-- The seven clauses on three variables satisfied by `x₀ = x₁ = x₂ = true`: each excludes one of
the other assignments. -/
def φ : CNF (Fin 3) :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, true), (1, false), (2, false)],
    [(0, false), (1, true), (2, true)], [(0, false), (1, true), (2, false)],
    [(0, false), (1, false), (2, true)]]

theorem φ_sat : φ.eval (fun _ => true) = true := by decide

theorem φ_len : ∀ c ∈ φ, c.length ≤ 3 := by decide

theorem φ_unique : ∀ τ, φ.eval τ = true → τ = fun _ => true := by
  have key : ∀ a b c : Bool, φ.eval ![a, b, c] = true → a = true ∧ b = true ∧ c = true := by
    decide
  intro τ h
  have hτ : τ = ![τ 0, τ 1, τ 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hτ] at h
  obtain ⟨h0, h1, h2⟩ := key _ _ _ h
  funext i
  fin_cases i <;> assumption

/-- Depth two: one round with `w = 3` succeeds with probability at least `2^{-(39/70) * 3}`. -/
example : (2 : ℝ) ^ (-(39 / 70 * 3 : ℝ)) ≤ ((round φ 3) fun _ => some true).toReal := by
  exact_mod_cast round_success_of_unique_three le_rfl φ_sat φ_unique φ_len

/-- Depth one recovers the PPZ bound `2^{-(2/3) n}` with `w = 1`. -/
example : (2 : ℝ) ^ (-(2 / 3 * 3 : ℝ)) ≤ ((round φ 1) fun _ => some true).toReal := by
  have h := round_success_of_unique (h := 1) (w := 1) φ_sat φ_unique φ_len (by decide)
  rw [qbar_one (by norm_num)] at h
  convert h using 3
  norm_num

/-- At depth two every variable is forced in at least `31 / 70` of the orders. -/
example (x : Fin 3) :
    (31 / 70 : ℝ) ≤ ((Finset.univ.filter fun π : Equiv.Perm (Fin 3) =>
      Forced φ 3 (fun _ => true) π x).card : ℝ) / Nat.factorial 3 :=
  qbar_three_two ▸ qbar_le_card_filter_forced_div_factorial φ_sat
    (isIsolated_of_unique φ_unique 2) φ_len (by decide) x

/-! ### Two solutions at distance three -/

/-- The six clauses on three variables satisfied by both `x₀ = x₁ = x₂ = true` and
`x₀ = x₁ = x₂ = false`. -/
def ψ : CNF (Fin 3) :=
  [[(0, true), (1, true), (2, false)], [(0, true), (1, false), (2, true)],
    [(0, true), (1, false), (2, false)], [(0, false), (1, true), (2, true)],
    [(0, false), (1, true), (2, false)], [(0, false), (1, false), (2, true)]]

theorem ψ_sat : ψ.eval (fun _ => true) = true := by decide

theorem ψ_len : ∀ c ∈ ψ, c.length ≤ 3 := by decide

-- The solution is not unique.
example : ψ.eval (fun _ => false) = true := by decide

/-- The all-true solution is `2`-isolated: flipping one or two variables falsifies `ψ`. -/
theorem ψ_isolated : IsIsolated ψ (fun _ => true) 2 := by
  unfold IsIsolated
  decide

/-- The all-true solution is not `3`-isolated: flipping all three variables gives the other
solution. -/
example : ¬IsIsolated ψ (fun _ => true) 3 := fun h =>
  h Finset.univ Finset.univ_nonempty (by decide) (by decide)

/-- The headline applies to the isolated, non-unique solution. -/
example : (2 : ℝ) ^ (-(39 / 70 * 3 : ℝ)) ≤ ((round ψ 3) fun _ => some true).toReal := by
  have h := round_success_of_isolated (w := 3) ψ_sat ψ_isolated ψ_len (by decide)
  rw [qbar_three_two] at h
  convert h using 3
  norm_num

end ComplexityTests.PPSZUnique
