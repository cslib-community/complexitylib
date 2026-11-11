/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SetCover.Greedy

/-!
# Worked greedy set-cover examples

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Algorithms.Lean.SetCover.greedy`:

1. A weighted instance on three elements where the greedy algorithm buys three singletons
   (cost `1/3 + 1/2 + 1 = 11/6`) although one set of weight `11/10` covers everything; Chvátal's
   bound `11/6 ≤ H 3 · 11/10 = 121/60` is applied to the optimal cover.
2. An unweighted instance where greedy takes the largest set first and needs three sets although
   two suffice, with the `H d` bound for `d = 3` (`3 ≤ (11/6) · 2`).
3. A fractional cover: three pairs covering a triangle with weight `1/2` each. The greedy cover
   costs `2`, within `H 2` times the fractional cost `3/2`, as
   `sum_greedy_le_harmonic_mul_fractional` requires.
4. Edge cases: tie-breaking toward the earliest candidate, an empty ground set, and an infeasible
   instance on which the loop stops with an incomplete cover, so the coverage hypothesis of
   `greedy_covers` cannot be dropped.
-/

public section

namespace ComplexityTests.SetCoverGreedy

open Cslib.Algorithms.Lean.SetCover

/-! ### 1. A weighted instance where greedy is not optimal -/

/-- Three singletons and the whole ground set `Fin 3`. -/
def T : Fin 4 → Finset (Fin 3)
  | 0 => {0}
  | 1 => {1}
  | 2 => {2}
  | 3 => {0, 1, 2}

/-- The singletons cost `1/3`, `1/2`, `1`; the whole set costs `11/10`. -/
def wT : Fin 4 → ℚ
  | 0 => 1 / 3
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 11 / 10

/-- Each round the cheapest remaining singleton beats the whole set's cost per uncovered
element (`11/30`, then `11/20`, then `11/10`). -/
example : greedy T wT [0, 1, 2, 3] Finset.univ = [0, 1, 2] := by decide +kernel

/-- The greedy cost `11/6` exceeds the cost `11/10` of the cover `{3}`. -/
example : ((greedy T wT [0, 1, 2, 3] Finset.univ).map wT).sum = 11 / 6 := by decide +kernel

example : ((greedy T wT [0, 1, 2, 3] Finset.univ).map wT).sum > ∑ j ∈ {3}, wT j := by
  decide +kernel

/-- Chvátal's bound against the cover `{3}`: `cost ≤ H 3 · 11/10 = 121/60`. -/
example : ((greedy T wT [0, 1, 2, 3] Finset.univ).map wT).sum ≤
    (harmonic 3 : ℚ) * ∑ j ∈ ({3} : Finset (Fin 4)), wT j :=
  sum_greedy_le_harmonic_card_mul (by decide +kernel) (by decide) (by decide)

/-- The bound is not vacuous here: `H 3 · 11/10 = 121/60`, and `11/6 < 121/60`. -/
example : (harmonic 3 : ℚ) * ∑ j ∈ ({3} : Finset (Fin 4)), wT j = 121 / 60 := by
  decide +kernel

/-! ### 2. An unweighted instance: largest set first -/

/-- A set of size four and two sets of size three on `Fin 6`. -/
def P : Fin 3 → Finset (Fin 6)
  | 0 => {0, 1, 2, 3}
  | 1 => {0, 2, 4}
  | 2 => {1, 3, 5}

/-- Greedy takes the large set `0` first, then both others; `{1, 2}` alone covers `Fin 6`. -/
example : greedy P (fun _ => (1 : ℚ)) [0, 1, 2] Finset.univ = [0, 1, 2] := by decide +kernel

example : ∀ a : Fin 6, ∃ j ∈ ({1, 2} : Finset (Fin 3)), a ∈ P j := by decide

/-- The `H d` bound with `d = 3`, the largest size of a set in the cover `{1, 2}`:
`3 ≤ H 3 · 2 = 11/3`. -/
example : ((greedy P (fun _ => (1 : ℚ)) [0, 1, 2] Finset.univ).map fun _ => (1 : ℚ)).sum ≤
    (harmonic 3 : ℚ) * ∑ _j ∈ ({1, 2} : Finset (Fin 3)), (1 : ℚ) :=
  sum_greedy_le_harmonic_mul (by decide +kernel) (by decide) (fun a _ => by revert a; decide)
    (by decide)

/-! ### 3. A fractional cover -/

/-- The three edges of a triangle on `Fin 3`. -/
def E : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}

/-- Weight `1/2` on each edge covers each vertex exactly once. -/
theorem half_cover (a : Fin 3) (_ : a ∈ Finset.univ) :
    1 ≤ ∑ j ∈ (Finset.univ : Finset (Fin 3)) with a ∈ E j, (1 / 2 : ℚ) := by
  revert a
  decide +kernel

example : greedy E (fun _ => (1 : ℚ)) [0, 1, 2] Finset.univ = [0, 1] := by decide +kernel

/-- Against the fractional cover of cost `3/2`: `2 ≤ H 2 · 3/2 = 9/4`. -/
example : ((greedy E (fun _ => (1 : ℚ)) [0, 1, 2] Finset.univ).map fun _ => (1 : ℚ)).sum ≤
    (harmonic 2 : ℚ) * ∑ _j ∈ (Finset.univ : Finset (Fin 3)), (1 / 2 : ℚ) * 1 :=
  sum_greedy_le_harmonic_mul_fractional (by decide +kernel) (by decide)
    (fun _ _ => by norm_num) half_cover (by decide)

/-- Every integral cover of the triangle uses two edges, so the fractional optimum `3/2` is
strictly smaller than the integral optimum. -/
example : ∀ C : Finset (Fin 3), (∀ a : Fin 3, ∃ j ∈ C, a ∈ E j) → 2 ≤ C.card := by decide

/-! ### 4. Edge cases -/

/-- Ties go to the earliest candidate of the list. -/
example : greedy E (fun _ => (1 : ℚ)) [2, 1, 0] Finset.univ = [2, 1] := by decide +kernel

/-- The empty ground set needs no sets. -/
example : greedy T wT [0, 1, 2, 3] ∅ = [] := by decide +kernel

/-- Without set `2`, element `2` of `Fin 3` cannot be covered: the loop stops after covering
`{0, 1}`. -/
example : greedy T wT [0, 1] Finset.univ = [0, 1] := by decide +kernel

example : ¬ ∀ a ∈ (Finset.univ : Finset (Fin 3)), ∃ i ∈ greedy T wT [0, 1] Finset.univ,
    a ∈ T i := by
  decide +kernel

end ComplexityTests.SetCoverGreedy
