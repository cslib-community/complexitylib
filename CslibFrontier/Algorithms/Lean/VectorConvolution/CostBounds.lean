/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.VectorConvolution
public import CslibFrontier.Foundations.Combinatorics.CubeCounts

/-!
# Explicit cost bounds for convolution in `[r]^d`

The exact tick count of `Cslib.Algorithms.Lean.VectorConvolution.solveM` (`time_solveM`) counts
the vectors of the cube `[r]^d` of size at most `s` and, for each query `C`, the vectors below `C`
of size at least `s`. With the counting bounds of
`CslibFrontier.Foundations.Combinatorics.CubeCounts` this gives explicit bounds for queries of
size `t` and `d` coordinates ([ChanItakuraMaYu2026], Lemma 3.2 with the estimates in the proof
of Theorem 3.4):

* `time_solveM_le`: if `s ≤ d (r - 1) / 2 - ε`, at most
  `3 (r d + 1) (r ^ d exp (-2 ε ^ 2 / (d (r - 1) ^ 2)) + |Cs| ∑_{j ≤ t - s} (t choose j))`;
* `time_solveM_le_of_le_mul`: if `s ≤ (1 - δ) d (r - 1) / 2`, at most
  `3 (r d + 1) (r ^ d exp (-δ ^ 2 d / 2) + |Cs| ∑_{j ≤ t - s} (t choose j))`.

These are inequalities for every `r`, `d`, `s`, `t` and every list of queries; the choice of `r`,
`δ` and `d` that gives the exponent of [ChanItakuraMaYu2026], Corollary 3.5, is not made here.

## Main results

* `Cslib.Algorithms.Lean.VectorConvolution.time_solveM_le`,
  `Cslib.Algorithms.Lean.VectorConvolution.time_solveM_le_of_le_mul`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.VectorConvolution

open Finset Real

universe u

variable {ι : Type u} [DecidableEq ι] [Fintype ι] {R : Type u} [CommRing R] {l : List ι}

omit [DecidableEq ι] in
private theorem length_eq_card (hl : l.Nodup) (hall : ∀ i, i ∈ l) : l.length = Fintype.card ι := by
  classical
  rw [← List.toFinset_card_of_nodup hl, ← card_univ]
  congr 1
  exact eq_univ_of_forall fun i => List.mem_toFinset.mpr (hall i)

/-- The query part of the cost: at most `∑_{j ≤ t - s} (t choose j)` cells per query of size
`t`. -/
private theorem sum_card_high_le {s t : ℕ} {Cs : List (ι → ℕ)} (hCs : ∀ C ∈ Cs, ∑ i, C i = t) :
    (Cs.map fun C => #((Iic C).filter fun y => s ≤ ∑ i, y i)).sum ≤
      Cs.length * ∑ j ∈ range (t - s + 1), t.choose j := by
  have := List.sum_le_length_nsmul (Cs.map fun C => #((Iic C).filter fun y => s ≤ ∑ i, y i))
    (∑ j ∈ range (t - s + 1), t.choose j) fun x hx => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx
      simpa [hCs C hC] using card_Iic_filter_le_sum_le C s
  simpa using this

/-- The cost of `solveM` for queries of size `t`, given any bound `B` on the number of small
vectors of the cube. -/
private theorem time_solveM_le_of_card_le (hl : l.Nodup) (hall : ∀ i, i ∈ l) {r s t : ℕ} {B : ℝ}
    (hlow : (#((Fintype.piFinset fun _ : ι => range r).filter fun x => ∑ i, x i ≤ s) : ℝ) ≤ B)
    (f g : (ι → ℕ) → R) {Cs : List (ι → ℕ)} (hCs : ∀ C ∈ Cs, ∑ i, C i = t) :
    ((solveM l r s f g Cs).time : ℝ) ≤ 3 * (r * Fintype.card ι + 1) *
      (B + Cs.length * ∑ j ∈ range (t - s + 1), (t.choose j : ℝ)) := by
  rw [time_solveM hl hall, length_eq_card hl hall]
  have hhigh : ((Cs.map fun C => #((Iic C).filter fun y => s ≤ ∑ i, y i)).sum : ℝ) ≤
      Cs.length * ∑ j ∈ range (t - s + 1), (t.choose j : ℝ) := by
    exact_mod_cast sum_card_high_le hCs
  push_cast at hhigh ⊢
  exact mul_le_mul_of_nonneg_left (add_le_add hlow hhigh) (by positivity)

/-- **Explicit cost of convolution in `[r]^d`**: for queries of size `t` and a threshold
`s ≤ d (r - 1) / 2 - ε`, `solveM` takes at most
`3 (r d + 1) (r ^ d exp (-2 ε ^ 2 / (d (r - 1) ^ 2)) + |Cs| ∑_{j ≤ t - s} (t choose j))` ticks. -/
theorem time_solveM_le (hl : l.Nodup) (hall : ∀ i, i ∈ l) {r s t : ℕ} (hr : 0 < r) {ε : ℝ}
    (hε : 0 ≤ ε) (hs : (s : ℝ) ≤ Fintype.card ι * (r - 1) / 2 - ε) (f g : (ι → ℕ) → R)
    {Cs : List (ι → ℕ)} (hCs : ∀ C ∈ Cs, ∑ i, C i = t) :
    ((solveM l r s f g Cs).time : ℝ) ≤ 3 * (r * Fintype.card ι + 1) *
      (r ^ Fintype.card ι * exp (-2 * ε ^ 2 / (Fintype.card ι * (r - 1) ^ 2)) +
        Cs.length * ∑ j ∈ range (t - s + 1), (t.choose j : ℝ)) :=
  time_solveM_le_of_card_le hl hall (card_cube_sum_le_le hr hε hs) f g hCs

/-- **Explicit cost, relative threshold**: for queries of size `t` and `s ≤ (1 - δ) d (r - 1) / 2`,
`solveM` takes at most `3 (r d + 1) (r ^ d exp (-δ ^ 2 d / 2) + |Cs| ∑_{j ≤ t - s} (t choose j))`
ticks. -/
theorem time_solveM_le_of_le_mul (hl : l.Nodup) (hall : ∀ i, i ∈ l) {r s t : ℕ} (hr : 1 < r)
    {δ : ℝ} (hδ : 0 ≤ δ) (hs : (s : ℝ) ≤ (1 - δ) * (Fintype.card ι * (r - 1) / 2))
    (f g : (ι → ℕ) → R) {Cs : List (ι → ℕ)} (hCs : ∀ C ∈ Cs, ∑ i, C i = t) :
    ((solveM l r s f g Cs).time : ℝ) ≤ 3 * (r * Fintype.card ι + 1) *
      (r ^ Fintype.card ι * exp (-(δ ^ 2 * Fintype.card ι / 2)) +
        Cs.length * ∑ j ∈ range (t - s + 1), (t.choose j : ℝ)) :=
  time_solveM_le_of_card_le hl hall (card_cube_sum_le_le_of_le_mul hr hδ hs) f g hCs

end Cslib.Algorithms.Lean.VectorConvolution
