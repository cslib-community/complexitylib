/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Preloss
public import Complexity.Foundations.Analysis.RowCompression.Reference
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith

/-!
# The stationary reference constructed from actual preloss

At the input of zero-based group `j`, the stationary reference in
[OpenAI2026LogSpace, Lemma 8.2] has the current default and row `truth + loss`, where `loss` is
the actual compressed prefix minus its uncompressed counterpart. `stationaryState` constructs
this state from `iterate`; `stationaryContinuation` runs the remaining capacities and floors
from their original indices, with no further increments.

For the explicit scaled dyadic floors, absence of overflow in groups `i < j ≤ m` bounds this
loss by `η / 100`. Consequently a true row with nonnegative first coordinates and second
coordinates of magnitude at most `η / 2` produces a reference with first coordinates at least
`-η` and second coordinates of magnitude at most `η`. The stationary preservation theorem then
applies to the actual remaining schedule. Its entry-support, rank-gate, and flat-region
hypotheses are scalar properties of the row output, not an assumed preservation conclusion.

Under explicit scalar support, flatness and root-Lipschitz laws, weighted preloss also controls
the reference's discrepancy from the true zero-padded output. A lower clipping at `η` removes
the influence of targets below `η / 2`, while rank stability controls the sensitive targets.
This comparison allows any exponent satisfying the stated scalar law; instantiating those laws
for all of the paper's row functions remains a separate obligation.

The zero-based prefix loss here is the paper's `L_{j-1}` before its group `j`. The floors are
the explicitly documented margin-scaled witness from `RowCompression.Floors`. This module
does not assert a post-overflow comparison with the incremented calculation or a machine-space
bound.

## Main definitions

* `Cslib.RowCompression.stationaryState`: the true row plus the actual accumulated preloss.
* `Cslib.RowCompression.stationaryContinuation`: the reference's shifted zero-increment run.

## Main results

* `Cslib.RowCompression.abs_stationaryState_row_sub_le_dyadic`: uniform small preloss.
* `Cslib.RowCompression.stationaryState_bounds_dyadic`: the constructed reference's shape.
* `Cslib.RowCompression.stationaryContinuation_output_eq_dyadic`: preservation along the
  remaining compression schedule.
* `Cslib.RowCompression.abs_stationaryState_root_sub_le_weighted_dyadic`: a weighted
  root-discrepancy bound under explicit scalar root-Lipschitz and support laws.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, Lemma 8.2, stationary-reference construction, preservation, and root comparison
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- The reference at a prefix has the current default and the true row plus the compression
loss already accumulated by the actual calculation. -/
@[expose] noncomputable def stationaryState (s : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (truth : ι → Fin 2 → ℝ) (j : ℕ) : State ι :=
  { defaultValue := (iterate s n K ρ Δ a j).defaultValue
    row := fun y ν => truth y ν +
      ((iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν) }

/-- Continue the constructed reference with the actual capacities and floors starting at
group `j`, a fixed positive rank in applications, and no further increments. -/
@[expose] noncomputable def stationaryContinuation (s : Finset ι) (n : ℕ → ℕ) (K : ℕ)
    (ρ : ℕ → ℝ) (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (truth : ι → Fin 2 → ℝ)
    (j r : ℕ) : State ι :=
  iterate s (fun i => n (j + i)) (fun _ => K) (fun i => ρ (j + i)) (fun _ => 0)
    (stationaryState s n (fun _ => K) ρ Δ a truth j) r

variable {s : Finset ι} {n K : ℕ → ℕ} {ρ : ℕ → ℝ}
  {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {truth : ι → Fin 2 → ℝ} {η : ℝ}

/-- The reference's discrepancy from truth is exactly the actual compression loss. -/
theorem stationaryState_row_sub (j : ℕ) (y : ι) (ν : Fin 2) :
    (stationaryState s n K ρ Δ a truth j).row y ν - truth y ν =
      (iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν := by
  simp only [stationaryState, add_sub_cancel_left]

private theorem six_sum_prefix_dyadicFloor_le (hη : 0 ≤ η) {m j : ℕ} (hj : j ≤ m) :
    6 * ∑ i ∈ range j, dyadicFloor η m i ≤ η / 100 := by
  have hsum : ∑ i ∈ range j, dyadicFloor η m i ≤ ∑ i ∈ range m, dyadicFloor η m i :=
    sum_le_sum_of_subset_of_nonneg (range_mono hj) (fun i _ _ => dyadicFloor_nonneg hη m i)
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans
    (six_sum_range_dyadicFloor_le_scale hη m)

/-- The constructed reference differs from truth by at most `η / 100` before overflow.
The numerical bound comes from the actual dyadic schedule, not an assumed error budget. -/
theorem abs_stationaryState_row_sub_le_dyadic (hη : 0 ≤ η) (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j, stepThreshold s n K (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (y : ι) (ν : Fin 2) :
    |(stationaryState s n K (dyadicFloor η m) Δ a truth j).row y ν - truth y ν| ≤ η / 100 := by
  rw [stationaryState_row_sub]
  exact (abs_iterate_sub_uncompressed_le_of_no_overflow j hno y ν).trans
    (six_sum_prefix_dyadicFloor_le hη hj)

/-- The true-row bounds and the proved preloss bound imply the shape needed by stationary
compression preservation. The reference row itself need not be nonnegative. -/
theorem stationaryState_bounds_dyadic (hη : 0 ≤ η) (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j, stepThreshold s n K (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ η / 2) :
    (∀ y ∈ s, -η ≤ (stationaryState s n K (dyadicFloor η m) Δ a truth j).row y 0) ∧
      ∀ y ∈ s, |(stationaryState s n K (dyadicFloor η m) Δ a truth j).row y 1| ≤ η := by
  constructor
  · intro y hy
    have h := (abs_le.mp (abs_stationaryState_row_sub_le_dyadic (truth := truth)
      hη m j hj hno y 0)).1
    linarith [hfirst y hy]
  · intro y hy
    have h := abs_le.mp (abs_stationaryState_row_sub_le_dyadic (truth := truth)
      hη m j hj hno y 1)
    have ht := abs_le.mp (hsecond y hy)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A small initial default remains below the flat-rank threshold before overflow. This is
useful when comparing the padded reference rank to the true row's zero-padded rank. -/
theorem stationaryState_defaultValue_le_dyadic (hη : 0 ≤ η)
    (ha : 0 ≤ a.defaultValue) (haη : a.defaultValue ≤ η / 2) (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j, stepThreshold s n K (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i) :
    (stationaryState s n K (dyadicFloor η m) Δ a truth j).defaultValue ≤ η := by
  have h := le_of_abs_le (abs_iterate_defaultValue_sub_le_of_no_overflow ha j hno)
  have hsum := six_sum_prefix_dyadicFloor_le hη hj
  change (iterate s n K (dyadicFloor η m) Δ a j).defaultValue ≤ η
  linarith

/-- The stationary reference constructed from actual preloss preserves its output through
any initial segment of the remaining schedule. Only earlier groups must avoid overflow. -/
theorem stationaryContinuation_output_eq_dyadic {K : ℕ} {H : ℝ → ℝ → ℝ → ℝ} {g e : ℝ}
    (hη : 0 ≤ η) (hK : 0 < K) (m j r : ℕ) (hr : j + r ≤ m)
    (hno : ∀ i < j,
      stepThreshold s n (fun _ => K) (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ η / 2)
    (hn : ∀ i, j ≤ i → i < m → K ≤ n i) (hηg : η < g) (hge : 3 * g < e)
    (hentry : ∀ x v q, x ≤ e → H x v q = 0)
    (hgate : ∀ x v q, g ≤ q → H x v q = 0)
    (hflat : ∀ x v q q', q ∈ Set.Icc 0 η → q' ∈ Set.Icc 0 η → H x v q = H x v q')
    (y : ι) (hy : y ∈ s) :
    let b := stationaryState s n (fun _ => K) (dyadicFloor η m) Δ a truth j
    let c := stationaryContinuation s n K (dyadicFloor η m) Δ a truth j r
    H (c.row y 0) (c.row y 1) (firstRank s K c.defaultValue c.row) =
      H (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row) := by
  have hj : j ≤ m := (Nat.le_add_right j r).trans hr
  have hb := stationaryState_bounds_dyadic hη m j hj hno hfirst hsecond
  apply reference_iterate_output_eq hη hK hb.1 hb.2 hηg hge hentry hgate hflat r
  · intro i hi
    exact hn (j + i) (Nat.le_add_right _ _) (by omega)
  · intro i _
    have h := dyadicFloor_le_scale_div hη m (j + i)
    linarith
  · exact hy

/-! ## Weighted discrepancy from the true output -/

/-- Weighted preloss applies at the smaller sensitivity threshold `η / 2` while using the
same floors scaled by `η`. Their explicit size also proves this stronger local margin. -/
theorem abs_stationaryState_row_sub_le_weighted_dyadic (hη : 0 < η) (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j, stepThreshold s n K (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (y : ι) (hd : η / 2 ≤ truth y 0) (ν : Fin 2) :
    |(stationaryState s n K (dyadicFloor η m) Δ a truth j).row y ν - truth y ν| ≤
      (12 * (1 + η / 2) / (η / 2)) * ∑ i ∈ range j,
        dyadicFloor η m i *
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) := by
  rw [stationaryState_row_sub]
  apply abs_iterate_sub_uncompressed_le_weighted (by linarith : 0 < η / 2) hd j hno
  · intro i _
    have h := dyadicFloor_le_scale_div hη.le m i
    linarith
  · intro i hi
    have hsum := six_sum_range_dyadicFloor_le hη.le (hi.trans_le hj)
    have hfloor := dyadicFloor_nonneg hη.le m i
    linarith

private theorem max_rank_le_add_of_clipped {K : ℕ} {f g : ι → ℝ} {δ : ℝ}
    (hK : 0 < K) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (h : ∀ y ∈ s, max η (f y) ≤ max η (g y) + δ) :
    max η (kthLargest K s f) ≤ max η (kthLargest K s g) + δ := by
  have ht : 0 ≤ max η (kthLargest K s g) := hη.trans (le_max_left _ _)
  refine max_le (by linarith [le_max_left η (kthLargest K s g)]) ?_
  by_contra hrank
  have hc := (lt_kthLargest_iff hK (add_nonneg ht hδ)).mp (lt_of_not_ge hrank)
  have hsub : ({y ∈ s | max η (kthLargest K s g) + δ < f y} : Finset ι) ⊆
      {y ∈ s | max η (kthLargest K s g) < g y} := by
    intro y hy
    obtain ⟨hys, hy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hys, ?_⟩
    have hmax : max η (kthLargest K s g) < max η (g y) := by
      linarith [h y hys, le_max_right η (f y)]
    exact (lt_max_iff.mp hmax).resolve_left (not_lt_of_ge (le_max_left _ _))
  have hg := (lt_kthLargest_iff hK ht).mpr (hc.trans (card_le_card hsub))
  exact (not_lt_of_ge (le_max_right _ _)) hg

private theorem abs_clipped_firstRank_sub_le {K : ℕ} {z z' δ : ℝ}
    {w w' : ι → Fin 2 → ℝ} (hK : 0 < K) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hz : z ≤ η) (hz' : z' ≤ η)
    (h : ∀ y ∈ s, |max η (w y 0) - max η (w' y 0)| ≤ δ) :
    |max η (firstRank s K z w) - max η (firstRank s K z' w')| ≤ δ := by
  simp only [firstRank, ← max_assoc, max_eq_left hz, max_eq_left hz']
  rw [abs_sub_le_iff]
  constructor
  · exact sub_le_iff_le_add'.mpr (max_rank_le_add_of_clipped hK hη hδ fun y hy =>
      sub_le_iff_le_add'.mp (le_of_abs_le (h y hy)))
  · exact sub_le_iff_le_add'.mpr (max_rank_le_add_of_clipped hK hη hδ fun y hy =>
      sub_le_iff_le_add'.mp (le_of_abs_le ((abs_sub_comm _ _).trans_le (h y hy))))

private theorem output_eq_lowerClipped {H : ℝ → ℝ → ℝ → ℝ} (hη : 0 ≤ η)
    (hentry : ∀ x v q, x ≤ η → H x v q = 0)
    (hflat : ∀ x v q q', q ∈ Set.Icc 0 η → q' ∈ Set.Icc 0 η → H x v q = H x v q')
    (x v q : ℝ) (hq : 0 ≤ q) : H x v q = H (max η x) v (max η q) := by
  by_cases hx : x ≤ η
  · rw [max_eq_left hx, hentry _ _ _ hx, hentry _ _ _ le_rfl]
  rw [max_eq_right (not_le.mp hx).le]
  by_cases hqη : q ≤ η
  · rw [max_eq_left hqη]
    exact hflat x v q η ⟨hq, hqη⟩ ⟨hη, le_rfl⟩
  rw [max_eq_right (not_le.mp hqη).le]

/-- A weighted discrepancy bound between the constructed stationary reference and truth.

`ε i` bounds the clipped errors of the actual uncompressed prefix at endpoints with true first
coordinate at least `η / 2`.
The scalar root output is assumed Lipschitz on the clipped first-coordinate and rank region;
this is a regularity hypothesis about `H`, independent of the compression calculation.
Targets below `η / 2` remain below entry support by the proved uniform loss bound. Their
possibly larger relative errors therefore do not enter the weighted rank comparison.

This theorem supplies the comparison at the start of the stationary calculation. Combined with
`stationaryContinuation_output_eq_dyadic`, it gives the same bound after its remaining updates.
Verifying these scalar laws for particular row functions is a separate obligation. -/
theorem abs_stationaryState_root_sub_le_weighted_dyadic {K : ℕ}
    {H : ℝ → ℝ → ℝ → ℝ} {p C : ℝ} {ε : ℕ → ℝ}
    (hη : 0 < η) (hK : 0 < K) (hC : 0 ≤ C)
    (ha : 0 ≤ a.defaultValue) (haη : a.defaultValue ≤ η / 2)
    (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j,
      stepThreshold s n (fun _ => K) (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (hε : ∀ i < j, 0 ≤ ε i)
    (herr : ∀ i < j, ∀ y ∈ s, η / 2 ≤ truth y 0 →
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i)
    (hentry : ∀ x v q, x ≤ η → H x v q = 0)
    (hflat : ∀ x v q q', q ∈ Set.Icc 0 η → q' ∈ Set.Icc 0 η → H x v q = H x v q')
    (hroot : ∀ x v q x' v' q', η ≤ x → η ≤ x' → η ≤ q → η ≤ q' →
      |H x v q ^ p - H x' v' q' ^ p| ≤
        C * (|x - x'| + |v - v'| + |q - q'|)) (y : ι) (hy : y ∈ s) :
    let b := stationaryState s n (fun _ => K) (dyadicFloor η m) Δ a truth j
    |H (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row) ^ p -
        H (truth y 0) (truth y 1) (firstRank s K 0 truth) ^ p| ≤
      3 * C * ((12 * (1 + η / 2) / (η / 2)) * ∑ i ∈ range j, dyadicFloor η m i * ε i) := by
  let b := stationaryState s n (fun _ => K) (dyadicFloor η m) Δ a truth j
  let B := (12 * (1 + η / 2) / (η / 2)) * ∑ i ∈ range j, dyadicFloor η m i * ε i
  change |H (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row) ^ p -
    H (truth y 0) (truth y 1) (firstRank s K 0 truth) ^ p| ≤ 3 * C * B
  have hcoef : 0 ≤ 12 * (1 + η / 2) / (η / 2) := by positivity
  have hB : 0 ≤ B := mul_nonneg hcoef (sum_nonneg fun i hi =>
    mul_nonneg (dyadicFloor_nonneg hη.le m i) (hε i (mem_range.mp hi)))
  have huniform (y : ι) (ν : Fin 2) : |b.row y ν - truth y ν| ≤ η / 100 :=
    abs_stationaryState_row_sub_le_dyadic hη.le m j hj hno y ν
  have hweighted (y : ι) (hy : y ∈ s) (hd : η / 2 ≤ truth y 0) (ν : Fin 2) :
      |b.row y ν - truth y ν| ≤ B := by
    refine (abs_stationaryState_row_sub_le_weighted_dyadic hη m j hj hno y hd ν).trans ?_
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (herr i (mem_range.mp hi) y hy hd)
        (dyadicFloor_nonneg hη.le m i)) hcoef
  have hlow (y : ι) (hy : truth y 0 < η / 2) : b.row y 0 ≤ η ∧ truth y 0 ≤ η := by
    have h := le_of_abs_le (huniform y 0)
    constructor <;> linarith
  have hclipped (y : ι) (hy : y ∈ s) : |max η (b.row y 0) - max η (truth y 0)| ≤ B := by
    by_cases hd : η / 2 ≤ truth y 0
    · exact (abs_max_sub_max_le_max _ _ _ _).trans
        (max_le (by simpa using hB) (hweighted y hy hd 0))
    · have hl := hlow y (not_le.mp hd)
      simpa only [max_eq_left hl.1, max_eq_left hl.2, sub_self, abs_zero] using hB
  have hrank : |max η (firstRank s K b.defaultValue b.row) -
      max η (firstRank s K 0 truth)| ≤ B :=
    abs_clipped_firstRank_sub_le hK hη.le hB
      (stationaryState_defaultValue_le_dyadic hη.le ha haη m j hj hno) hη.le hclipped
  by_cases hd : η / 2 ≤ truth y 0
  · rw [output_eq_lowerClipped hη.le hentry hflat _ _ _ firstRank_nonneg,
      output_eq_lowerClipped hη.le hentry hflat _ _ _ firstRank_nonneg]
    calc _ ≤ C * (|max η (b.row y 0) - max η (truth y 0)| + |b.row y 1 - truth y 1| +
          |max η (firstRank s K b.defaultValue b.row) - max η (firstRank s K 0 truth)|) :=
        hroot _ _ _ _ _ _ (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      _ ≤ C * (B + B + B) := mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (hclipped y hy) (hweighted y hy hd 1)) hrank) hC
      _ = 3 * C * B := by ring
  · have hl := hlow y (not_le.mp hd)
    rw [hentry _ _ _ hl.1, hentry _ _ _ hl.2, sub_self, abs_zero]
    positivity

end Cslib.RowCompression
