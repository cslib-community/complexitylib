/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Finset.KthLargest
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compression of two-coordinate rows

The local update of [OpenAI2026LogSpace, Section 8.2, (8.5)--(8.6), Lemma 8.1] replaces a
real row by a common default and a bounded number of exceptions. This is the deterministic
compression step of the logspace estimator; no probability or machine-space bound is asserted.

For an old default `(z, 0)`, a floor `ρ`, and an input row `w`, put
`m y = max |w y 0| |w y 1|` and `u = max z (max ρ (rank_n m))`. The new default is
`z' = max u (min (max z (rank_K (w · 0))) (3 * u))`. Every displacement from `(z', 0)`
is clipped to radius `7 * max (m y - 2 * u) 0`.

`Finset.kthLargest` pads with zeros. For a nonnegative old default `z`, taking `max z` of this
rank accounts for the paper's dummy copies of `(z, 0)`. In the size rank this maximum is already
absorbed by `u`. The finite set `s` consists of real endpoint IDs; dummy positions never enter
the support count. Input coordinates may be negative. Positive `n` and `K` suffice for stability;
the later condition `K ≤ n` is not needed for this local result.

## Main definitions

* `Cslib.RowCompression.threshold`, `Cslib.RowCompression.newDefault`: the thresholds.
* `Cslib.RowCompression.update`: the compressed row, as a mathematical function.
* `Cslib.RowCompression.candidates`: a list of possible exceptions, selected by input size.

## Main results

* `Cslib.RowCompression.update_eq_default_of_size_le`: small entries become default.
* `Cslib.RowCompression.update_eq_self_of_three_mul_le`: large entries are unchanged.
* `Cslib.RowCompression.update_mem_Icc`: each coordinate lies between input and default.
* `Cslib.RowCompression.abs_update_sub_le_six_mul`: one update changes a coordinate by at most
  six times its threshold, the local bound used in the subsequent preloss argument.
* `Cslib.RowCompression.le_newDefault`: defaults are nondecreasing.
* `Cslib.RowCompression.card_candidates_lt`: fewer than `n` candidates suffice.
* `Cslib.RowCompression.update_eq_default_of_not_mem_candidates`: the candidate set represents
  the entire row on `s`.
* `Cslib.RowCompression.candidates_subset`: candidates come from the previous list and new IDs.
* `Cslib.RowCompression.abs_update_sub_update_le`: the full update is uniformly 28-Lipschitz.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.2, (8.5)--(8.6), Lemma 8.1 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- The sup norm of a two-coordinate entry. -/
@[expose] noncomputable def entrySize (w : Fin 2 → ℝ) : ℝ := max |w 0| |w 1|

/-- The common default entry `(z, 0)`. -/
@[expose] def defaultEntry (z : ℝ) (ν : Fin 2) : ℝ := if ν = 0 then z else 0

/-- The clipping radius for an entry at threshold `u`. -/
@[expose] noncomputable def radius (u : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  7 * max (entrySize w - 2 * u) 0

/-- Clip each displacement from `(z, 0)` to the entry's radius. -/
@[expose] noncomputable def updateEntry (u z : ℝ) (w : Fin 2 → ℝ) (ν : Fin 2) : ℝ :=
  defaultEntry z ν + max (-radius u w) (min (w ν - defaultEntry z ν) (radius u w))

/-- The size threshold, with dummy copies of the old default included in its rank. -/
@[expose] noncomputable def threshold (s : Finset ι) (n : ℕ) (ρ z : ℝ)
    (w : ι → Fin 2 → ℝ) : ℝ :=
  max z (max ρ (kthLargest n s fun y => entrySize (w y)))

/-- The new nonnegative default; `max z` accounts for dummy copies in the first-coordinate rank.
For nonnegative `z` this is exactly (8.5) of [OpenAI2026LogSpace]. -/
@[expose] noncomputable def newDefault (s : Finset ι) (n K : ℕ) (ρ z : ℝ)
    (w : ι → Fin 2 → ℝ) : ℝ :=
  max (threshold s n ρ z w)
    (min (max z (kthLargest K s fun y => w y 0)) (3 * threshold s n ρ z w))

/-- The compression update of [OpenAI2026LogSpace, (8.6)]. -/
@[expose] noncomputable def update (s : Finset ι) (n K : ℕ) (ρ z : ℝ)
    (w : ι → Fin 2 → ℝ) (y : ι) : Fin 2 → ℝ :=
  updateEntry (threshold s n ρ z w) (newDefault s n K ρ z w) (w y)

/-- A coarse candidate list: every non-default output has input size greater than `u`. -/
@[expose] noncomputable def candidates (s : Finset ι) (n : ℕ) (ρ z : ℝ)
    (w : ι → Fin 2 → ℝ) : Finset ι :=
  {y ∈ s | threshold s n ρ z w < entrySize (w y)}

variable {s : Finset ι} {n K : ℕ} {ρ z : ℝ} {w : ι → Fin 2 → ℝ}

theorem entrySize_nonneg (v : Fin 2 → ℝ) : 0 ≤ entrySize v :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem abs_apply_le_entrySize (v : Fin 2 → ℝ) (ν : Fin 2) : |v ν| ≤ entrySize v := by
  fin_cases ν
  · exact le_max_left _ _
  · exact le_max_right _ _

@[simp]
theorem entrySize_defaultEntry (hz : 0 ≤ z) : entrySize (defaultEntry z) = z := by
  simp [entrySize, defaultEntry, abs_of_nonneg hz, hz]

theorem radius_nonneg (u : ℝ) (v : Fin 2 → ℝ) : 0 ≤ radius u v := by
  unfold radius
  positivity

theorem threshold_nonneg : 0 ≤ threshold s n ρ z w :=
  kthLargest_nonneg.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem le_threshold : z ≤ threshold s n ρ z w := le_max_left _ _

theorem floor_le_threshold : ρ ≤ threshold s n ρ z w :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem threshold_le_newDefault : threshold s n ρ z w ≤ newDefault s n K ρ z w :=
  le_max_left _ _

theorem newDefault_le_three_mul : newDefault s n K ρ z w ≤ 3 * threshold s n ρ z w :=
  max_le (by linarith [threshold_nonneg (s := s) (n := n) (ρ := ρ) (z := z) (w := w)])
    (min_le_right _ _)

theorem le_newDefault : z ≤ newDefault s n K ρ z w :=
  le_threshold.trans threshold_le_newDefault

theorem newDefault_nonneg : 0 ≤ newDefault s n K ρ z w :=
  threshold_nonneg.trans threshold_le_newDefault

theorem updateEntry_eq_default_of_size_le {u b : ℝ} {v : Fin 2 → ℝ}
    (hv : entrySize v ≤ 2 * u) : updateEntry u b v = defaultEntry b := by
  funext ν
  simp [updateEntry, radius, max_eq_right (sub_nonpos.mpr hv)]

theorem updateEntry_eq_self_of_three_mul_le {u b : ℝ} {v : Fin 2 → ℝ}
    (hu : 0 ≤ u) (hb : 0 ≤ b) (hb' : b ≤ 3 * u) (hv : 3 * u ≤ entrySize v) :
    updateEntry u b v = v := by
  have hr : radius u v = 7 * (entrySize v - 2 * u) := by
    rw [radius, max_eq_left (by linarith)]
  funext ν
  have hν := abs_apply_le_entrySize v ν
  have hd : |defaultEntry b ν| ≤ 3 * u := by
    unfold defaultEntry
    split_ifs
    · simpa [abs_of_nonneg hb] using hb'
    · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hu
  have hdiff : |v ν - defaultEntry b ν| ≤ radius u v := by
    calc |v ν - defaultEntry b ν| ≤ |v ν| + |defaultEntry b ν| := abs_sub _ _
      _ ≤ radius u v := by rw [hr]; linarith
  rw [updateEntry, min_eq_left (abs_le.mp hdiff).2,
    max_eq_right (abs_le.mp hdiff).1, add_sub_cancel]

private theorem add_clip_mem_Icc (b x r : ℝ) (hr : 0 ≤ r) :
    b + max (-r) (min (x - b) r) ∈ Set.Icc (min x b) (max x b) := by
  rcases le_total x b with h | h
  · rw [min_eq_left h, max_eq_right h, min_eq_left (by linarith : x - b ≤ r)]
    exact ⟨by linarith [le_max_right (-r) (x - b)],
      by have := max_le (by linarith : -r ≤ 0) (sub_nonpos.mpr h); linarith⟩
  · rw [min_eq_right h, max_eq_left h]
    have hlo : 0 ≤ max (-r) (min (x - b) r) :=
      (le_min (sub_nonneg.mpr h) hr).trans (le_max_right _ _)
    have hhi : max (-r) (min (x - b) r) ≤ x - b :=
      max_le (by linarith) (min_le_left _ _)
    exact ⟨by linarith, by linarith⟩

theorem updateEntry_mem_Icc (u b : ℝ) (v : Fin 2 → ℝ) (ν : Fin 2) :
    updateEntry u b v ν ∈ Set.Icc (min (v ν) (defaultEntry b ν))
      (max (v ν) (defaultEntry b ν)) :=
  add_clip_mem_Icc _ _ _ (radius_nonneg _ _)

/-- Clipping toward the default changes a coordinate by no more than its distance to it. -/
theorem abs_updateEntry_sub_le (u b : ℝ) (v : Fin 2 → ℝ) (ν : Fin 2) :
    |updateEntry u b v ν - v ν| ≤ |v ν - defaultEntry b ν| := by
  have h := updateEntry_mem_Icc u b v ν
  rcases le_total (v ν) (defaultEntry b ν) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle] at h
    rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith [h.2]
  · rw [min_eq_right hle, max_eq_left hle] at h
    rw [abs_of_nonpos (sub_nonpos.mpr h.2), abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith [h.1]

/-- Entries of size at most twice the threshold become the new default. -/
theorem update_eq_default_of_size_le {y : ι}
    (hy : entrySize (w y) ≤ 2 * threshold s n ρ z w) :
    update s n K ρ z w y = defaultEntry (newDefault s n K ρ z w) :=
  updateEntry_eq_default_of_size_le hy

/-- Entries of size at least three times the threshold are preserved, including signed entries. -/
theorem update_eq_self_of_three_mul_le {y : ι}
    (hy : 3 * threshold s n ρ z w ≤ entrySize (w y)) : update s n K ρ z w y = w y :=
  updateEntry_eq_self_of_three_mul_le threshold_nonneg newDefault_nonneg newDefault_le_three_mul hy

/-- Compression moves each coordinate toward the new default without overshooting. -/
theorem update_mem_Icc (y : ι) (ν : Fin 2) :
    update s n K ρ z w y ν ∈ Set.Icc (min (w y ν) (defaultEntry (newDefault s n K ρ z w) ν))
      (max (w y ν) (defaultEntry (newDefault s n K ρ z w) ν)) :=
  updateEntry_mem_Icc _ _ _ _

/-- The local change bound used before the first overflow in [OpenAI2026LogSpace, Section 8.3].
When the threshold equals the prescribed floor `ρ`, each coordinate changes by at most `6 * ρ`.
This does not yet sum changes over a schedule or prove the later weighted preloss estimate. -/
theorem abs_update_sub_le_six_mul (y : ι) (ν : Fin 2) :
    |update s n K ρ z w y ν - w y ν| ≤ 6 * threshold s n ρ z w := by
  by_cases hy : 3 * threshold s n ρ z w ≤ entrySize (w y)
  · rw [update_eq_self_of_three_mul_le hy, sub_self, abs_zero]
    exact mul_nonneg (by norm_num) threshold_nonneg
  have hm : entrySize (w y) < 3 * threshold s n ρ z w := lt_of_not_ge hy
  have hb : |defaultEntry (newDefault s n K ρ z w) ν| ≤ 3 * threshold s n ρ z w := by
    unfold defaultEntry
    split_ifs
    · rw [abs_of_nonneg newDefault_nonneg]
      exact newDefault_le_three_mul
    · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (threshold_nonneg (s := s) (n := n) (ρ := ρ) (z := z) (w := w))
  calc |update s n K ρ z w y ν - w y ν|
      ≤ |w y ν - defaultEntry (newDefault s n K ρ z w) ν| := abs_updateEntry_sub_le _ _ _ _
    _ ≤ |w y ν| + |defaultEntry (newDefault s n K ρ z w) ν| := abs_sub _ _
    _ ≤ 6 * threshold s n ρ z w := by linarith [abs_apply_le_entrySize (w y) ν]

/-- The coarse candidate list is strictly smaller than the capacity, hence also at most `n`. -/
theorem card_candidates_lt (hn : 0 < n) : #(candidates s n ρ z w) < n := by
  apply Nat.lt_of_not_ge
  intro h
  have hlt := (lt_kthLargest_iff hn threshold_nonneg).mpr h
  exact (not_lt_of_ge ((le_max_right _ _).trans (le_max_right _ _))) hlt

/-- Outside the candidate list every real endpoint has the new default value. -/
theorem update_eq_default_of_not_mem_candidates {y : ι} (hy : y ∈ s)
    (hnot : y ∉ candidates s n ρ z w) :
    update s n K ρ z w y = defaultEntry (newDefault s n K ρ z w) := by
  have hle : entrySize (w y) ≤ threshold s n ρ z w := by
    simpa only [candidates, mem_filter, hy, true_and, not_lt] using hnot
  have hnonneg : 0 ≤ threshold s n ρ z w := threshold_nonneg
  exact update_eq_default_of_size_le (by linarith)

open scoped Classical in
/-- The exact exception set is smaller than `n`, regardless of coincidences with the default. -/
theorem card_exceptions_lt (hn : 0 < n) :
    #{y ∈ s | update s n K ρ z w y ≠ defaultEntry (newDefault s n K ρ z w)} < n := by
  refine (card_le_card ?_).trans_lt (card_candidates_lt (s := s) (ρ := ρ) (z := z) (w := w) hn)
  intro y hy
  simp only [mem_filter] at hy
  by_contra h
  exact hy.2 (update_eq_default_of_not_mem_candidates hy.1 h)

/-- Candidates can be selected entirely from any set containing the non-default input IDs.
Use the union of the previous exception list and the newly touched IDs for that set. -/
theorem candidates_subset (hz : 0 ≤ z) (t : Finset ι)
    (hw : ∀ y ∈ s, y ∉ t → w y = defaultEntry z) : candidates s n ρ z w ⊆ t := by
  intro y hy
  obtain ⟨hys, hy⟩ := mem_filter.mp hy
  by_contra hyt
  rw [hw y hys hyt, entrySize_defaultEntry hz] at hy
  exact (not_lt_of_ge le_threshold) hy

/-! ## Stability independent of the row width -/

private theorem abs_max_sub_max_le {a b c d ε : ℝ} (ha : |a - c| ≤ ε)
    (hb : |b - d| ≤ ε) : |max a b - max c d| ≤ ε :=
  (abs_max_sub_max_le_max _ _ _ _).trans (max_le ha hb)

private theorem abs_min_sub_min_le {a b c d ε : ℝ} (ha : |a - c| ≤ ε)
    (hb : |b - d| ≤ ε) : |min a b - min c d| ≤ ε :=
  (abs_min_sub_min_le_max _ _ _ _).trans (max_le ha hb)

theorem abs_entrySize_sub_entrySize_le {v v' : Fin 2 → ℝ} {δ : ℝ}
    (h : ∀ ν, |v ν - v' ν| ≤ δ) : |entrySize v - entrySize v'| ≤ δ :=
  abs_max_sub_max_le ((abs_abs_sub_abs_le _ _).trans (h 0))
    ((abs_abs_sub_abs_le _ _).trans (h 1))

theorem abs_defaultEntry_sub_defaultEntry_le {b b' δ : ℝ} (hδ : 0 ≤ δ)
    (hb : |b - b'| ≤ δ) (ν : Fin 2) : |defaultEntry b ν - defaultEntry b' ν| ≤ δ := by
  unfold defaultEntry
  split_ifs
  · exact hb
  · simpa using hδ

variable {z' δ : ℝ} {w' : ι → Fin 2 → ℝ}

/-- The threshold varies by at most the sup perturbation of the row and old default. -/
theorem abs_threshold_sub_threshold_le (hn : 0 < n) (hδ : 0 ≤ δ) (hz : |z - z'| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |w y ν - w' y ν| ≤ δ) :
    |threshold s n ρ z w - threshold s n ρ z' w'| ≤ δ := by
  refine abs_max_sub_max_le hz (abs_max_sub_max_le (by simpa using hδ) ?_)
  exact abs_kthLargest_sub_kthLargest_le hn hδ fun y hy =>
    abs_entrySize_sub_entrySize_le (hw y hy)

/-- The default has Lipschitz constant three, uniformly in the capacities and row width. -/
theorem abs_newDefault_sub_newDefault_le (hn : 0 < n) (hK : 0 < K) (hδ : 0 ≤ δ)
    (hz : |z - z'| ≤ δ) (hw : ∀ y ∈ s, ∀ ν, |w y ν - w' y ν| ≤ δ) :
    |newDefault s n K ρ z w - newDefault s n K ρ z' w'| ≤ 3 * δ := by
  have hu := abs_threshold_sub_threshold_le (ρ := ρ) hn hδ hz hw
  have hq : |max z (kthLargest K s fun y => w y 0) -
      max z' (kthLargest K s fun y => w' y 0)| ≤ δ :=
    abs_max_sub_max_le hz (abs_kthLargest_sub_kthLargest_le hK hδ fun y hy => hw y hy 0)
  refine abs_max_sub_max_le (hu.trans (by linarith))
    (abs_min_sub_min_le (hq.trans (by linarith)) ?_)
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  exact mul_le_mul_of_nonneg_left hu (by norm_num)

/-- The radius is 21-Lipschitz jointly in the entry and the threshold. -/
theorem abs_radius_sub_radius_le {u u' : ℝ} {v v' : Fin 2 → ℝ} (hδ : 0 ≤ δ)
    (hu : |u - u'| ≤ δ) (hv : ∀ ν, |v ν - v' ν| ≤ δ) :
    |radius u v - radius u' v'| ≤ 21 * δ := by
  have hm := abs_entrySize_sub_entrySize_le hv
  have hsub : |(entrySize v - 2 * u) - (entrySize v' - 2 * u')| ≤ 3 * δ := by
    calc |(entrySize v - 2 * u) - (entrySize v' - 2 * u')|
        = |(entrySize v - entrySize v') - 2 * (u - u')| := by congr 1; ring
      _ ≤ |entrySize v - entrySize v'| + |2 * (u - u')| := abs_sub _ _
      _ ≤ 3 * δ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hmax := abs_max_sub_max_le (b := 0) (d := 0) hsub
    (by simpa using (show 0 ≤ 3 * δ by positivity))
  unfold radius
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
  linarith

/-- The update is 28-Lipschitz in the row and old default, with the floor and capacities fixed.
The estimate is on real endpoints `y ∈ s`; it is independent of their number and magnitudes. -/
theorem abs_update_sub_update_le (hn : 0 < n) (hK : 0 < K) (hδ : 0 ≤ δ)
    (hz : |z - z'| ≤ δ) (hw : ∀ y ∈ s, ∀ ν, |w y ν - w' y ν| ≤ δ)
    {y : ι} (hy : y ∈ s) (ν : Fin 2) :
    |update s n K ρ z w y ν - update s n K ρ z' w' y ν| ≤ 28 * δ := by
  have hu := abs_threshold_sub_threshold_le (ρ := ρ) hn hδ hz hw
  have hb := abs_newDefault_sub_newDefault_le (ρ := ρ) hn hK hδ hz hw
  have hbν := abs_defaultEntry_sub_defaultEntry_le (by positivity : 0 ≤ 3 * δ) hb ν
  have hr := abs_radius_sub_radius_le hδ hu (hw y hy)
  have hd : |(w y ν - defaultEntry (newDefault s n K ρ z w) ν) -
      (w' y ν - defaultEntry (newDefault s n K ρ z' w') ν)| ≤ 4 * δ := by
    calc _ = |(w y ν - w' y ν) -
          (defaultEntry (newDefault s n K ρ z w) ν -
            defaultEntry (newDefault s n K ρ z' w') ν)| := by congr 1; ring
      _ ≤ |w y ν - w' y ν| + |defaultEntry (newDefault s n K ρ z w) ν -
          defaultEntry (newDefault s n K ρ z' w') ν| := abs_sub _ _
      _ ≤ 4 * δ := by linarith [hw y hy ν]
  have hneg : |-radius (threshold s n ρ z w) (w y) -
      -radius (threshold s n ρ z' w') (w' y)| ≤ 21 * δ := by
    simpa only [neg_sub_neg, abs_sub_comm] using hr
  have hclip := abs_max_sub_max_le hneg
    (abs_min_sub_min_le (hd.trans (by linarith : 4 * δ ≤ 21 * δ)) hr)
  unfold update updateEntry
  calc _ ≤ |defaultEntry (newDefault s n K ρ z w) ν -
          defaultEntry (newDefault s n K ρ z' w') ν| +
        |max (-radius (threshold s n ρ z w) (w y))
            (min (w y ν - defaultEntry (newDefault s n K ρ z w) ν)
              (radius (threshold s n ρ z w) (w y))) -
          max (-radius (threshold s n ρ z' w') (w' y))
            (min (w' y ν - defaultEntry (newDefault s n K ρ z' w') ν)
              (radius (threshold s n ρ z' w') (w' y)))| := by
          rw [add_sub_add_comm]
          exact abs_add_le _ _
    _ ≤ 28 * δ := by linarith

end Cslib.RowCompression
