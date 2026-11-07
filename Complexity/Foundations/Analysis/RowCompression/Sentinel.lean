/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Reference
import Mathlib.Tactic.Linarith

/-!
# Exact sentinel replacement under row compression

Replace the first coordinate at a finite set of marked endpoints by one common positive
sentinel, leaving every second coordinate unchanged. When the modified first rank and size
threshold are at most `R ≥ 0`, and both old and sentinel first coordinates at marked endpoints
are strictly above `3R`, the original and modified calculations have identical ranks, thresholds,
and new defaults. Compression is identity in both channels at marked endpoints, and sentinel
replacement commutes with the actual update on every retained endpoint.

The proof uses `Finset.kthLargest_eq_of_eq_or_gt`, including its boundary case where a rank equals
the ceiling. It preserves actual padded ranks, rather than only clipped ranks. No bound on the
largest original entry is needed. The modified first-rank bound also implies that fewer than
`K` retained endpoints can be marked.

This is the exact rank and update step in the sentinel argument of [OpenAI2026LogSpace,
Lemma 8.3], when the proof removes its modification of first coordinates above `L₁`. It does not
identify or store sentinels in the algorithm. Maintaining the large-coordinate bounds through
later increments, iterating the comparison, upper saturation of row outputs, and the full
post-overflow stability estimate remain separate. No root exponent or machine-resource bound
is asserted here.

## Main definitions

* `Cslib.RowCompression.sentinelFirst`: change only the marked first coordinates.

## Main results

* `Cslib.RowCompression.firstRank_eq_sentinelFirst`,
  `Cslib.RowCompression.threshold_eq_sentinelFirst`,
  `Cslib.RowCompression.newDefault_eq_sentinelFirst`: exact invariance below the ceiling.
* `Cslib.RowCompression.update_eq_self_of_mem_sentinelFirst`: both channels at marked endpoints
  are in the actual compression identity region.
* `Cslib.RowCompression.sentinelFirst_update`: one-step commutation on retained endpoints.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, proof of Lemma 8.3, the sentinel replacement and its removal
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

open scoped Classical in
/-- Replace marked first coordinates by one sentinel, keeping every second coordinate. -/
@[expose] noncomputable def sentinelFirst (marked : Finset ι) (L : ℝ)
    (w : ι → Fin 2 → ℝ) (y : ι) (ν : Fin 2) : ℝ :=
  if y ∈ marked ∧ ν = 0 then L else w y ν

variable {s marked : Finset ι} {n K : ℕ} {ρ z R L : ℝ} {w : ι → Fin 2 → ℝ} {y : ι}

theorem sentinelFirst_zero_of_mem (hy : y ∈ marked) : sentinelFirst marked L w y 0 = L := by
  simp [sentinelFirst, hy]

theorem sentinelFirst_one : sentinelFirst marked L w y 1 = w y 1 := by
  simp [sentinelFirst]

theorem sentinelFirst_of_not_mem (hy : y ∉ marked) : sentinelFirst marked L w y = w y := by
  funext ν
  simp [sentinelFirst, hy]

/-- A padded first rank below the ceiling is unchanged by replacing larger first coordinates. -/
theorem firstRank_eq_sentinelFirst (hK : 0 < K) (hR : 0 ≤ R) (hL : R < L)
    (hw : ∀ y ∈ s, y ∈ marked → R < w y 0)
    (hq : firstRank s K z (sentinelFirst marked L w) ≤ R) :
    firstRank s K z w = firstRank s K z (sentinelFirst marked L w) := by
  have hrank : kthLargest K s (fun y => w y 0) =
      kthLargest K s (fun y => sentinelFirst marked L w y 0) := by
    apply kthLargest_eq_of_eq_or_gt hK hR _ (kthLargest_le_firstRank.trans hq)
    intro y hy
    by_cases hm : y ∈ marked
    · exact Or.inr ⟨hw y hy hm, by rwa [sentinelFirst_zero_of_mem hm]⟩
    · exact Or.inl (congrFun (sentinelFirst_of_not_mem hm) 0).symm
  exact congrArg (max z) hrank

/-- The actual size threshold is unchanged, including its floor and old-default terms. -/
theorem threshold_eq_sentinelFirst (hn : 0 < n) (hR : 0 ≤ R) (hL : R < L)
    (hw : ∀ y ∈ s, y ∈ marked → R < w y 0)
    (hu : threshold s n ρ z (sentinelFirst marked L w) ≤ R) :
    threshold s n ρ z w = threshold s n ρ z (sentinelFirst marked L w) := by
  have hrank : kthLargest n s (fun y => entrySize (w y)) =
      kthLargest n s (fun y => entrySize (sentinelFirst marked L w y)) := by
    apply kthLargest_eq_of_eq_or_gt hn hR _
      (((le_max_right _ _).trans (le_max_right _ _)).trans hu)
    intro y hy
    by_cases hm : y ∈ marked
    · refine Or.inr ⟨(hw y hy hm).trans_le
        ((le_abs_self _).trans (abs_apply_le_entrySize _ 0)), ?_⟩
      have hs : R < sentinelFirst marked L w y 0 := by rwa [sentinelFirst_zero_of_mem hm]
      exact hs.trans_le ((le_abs_self _).trans (abs_apply_le_entrySize _ 0))
    · exact Or.inl (congrArg entrySize (sentinelFirst_of_not_mem hm)).symm
  exact congrArg (fun q => max z (max ρ q)) hrank

/-- Both actual rank quantities, and consequently the new default, agree exactly. -/
theorem newDefault_eq_sentinelFirst (hn : 0 < n) (hK : 0 < K) (hR : 0 ≤ R) (hL : R < L)
    (hw : ∀ y ∈ s, y ∈ marked → R < w y 0)
    (hq : firstRank s K z (sentinelFirst marked L w) ≤ R)
    (hu : threshold s n ρ z (sentinelFirst marked L w) ≤ R) :
    newDefault s n K ρ z w = newDefault s n K ρ z (sentinelFirst marked L w) := by
  change max (threshold s n ρ z w) (min (firstRank s K z w) (3 * threshold s n ρ z w)) =
    max (threshold s n ρ z (sentinelFirst marked L w))
      (min (firstRank s K z (sentinelFirst marked L w))
        (3 * threshold s n ρ z (sentinelFirst marked L w)))
  rw [threshold_eq_sentinelFirst hn hR hL hw hu, firstRank_eq_sentinelFirst hK hR hL hw hq]

/-- The bounded modified first rank itself forces strict cardinality of the marked set. -/
theorem card_marked_lt_of_sentinelFirst (hK : 0 < K) (hR : 0 ≤ R) (hL : R < L)
    (hmarked : marked ⊆ s) (hq : firstRank s K z (sentinelFirst marked L w) ≤ R) :
    #marked < K := by
  classical
  refine not_le.mp fun hc => ?_
  have hsub : marked ⊆ {y ∈ s | R < sentinelFirst marked L w y 0} := by
    intro y hy
    exact mem_filter.mpr ⟨hmarked hy, by rwa [sentinelFirst_zero_of_mem hy]⟩
  have hlt := (lt_kthLargest_iff hK hR).mpr (hc.trans (card_le_card hsub))
  exact (not_lt_of_ge (kthLargest_le_firstRank.trans hq)) hlt

/-- Original and sentinel entries are both in the identity region at every marked retained ID.
The second coordinate is untouched, even if it is signed or large. -/
theorem update_eq_self_of_mem_sentinelFirst (hn : 0 < n) (hR : 0 ≤ R) (hL : 3 * R < L)
    (hw : ∀ y ∈ s, y ∈ marked → 3 * R < w y 0)
    (hu : threshold s n ρ z (sentinelFirst marked L w) ≤ R)
    (hy : y ∈ s) (hm : y ∈ marked) :
    update s n K ρ z w y = w y ∧
      update s n K ρ z (sentinelFirst marked L w) y = sentinelFirst marked L w y := by
  have hL' : R < L := by linarith
  have hw' : ∀ y ∈ s, y ∈ marked → R < w y 0 := by
    intro y hy hm
    linarith [hw y hy hm]
  have hu' : threshold s n ρ z w ≤ R :=
    (threshold_eq_sentinelFirst hn hR hL' hw' hu).trans_le hu
  constructor
  · apply update_eq_self_of_three_mul_le
    exact (by linarith [hw y hy hm] : 3 * threshold s n ρ z w ≤ w y 0).trans
      ((le_abs_self _).trans (abs_apply_le_entrySize _ 0))
  · apply update_eq_self_of_three_mul_le
    have hfirst : 3 * R < sentinelFirst marked L w y 0 := by
      rwa [sentinelFirst_zero_of_mem hm]
    exact (by linarith : 3 * threshold s n ρ z (sentinelFirst marked L w) ≤
      sentinelFirst marked L w y 0).trans ((le_abs_self _).trans (abs_apply_le_entrySize _ 0))

/-- Sentinel replacement commutes with the concrete compression update on every retained ID.
This also gives equality of both channels off the marked set; it assumes no row-output law. -/
theorem sentinelFirst_update (hK : 0 < K) (hKn : K ≤ n) (hR : 0 ≤ R) (hL : 3 * R < L)
    (hw : ∀ y ∈ s, y ∈ marked → 3 * R < w y 0)
    (hq : firstRank s K z (sentinelFirst marked L w) ≤ R)
    (hu : threshold s n ρ z (sentinelFirst marked L w) ≤ R) (hy : y ∈ s) :
    sentinelFirst marked L (update s n K ρ z w) y =
      update s n K ρ z (sentinelFirst marked L w) y := by
  have hn : 0 < n := hK.trans_le hKn
  by_cases hm : y ∈ marked
  · obtain ⟨ho, hs⟩ := update_eq_self_of_mem_sentinelFirst hn hR hL hw hu hy hm
    rw [hs]
    funext ν
    simp only [sentinelFirst, ho]
  · have hL' : R < L := by linarith
    have hw' : ∀ y ∈ s, y ∈ marked → R < w y 0 := by
      intro y hy hm
      linarith [hw y hy hm]
    rw [sentinelFirst_of_not_mem hm]
    unfold update
    rw [threshold_eq_sentinelFirst hn hR hL' hw' hu,
      newDefault_eq_sentinelFirst hn hK hR hL' hw' hq hu, sentinelFirst_of_not_mem hm]

end Cslib.RowCompression
