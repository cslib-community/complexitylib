/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Iteration
import Mathlib.Tactic.Linarith

/-!
# Stationary reference rows under compression

This module proves the stationary-output assertion of [OpenAI2026LogSpace, Lemma 8.2].
The first coordinates of a reference row are at least `-η`, and the absolute values of its
second coordinates are at most `η`. Compression has floor at most `η` and capacity `n ≥ K`.
Write `q` for the `K`-th first-coordinate rank padded by the old default. The actual threshold,
new default and new padded rank are at most `max η q`. If `η < q`, the padded rank is preserved
exactly; otherwise both old and new ranks remain in `[0,η]`. The row bounds are preserved too.

A row output `H(first, second, rank)` is preserved when it is zero below an entry threshold `e`,
zero above a gate-closing rank `g`, and independent of rank within `[0,η]`, where
`η < g` and `3 * g < e`. When the gate is open, entries above `e` are unchanged and entries
below `e` cannot enter the support. The theorem also iterates the concrete updates with no
increments, allowing arbitrary floors at most `η` and capacities at least the fixed rank `K`.

This is output preservation, not equality of whole rows: defaults and small entries may move.
No root-discrepancy bound, comparison with a perturbed reference, or post-overflow error estimate
is asserted. The arithmetic rank includes zero padding; for the source's nonnegative defaults
it agrees with padding by arbitrarily many copies of the default.

## Main definitions

* `Cslib.RowCompression.firstRank`: the padded first-coordinate rank.

## Main results

* `Cslib.RowCompression.reference_threshold_le`: the actual threshold is at most `max η q`.
* `Cslib.RowCompression.reference_firstRank_eq`: ranks above `η` are preserved exactly.
* `Cslib.RowCompression.reference_update_output_eq`: a gated row output is preserved.
* `Cslib.RowCompression.reference_iterate_output_eq`: preservation through zero-increment
  iteration.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, Lemma 8.2, stationary-reference assertion
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- The first-coordinate rank, padded by the old default as well as zero. For a nonnegative
default this is the rank obtained by adjoining arbitrarily many copies of `(z,0)`. -/
@[expose] noncomputable def firstRank (s : Finset ι) (K : ℕ) (z : ℝ)
    (w : ι → Fin 2 → ℝ) : ℝ := max z (kthLargest K s fun y => w y 0)

variable {s : Finset ι} {n K : ℕ} {ρ z η : ℝ} {w : ι → Fin 2 → ℝ}

theorem firstRank_nonneg : 0 ≤ firstRank s K z w :=
  kthLargest_nonneg.trans (le_max_right _ _)

theorem default_le_firstRank : z ≤ firstRank s K z w := le_max_left _ _

theorem kthLargest_le_firstRank : kthLargest K s (fun y => w y 0) ≤ firstRank s K z w :=
  le_max_right _ _

/-- With small negative first coordinates and small second coordinates, size ranks cannot
exceed the first-coordinate rank or `η`, whichever is larger. -/
theorem reference_threshold_le (hη : 0 ≤ η) (hρ : ρ ≤ η) (hK : 0 < K) (hKn : K ≤ n)
    (hfirst : ∀ y ∈ s, -η ≤ w y 0) (hsecond : ∀ y ∈ s, |w y 1| ≤ η) :
    threshold s n ρ z w ≤ max η (firstRank s K z w) := by
  let Q := max η (firstRank s K z w)
  have hηQ : η ≤ Q := le_max_left _ _
  have hqQ : firstRank s K z w ≤ Q := le_max_right _ _
  have hQ0 : 0 ≤ Q := hη.trans hηQ
  have hrank : kthLargest n s (fun y => entrySize (w y)) ≤ Q := by
    by_contra h
    have hcard := (lt_kthLargest_iff (hK.trans_le hKn) hQ0).mp (lt_of_not_ge h)
    have hsub : ({y ∈ s | Q < entrySize (w y)} : Finset ι) ⊆ {y ∈ s | Q < w y 0} := by
      intro y hy
      obtain ⟨hys, hy⟩ := mem_filter.mp hy
      refine mem_filter.mpr ⟨hys, ?_⟩
      by_contra hfirstQ
      have hsize : entrySize (w y) ≤ Q :=
        max_le (abs_le.mpr ⟨by linarith [hfirst y hys], not_lt.mp hfirstQ⟩)
          ((hsecond y hys).trans hηQ)
      exact (not_lt_of_ge hsize) hy
    have hfirstRank : Q < kthLargest K s (fun y => w y 0) :=
      (lt_kthLargest_iff hK hQ0).mpr (hKn.trans (hcard.trans (card_le_card hsub)))
    exact (not_lt_of_ge (kthLargest_le_firstRank.trans hqQ)) hfirstRank
  exact max_le (default_le_firstRank.trans hqQ) (max_le (hρ.trans hηQ) hrank)

/-- The new default is at most the larger of `η` and the old padded rank. -/
theorem reference_newDefault_le (hη : 0 ≤ η) (hρ : ρ ≤ η) (hK : 0 < K) (hKn : K ≤ n)
    (hfirst : ∀ y ∈ s, -η ≤ w y 0) (hsecond : ∀ y ∈ s, |w y 1| ≤ η) :
    newDefault s n K ρ z w ≤ max η (firstRank s K z w) :=
  max_le (reference_threshold_le hη hρ hK hKn hfirst hsecond)
    ((min_le_left _ _).trans (le_max_right _ _))

/-- Moving coordinates toward a nonnegative first-coordinate default and zero second
coordinate preserves the reference row's small negative and second-coordinate bounds. -/
theorem reference_update_bounds (hη : 0 ≤ η) {y : ι}
    (hfirst : -η ≤ w y 0) (hsecond : |w y 1| ≤ η) :
    -η ≤ update s n K ρ z w y 0 ∧ |update s n K ρ z w y 1| ≤ η := by
  have h0 := update_mem_Icc (s := s) (n := n) (K := K) (ρ := ρ) (z := z) (w := w) y 0
  have h1 := update_mem_Icc (s := s) (n := n) (K := K) (ρ := ρ) (z := z) (w := w) y 1
  change min (w y 0) (newDefault s n K ρ z w) ≤ update s n K ρ z w y 0 ∧
    update s n K ρ z w y 0 ≤ max (w y 0) (newDefault s n K ρ z w) at h0
  change min (w y 1) 0 ≤ update s n K ρ z w y 1 ∧
    update s n K ρ z w y 1 ≤ max (w y 1) 0 at h1
  have hznew : 0 ≤ newDefault s n K ρ z w := newDefault_nonneg
  refine ⟨(le_min hfirst (by linarith)).trans h0.1, abs_le.mpr ⟨?_, ?_⟩⟩
  · exact (le_min (abs_le.mp hsecond).1 (by linarith)).trans h1.1
  · exact h1.2.trans (max_le (abs_le.mp hsecond).2 hη)

/-- The new padded rank is at most the larger of `η` and the old padded rank. -/
theorem reference_firstRank_le (hη : 0 ≤ η) (hρ : ρ ≤ η) (hK : 0 < K) (hKn : K ≤ n)
    (hfirst : ∀ y ∈ s, -η ≤ w y 0) (hsecond : ∀ y ∈ s, |w y 1| ≤ η) :
    firstRank s K (newDefault s n K ρ z w) (update s n K ρ z w) ≤
      max η (firstRank s K z w) := by
  let Q := max η (firstRank s K z w)
  have hQ0 : 0 ≤ Q := hη.trans (le_max_left _ _)
  have hb : newDefault s n K ρ z w ≤ Q :=
    reference_newDefault_le hη hρ hK hKn hfirst hsecond
  refine max_le hb ?_
  by_contra h
  have hcard := (lt_kthLargest_iff hK hQ0).mp (lt_of_not_ge h)
  have hsub : ({y ∈ s | Q < update s n K ρ z w y 0} : Finset ι) ⊆
      {y ∈ s | Q < w y 0} := by
    intro y hy
    obtain ⟨hys, hy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hys, ?_⟩
    by_contra hfirstQ
    have hu := (update_mem_Icc (s := s) (n := n) (K := K) (ρ := ρ) (z := z) (w := w) y 0).2
    change update s n K ρ z w y 0 ≤ max (w y 0) (newDefault s n K ρ z w) at hu
    exact (not_lt_of_ge (hu.trans (max_le (not_lt.mp hfirstQ) hb))) hy
  have hfirstRank : Q < kthLargest K s (fun y => w y 0) :=
    (lt_kthLargest_iff hK hQ0).mpr (hcard.trans (card_le_card hsub))
  exact (not_lt_of_ge (kthLargest_le_firstRank.trans (le_max_right _ _))) hfirstRank

/-- Above the flat rank region, the padded rank is preserved exactly. If the new default
does not already equal the old rank, all old rank witnesses lie in the identity region. -/
theorem reference_firstRank_eq (hη : 0 ≤ η) (hρ : ρ ≤ η) (hK : 0 < K) (hKn : K ≤ n)
    (hfirst : ∀ y ∈ s, -η ≤ w y 0) (hsecond : ∀ y ∈ s, |w y 1| ≤ η)
    (hq : η < firstRank s K z w) :
    firstRank s K (newDefault s n K ρ z w) (update s n K ρ z w) = firstRank s K z w := by
  have hu : threshold s n ρ z w ≤ firstRank s K z w := by
    simpa only [max_eq_right hq.le] using
      reference_threshold_le (z := z) hη hρ hK hKn hfirst hsecond
  refine le_antisymm ?_ ?_
  · simpa only [max_eq_right hq.le] using
      reference_firstRank_le (z := z) hη hρ hK hKn hfirst hsecond
  by_cases hqu : firstRank s K z w ≤ 3 * threshold s n ρ z w
  · have hb : newDefault s n K ρ z w = firstRank s K z w := by
      change max (threshold s n ρ z w) (min (firstRank s K z w) (3 * threshold s n ρ z w)) = _
      rw [min_eq_left hqu, max_eq_right hu]
    exact hb ▸ (default_le_firstRank (s := s) (K := K) (z := newDefault s n K ρ z w)
      (w := update s n K ρ z w))
  have h3u : 3 * threshold s n ρ z w < firstRank s K z w := lt_of_not_ge hqu
  have hzq : z < firstRank s K z w := by
    have hz : z ≤ threshold s n ρ z w := le_threshold
    have hu0 : 0 ≤ threshold s n ρ z w := threshold_nonneg
    linarith
  have hqreal : firstRank s K z w ≤ kthLargest K s (fun y => w y 0) := by
    have hmax := le_max_iff.mp
      (show firstRank s K z w ≤ max z (kthLargest K s fun y => w y 0) from le_rfl)
    exact hmax.resolve_left (not_le.mpr hzq)
  have hq0 : 0 < firstRank s K z w := hη.trans_lt hq
  have hcard := (le_kthLargest_iff hK hq0).mp hqreal
  have hsub : ({y ∈ s | firstRank s K z w ≤ w y 0} : Finset ι) ⊆
      {y ∈ s | firstRank s K z w ≤ update s n K ρ z w y 0} := by
    intro y hy
    obtain ⟨hys, hy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hys, ?_⟩
    have hid : update s n K ρ z w y = w y :=
      update_eq_self_of_three_mul_le
        (h3u.le.trans ((hy.trans (le_abs_self _)).trans (abs_apply_le_entrySize (w y) 0)))
    rw [hid]
    exact hy
  exact ((le_kthLargest_iff hK hq0).mpr (hcard.trans (card_le_card hsub))).trans
    kthLargest_le_firstRank

/-- Compression preserves any row output with a separated entry support and rank gate, and
with no rank sensitivity in `[0,η]`. These are the structural hypotheses used in the
stationary-reference part of [OpenAI2026LogSpace, Lemma 8.2]. -/
theorem reference_update_output_eq {H : ℝ → ℝ → ℝ → ℝ} {g e : ℝ}
    (hη : 0 ≤ η) (hρ : ρ ≤ η) (hK : 0 < K) (hKn : K ≤ n)
    (hfirst : ∀ y ∈ s, -η ≤ w y 0) (hsecond : ∀ y ∈ s, |w y 1| ≤ η)
    (hηg : η < g) (hge : 3 * g < e)
    (hentry : ∀ x v r, x ≤ e → H x v r = 0)
    (hgate : ∀ x v r, g ≤ r → H x v r = 0)
    (hflat : ∀ x v q r, q ∈ Set.Icc 0 η → r ∈ Set.Icc 0 η → H x v q = H x v r)
    (y : ι) (_hy : y ∈ s) :
    H (update s n K ρ z w y 0) (update s n K ρ z w y 1)
        (firstRank s K (newDefault s n K ρ z w) (update s n K ρ z w)) =
      H (w y 0) (w y 1) (firstRank s K z w) := by
  let q := firstRank s K z w
  let q' := firstRank s K (newDefault s n K ρ z w) (update s n K ρ z w)
  change H (update s n K ρ z w y 0) (update s n K ρ z w y 1) q' = H (w y 0) (w y 1) q
  by_cases hclosed : g ≤ q
  · have heq : q' = q :=
      reference_firstRank_eq hη hρ hK hKn hfirst hsecond (hηg.trans_le hclosed)
    rw [heq, hgate _ _ _ hclosed, hgate _ _ _ hclosed]
  have hQg : max η q < g := max_lt hηg (lt_of_not_ge hclosed)
  have hg0 : 0 < g := hη.trans_lt hηg
  have hu : threshold s n ρ z w ≤ max η q :=
    reference_threshold_le hη hρ hK hKn hfirst hsecond
  have hb : newDefault s n K ρ z w ≤ max η q :=
    reference_newDefault_le hη hρ hK hKn hfirst hsecond
  have hb_e : newDefault s n K ρ z w ≤ e := by linarith
  by_cases hsmall : w y 0 ≤ e
  · have hcoord := (update_mem_Icc (s := s) (n := n) (K := K) (ρ := ρ) (z := z)
      (w := w) y 0).2
    change update s n K ρ z w y 0 ≤ max (w y 0) (newDefault s n K ρ z w) at hcoord
    have hnew : update s n K ρ z w y 0 ≤ e := hcoord.trans (max_le hsmall hb_e)
    rw [hentry _ _ _ hnew, hentry _ _ _ hsmall]
  have h3u : 3 * threshold s n ρ z w < e := by linarith
  have hid : update s n K ρ z w y = w y :=
    update_eq_self_of_three_mul_le (h3u.le.trans ((lt_of_not_ge hsmall).le.trans
      ((le_abs_self _).trans (abs_apply_le_entrySize (w y) 0))))
  rw [hid]
  by_cases hq : η < q
  · have heq : q' = q := reference_firstRank_eq hη hρ hK hKn hfirst hsecond hq
    rw [heq]
  have hqη : q ≤ η := not_lt.mp hq
  have hq'η : q' ≤ η := by
    have h := reference_firstRank_le (z := z) hη hρ hK hKn hfirst hsecond
    exact h.trans (max_le le_rfl hqη)
  exact hflat _ _ _ _ ⟨firstRank_nonneg, hq'η⟩ ⟨firstRank_nonneg, hqη⟩

section Iteration

variable {n : ℕ → ℕ} {ρ : ℕ → ℝ} {a : State ι}

/-- Zero-increment compression preserves the reference row's coordinate bounds at every
stage. This uses only movement toward the nonnegative default, not rank preservation. -/
theorem reference_iterate_bounds (hη : 0 ≤ η)
    (hfirst : ∀ y ∈ s, -η ≤ a.row y 0) (hsecond : ∀ y ∈ s, |a.row y 1| ≤ η) (j : ℕ) :
    (∀ y ∈ s, -η ≤ (iterate s n (fun _ => K) ρ (fun _ => 0) a j).row y 0) ∧
      ∀ y ∈ s, |(iterate s n (fun _ => K) ρ (fun _ => 0) a j).row y 1| ≤ η := by
  induction j with
  | zero => exact ⟨hfirst, hsecond⟩
  | succ j ih =>
    have h (y : ι) (hy : y ∈ s) := reference_update_bounds (s := s) (n := n j) (K := K)
      (ρ := ρ j) (z := (iterate s n (fun _ => K) ρ (fun _ => 0) a j).defaultValue)
      hη (ih.1 y hy) (ih.2 y hy)
    constructor
    · intro y hy
      simpa only [iterate_succ, advance, add_zero] using (h y hy).1
    · intro y hy
      simpa only [iterate_succ, advance, add_zero] using (h y hy).2

/-- Stationary reference outputs survive any finite zero-increment compression schedule
whose floors are at most `η` and whose capacities are at least the fixed rank `K`.
Neither the row entries, the defaults, nor the chosen exception lists need remain fixed. -/
theorem reference_iterate_output_eq {H : ℝ → ℝ → ℝ → ℝ} {g e : ℝ}
    (hη : 0 ≤ η) (hK : 0 < K)
    (hfirst : ∀ y ∈ s, -η ≤ a.row y 0) (hsecond : ∀ y ∈ s, |a.row y 1| ≤ η)
    (hηg : η < g) (hge : 3 * g < e)
    (hentry : ∀ x v r, x ≤ e → H x v r = 0)
    (hgate : ∀ x v r, g ≤ r → H x v r = 0)
    (hflat : ∀ x v q r, q ∈ Set.Icc 0 η → r ∈ Set.Icc 0 η → H x v q = H x v r)
    (j : ℕ) (hn : ∀ i < j, K ≤ n i) (hρ : ∀ i < j, ρ i ≤ η) (y : ι) (hy : y ∈ s) :
    H ((iterate s n (fun _ => K) ρ (fun _ => 0) a j).row y 0)
        ((iterate s n (fun _ => K) ρ (fun _ => 0) a j).row y 1)
        (firstRank s K (iterate s n (fun _ => K) ρ (fun _ => 0) a j).defaultValue
          (iterate s n (fun _ => K) ρ (fun _ => 0) a j).row) =
      H (a.row y 0) (a.row y 1) (firstRank s K a.defaultValue a.row) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hb := reference_iterate_bounds (n := n) (K := K) (ρ := ρ) hη hfirst hsecond j
    have hstep := reference_update_output_eq (n := n j) (K := K) (ρ := ρ j)
      (z := (iterate s n (fun _ => K) ρ (fun _ => 0) a j).defaultValue)
      (H := H) hη (hρ j (Nat.lt_succ_self j)) hK (hn j (Nat.lt_succ_self j))
      hb.1 hb.2 hηg hge hentry hgate hflat y hy
    have hprev := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
      (fun i hi => hρ i (Nat.lt_succ_of_lt hi))
    simpa only [iterate_succ, advance, add_zero] using hstep.trans hprev

end Iteration

end Cslib.RowCompression
