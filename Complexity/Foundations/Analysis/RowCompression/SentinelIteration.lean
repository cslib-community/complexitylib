/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Sentinel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Removing sentinels through an actual compression schedule

The modified calculation starts from `sentinelState marked L a` and uses increments
`sentinelFirst marked 0 (Δ i)`. Thus only marked first-channel increments are removed; second
increments are unchanged. If the actual modified input ranks and thresholds are bounded by
`R ≥ 0`, and `3R` plus the total absolute first-channel variation is below every marked initial
first coordinate, the two actual calculations remain coupled at every prefix.

Their defaults agree, the modified full row is the sentinel replacement of the original row,
and both original marked coordinates follow their actual uncompressed prefixes. The latter
fact derives the large-input condition needed at the next step. After every positive prefix,
the padded first ranks also agree and are at most `R`.

This supplies the removal induction in [OpenAI2026LogSpace, Lemma 8.3]. It assumes explicit
ceilings only for the modified calculation; no bound on original compressed inputs or desired
final output is assumed. Deriving the ceilings and variation hypothesis from clipped errors,
upper saturation of row functions, the heavy-count case, and full post-overflow stability remain
separate. No implementation for finding or storing the analytical sentinels is asserted.

## Main definitions

* `Cslib.RowCompression.sentinelState`: preserve the default and replace marked first entries.

## Main results

* `Cslib.RowCompression.firstRank_update_le_of_le`: explicit input rank and threshold ceilings
  bound the updated padded rank, without reference-row shape hypotheses.
* `Cslib.RowCompression.iterate_sentinelState_of_sum_abs_lt`: actual multi-step removal with
  raw-prefix preservation at marked endpoints and exact rank equality after positive prefixes.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, proof of Lemma 8.3, induction removing the sentinel modification
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- Replace marked first entries in a state, retaining its actual common default. -/
@[expose] noncomputable def sentinelState (marked : Finset ι) (L : ℝ) (a : State ι) : State ι :=
  { defaultValue := a.defaultValue, row := sentinelFirst marked L a.row }

/-- Clearing marked first increments makes addition commute exactly with sentinel replacement. -/
theorem sentinelFirst_add (marked : Finset ι) (L : ℝ) (w Δ : ι → Fin 2 → ℝ) :
    sentinelFirst marked L (w + Δ) = sentinelFirst marked L w + sentinelFirst marked 0 Δ := by
  classical
  funext y ν
  by_cases h : y ∈ marked ∧ ν = 0 <;> simp [sentinelFirst, h]

section Update

variable {s marked : Finset ι} {n K : ℕ} {ρ z R L : ℝ} {w : ι → Fin 2 → ℝ}

/-- The updated padded first rank remains below a common input rank and threshold ceiling.
No lower bound on raw first entries or upper bound on second entries is needed. -/
theorem firstRank_update_le_of_le (hK : 0 < K) (hR : 0 ≤ R)
    (hq : firstRank s K z w ≤ R) (hu : threshold s n ρ z w ≤ R) :
    firstRank s K (newDefault s n K ρ z w) (update s n K ρ z w) ≤ R := by
  have hb : newDefault s n K ρ z w ≤ R :=
    max_le hu ((min_le_left _ _).trans hq)
  refine max_le hb ?_
  by_contra h
  have hcard := (lt_kthLargest_iff hK hR).mp (lt_of_not_ge h)
  have hsub : ({y ∈ s | R < update s n K ρ z w y 0} : Finset ι) ⊆
      {y ∈ s | R < w y 0} := by
    intro y hy
    obtain ⟨hys, hy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hys, ?_⟩
    by_contra hfirst
    have hout := (update_mem_Icc (s := s) (n := n) (K := K) (ρ := ρ) (z := z) (w := w) y 0).2
    change update s n K ρ z w y 0 ≤ max (w y 0) (newDefault s n K ρ z w) at hout
    exact (not_lt_of_ge (hout.trans (max_le (not_lt.mp hfirst) hb))) hy
  have hlt := (lt_kthLargest_iff hK hR).mpr (hcard.trans (card_le_card hsub))
  exact (not_lt_of_ge (kthLargest_le_firstRank.trans hq)) hlt

private theorem sentinelFirst_update_all (hmarked : marked ⊆ s)
    (hK : 0 < K) (hKn : K ≤ n) (hR : 0 ≤ R) (hL : 3 * R < L)
    (hw : ∀ y ∈ s, y ∈ marked → 3 * R < w y 0)
    (hq : firstRank s K z (sentinelFirst marked L w) ≤ R)
    (hu : threshold s n ρ z (sentinelFirst marked L w) ≤ R) :
    sentinelFirst marked L (update s n K ρ z w) =
      update s n K ρ z (sentinelFirst marked L w) := by
  funext y
  by_cases hm : y ∈ marked
  · exact sentinelFirst_update hK hKn hR hL hw hq hu (hmarked hm)
  · have hL' : R < L := by linarith
    have hw' : ∀ y ∈ s, y ∈ marked → R < w y 0 := by
      intro y hy hm
      linarith [hw y hy hm]
    rw [sentinelFirst_of_not_mem hm]
    unfold update
    rw [threshold_eq_sentinelFirst (hK.trans_le hKn) hR hL' hw' hu,
      newDefault_eq_sentinelFirst (hK.trans_le hKn) hK hR hL' hw' hq hu,
      sentinelFirst_of_not_mem hm]

private theorem advance_sentinelState {a : State ι} {Δ : ι → Fin 2 → ℝ}
    (hmarked : marked ⊆ s) (hK : 0 < K) (hKn : K ≤ n) (hR : 0 ≤ R) (hL : 3 * R < L)
    (hw : ∀ y ∈ s, y ∈ marked → 3 * R < (a.row + Δ) y 0)
    (hq : firstRank s K a.defaultValue (sentinelFirst marked L (a.row + Δ)) ≤ R)
    (hu : threshold s n ρ a.defaultValue (sentinelFirst marked L (a.row + Δ)) ≤ R) :
    advance s n K ρ (sentinelFirst marked 0 Δ) (sentinelState marked L a) =
      sentinelState marked L (advance s n K ρ Δ a) := by
  have hL' : R < L := by linarith
  have hw' : ∀ y ∈ s, y ∈ marked → R < (a.row + Δ) y 0 := by
    intro y hy hm
    linarith [hw y hy hm]
  unfold advance sentinelState
  rw [← sentinelFirst_add]
  congr 1
  · exact (newDefault_eq_sentinelFirst (hK.trans_le hKn) hK hR hL' hw' hq hu).symm
  · exact (sentinelFirst_update_all hmarked hK hKn hR hL hw hq hu).symm

end Update

section Iteration

variable {s marked : Finset ι} {n : ℕ → ℕ} {K : ℕ} {ρ : ℕ → ℝ} {R L : ℝ}
  {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι}

private theorem raw_first_gt_of_sum_abs_lt {m j : ℕ} {y : ι} (hj : j ≤ m)
    (hvar : 3 * R + ∑ i ∈ range m, |Δ i y 0| < a.row y 0) :
    3 * R < uncompressedRow Δ a.row j y 0 := by
  have hsum : ∑ i ∈ range j, |Δ i y 0| ≤ ∑ i ∈ range m, |Δ i y 0| :=
    sum_le_sum_of_subset_of_nonneg (range_mono hj) (fun _ _ _ => abs_nonneg _)
  have habs : |∑ i ∈ range j, Δ i y 0| ≤ ∑ i ∈ range m, |Δ i y 0| :=
    (abs_sum_le_sum_abs _ _).trans hsum
  have hlo := (abs_le.mp habs).1
  change 3 * R < a.row y 0 + ∑ i ∈ range j, Δ i y 0
  linarith

/-- **Actual multi-step sentinel removal**. Only the modified run's input ranks and thresholds
are assumed bounded. Total raw first-channel variation proves that original marked inputs stay
in the compression identity region. Both original marked channels follow their raw prefixes.

The result also identifies the actual padded ranks after every positive prefix and bounds them
by `R`. No equality or regularity law for final row outputs is assumed. -/
theorem iterate_sentinelState_of_sum_abs_lt (m : ℕ) (hmarked : marked ⊆ s)
    (hK : 0 < K) (hKn : ∀ i < m, K ≤ n i) (hR : 0 ≤ R) (hL : 3 * R < L)
    (hvar : ∀ y ∈ marked, 3 * R + ∑ i ∈ range m, |Δ i y 0| < a.row y 0) :
    let Δ' := fun i => sentinelFirst marked 0 (Δ i)
    let b := sentinelState marked L a
    (∀ i < m, firstRank s K (iterate s n (fun _ => K) ρ Δ' b i).defaultValue
      (inputRow s n (fun _ => K) ρ Δ' b i) ≤ R) →
    (∀ i < m, stepThreshold s n (fun _ => K) ρ Δ' b i ≤ R) →
    ∀ j ≤ m,
      let original := iterate s n (fun _ => K) ρ Δ a j
      let modified := iterate s n (fun _ => K) ρ Δ' b j
      modified = sentinelState marked L original ∧
        (∀ y ∈ marked, original.row y = uncompressedRow Δ a.row j y) ∧
        (0 < j → firstRank s K original.defaultValue original.row =
          firstRank s K modified.defaultValue modified.row ∧
            firstRank s K modified.defaultValue modified.row ≤ R) := by
  let Δ' := fun i => sentinelFirst marked 0 (Δ i)
  let b := sentinelState marked L a
  let A := iterate s n (fun _ => K) ρ Δ a
  let B := iterate s n (fun _ => K) ρ Δ' b
  change (∀ i < m, firstRank s K (B i).defaultValue
      (inputRow s n (fun _ => K) ρ Δ' b i) ≤ R) →
    (∀ i < m, stepThreshold s n (fun _ => K) ρ Δ' b i ≤ R) →
    ∀ j ≤ m, B j = sentinelState marked L (A j) ∧
      (∀ y ∈ marked, (A j).row y = uncompressedRow Δ a.row j y) ∧
      (0 < j → firstRank s K (A j).defaultValue (A j).row =
        firstRank s K (B j).defaultValue (B j).row ∧
          firstRank s K (B j).defaultValue (B j).row ≤ R)
  intro hq hu j
  induction j with
  | zero =>
    intro _
    refine ⟨rfl, ?_, fun h => (Nat.not_lt_zero _ h).elim⟩
    intro y _
    simp only [uncompressedRow_zero, A, iterate_zero]
  | succ j ih =>
    intro hj
    have hjm : j < m := (Nat.lt_succ_self j).trans_le hj
    obtain ⟨heq, hraw, _⟩ := ih ((Nat.le_succ j).trans hj)
    have hinput : inputRow s n (fun _ => K) ρ Δ' b j =
        sentinelFirst marked L (inputRow s n (fun _ => K) ρ Δ a j) := by
      change (B j).row + Δ' j = sentinelFirst marked L ((A j).row + Δ j)
      rw [heq]
      exact (sentinelFirst_add marked L (A j).row (Δ j)).symm
    have hq' : firstRank s K (A j).defaultValue
        (sentinelFirst marked L (inputRow s n (fun _ => K) ρ Δ a j)) ≤ R := by
      have h := hq j hjm
      rw [hinput, heq] at h
      exact h
    have hu' : threshold s (n j) (ρ j) (A j).defaultValue
        (sentinelFirst marked L (inputRow s n (fun _ => K) ρ Δ a j)) ≤ R := by
      have h := hu j hjm
      change threshold s (n j) (ρ j) (B j).defaultValue
        (inputRow s n (fun _ => K) ρ Δ' b j) ≤ R at h
      rw [hinput, heq] at h
      exact h
    have hrawInput (y : ι) (hy : y ∈ marked) :
        inputRow s n (fun _ => K) ρ Δ a j y = uncompressedRow Δ a.row (j + 1) y := by
      funext ν
      change (A j).row y ν + Δ j y ν = _
      rw [hraw y hy, uncompressedRow_succ]
    have hhigh : ∀ y ∈ s, y ∈ marked →
        3 * R < inputRow s n (fun _ => K) ρ Δ a j y 0 := by
      intro y _ hy
      rw [hrawInput y hy]
      exact raw_first_gt_of_sum_abs_lt hj (hvar y hy)
    have hnext : B (j + 1) = sentinelState marked L (A (j + 1)) := by
      change advance s (n j) K (ρ j) (Δ' j) (B j) =
        sentinelState marked L (advance s (n j) K (ρ j) (Δ j) (A j))
      rw [heq]
      exact advance_sentinelState hmarked hK (hKn j hjm) hR hL hhigh hq' hu'
    have hrawNext (y : ι) (hy : y ∈ marked) :
        (A (j + 1)).row y = uncompressedRow Δ a.row (j + 1) y := by
      exact (update_eq_self_of_mem_sentinelFirst (hK.trans_le (hKn j hjm)) hR hL
        hhigh hu' (hmarked hy) hy).1.trans (hrawInput y hy)
    have hbound : firstRank s K (B (j + 1)).defaultValue (B (j + 1)).row ≤ R :=
      firstRank_update_le_of_le hK hR (hq j hjm) (hu j hjm)
    have hfinal : firstRank s K (A (j + 1)).defaultValue (A (j + 1)).row =
        firstRank s K (B (j + 1)).defaultValue (B (j + 1)).row := by
      rw [hnext] at hbound ⊢
      apply firstRank_eq_sentinelFirst hK hR (by linarith) _ hbound
      intro y _ hy
      rw [hrawNext y hy]
      have h := raw_first_gt_of_sum_abs_lt hj (hvar y hy)
      linarith
    exact ⟨hnext, hrawNext, fun _ => ⟨hfinal, hbound⟩⟩

end Iteration

end Cslib.RowCompression
