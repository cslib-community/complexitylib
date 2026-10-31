/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows.RootError
public import Complexity.Foundations.Analysis.RowCompression.GateClosure
public import Complexity.Foundations.Analysis.RowCompression.SentinelRelative
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relative stability of actual polynomial row outputs

The preparation, auxiliary score, and witness have a uniform fourth-root comparison between
the actual compression schedule and the zero-increment reference with the same initial loss.
The coefficient depends only on the chosen function and its support scale. It does not depend
on entry magnitudes, retained width, capacities, horizon, compression scale, or errors.

The proof treats every error budget. A large budget uses the concrete output range. For a
small budget, at least `K` large true entries close both actual padded-rank gates. Otherwise,
common sentinel replacement gives quantitative state stability; upper entry saturation and
exact rank coupling transfer it back to the actual outputs. No final-error, count, threshold
ceiling, or scalar regularity assumption is passed to the public comparison theorem.

## Main results

* `Cslib.PolynomialAtomRow.eval_eq_of_entry_ge`: upper entry saturation for all three functions.
* `Cslib.PolynomialAtomRow.exists_iterate_root_bound`: uniform relative fourth-root stability
  for the actual calculation and its stationary reference, for every error budget.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, Lemma 8.3, specialized to the concrete polynomial fourth-root family
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression

variable (kind : PolynomialAtomRow) {θ η : ℝ}

/-- All three entry factors have saturated by the common sufficient bound `θ`. -/
theorem eval_eq_of_entry_ge {v v' r : ℝ} (hθ : 0 < θ) (hv : θ ≤ v) (hv' : θ ≤ v') :
    kind.eval θ v r = kind.eval θ v' r := by
  cases kind
  · simp only [eval, polynomialPrepRow4,
      polynomialPrepCutoff4_eq_one hθ (by linarith : 3 * θ / 4 ≤ v),
      polynomialPrepCutoff4_eq_one hθ (by linarith : 3 * θ / 4 ≤ v')]
  · simp only [eval, polynomialAuxCutoff4,
      polynomialSwitch4_of_ge (by linarith : θ / 8 < θ / 4) (by linarith : θ / 4 ≤ v),
      polynomialSwitch4_of_ge (by linarith : θ / 8 < θ / 4) (by linarith : θ / 4 ≤ v')]
  · simp only [eval, polynomialWitnessCutoff4,
      polynomialSwitch4_of_ge (by linarith : 82 * θ / 1000 < 90 * θ / 1000)
        (by linarith : 90 * θ / 1000 ≤ v),
      polynomialSwitch4_of_ge (by linarith : 82 * θ / 1000 < 90 * θ / 1000)
        (by linarith : 90 * θ / 1000 ≤ v')]

private theorem gateThreshold_le_scale (hθ : 0 < θ) : kind.gateThreshold θ ≤ θ := by
  cases kind <;> dsimp only [gateThreshold] <;> linarith

private theorem three_mul_scale_le_of_small_error {d e raw loss : ℝ}
    (hθ : 0 < θ) (hmargin : η ≤ θ / 10000) (hd : 16 * (θ + 1) < d)
    (he : e ≤ 1 / 8) (hraw : |raw - d| ≤ (1 + d) * e) (hloss : |loss| ≤ η / 2) :
    3 * θ ≤ raw + loss := by
  have hd0 : 0 ≤ 1 + d := by linarith
  have he' := mul_le_mul_of_nonneg_left he hd0
  have hr := (abs_le.mp hraw).1
  have hl := (abs_le.mp hloss).1
  nlinarith

private theorem eval_iterate_eq_sentinel {ι : Type*} {s : Finset ι} {n : ℕ → ℕ}
    {K : ℕ} {ρ : ℕ → ℝ} {z : ℝ} {truth raw₀ loss : ι → Fin 2 → ℝ}
    {Δ : ℕ → ι → Fin 2 → ℝ} {ε : ℕ → ℝ} (hθ : 0 < θ) (hη : 0 ≤ η)
    (hmargin : η ≤ θ / 10000) (hz : z ≤ η) (hK : 0 < K) (m : ℕ) (hm : 0 < m)
    (hKn : ∀ i < m, K ≤ n i) (hρ : ∀ i < m, ρ i ≤ η)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ η / 2)
    (hloss : ∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2)
    (hcount : #{y ∈ s | 16 * (θ + 1) < truth y 0} < K)
    (hε : ∀ i ≤ m, 0 ≤ ε i)
    (herr : ∀ i ≤ m, ∀ y ∈ s,
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw₀ i y) ≤ ε i)
    (hsmall : (1 + 16 * (16 * (θ + 1) + 1)) * prefixErrorBudget ε m ≤ 1 / 8)
    (y : ι) (hy : y ∈ s) :
    let L := 16 * (16 * (θ + 1) + 1)
    let marked := {y ∈ s | L < truth y 0}
    let a : State ι := ⟨z, raw₀ + loss⟩
    let actual := iterate s n (fun _ => K) ρ Δ a m
    let modified := iterate s n (fun _ => K) ρ
      (fun i => sentinelFirst marked 0 (Δ i)) (sentinelState marked L a) m
    kind.eval θ (actual.row y 0) (firstRank s K actual.defaultValue actual.row) =
      kind.eval θ (modified.row y 0) (firstRank s K modified.defaultValue modified.row) := by
  classical
  let L := 16 * (16 * (θ + 1) + 1)
  let marked := {y ∈ s | L < truth y 0}
  let a : State ι := ⟨z, raw₀ + loss⟩
  let actual := iterate s n (fun _ => K) ρ Δ a m
  let modified := iterate s n (fun _ => K) ρ
    (fun i => sentinelFirst marked 0 (Δ i)) (sentinelState marked L a) m
  have hc := iterate_sentinelState_of_clippedError_le (L₀ := 16 * (θ + 1)) m hη
    (by linarith) hz hK hKn hρ hfirst hsecond hloss hcount hε herr hsmall m (le_refl m)
  change modified = sentinelState marked L actual ∧
    (∀ y ∈ marked, actual.row y = uncompressedRow Δ a.row m y) ∧
    (0 < m → firstRank s K actual.defaultValue actual.row =
      firstRank s K modified.defaultValue modified.row ∧
      firstRank s K modified.defaultValue modified.row ≤ 2 * (16 * (θ + 1)) + 1) at hc
  change kind.eval θ (actual.row y 0) (firstRank s K actual.defaultValue actual.row) =
    kind.eval θ (modified.row y 0) (firstRank s K modified.defaultValue modified.row)
  rw [(hc.2.2 hm).1, hc.1]
  by_cases hmarked : y ∈ marked
  · have hE : prefixErrorBudget ε m ≤ 1 / 8 :=
      (le_mul_of_one_le_left (prefixErrorBudget_nonneg hε)
        (by dsimp only [L]; linarith : 1 ≤ 1 + L)).trans hsmall
    have he : ε m ≤ 1 / 8 := (le_prefixErrorBudget hε (le_refl _)).trans hE
    have hraw := (abs_sub_le_of_clippedError_le (hfirst y hy) (by linarith : ε m < 1)
      (herr m (le_refl m) y hy)).1
    have hd : 16 * (θ + 1) < truth y 0 := by
      have hd := (mem_filter.mp hmarked).2
      dsimp only [L] at hd
      linarith
    have hlarge := three_mul_scale_le_of_small_error hθ hmargin hd he hraw (hloss y hy 0)
    have hv : θ ≤ actual.row y 0 := by
      rw [hc.2.1 y hmarked]
      change θ ≤ uncompressedRow Δ (raw₀ + loss) m y 0
      have heq : uncompressedRow Δ (raw₀ + loss) m y 0 =
          uncompressedRow Δ raw₀ m y 0 + loss y 0 := by
        simp only [uncompressedRow, Pi.add_apply]
        ring
      rw [heq]
      linarith
    change kind.eval θ (actual.row y 0) _ =
      kind.eval θ (sentinelFirst marked L actual.row y 0) _
    rw [sentinelFirst_zero_of_mem hmarked]
    exact kind.eval_eq_of_entry_ge hθ hv (by dsimp only [L]; linarith)
  · change kind.eval θ (actual.row y 0) _ =
      kind.eval θ (sentinelFirst marked L actual.row y 0) _
    rw [sentinelFirst_of_not_mem hmarked]

/-- **Relative stability for the concrete fourth-root family.** The constant is uniform in
all calculation data, including the compression scale. The actual schedule is compared with
the zero-increment reference having the same initial loss. There is no small-error or
heavy-count premise: both count branches and every nonnegative error budget are covered. -/
theorem exists_iterate_root_bound (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ) (ρ : ℕ → ℝ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (truth raw₀ loss : ι → Fin 2 → ℝ) (z η : ℝ) (K : ℕ),
      0 < η → η ≤ θ / 10000 → z ≤ η → 0 < K →
      ∀ (m : ℕ), 0 < m → (∀ i < m, K ≤ n i) → (∀ i < m, ρ i ≤ η) →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
      (∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2) →
      ∀ (ε : ℕ → ℝ), (∀ i ≤ m, 0 ≤ ε i) →
      (∀ i ≤ m, ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw₀ i y) ≤ ε i) →
      ∀ y ∈ s,
      |kind.stateRootError θ s K
        (iterate s n (fun _ => K) ρ Δ ⟨z, raw₀ + loss⟩ m)
        (iterate s n (fun _ => K) ρ (fun _ => 0) ⟨z, truth + loss⟩ m) y| ≤
        C * prefixErrorBudget ε m := by
  classical
  obtain ⟨A, hA, hroot⟩ := kind.exists_abs_eval_root_sub_le θ
  let L := 16 * (16 * (θ + 1) + 1)
  let c := 1 + L
  have hc1 : 1 ≤ c := by dsimp only [c, L]; linarith
  have hc0 : 0 ≤ c := by linarith
  refine ⟨(8 + 2 * A) * c, mul_nonneg (by positivity) hc0, ?_⟩
  intro ι s n ρ Δ truth raw₀ loss z η K hη hmargin hz hK m hm hKn hρ
    hfirst hsecond hloss ε hε herr y hy
  let a : State ι := ⟨z, raw₀ + loss⟩
  let b : State ι := ⟨z, truth + loss⟩
  let actual := iterate s n (fun _ => K) ρ Δ a m
  let reference := iterate s n (fun _ => K) ρ (fun _ => 0) b m
  let E := prefixErrorBudget ε m
  have hE0 : 0 ≤ E := prefixErrorBudget_nonneg hε
  change |kind.stateRootError θ s K actual reference y| ≤ (8 + 2 * A) * c * E
  by_cases hsmall : c * E ≤ 1 / 8
  · have hE : E ≤ 1 / 8 := (le_mul_of_one_le_left hE0 hc1).trans hsmall
    have he (i : ℕ) (hi : i ≤ m) : ε i ≤ 1 / 8 :=
      (le_prefixErrorBudget hε hi).trans hE
    have hεlt (i : ℕ) (hi : i ≤ m) : ε i < 1 := by linarith [he i hi]
    by_cases hcount : #{y ∈ s | 16 * (θ + 1) < truth y 0} < K
    · let marked := {y ∈ s | L < truth y 0}
      let modified := iterate s n (fun _ => K) ρ
        (fun i => sentinelFirst marked 0 (Δ i)) (sentinelState marked L a) m
      let modifiedReference := iterate s n (fun _ => K) ρ
        (fun _ => 0) (sentinelState marked L b) m
      have ha := kind.eval_iterate_eq_sentinel hθ hη.le hmargin hz hK m hm hKn hρ
        hfirst hsecond hloss hcount hε herr hsmall y hy
      change kind.eval θ (actual.row y 0) (firstRank s K actual.defaultValue actual.row) =
        kind.eval θ (modified.row y 0) (firstRank s K modified.defaultValue modified.row) at ha
      have hb := kind.eval_iterate_eq_sentinel (Δ := fun _ => 0) (raw₀ := truth)
        (ε := fun _ => 0) hθ hη.le hmargin hz hK m hm hKn hρ
        hfirst hsecond hloss hcount (by intros; norm_num)
        (by intros; simp [uncompressedRow, clippedError])
        (by simp [prefixErrorBudget]) y hy
      have hzero (D : Finset ι) : sentinelFirst D 0 (0 : ι → Fin 2 → ℝ) = 0 := by
        funext y ν
        simp [sentinelFirst]
      dsimp only at hb
      rw [hzero] at hb
      change kind.eval θ (reference.row y 0) (firstRank s K reference.defaultValue reference.row) =
        kind.eval θ (modifiedReference.row y 0)
          (firstRank s K modifiedReference.defaultValue modifiedReference.row) at hb
      have hs := (iterate_sentinelState_stability_of_clippedError_le
        (ρ := ρ) (L := L) (z := z) (loss := loss) m
        (by dsimp only [L]; linarith) hK (fun i hi => hK.trans_le (hKn i hi))
        hfirst hε hεlt herr).2 m (le_refl m)
      change |modified.defaultValue - modifiedReference.defaultValue| ≤ c * E ∧
        ∀ y ∈ s, ∀ ν, |modified.row y ν - modifiedReference.row y ν| ≤ c * E at hs
      have hq : |firstRank s K modified.defaultValue modified.row -
          firstRank s K modifiedReference.defaultValue modifiedReference.row| ≤ c * E :=
        (abs_max_sub_max_le_max _ _ _ _).trans (max_le hs.1
          (abs_kthLargest_sub_kthLargest_le hK (mul_nonneg hc0 hE0)
            (fun y hy => hs.2 y hy 0)))
      unfold stateRootError
      rw [ha, hb]
      calc
        _ ≤ A * (|modified.row y 0 - modifiedReference.row y 0| +
            |firstRank s K modified.defaultValue modified.row -
              firstRank s K modifiedReference.defaultValue modifiedReference.row|) := hroot _ _ _ _
        _ ≤ A * (c * E + c * E) := mul_le_mul_of_nonneg_left
          (add_le_add (hs.2 y hy 0) hq) hA
        _ ≤ (8 + 2 * A) * c * E := by nlinarith [mul_nonneg hc0 hE0]
    · let D := {y ∈ s | 16 * (θ + 1) < truth y 0}
      have hDs : D ⊆ s := filter_subset _ _
      have hcard : K ≤ #D := not_lt.mp hcount
      have hraw (i : ℕ) (hi : i ≤ m) (y : ι) (hy : y ∈ D) :
          3 * θ ≤ uncompressedRow Δ a.row i y 0 := by
        have hys := hDs hy
        have hd := (mem_filter.mp hy).2
        have hr := (abs_sub_le_of_clippedError_le (hfirst y hys) (hεlt i hi)
          (herr i hi y hys)).1
        have hlarge := three_mul_scale_le_of_small_error hθ hmargin hd (he i hi) hr
          (hloss y hys 0)
        change 3 * θ ≤ uncompressedRow Δ (raw₀ + loss) i y 0
        simpa only [uncompressedRow, Pi.add_apply, add_assoc, add_comm, add_left_comm] using hlarge
      have hreference (i : ℕ) (_hi : i ≤ m) (y : ι) (hy : y ∈ D) :
          3 * θ ≤ uncompressedRow (fun _ => 0) b.row i y 0 := by
        have hd := (mem_filter.mp hy).2
        have hl := (abs_le.mp (hloss y (hDs hy) 0)).1
        simp only [uncompressedRow, Pi.zero_apply, sum_const_zero, add_zero]
        change 3 * θ ≤ truth y 0 + loss y 0
        linarith
      have hqa := le_iterate_firstRank_of_raw_large (s := s) (n := n)
        (K := fun _ => K) (ρ := ρ) hθ hK hDs hcard m hraw
      have hqb := le_iterate_firstRank_of_raw_large (s := s) (n := n)
        (K := fun _ => K) (ρ := ρ) hθ hK hDs hcard m hreference
      have ha := kind.eval_eq_zero_of_rank_ge (v := actual.row y 0) hθ
        ((kind.gateThreshold_le_scale hθ).trans hqa)
      have hb := kind.eval_eq_zero_of_rank_ge (v := reference.row y 0) hθ
        ((kind.gateThreshold_le_scale hθ).trans hqb)
      unfold stateRootError
      rw [ha, hb, sub_self, abs_zero]
      positivity
  · apply (kind.abs_stateRootError_le_one θ s K actual reference y).trans
    have hlarge := not_le.mp hsmall
    have hpositive := mul_nonneg hA (mul_nonneg hc0 hE0)
    nlinarith

end Cslib.PolynomialAtomRow
