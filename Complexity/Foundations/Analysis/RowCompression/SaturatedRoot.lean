/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Complexity.Foundations.Analysis.RowCompression.SentinelRelative
import Complexity.Foundations.Analysis.RowCompression.GateClosure
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relative comparison through saturation and exact sentinel coupling

For an output `H d v r`, upper saturation in the first signal and closure at large padded
rank transfer sentinel stability to the actual fourth-root outputs. Both signal coordinates
are retained. The root regularity and range contracts concern the scalar output, independently
of schedules, entry magnitudes and the compression scale. No raw prefix or state is capped.

The proof is extracted from `PolynomialAtomRows.Relative` and extended to a second signal.
Its polynomial specialization recovers the existing public relative comparison. The conclusion
requires a positive horizon, nonnegative true first signal, a small true second signal and
bounded common losses in both coordinates. It is a deterministic comparison, not an integrated
moment bound or a machine-resource theorem.

## Main definitions

* `Cslib.RowCompression.stateRootError`: fourth-root discrepancy of an output depending on
  both signals and the actual default-padded first rank.

## Main results

* `Cslib.RowCompression.exists_iterate_root_bound`: relative stability for saturated outputs
  with a closed rank gate, for every nonnegative prefix-error budget.
-/

public section

universe u

namespace Cslib.RowCompression

open Finset

/-- Fourth-root discrepancy using both signals and each state's actual padded first rank. -/
@[expose] noncomputable def stateRootError (H : ℝ → ℝ → ℝ → ℝ) {ι : Type u}
    (s : Finset ι) (K : ℕ) (a b : State ι) (y : ι) : ℝ :=
  H (a.row y 0) (a.row y 1) (firstRank s K a.defaultValue a.row) ^ (4⁻¹ : ℝ) -
  H (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row) ^ (4⁻¹ : ℝ)

variable {θ η : ℝ} (H : ℝ → ℝ → ℝ → ℝ)
  (hsaturate : ∀ d d' v r, θ ≤ d → θ ≤ d' → H d v r = H d' v r)
include hsaturate

omit hsaturate in
private theorem three_mul_scale_le_of_small_error {d e raw loss : ℝ}
    (hθ : 0 < θ) (hmargin : η ≤ θ / 10000) (hd : 16 * (θ + 1) < d)
    (he : e ≤ 1 / 8) (hraw : |raw - d| ≤ (1 + d) * e) (hloss : |loss| ≤ η / 2) :
    3 * θ ≤ raw + loss := by
  have hd0 : 0 ≤ 1 + d := by linarith
  have he' := mul_le_mul_of_nonneg_left he hd0
  have hr := (abs_le.mp hraw).1
  have hl := (abs_le.mp hloss).1
  nlinarith

private theorem eval_iterate_eq_sentinel {ι : Type u} {s : Finset ι} {n : ℕ → ℕ}
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
    H (actual.row y 0) (actual.row y 1) (firstRank s K actual.defaultValue actual.row) =
      H (modified.row y 0) (modified.row y 1)
        (firstRank s K modified.defaultValue modified.row) := by
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
  change H (actual.row y 0) (actual.row y 1) (firstRank s K actual.defaultValue actual.row) =
    H (modified.row y 0) (modified.row y 1) (firstRank s K modified.defaultValue modified.row)
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
    change H (actual.row y 0) (actual.row y 1) _ =
      H (sentinelFirst marked L actual.row y 0) (sentinelFirst marked L actual.row y 1) _
    rw [sentinelFirst_zero_of_mem hmarked, sentinelFirst_one]
    exact hsaturate _ _ _ _ hv (by dsimp only [L]; linarith)
  · change H (actual.row y 0) (actual.row y 1) _ =
      H (sentinelFirst marked L actual.row y 0) (sentinelFirst marked L actual.row y 1) _
    rw [sentinelFirst_of_not_mem hmarked]

variable (R : ℝ) (hR : 0 ≤ R)
  (hrange : ∀ {ι : Type u} (s : Finset ι) (K : ℕ) (a b : State ι) (y : ι),
    |stateRootError H s K a b y| ≤ R)
  (hrootExists : ∃ A : ℝ, 0 ≤ A ∧ ∀ d v r d' v' r',
    |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
      A * (|d - d'| + |v - v'| + |r - r'|))
  (hgate : ∀ d v r, θ ≤ r → H d v r = 0)
include hR hrange hrootExists hgate

/-- Relative fourth-root comparison for a saturated output with a closed rank gate.
The input scalar contracts are independent of all schedules and entry magnitudes. -/
theorem exists_iterate_root_bound (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ) (ρ : ℕ → ℝ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (truth raw₀ loss : ι → Fin 2 → ℝ) (z η : ℝ) (K : ℕ),
      0 < η → η ≤ θ / 10000 → z ≤ η → 0 < K →
      ∀ (m : ℕ), 0 < m → (∀ i < m, K ≤ n i) → (∀ i < m, ρ i ≤ η) →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
      (∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2) →
      ∀ (ε : ℕ → ℝ), (∀ i ≤ m, 0 ≤ ε i) →
      (∀ i ≤ m, ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw₀ i y) ≤ ε i) →
      ∀ y ∈ s,
      |stateRootError H s K
        (iterate s n (fun _ => K) ρ Δ ⟨z, raw₀ + loss⟩ m)
        (iterate s n (fun _ => K) ρ (fun _ => 0) ⟨z, truth + loss⟩ m) y| ≤
        C * prefixErrorBudget ε m := by
  classical
  obtain ⟨A, hA, hroot⟩ := hrootExists
  let L := 16 * (16 * (θ + 1) + 1)
  let c := 1 + L
  have hc1 : 1 ≤ c := by dsimp only [c, L]; linarith
  have hc0 : 0 ≤ c := by linarith
  refine ⟨(8 * R + 3 * A) * c, mul_nonneg (by positivity) hc0, ?_⟩
  intro ι s n ρ Δ truth raw₀ loss z η K hη hmargin hz hK m hm hKn hρ
    hfirst hsecond hloss ε hε herr y hy
  let a : State ι := ⟨z, raw₀ + loss⟩
  let b : State ι := ⟨z, truth + loss⟩
  let actual := iterate s n (fun _ => K) ρ Δ a m
  let reference := iterate s n (fun _ => K) ρ (fun _ => 0) b m
  let E := prefixErrorBudget ε m
  have hE0 : 0 ≤ E := prefixErrorBudget_nonneg hε
  change |stateRootError H s K actual reference y| ≤ (8 * R + 3 * A) * c * E
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
      have ha := eval_iterate_eq_sentinel H hsaturate hθ hη.le hmargin hz hK m hm hKn hρ
        hfirst hsecond hloss hcount hε herr hsmall y hy
      change H (actual.row y 0) (actual.row y 1) (firstRank s K actual.defaultValue actual.row) =
        H (modified.row y 0) (modified.row y 1)
          (firstRank s K modified.defaultValue modified.row) at ha
      have hb := eval_iterate_eq_sentinel H hsaturate (Δ := fun _ => 0) (raw₀ := truth)
        (ε := fun _ => 0) hθ hη.le hmargin hz hK m hm hKn hρ
        hfirst hsecond hloss hcount (by intros; norm_num)
        (by intros; simp [uncompressedRow, clippedError])
        (by simp [prefixErrorBudget]) y hy
      have hzero (D : Finset ι) : sentinelFirst D 0 (0 : ι → Fin 2 → ℝ) = 0 := by
        funext y ν
        simp [sentinelFirst]
      dsimp only at hb
      rw [hzero] at hb
      change H (reference.row y 0) (reference.row y 1)
        (firstRank s K reference.defaultValue reference.row) =
        H (modifiedReference.row y 0) (modifiedReference.row y 1)
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
            |modified.row y 1 - modifiedReference.row y 1| +
            |firstRank s K modified.defaultValue modified.row -
              firstRank s K modifiedReference.defaultValue modifiedReference.row|) :=
          hroot _ _ _ _ _ _
        _ ≤ A * (c * E + c * E + c * E) := mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (hs.2 y hy 0) (hs.2 y hy 1)) hq) hA
        _ ≤ (8 * R + 3 * A) * c * E := by
          nlinarith [mul_nonneg hc0 hE0, mul_nonneg hR (mul_nonneg hc0 hE0)]
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
      have ha := hgate (actual.row y 0) (actual.row y 1) _ hqa
      have hb := hgate (reference.row y 0) (reference.row y 1) _ hqb
      unfold stateRootError
      rw [ha, hb, sub_self, abs_zero]
      positivity
  · apply (hrange s K actual reference y).trans
    have hlarge := not_le.mp hsmall
    have hpositive := mul_nonneg hA (mul_nonneg hc0 hE0)
    nlinarith

end Cslib.RowCompression
