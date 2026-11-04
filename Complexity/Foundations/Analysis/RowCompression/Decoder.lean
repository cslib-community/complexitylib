/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.BoundedCap
public import Complexity.Foundations.Analysis.RowCompression.SaturatedRoot
public import Complexity.Foundations.Analysis.RowCompression.Reference
import Complexity.Foundations.Data.Finset.KthLargest.Truncation

/-!
# Saturated decoder comparison

The shared deterministic accuracy kernel accepts a decoder with bounded, Lipschitz fourth
root and an upper saturation threshold. No monotonicity of its numerator is required.
The common-loss proof is extracted from the hierarchy atom specialization; the iteration
comparison reuses the cap-free compression engine and its stationary reference law.
These results assume raw clipped-prefix errors, not output accuracy. Deriving those errors
from a recursive history is a separate obligation.
-/

public section
universe u
namespace Cslib.RowCompression
open Finset
open scoped BigOperators

/-- Common-loss comparison with arbitrary nonnegative truth and bounded first loss.
Only the decoder is saturated; raw signals and compression defaults retain their units. -/
theorem boundedLoss_decoder_bound (H : ℝ → ℝ → ℝ → ℝ) {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hsat : ∀ d v r, H d v r = H (min T d) v (min T r))
    (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
    {L : ℝ} (hL : 0 ≤ L) (hroot : ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        L * (|d - d'| + |v - v'| + |r - r'|))
    {K : ℕ} (hK : 0 < K) :
    ∀ {ι : Type*} (s : Finset ι) (z : ℝ)
      (truth raw loss : ι → Fin 2 → ℝ),
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |loss y 0| ≤ T) →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ≤ ε) →
      ∀ y ∈ s, |stateRootError H s K ⟨z, raw + loss⟩ ⟨z, truth + loss⟩ y| ≤
        (4 * R + L * (2 * (4 * T + 5) + 1)) * ε := by
  let B := 4*T+5
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  intro ι s z truth raw loss hfirst hloss ε hε herr y hy
  by_cases hs : ε ≤ 1/2
  · have he (x : ι) (hx : x ∈ s) := abs_sub_le_of_clippedError_le
      (hfirst x hx) (by linarith : ε < 1) (herr x hx)
    have hc (x : ι) (hx : x ∈ s) :
        |min T ((raw+loss) x 0)-min T ((truth+loss) x 0)| ≤ B*ε :=
      abs_min_add_sub_min_add_le hT hε hs (he x hx).1 (hloss x hx)
    have hq : |min T (firstRank s K z (raw+loss))-
        min T (firstRank s K z (truth+loss))| ≤ B*ε := by
      simp only [firstRank, min_max_distrib_left]
      rw [← kthLargest_min (f := fun x => (raw+loss) x 0) hK hT.le,
        ← kthLargest_min (f := fun x => (truth+loss) x 0) hK hT.le]
      exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le
        (by simpa only [sub_self, abs_zero] using mul_nonneg hB hε)
        (abs_kthLargest_sub_kthLargest_le hK (mul_nonneg hB hε) hc))
    unfold stateRootError
    rw [hsat, hsat ((truth+loss) y 0)]
    apply (hroot _ _ _ _ _ _).trans
    have hv : |(raw+loss) y 1-(truth+loss) y 1| ≤ ε := by
      simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using (he y hy).2
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hc y hy) hv) hq) hL
    nlinarith [mul_nonneg hR hε]
  · have ha := hrange ((raw+loss) y 0) ((raw+loss) y 1) (firstRank s K z (raw+loss))
    have hb := hrange ((truth+loss) y 0) ((truth+loss) y 1) (firstRank s K z
      (truth+loss))
    change 0 ≤ _ ∧ _ ≤ R at ha hb
    have hh : |stateRootError (H) s K ⟨z,raw+loss⟩
      ⟨z,truth+loss⟩ y| ≤ R :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    apply hh.trans
    have he : 1/2 < ε := not_le.mp hs
    nlinarith [mul_nonneg (by positivity : 0 ≤ L*(2*B+1)) hε]

/-- Existential form of the explicit common-loss decoder coefficient. -/
theorem exists_boundedLoss_decoder_bound (H : ℝ → ℝ → ℝ → ℝ) {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hsat : ∀ d v r, H d v r = H (min T d) v (min T r))
    (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
    (hdist : ∃ L : ℝ, 0 ≤ L ∧ ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        L * (|d - d'| + |v - v'| + |r - r'|))
    {K : ℕ} (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι) (z : ℝ)
      (truth raw loss : ι → Fin 2 → ℝ),
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |loss y 0| ≤ T) →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (raw y) ≤ ε) →
      ∀ y ∈ s, |stateRootError H s K ⟨z, raw + loss⟩ ⟨z, truth + loss⟩ y| ≤ C * ε := by
  obtain ⟨L, hL, hroot⟩ := hdist
  exact ⟨4 * R + L * (2 * (4 * T + 5) + 1), by positivity,
    boundedLoss_decoder_bound H hT hR hsat hrange hL hroot hK⟩

/-- Accuracy against the uncompressed truth from all actual raw-prefix clipped errors.
The decoder constant precedes the scale, schedule, horizon and input rows. Stationary
reference preservation removes the comparison iterate; no true-entry cap is assumed. -/
theorem iterate_truth_root_bound (H : ℝ → ℝ → ℝ → ℝ) {T R e g f L : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R)
    (hsat : ∀ d d' v r, T ≤ d → T ≤ d' → H d v r = H d' v r)
    (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
    (hL : 0 ≤ L) (hdist : ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        L * (|d - d'| + |v - v'| + |r - r'|))
    (hgT : g ≤ T) (hge : 3 * g < e) (hfg : f < g)
    (hentry : ∀ d v r, d ≤ e → H d v r = 0)
    (hgate : ∀ d v r, g ≤ r → H d v r = 0)
    (hflat : ∀ d v q r, q ≤ f → r ≤ f → H d v q = H d v r) :
    ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (floors : ℕ → ℝ) (Δ : ℕ → ι → Fin 2 → ℝ)
      (truth raw : ι → Fin 2 → ℝ) (scale : ℝ) (K m : ℕ),
      0 < scale → scale ≤ T / 10000 → scale ≤ f → 0 < K → 0 < m →
      (∀ i < m, K ≤ n i) → (∀ i < m, floors i ≤ scale) →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      ∀ ε : ℕ → ℝ, (∀ i ≤ m, 0 ≤ ε i) →
      (∀ i ≤ m, ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw i y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError H s K
        (iterate s n (fun _ => K) floors Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
        ((8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1))) * prefixErrorBudget ε m := by
  have hr {ι : Type u} (s : Finset ι) (K : ℕ) (a b : State ι) (y : ι) :
      |stateRootError H s K a b y| ≤ R := by
    have ha := hrange (a.row y 0) (a.row y 1) (firstRank s K a.defaultValue a.row)
    have hb := hrange (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row)
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  intro ι s n floors Δ truth raw scale K m hs hscale hsf hK hm hn hf hfirst hsecond ε hε herr y hy
  have hc := iterate_root_bound H hsat R hR @hr
    (fun d v r ht => hgate d v r (hgT.trans ht)) hT hL hdist (ι := ι)
  have hb := hc s n floors Δ truth raw 0 0 scale K hs hscale (by linarith) hK m hm hn hf
    hfirst hsecond (by intro y _ ν; simp only [Pi.zero_apply, abs_zero]; linarith)
    ε hε herr y hy
  simp only [add_zero] at hb
  have href := reference_iterate_output_eq (H := H) (a := (⟨0, truth⟩ : State ι)) hs.le hK
    (fun y hy => by have := hfirst y hy; dsimp only; linarith)
    (fun y hy => (hsecond y hy).trans (by linarith)) (hsf.trans_lt hfg) hge hentry hgate
    (fun d v q r hq hr => hflat d v q r (hq.2.trans hsf) (hr.2.trans hsf)) m hn hf y hy
  unfold stateRootError at hb ⊢
  rw [href] at hb
  exact hb

end Cslib.RowCompression
