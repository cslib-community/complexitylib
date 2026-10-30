/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.PMF.UniformSubset
public import Complexity.Computability.WordRAM.Randomized.Expected
import Complexity.Foundations.Analysis.ENNRealTsum

/-!
# Uniform Rejection-Sampling Loop Exit Law on the Randomized Word RAM

This module proves `Cslib.WordRAM.Randomized.loopExitPMF_map_eq_uniformOfFinset`: when a Word-RAM
loop `Code.loop cond body` repeatedly resamples a projection `f : Data r → α` uniformly over a
finite type `α` and exits iff `f y ∈ E` for a nonempty target subset `E : Finset α`, the exit
state distribution `loopExitPMF cond μ_body x` mapped under `f` is the exact conditional uniform
distribution `PMF.uniformOfFinset E`.

## Main results

* `Cslib.WordRAM.Randomized.loopExitPMF_map_eq_uniformOfFinset`: exact conditional-uniform exit law
  under `f` for a uniform rejection-sampling Word-RAM loop.
-/

public section

namespace Cslib.WordRAM.Randomized

open Cslib.Probability
open Cslib.Probability.PMF
open scoped ENNReal

private noncomputable def exitMass {r : ℕ} {α : Type*} [DecidableEq α]
    (cond : Cond r) (μ_body : Data r → PMF (Data r)) (f : Data r → α)
    (K : ℕ) (x : Data r) (θ : α) : ℝ≥0∞ :=
  ∑' y : Data r,
    if θ = f y then Set.indicator {w | ¬cond.Holds w} (loopIterPMF cond μ_body K x) y else 0

private noncomputable def exitWeightSeq (α : Type*) [Fintype α] [Nonempty α] (E : Finset α) :
    ℕ → ℝ≥0∞
  | 0 => 0
  | K + 1 =>
    (Fintype.card α : ℝ≥0∞)⁻¹ +
      (PMF.uniformOfFintype α).toOuterMeasure {θ : α | θ ∉ E} * exitWeightSeq α E K

private theorem exitMass_zero_of_holds {r : ℕ} {α : Type*} [DecidableEq α]
    {cond : Cond r} {μ_body : Data r → PMF (Data r)} {f : Data r → α}
    {x : Data r} (hcx : cond.Holds x) (θ : α) :
    exitMass cond μ_body f 0 x θ = 0 := by
  unfold exitMass
  refine tsum_eq_zero_iff.mpr fun y => ?_
  rw [loopIterPMF_zero]
  by_cases hyx : y = x
  · subst hyx
    have hnot : y ∉ {w | ¬cond.Holds w} := fun h => h hcx
    simp [Set.indicator_of_notMem hnot]
  · simp [PMF.pure_apply, hyx]

private theorem exitMass_of_not_holds {r : ℕ} {α : Type*} [DecidableEq α]
    {cond : Cond r} {μ_body : Data r → PMF (Data r)} {f : Data r → α}
    {x : Data r} (hnc : ¬cond.Holds x) (K : ℕ) (θ : α) :
    exitMass cond μ_body f K x θ = if θ = f x then 1 else 0 := by
  unfold exitMass
  rw [loopIterPMF_of_not_holds hnc, tsum_eq_single x]
  · have hin : x ∈ {w | ¬cond.Holds w} := hnc
    simp [Set.indicator_of_mem hin]
  · intro y hyx
    simp [PMF.pure_apply, hyx]

private theorem exitMass_succ_of_holds {r : ℕ} {α : Type*} [DecidableEq α]
    {cond : Cond r} {μ_body : Data r → PMF (Data r)} {f : Data r → α}
    {x : Data r} (hcx : cond.Holds x) (K : ℕ) (θ : α) :
    exitMass cond μ_body f (K + 1) x θ =
      ∑' z : Data r, μ_body x z * exitMass cond μ_body f K z θ := by
  unfold exitMass
  have hstep : ∀ y : Data r,
      (if θ = f y then
        Set.indicator {w | ¬cond.Holds w} (loopIterPMF cond μ_body (K + 1) x) y else 0) =
      ∑' z : Data r,
        μ_body x z *
          (if θ = f y then
            Set.indicator {w | ¬cond.Holds w} (loopIterPMF cond μ_body K z) y else 0) := by
    intro y
    rw [loopIterPMF_succ, loopStepPMF_of_holds hcx]
    by_cases hθ : θ = f y
    · simp only [hθ, ↓reduceIte]
      by_cases hy : y ∈ {w | ¬cond.Holds w}
      · simp only [Set.indicator_of_mem hy, PMF.bind_apply]
      · simp only [Set.indicator_of_notMem hy, mul_zero, tsum_zero]
    · simp [hθ]
  simp_rw [hstep]
  rw [tsum_comm]
  refine tsum_congr fun z => ?_
  rw [ENNReal.tsum_mul_left]

private theorem exitMass_eq_ite_exitWeightSeq {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {cond : Cond r} {I Q : Data r → Prop} {μ_body : Data r → PMF (Data r)}
    {f : Data r → α} {E : Finset α}
    (hinv : ∀ z, I z → cond.Holds z →
      ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y ∧ (¬cond.Holds y ↔ f y ∈ E))
    (hlaw : ∀ z, I z → cond.Holds z → (μ_body z).map f = PMF.uniformOfFintype α)
    (K : ℕ) {x : Data r} (hIx : I x) (hcx : cond.Holds x) (θ : α) :
    exitMass cond μ_body f K x θ = if θ ∈ E then exitWeightSeq α E K else 0 := by
  induction K generalizing x with
  | zero =>
    rw [exitMass_zero_of_holds hcx, exitWeightSeq]
    split_ifs <;> rfl
  | succ K ih =>
    rw [exitMass_succ_of_holds hcx]
    by_cases hθ : θ ∈ E
    · simp only [hθ, ↓reduceIte, exitWeightSeq]
      have hterm : ∀ z : Data r,
          μ_body x z * exitMass cond μ_body f K z θ =
            (if θ = f z then μ_body x z else 0) +
              ({w : Data r | f w ∉ E}.indicator (μ_body x) z) * exitWeightSeq α E K := by
        intro z
        by_cases hz : z ∈ (μ_body x).support
        · obtain ⟨hloop_z, hiff_z⟩ := hinv x hIx hcx z hz
          rcases hloop_z with ⟨hcz, hIz⟩ | ⟨hncz, _⟩
          · have hfz_not : f z ∉ E := fun h => (hiff_z.mpr h) hcz
            have hne : θ ≠ f z := fun h => hfz_not (h ▸ hθ)
            have hin : z ∈ {w : Data r | f w ∉ E} := hfz_not
            rw [ih hIz hcz, Set.indicator_of_mem hin]
            simp [hθ, hne]
          · have hfz_in : f z ∈ E := hiff_z.mp hncz
            have hnot_in : z ∉ {w : Data r | f w ∉ E} := fun h => h hfz_in
            rw [exitMass_of_not_holds hncz, Set.indicator_of_notMem hnot_in, zero_mul, add_zero]
            split_ifs <;> simp
        · have hz0 : μ_body x z = 0 := (PMF.apply_eq_zero_iff _ _).mpr hz
          by_cases hin : z ∈ {w : Data r | f w ∉ E}
          · rw [Set.indicator_of_mem hin, hz0]
            simp
          · rw [Set.indicator_of_notMem hin, hz0]
            simp
      simp_rw [hterm]
      rw [Summable.tsum_add CompleteLattice.summable CompleteLattice.summable,
        ENNReal.tsum_mul_right]
      have h1 : (∑' z : Data r, if θ = f z then μ_body x z else 0) =
          (Fintype.card α : ℝ≥0∞)⁻¹ := by
        have hmap := congrArg (fun p : PMF α => p θ) (hlaw x hIx hcx)
        rw [PMF.map_apply, PMF.uniformOfFintype_apply] at hmap
        rw [← hmap]
        congr 1; ext z; split_ifs <;> rfl
      have h2 : (∑' z : Data r, {w : Data r | f w ∉ E}.indicator (μ_body x) z) =
          (PMF.uniformOfFintype α).toOuterMeasure {θ' : α | θ' ∉ E} := by
        rw [← PMF.toOuterMeasure_apply, ← hlaw x hIx hcx, PMF.toOuterMeasure_map_apply]
        rfl
      rw [h1, h2]
    · simp only [hθ, ↓reduceIte]
      refine tsum_eq_zero_iff.mpr fun z => ?_
      by_cases hz : z ∈ (μ_body x).support
      · obtain ⟨hloop_z, hiff_z⟩ := hinv x hIx hcx z hz
        rcases hloop_z with ⟨hcz, hIz⟩ | ⟨hncz, _⟩
        · rw [ih hIz hcz]
          simp [hθ]
        · have hfz_in : f z ∈ E := hiff_z.mp hncz
          have hne : θ ≠ f z := fun h => hθ (h ▸ hfz_in)
          rw [exitMass_of_not_holds hncz]
          simp [hne]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul]

/-- If each iteration of a Word-RAM loop `Code.loop cond body` samples `f y` uniformly from a finite
type `α` and exits iff `f y ∈ E` for a nonempty target subset `E : Finset α`, then the loop exit
distribution `loopExitPMF cond μ_body x` mapped under `f` equals `PMF.uniformOfFinset E hE`. -/
theorem loopExitPMF_map_eq_uniformOfFinset {r : ℕ} {α : Type*} [Fintype α]
    [Nonempty α] {cond : Cond r} {I Q : Data r → Prop} {μ_body : Data r → PMF (Data r)}
    {p_exit : ℝ≥0∞} {f : Data r → α} {E : Finset α} (hE : E.Nonempty)
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ z, I z → cond.Holds z →
      ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y ∧ (¬cond.Holds y ↔ f y ∈ E))
    (hp_exit : ∀ z, I z → cond.Holds z →
      p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (hlaw : ∀ z, I z → cond.Holds z → (μ_body z).map f = PMF.uniformOfFintype α)
    {x : Data r} (hIx : I x) (hcx : cond.Holds x) :
    (loopExitPMF cond μ_body x).map f = PMF.uniformOfFinset E hE := by
  classical
  have hinv1 : ∀ z, I z → cond.Holds z → ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y :=
    fun z hz hcz y hy => (hinv z hz hcz y hy).1
  have hx_inv : LoopStateInv cond I Q x := Or.inl ⟨hcx, hIx⟩
  refine pmf_eq_uniformOfFinset_of_ite_const hE (c := ⨆ K : ℕ, exitWeightSeq α E K) fun θ => ?_
  rw [PMF.map_apply]
  have hpoint : ∀ y : Data r,
      (if θ = f y then loopExitPMF cond μ_body x y else 0) =
      ⨆ K : ℕ,
        if θ = f y then
          Set.indicator {w | ¬cond.Holds w} (loopIterPMF cond μ_body K x) y
        else 0 := by
    intro y
    by_cases hθ : θ = f y
    · simp only [hθ, ↓reduceIte]
      exact loopExitPMF_apply_of_hasSum
        (hasSum_loopExitDensity hp_pos hp_top hinv1 hp_exit hx_inv) y
    · simp [hθ]
  simp_rw [hpoint]
  rw [ENNReal.tsum_iSup_of_monotone]
  · change (⨆ K : ℕ, exitMass cond μ_body f K x θ) = _
    simp_rw [exitMass_eq_ite_exitWeightSeq hinv hlaw _ hIx hcx θ]
    by_cases hθ : θ ∈ E <;> simp [hθ]
  · intro y K₁ K₂ hK
    by_cases hθ : θ = f y
    · simp only [hθ, ↓reduceIte]
      exact loopIterPMF_indicator_mono cond μ_body x y hK
    · simp [hθ]

end Cslib.WordRAM.Randomized
