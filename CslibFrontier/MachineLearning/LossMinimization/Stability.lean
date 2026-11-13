/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Basic
import CslibFrontier.MachineLearning.PACLearning.DoubleSample
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Replace-one stability

A learning rule `A : (Fin m → Z) → W` *overfits* when the risk of `A S` on the training sample
`S` is much smaller than its true risk. Replace-one stability measures how much the loss of `A S`
on a training example `S i` grows when that example is replaced by a fresh one `z'`
[ShalevShwartzBenDavid2014, Chapter 13]. This file proves that the two quantities agree in
expectation, and that a rule that is stable at rate `ε` generalizes at rate `ε`.

The fresh example and the sample are drawn together from `(Measure.pi fun _ => D).prod D`; a pair
`p` consists of the sample `p.1` and the replacement `p.2`, and `Function.update p.1 i p.2` is the
sample `S⁽ⁱ⁾` of [ShalevShwartzBenDavid2014, Section 13.2].

## Main definitions

* `Cslib.MachineLearning.replaceOneGap`: the expected replace-one gap
  `𝔼_{(S, z'), i} [ℓ(A(S⁽ⁱ⁾), z_i) - ℓ(A S, z_i)]`.
* `Cslib.MachineLearning.IsReplaceOneStable`: on-average-replace-one stability at a given rate.

## Main results

* `Cslib.MachineLearning.integral_trueRisk_sub_empiricalRisk`: the expected generalization gap
  `𝔼_S [L_D(A S) - L_S(A S)]` equals the expected replace-one gap
  [ShalevShwartzBenDavid2014, Theorem 13.2].
* `Cslib.MachineLearning.integral_update_eval`: replacing the `i`-th example by a fresh one and
  keeping the replaced example as the fresh one preserves expectations.
* `Cslib.MachineLearning.integral_trueRisk_le_of_replaceOneGap_le`: a rule whose expected
  replace-one gap under `D` is at most `ε` generalizes at rate `ε` under `D`.
* `Cslib.MachineLearning.IsReplaceOneStable.integral_trueRisk_le`: a stable rule generalizes:
  `𝔼_S [L_D(A S)] ≤ 𝔼_S [L_S(A S)] + ε`.
* `Cslib.MachineLearning.isReplaceOneStable_of_forall_le`: a rule whose loss on every example
  changes by at most `ε` when one example of the sample is replaced is replace-one stable at rate
  `ε`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Sections 13.1–13.2
-/

public section

open MeasureTheory Finset
open scoped BigOperators

namespace Cslib.MachineLearning

variable {W Z : Type*}

/-! ### The replace-one gap -/

/-- Replace the `i`-th example of the sample by the fresh example, and keep the replaced example
as the fresh one. -/
private def replaceOne {m : ℕ} (i : Fin m) (p : (Fin m → Z) × Z) : (Fin m → Z) × Z :=
  (Function.update p.1 i p.2, p.1 i)

private theorem replaceOne_involutive {m : ℕ} (i : Fin m) :
    Function.Involutive (replaceOne (Z := Z) i) := by
  intro p
  simp only [replaceOne, Function.update_self, Function.update_idem, Function.update_eq_self]

variable [MeasurableSpace Z]

/-- The **expected replace-one gap** of a learning rule `A` on `m` examples from `D`: the expected
increase `𝔼_{(S, z'), i} [ℓ(A(S⁽ⁱ⁾), z_i) - ℓ(A S, z_i)]` of the loss on the `i`-th example when
it is replaced by an independent example `z'`, for a uniformly random index `i`
[ShalevShwartzBenDavid2014, Theorem 13.2]. Here `S⁽ⁱ⁾` is `Function.update S i z'`.

Both terms are Bochner integrals, which are `0` for non-integrable integrands. So a rule whose
losses are not integrable under `D` has gap `0`, and the gap, and stability defined from it, carry
information only for integrable losses; the results below assume integrability. -/
noncomputable def replaceOneGap (ℓ : W → Z → ℝ) (D : Measure Z) {m : ℕ}
    (A : (Fin m → Z) → W) : ℝ :=
  𝔼 i, ∫ p, (ℓ (A (Function.update p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i))
    ∂(Measure.pi fun _ : Fin m => D).prod D

theorem replaceOneGap_def (ℓ : W → Z → ℝ) (D : Measure Z) {m : ℕ} (A : (Fin m → Z) → W) :
    replaceOneGap ℓ D A =
      𝔼 i, ∫ p, (ℓ (A (Function.update p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i))
        ∂(Measure.pi fun _ : Fin m => D).prod D := by
  rw [replaceOneGap]

private theorem measurable_replaceOne {m : ℕ} (i : Fin m) :
    Measurable (replaceOne (Z := Z) i) :=
  measurable_update'.prodMk ((measurable_pi_apply i).comp measurable_fst)

/-- Replacing one example of an i.i.d. sample by an independent example from the same distribution
preserves the joint distribution. This is the replace-one case of
`Cslib.MachineLearning.PACLearning.measurePreserving_swapSamples`. -/
private theorem measurePreserving_replaceOne (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (i : Fin m) :
    MeasurePreserving (replaceOne i) ((Measure.pi fun _ : Fin m => D).prod D)
      ((Measure.pi fun _ : Fin m => D).prod D) := by
  set μ := Measure.pi fun _ : Fin m => D
  -- `π (S, S') = (S, S' i)` sends the double sample distribution to the joint distribution.
  set π : (Fin m → Z) × (Fin m → Z) → (Fin m → Z) × Z := fun q => (q.1, q.2 i) with hπ_def
  have hπ : MeasurePreserving π (μ.prod μ) (μ.prod D) :=
    (MeasurePreserving.id μ).prod (measurePreserving_eval (fun _ : Fin m => D) i)
  have hσ := PACLearning.measurePreserving_swapSamples D (fun j => decide (j = i))
  -- `replaceOne i ∘ π = π ∘ swapSamples (indicator of i)`.
  have hcomm : replaceOne i ∘ π = π ∘ PACLearning.swapSamples (fun j => decide (j = i)) := by
    funext q
    refine Prod.ext (funext fun j => ?_) ?_
    · by_cases hj : j = i
      · subst hj
        simp [π, replaceOne]
      · simp [π, replaceOne, hj]
    · simp [π, replaceOne]
  refine ⟨measurable_replaceOne i, ?_⟩
  calc Measure.map (replaceOne i) (μ.prod D)
      = Measure.map (replaceOne i) (Measure.map π (μ.prod μ)) := by rw [hπ.map_eq]
    _ = Measure.map (π ∘ PACLearning.swapSamples (fun j => decide (j = i))) (μ.prod μ) := by
        rw [Measure.map_map (measurable_replaceOne i) hπ.measurable, hcomm]
    _ = μ.prod D := by
        rw [← Measure.map_map hπ.measurable hσ.measurable, hσ.map_eq, hπ.map_eq]

/-- **Replacing one example by a fresh one preserves expectations**: for `m` i.i.d. examples and an
independent example `z'` from `D`, `𝔼 [g(S⁽ⁱ⁾, z_i)] = 𝔼 [g(S, z')]`, where `S⁽ⁱ⁾` is
`Function.update S i z'`. -/
theorem integral_update_eval (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (i : Fin m)
    (g : (Fin m → Z) × Z → ℝ) :
    ∫ p, g (Function.update p.1 i p.2, p.1 i) ∂(Measure.pi fun _ : Fin m => D).prod D =
      ∫ p, g p ∂(Measure.pi fun _ : Fin m => D).prod D :=
  (measurePreserving_replaceOne D i).integral_comp (MeasurableEquiv.ofInvolutive _
    (replaceOne_involutive i) (measurable_replaceOne i)).measurableEmbedding g

/-- The integrability counterpart of `Cslib.MachineLearning.integral_update_eval`. -/
theorem integrable_update_eval {D : Measure Z} [IsProbabilityMeasure D] {m : ℕ} (i : Fin m)
    {g : (Fin m → Z) × Z → ℝ} (hg : Integrable g ((Measure.pi fun _ : Fin m => D).prod D)) :
    Integrable (fun p => g (Function.update p.1 i p.2, p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) :=
  (measurePreserving_replaceOne D i).integrable_comp_of_integrable hg

/-- If the loss of `A S` on a fresh example is integrable over the joint distribution, the true risk
of `A S` is integrable over the samples. -/
private theorem integrable_trueRisk_comp {ℓ : W → Z → ℝ} {D : Measure Z} [IsProbabilityMeasure D]
    {m : ℕ} {A : (Fin m → Z) → W}
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D)) :
    Integrable (fun S => trueRisk ℓ D (A S)) (Measure.pi fun _ : Fin m => D) := by
  simpa only [trueRisk_def] using hint.integral_prod_left

/-- **The expected generalization gap is the expected replace-one gap**
[ShalevShwartzBenDavid2014, Theorem 13.2]: for `m > 0` i.i.d. examples from `D`,
`𝔼_S [L_D(A S) - L_S(A S)] = 𝔼_{(S, z'), i} [ℓ(A(S⁽ⁱ⁾), z_i) - ℓ(A S, z_i)]`.

The hypotheses ask that the loss of `A S` on a fresh example be integrable over the joint
distribution and its loss on each training example be integrable over the samples; they hold, for
example, for bounded losses that are jointly measurable with a measurable rule, and on finite
example spaces with measurable singletons. -/
theorem integral_trueRisk_sub_empiricalRisk (ℓ : W → Z → ℝ) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) (A : (Fin m → Z) → W)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D)) :
    ∫ S, (trueRisk ℓ D (A S) - empiricalRisk ℓ S (A S)) ∂(Measure.pi fun _ : Fin m => D) =
      replaceOneGap ℓ D A := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set μ := Measure.pi fun _ : Fin m => D
  -- Each index contributes `∫ ℓ(A(S⁽ⁱ⁾), z_i) = ∫ ℓ(A S, z')` and `∫ ℓ(A S, z_i)`.
  have hfresh : ∀ i, ∫ p, ℓ (A (Function.update p.1 i p.2)) (p.1 i) ∂(μ.prod D) =
      ∫ p, ℓ (A p.1) p.2 ∂(μ.prod D) := fun i =>
    integral_update_eval D i fun p => ℓ (A p.1) p.2
  have hfresh_int : ∀ i, Integrable (fun p => ℓ (A (Function.update p.1 i p.2)) (p.1 i))
      (μ.prod D) := fun i => integrable_update_eval (g := fun p => ℓ (A p.1) p.2) i hint
  have hold : ∀ i, ∫ p, ℓ (A p.1) (p.1 i) ∂(μ.prod D) = ∫ S, ℓ (A S) (S i) ∂μ := fun i => by
    rw [integral_fun_fst (fun S => ℓ (A S) (S i)), probReal_univ, one_smul]
  have hold_int : ∀ i, Integrable (fun p => ℓ (A p.1) (p.1 i)) (μ.prod D) := fun i =>
    (hint' i).comp_fst D
  have htrue : ∫ S, trueRisk ℓ D (A S) ∂μ = ∫ p, ℓ (A p.1) p.2 ∂(μ.prod D) := by
    simp only [trueRisk_def]
    exact (integral_prod _ hint).symm
  have htrue_int : Integrable (fun S => trueRisk ℓ D (A S)) μ := integrable_trueRisk_comp hint
  rw [integral_sub htrue_int (integrable_empiricalRisk_comp ℓ μ A hint'),
    htrue, integral_empiricalRisk_comp ℓ μ A hint', replaceOneGap_def]
  calc ∫ p, ℓ (A p.1) p.2 ∂(μ.prod D) - 𝔼 i, ∫ S, ℓ (A S) (S i) ∂μ
      = 𝔼 i, (∫ p, ℓ (A p.1) p.2 ∂(μ.prod D) - ∫ S, ℓ (A S) (S i) ∂μ) := by
        rw [Finset.expect_sub_distrib, Finset.expect_const univ_nonempty]
    _ = _ := by
        refine Finset.expect_congr rfl fun i _ => ?_
        rw [integral_sub (hfresh_int i) (hold_int i), hfresh i, hold i]

/-! ### Stability -/

/-- A learning rule `A` on `m` examples is **on-average-replace-one stable at rate `ε`** for the
loss `ℓ` if its expected replace-one gap is at most `ε` under every distribution `D` on examples
[ShalevShwartzBenDavid2014, Definition 13.3].

The source considers a family of rules, one for each sample size, with a monotonically decreasing
rate `ε : ℕ → ℝ`; that family is stable when `IsReplaceOneStable ℓ (A m) (ε m)` holds for every
`m`. Monotonicity is not used by any of the results and is not required here. -/
def IsReplaceOneStable (ℓ : W → Z → ℝ) {m : ℕ} (A : (Fin m → Z) → W) (ε : ℝ) : Prop :=
  ∀ (D : Measure Z) [IsProbabilityMeasure D], replaceOneGap ℓ D A ≤ ε

theorem isReplaceOneStable_iff (ℓ : W → Z → ℝ) {m : ℕ} (A : (Fin m → Z) → W) (ε : ℝ) :
    IsReplaceOneStable ℓ A ε ↔
      ∀ (D : Measure Z) [IsProbabilityMeasure D], replaceOneGap ℓ D A ≤ ε := by
  rw [IsReplaceOneStable]

/-- Stability at a rate implies stability at every larger rate. -/
theorem IsReplaceOneStable.mono {ℓ : W → Z → ℝ} {m : ℕ} {A : (Fin m → Z) → W} {ε ε' : ℝ}
    (hA : IsReplaceOneStable ℓ A ε) (h : ε ≤ ε') : IsReplaceOneStable ℓ A ε' :=
  fun D _ => (hA D).trans h

/-- If the expected replace-one gap of `A` under `D` is at most `ε`, its expected true risk exceeds
its expected empirical risk by at most `ε` [ShalevShwartzBenDavid2014, Theorem 13.2]. -/
theorem integral_trueRisk_le_of_replaceOneGap_le {ℓ : W → Z → ℝ} {m : ℕ} {A : (Fin m → Z) → W}
    {ε : ℝ} (D : Measure Z) [IsProbabilityMeasure D] (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    (hgap : replaceOneGap ℓ D A ≤ ε) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) + ε := by
  have h := integral_trueRisk_sub_empiricalRisk ℓ D hm A hint hint'
  have htrue_int : Integrable (fun S => trueRisk ℓ D (A S)) (Measure.pi fun _ : Fin m => D) :=
    integrable_trueRisk_comp hint
  rw [integral_sub htrue_int (integrable_empiricalRisk_comp ℓ _ A hint')] at h
  linarith

/-- **Stable rules do not overfit** [ShalevShwartzBenDavid2014, Theorem 13.2 and Definition 13.3]:
if `A` is replace-one stable at rate `ε`, its expected true risk exceeds its expected empirical risk
by at most `ε`. -/
theorem IsReplaceOneStable.integral_trueRisk_le {ℓ : W → Z → ℝ} {m : ℕ}
    {A : (Fin m → Z) → W} {ε : ℝ} (hA : IsReplaceOneStable ℓ A ε) (D : Measure Z)
    [IsProbabilityMeasure D] (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D)) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) + ε :=
  integral_trueRisk_le_of_replaceOneGap_le D hm hint hint' (hA D)

/-- A function bounded above by a nonnegative constant has integral at most that constant under a
probability measure, whether or not it is integrable. -/
private theorem integral_le_of_forall_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ a, f a ≤ c) :
    ∫ a, f a ∂μ ≤ c := by
  by_cases hfi : Integrable f μ
  · calc ∫ a, f a ∂μ ≤ ∫ _, c ∂μ := integral_mono hfi (integrable_const c) hf
      _ = c := by rw [integral_const, probReal_univ, one_smul]
  · rw [integral_undef hfi]
    exact hc

/-- **Uniform stability implies replace-one stability**: if replacing any one example of any
sample changes the loss of `A` on every example by at most `ε ≥ 0`, then `A` is replace-one stable
at rate `ε`. No measurability is needed. -/
theorem isReplaceOneStable_of_forall_le {ℓ : W → Z → ℝ} {m : ℕ} {A : (Fin m → Z) → W} {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : ∀ (S : Fin m → Z) (i : Fin m) (z' z : Z),
      ℓ (A (Function.update S i z')) z - ℓ (A S) z ≤ ε) :
    IsReplaceOneStable ℓ A ε := by
  intro D _
  rw [replaceOneGap_def]
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · simp only [univ_eq_empty, Finset.expect_empty]
    exact hε
  · exact Finset.expect_le univ_nonempty fun i _ =>
      integral_le_of_forall_le hε fun p => h p.1 i p.2 (p.1 i)

end Cslib.MachineLearning
