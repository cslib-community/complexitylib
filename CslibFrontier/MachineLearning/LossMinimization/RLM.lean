/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Stability
public import CslibFrontier.Foundations.Analysis.Convex.Strong
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Regularized loss minimization

The *regularized loss minimization* (RLM) rule with regularizer `R : E → ℝ` returns, on a sample
`S`, a minimizer of `L_S(w) + R(w)` [ShalevShwartzBenDavid2014, Section 13.1]. With *Tikhonov
regularization* `R(w) = r‖w‖²` (the source writes `λ` for `r`), convex `ρ`-Lipschitz losses and
`m` examples, the rule is replace-one stable with rate `ρ² / (r m)`. Combined with the general
oracle inequality `IsRLM.integral_trueRisk_le`, this gives
`𝔼_S [L_D(A S)] ≤ L_D(w) + r‖w‖² + 2ρ² / (r m)` and, for comparators of norm at most `B`, the
bound `ρ B √(8 / m)` on the excess risk.

The rule minimizes over a convex set `K` on which the losses are convex and Lipschitz; the source's
convex-Lipschitz-bounded learning problems [ShalevShwartzBenDavid2014, Definition 12.12] take `K`
to be the hypothesis class `H`, and the unconstrained rule takes `K = Set.univ`.

The stability rate is half of the rate `2ρ² / (r m)` of [ShalevShwartzBenDavid2014,
Corollary 13.6]: the source compares the two minimizers through the quadratic growth of one
objective, while `IsRLM.norm_sub_le` adds the quadratic growth of both. The same rate follows from
[BousquetElisseeff2002, Theorem 22], which bounds the effect of removing one example by
`ρ² / (2 r m)` for losses that are `ρ`-Lipschitz in the prediction `⟪w, x⟫` and features of norm
at most `1`; a replacement is a removal followed by an insertion. The source's bounds follow, and
are stated in the source's form.

## Main definitions

* `Cslib.MachineLearning.IsRLM`: `A` is a regularized loss minimization rule on `K` for the
  regularizer `R`.

## Main results

* `Cslib.MachineLearning.exists_isRLM`: on a nonempty compact set, continuous losses and
  regularizer admit an RLM rule.
* `Cslib.MachineLearning.exists_isRLM_tikhonov`: on a nonempty closed subset of a proper space,
  continuous losses bounded below admit a Tikhonov RLM rule; this covers unconstrained
  minimization.
* `Cslib.MachineLearning.IsRLM.mul_norm_sub_sq_le`: for a `σ`-strongly convex regularizer and
  convex losses, the minimizers `u` and `v` on two samples that differ in one example satisfy
  `σ m ‖v - u‖² ≤ X + Y`, where `X` and `Y` are the loss changes on the two differing examples.
* `Cslib.MachineLearning.IsRLM.norm_sub_le`, `Cslib.MachineLearning.IsRLM.sub_le`,
  `Cslib.MachineLearning.IsRLM.isReplaceOneStable`: for a `σ`-strongly convex regularizer and
  convex `ρ`-Lipschitz losses, replacing one example moves the minimizer by at most `2ρ / (σ m)`
  and changes every loss by at most `2ρ² / (σ m)`, so the rule is replace-one stable at that
  rate.
* `Cslib.MachineLearning.IsRLM.isReplaceOneStable_tikhonov`: Tikhonov RLM is replace-one stable
  with rate `ρ² / (r m)`, hence with the rate `2ρ² / (r m)` of [ShalevShwartzBenDavid2014,
  Corollary 13.6].
* `Cslib.MachineLearning.IsRLM.integral_empiricalRisk_le`: the fitting term
  `𝔼_S [L_S(A S)] ≤ L_D(w) + R(w)` for a nonnegative regularizer [ShalevShwartzBenDavid2014,
  (13.16)].
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_le`: the oracle inequality for a stable RLM rule
  with a nonnegative regularizer.
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_le_tikhonov`: the oracle inequality
  `𝔼_S [L_D(A S)] ≤ L_D(w) + r‖w‖² + 2ρ² / (r m)` [ShalevShwartzBenDavid2014, Corollary 13.8].
* `Cslib.MachineLearning.IsRLM.integral_trueRisk_le_add_sqrt`: for `r = √(2ρ² / (B² m))` and
  every `w ∈ K` with `‖w‖ ≤ B`, `𝔼_S [L_D(A S)] ≤ L_D(w) + ρ B √(8 / m)`
  [ShalevShwartzBenDavid2014, Corollary 13.9].

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Sections 13.1–13.4
* [O. Bousquet, A. Elisseeff, *Stability and Generalization*][BousquetElisseeff2002], Theorem 22
-/

public section

open MeasureTheory Set Filter Topology

namespace Cslib.MachineLearning

variable {E Z : Type*}

/-! ### The rule -/

/-- `A` is a **regularized loss minimization (RLM) rule** on `K` for the loss `ℓ` and the
regularizer `R` if, on every sample `S`, it returns a minimizer over `K` of the regularized
empirical risk `L_S(w) + R(w)` [ShalevShwartzBenDavid2014, Section 13.1]. -/
structure IsRLM (ℓ : E → Z → ℝ) (R : E → ℝ) (K : Set E) {m : ℕ} (A : (Fin m → Z) → E) :
    Prop where
  /-- The rule returns a point of `K`. -/
  mem : ∀ S, A S ∈ K
  /-- The rule minimizes the regularized empirical risk over `K`. -/
  isMinOn : ∀ S, IsMinOn (fun w => empiricalRisk ℓ S w + R w) K (A S)

/-- The regularized empirical risk of an RLM rule's output is at most that of any `w ∈ K`. -/
theorem IsRLM.le {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} {m : ℕ} {A : (Fin m → Z) → E}
    (hA : IsRLM ℓ R K A) (S : Fin m → Z) {w : E} (hw : w ∈ K) :
    empiricalRisk ℓ S (A S) + R (A S) ≤ empiricalRisk ℓ S w + R w :=
  hA.isMinOn S hw

section Existence

variable [TopologicalSpace E]

/-- **Existence of RLM rules on compact sets**: if `K` is compact and nonempty, and the losses and
the regularizer are continuous on `K`, some rule minimizes the regularized empirical risk. -/
theorem exists_isRLM {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hℓ : ∀ z, ContinuousOn (fun w => ℓ w z) K) (hR : ContinuousOn R K)
    (m : ℕ) : ∃ A : (Fin m → Z) → E, IsRLM ℓ R K A := by
  have h : ∀ S : Fin m → Z, ∃ w ∈ K, IsMinOn (fun w => empiricalRisk ℓ S w + R w) K w :=
    fun S => hK.exists_isMinOn hne ((continuousOn_empiricalRisk fun i => hℓ (S i)).add hR)
  choose A hAK hAmin using h
  exact ⟨A, ⟨hAK, hAmin⟩⟩

end Existence

section Normed

variable [NormedAddCommGroup E]

/-- **Existence of Tikhonov RLM rules**: in a proper space, if `K` is closed and nonempty, the
losses are continuous on `K` and bounded below by `c` there, and `r > 0`, some rule minimizes
`L_S(w) + r‖w‖²` over `K`. Taking `K = Set.univ` gives the unconstrained rule. -/
theorem exists_isRLM_tikhonov [ProperSpace E] {ℓ : E → Z → ℝ} {K : Set E} (hK : IsClosed K)
    (hne : K.Nonempty) (hℓ : ∀ z, ContinuousOn (fun w => ℓ w z) K) {c : ℝ}
    (hc : ∀ w ∈ K, ∀ z, c ≤ ℓ w z) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ A : (Fin m → Z) → E, IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A := by
  obtain ⟨w₀, hw₀⟩ := hne
  have h : ∀ S : Fin m → Z,
      ∃ w ∈ K, IsMinOn (fun w => empiricalRisk ℓ S w + r * ‖w‖ ^ 2) K w := by
    intro S
    set f := fun w => empiricalRisk ℓ S w + r * ‖w‖ ^ 2 with hf_def
    have hf : ContinuousOn f K :=
      (continuousOn_empiricalRisk fun i => hℓ (S i)).add (by fun_prop)
    -- The empirical risk is at least `min c 0` on `K` (it is `0` on the empty sample).
    have hlow : ∀ w ∈ K, min c 0 + r * ‖w‖ ^ 2 ≤ f w := fun w hw => by
      have : min c 0 ≤ empiricalRisk ℓ S w := by
        rw [empiricalRisk_def]
        rcases isEmpty_or_nonempty (Fin m) with hm | hm
        · simp only [Finset.univ_eq_empty, Finset.expect_empty]
          exact min_le_right _ _
        · exact Finset.le_expect Finset.univ_nonempty fun i _ =>
            (min_le_left _ _).trans (hc w hw (S i))
      simp only [hf_def]
      linarith
    -- Away from a large ball, `r‖w‖²` exceeds `f w₀ - min c 0`.
    set ρ₀ := |f w₀ - min c 0| / r + 1
    have hev : ∀ᶠ w in cocompact E ⊓ Filter.principal K, f w₀ ≤ f w := by
      rw [eventually_inf_principal]
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop ρ₀] with w hw hwK
      have h1 : 1 ≤ ‖w‖ := by
        have := div_nonneg (abs_nonneg (f w₀ - min c 0)) hr.le
        linarith
      have h2 : |f w₀ - min c 0| ≤ r * ‖w‖ := by
        have : |f w₀ - min c 0| / r ≤ ‖w‖ := by linarith
        rwa [div_le_iff₀ hr, mul_comm] at this
      have h3 : r * ‖w‖ ≤ r * ‖w‖ ^ 2 :=
        calc r * ‖w‖ = r * ‖w‖ * 1 := by ring
          _ ≤ r * ‖w‖ * ‖w‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = r * ‖w‖ ^ 2 := by ring
      have := hlow w hwK
      linarith [le_abs_self (f w₀ - min c 0)]
    exact hf.exists_isMinOn' hK hw₀ hev
  choose A hAK hAmin using h
  exact ⟨A, ⟨hAK, hAmin⟩⟩

end Normed

/-! ### Stability -/

section Stability

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Two-minimizer growth**: if `R` is `σ`-strongly convex on `K` and every loss is convex on `K`,
then the outputs `u = A S` and `v = A S⁽ⁱ⁾` of an RLM rule on `m` examples satisfy
`σ m ‖v - u‖² ≤ (ℓ(v, z_i) - ℓ(u, z_i)) + (ℓ(u, z') - ℓ(v, z'))`, where `S⁽ⁱ⁾` replaces the `i`-th
example by `z'`. This adds the quadratic growth of both regularized empirical risks at their
minimizers (compare [ShalevShwartzBenDavid2014, (13.10)], which uses one). -/
theorem IsRLM.mul_norm_sub_sq_le {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} {m : ℕ}
    {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hR : StrongConvexOn K σ R)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) (S : Fin m → Z) (i : Fin m) (z' : Z) :
    σ * m * ‖A (Function.update S i z') - A S‖ ^ 2 ≤
      (ℓ (A (Function.update S i z')) (S i) - ℓ (A S) (S i)) +
        (ℓ (A S) z' - ℓ (A (Function.update S i z')) z') := by
  have hm : (0 : ℝ) < m := by exact_mod_cast i.pos
  have hu := hA.mem S
  have hv := hA.mem (Function.update S i z')
  -- Both regularized empirical risks are `σ`-strongly convex, so both minimizers have quadratic
  -- growth.
  have hstrong : ∀ T : Fin m → Z, StrongConvexOn K σ fun w => empiricalRisk ℓ T w + R w :=
    fun T => by
      have h := hR.add_convexOn (convexOn_empiricalRisk hR.1 fun j => hconv (T j))
      rw [add_comm] at h
      exact h
  have h₁ := (hstrong S).add_le_of_isMinOn hu (hA.isMinOn S) hv
  have h₂ := (hstrong (Function.update S i z')).add_le_of_isMinOn hv (hA.isMinOn _) hu
  rw [norm_sub_rev, empiricalRisk_update, empiricalRisk_update] at h₂
  have h : σ * ‖A (Function.update S i z') - A S‖ ^ 2 ≤
      ((ℓ (A S) z' - ℓ (A S) (S i)) -
        (ℓ (A (Function.update S i z')) z' - ℓ (A (Function.update S i z')) (S i))) / m := by
    rw [sub_div]
    linarith
  rw [le_div_iff₀ hm] at h
  linarith

/-- **RLM rules with a strongly convex regularizer are stable** (compare
[ShalevShwartzBenDavid2014, Corollary 13.6]): if `R` is
`σ`-strongly convex on `K` with `σ > 0` and every loss is convex and `ρ`-Lipschitz on `K`, then
replacing one of `m` examples moves the output of an RLM rule by at most `2ρ / (σ m)`. -/
theorem IsRLM.norm_sub_le {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} {m : ℕ}
    {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hσ : 0 < σ) (hR : StrongConvexOn K σ R)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) {ρ : NNReal}
    (hlip : ∀ z, LipschitzOnWith ρ (fun w => ℓ w z) K) (S : Fin m → Z) (i : Fin m) (z' : Z) :
    ‖A (Function.update S i z') - A S‖ ≤ 2 * ρ / (σ * m) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast i.pos
  have hu := hA.mem S
  have hv := hA.mem (Function.update S i z')
  have hgrowth := hA.mul_norm_sub_sq_le hR hconv S i z'
  -- Lipschitz bounds on the two changed losses.
  have hlip₁ := (hlip z').le_add_mul hu hv
  have hlip₂ := (hlip (S i)).le_add_mul hv hu
  rw [dist_eq_norm, norm_sub_rev] at hlip₁
  rw [dist_eq_norm] at hlip₂
  have hd0 : 0 ≤ ‖A (Function.update S i z') - A S‖ := norm_nonneg _
  generalize ‖A (Function.update S i z') - A S‖ = d at hgrowth hlip₁ hlip₂ hd0 ⊢
  -- The change in the two losses is at most `2 ρ d`.
  have key : σ * m * d ^ 2 ≤ 2 * ρ * d := by linarith
  rcases hd0.eq_or_lt with hd | hd
  · rw [← hd]
    positivity
  · rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- **RLM rules with a strongly convex regularizer are uniformly stable**: under the hypotheses of
`Cslib.MachineLearning.IsRLM.norm_sub_le`, replacing one of `m` examples changes the loss of the
output on every example by at most `2ρ² / (σ m)`. -/
theorem IsRLM.sub_le {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E} {m : ℕ}
    {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hσ : 0 < σ) (hR : StrongConvexOn K σ R)
    (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) {ρ : NNReal}
    (hlip : ∀ z, LipschitzOnWith ρ (fun w => ℓ w z) K) (S : Fin m → Z) (i : Fin m) (z' z : Z) :
    ℓ (A (Function.update S i z')) z - ℓ (A S) z ≤ 2 * ρ ^ 2 / (σ * m) := by
  have h := (hlip z).le_add_mul (hA.mem (Function.update S i z')) (hA.mem S)
  rw [dist_eq_norm] at h
  have hd := hA.norm_sub_le hσ hR hconv hlip S i z'
  calc ℓ (A (Function.update S i z')) z - ℓ (A S) z
      ≤ ρ * ‖A (Function.update S i z') - A S‖ := by linarith
    _ ≤ ρ * (2 * ρ / (σ * m)) := by gcongr
    _ = 2 * ρ ^ 2 / (σ * m) := by ring

/-- RLM rules with a `σ`-strongly convex regularizer and convex `ρ`-Lipschitz losses are
replace-one stable with rate `2ρ² / (σ m)`. -/
theorem IsRLM.isReplaceOneStable [MeasurableSpace Z] {ℓ : E → Z → ℝ} {R : E → ℝ} {K : Set E}
    {m : ℕ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A) {σ : ℝ} (hσ : 0 < σ)
    (hR : StrongConvexOn K σ R) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) {ρ : NNReal}
    (hlip : ∀ z, LipschitzOnWith ρ (fun w => ℓ w z) K) :
    IsReplaceOneStable ℓ A (2 * ρ ^ 2 / (σ * m)) :=
  isReplaceOneStable_of_forall_le (by positivity) (hA.sub_le hσ hR hconv hlip)

end Stability

/-! ### The oracle inequality -/

/-- **The fitting term of the oracle inequality** [ShalevShwartzBenDavid2014, (13.16)]: for an RLM
rule on `K` with a regularizer that is nonnegative on `K`, `m > 0` i.i.d. examples from `D` and
every `w ∈ K` with `D`-integrable loss, `𝔼_S [L_S(A S)] ≤ L_D(w) + R(w)`. -/
theorem IsRLM.integral_empiricalRisk_le [MeasurableSpace Z] {ℓ : E → Z → ℝ} {R : E → ℝ}
    {K : Set E} {m : ℕ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A)
    (hR : ∀ w ∈ K, 0 ≤ R w) (D : Measure Z) [IsProbabilityMeasure D] (hm : 0 < m)
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwint : Integrable (ℓ w) D) :
    ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) ≤ trueRisk ℓ D w + R w := by
  -- `L_S(A S) ≤ L_S(A S) + R(A S) ≤ L_S(w) + R(w)`, and `𝔼_S [L_S(w)] = L_D(w)`.
  have hwint' : ∀ i, Integrable (fun S : Fin m → Z => ℓ w (S i))
      (Measure.pi fun _ : Fin m => D) := fun i => integrable_comp_eval (i := i) hwint
  have hemp : ∫ S, empiricalRisk ℓ S (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      ∫ S, (empiricalRisk ℓ S w + R w) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_mono (integrable_empiricalRisk_comp ℓ _ A hint')
      ((integrable_empiricalRisk_comp ℓ _ (fun _ => w) hwint').add (integrable_const _))
      fun S => by
        have := hA.le S hw
        have := hR _ (hA.mem S)
        linarith
  rwa [integral_add (integrable_empiricalRisk_comp ℓ _ (fun _ => w) hwint') (integrable_const _),
    integral_empiricalRisk ℓ D hm w hwint, integral_const, probReal_univ, one_smul] at hemp

/-- **The oracle inequality for stable RLM rules** [ShalevShwartzBenDavid2014, (13.15) and
(13.16)]: if an RLM rule on `K` with a regularizer that is nonnegative on `K` is replace-one stable
at rate `ε`, then for `m > 0` i.i.d. examples from `D` and every `w ∈ K` with `D`-integrable loss,
`𝔼_S [L_D(A S)] ≤ L_D(w) + R(w) + ε`. The integrability hypotheses are those of
`Cslib.MachineLearning.integral_trueRisk_sub_empiricalRisk`. -/
theorem IsRLM.integral_trueRisk_le [MeasurableSpace Z] {ℓ : E → Z → ℝ} {R : E → ℝ}
    {K : Set E} {m : ℕ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ R K A)
    (hR : ∀ w ∈ K, 0 ≤ R w) {ε : ℝ} (hstab : IsReplaceOneStable ℓ A ε) (D : Measure Z)
    [IsProbabilityMeasure D] (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwint : Integrable (ℓ w) D) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤ trueRisk ℓ D w + R w + ε := by
  have hgen := hstab.integral_trueRisk_le D hm hint hint'
  have hemp := hA.integral_empiricalRisk_le hR D hm hint' hw hwint
  linarith

section Tikhonov

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Tikhonov RLM is stable** [ShalevShwartzBenDavid2014, Corollary 13.6]: for the regularizer
`r‖w‖²` with `r > 0` on a convex set `K` and convex `ρ`-Lipschitz losses, an RLM rule on `m`
examples is replace-one stable with rate `ρ² / (r m)`. This is half the rate `2ρ² / (r m)` of the
source, which follows by `Cslib.MachineLearning.IsReplaceOneStable.mono`. -/
theorem IsRLM.isReplaceOneStable_tikhonov [MeasurableSpace Z] {ℓ : E → Z → ℝ} {K : Set E}
    {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A)
    (hK : Convex ℝ K) (hr : 0 < r) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) {ρ : NNReal}
    (hlip : ∀ z, LipschitzOnWith ρ (fun w => ℓ w z) K) :
    IsReplaceOneStable ℓ A (ρ ^ 2 / (r * m)) := by
  have h := hA.isReplaceOneStable (by positivity) (strongConvexOn_mul_norm_sq hK r) hconv hlip
  convert h using 1
  field_simp

/-- **The oracle inequality for Tikhonov RLM** [ShalevShwartzBenDavid2014, Corollary 13.8]: for
the regularizer `r‖w‖²` with `r > 0` on a convex set `K`, convex `ρ`-Lipschitz losses and `m > 0`
i.i.d. examples from `D`, every `w ∈ K` with `D`-integrable loss satisfies
`𝔼_S [L_D(A S)] ≤ L_D(w) + r‖w‖² + 2ρ² / (r m)`.

The rate `2ρ² / (r m)` is the source's; the proof gives `ρ² / (r m)`. The comparator `w` ranges
over `K`, the set the rule minimizes over; the source takes `K` to be the whole space. The
integrability hypotheses are those of
`Cslib.MachineLearning.integral_trueRisk_sub_empiricalRisk`. -/
theorem IsRLM.integral_trueRisk_le_tikhonov [MeasurableSpace Z] {ℓ : E → Z → ℝ} {K : Set E}
    {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A)
    (hK : Convex ℝ K) (hr : 0 < r) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) {ρ : NNReal}
    (hlip : ∀ z, LipschitzOnWith ρ (fun w => ℓ w z) K) (D : Measure Z) [IsProbabilityMeasure D]
    (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwint : Integrable (ℓ w) D) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      trueRisk ℓ D w + r * ‖w‖ ^ 2 + 2 * ρ ^ 2 / (r * m) := by
  have h := hA.integral_trueRisk_le (fun _ _ => by positivity)
    (hA.isReplaceOneStable_tikhonov hK hr hconv hlip) D hm hint hint' hw hwint
  have hle : ρ ^ 2 / (r * m) ≤ 2 * ρ ^ 2 / (r * m) := by
    gcongr
    linarith [sq_nonneg (ρ : ℝ)]
  linarith

/-- **Convex-Lipschitz-bounded problems** [ShalevShwartzBenDavid2014, Corollary 13.9]: for
convex `ρ`-Lipschitz losses on a convex set `K` with `ρ > 0`, a bound `B > 0`, `m > 0` i.i.d.
examples from `D` and the regularization weight `r = √(2ρ² / (B² m))`, Tikhonov RLM satisfies
`𝔼_S [L_D(A S)] ≤ L_D(w) + ρ B √(8 / m)` for every `w ∈ K` with `‖w‖ ≤ B` and integrable loss.
The source states this against `min_{w ∈ H} L_D(w)`; the form here holds for every comparator, so
it bounds the infimum without assuming that it is attained. Combining `IsRLM.integral_trueRisk_le`
with the rate `ρ² / (r m)` of `IsRLM.isReplaceOneStable_tikhonov` instead, the weight
`r = ρ / (B √m)` gives the smaller excess `2 ρ B / √m`. -/
theorem IsRLM.integral_trueRisk_le_add_sqrt [MeasurableSpace Z] {ℓ : E → Z → ℝ} {K : Set E}
    {m : ℕ} {r : ℝ} {A : (Fin m → Z) → E} (hA : IsRLM ℓ (fun w => r * ‖w‖ ^ 2) K A)
    (hK : Convex ℝ K) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z) {ρ : NNReal}
    (hlip : ∀ z, LipschitzOnWith ρ (fun w => ℓ w z) K) {B : ℝ} (hρ : 0 < (ρ : ℝ)) (hB : 0 < B)
    (hr : r = √(2 * (ρ : ℝ) ^ 2 / (B ^ 2 * m))) (D : Measure Z) [IsProbabilityMeasure D]
    (hm : 0 < m)
    (hint : Integrable (fun p : (Fin m → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D))
    (hint' : ∀ i, Integrable (fun S => ℓ (A S) (S i)) (Measure.pi fun _ : Fin m => D))
    {w : E} (hw : w ∈ K) (hwB : ‖w‖ ≤ B) (hwint : Integrable (ℓ w) D) :
    ∫ S, trueRisk ℓ D (A S) ∂(Measure.pi fun _ : Fin m => D) ≤
      trueRisk ℓ D w + ρ * B * √(8 / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr2 : r ^ 2 * (B ^ 2 * m) = 2 * ρ ^ 2 := by
    rw [hr, Real.sq_sqrt (by positivity)]
    field_simp
  set t := √(8 / (m : ℝ))
  have ht2 : t ^ 2 * m = 8 := by
    simp only [t]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have h := hA.integral_trueRisk_le (fun _ _ => by positivity)
    (hA.isReplaceOneStable_tikhonov hK hr0 hconv hlip) D hm hint hint' hw hwint
  -- `r‖w‖² ≤ r B²`, `ρ² / (r m) = r B² / 2` and `ρ B t = 2 r B²`.
  have hw2 : r * ‖w‖ ^ 2 ≤ r * B ^ 2 := by gcongr
  have hstab : (ρ : ℝ) ^ 2 / (r * m) = r * B ^ 2 / 2 := by
    rw [div_eq_iff (by positivity)]
    nlinarith
  have hρt : (ρ : ℝ) * t = 2 * B * r := by
    have hsq : ((ρ : ℝ) * t) ^ 2 = (2 * B * r) ^ 2 := by
      have : ((ρ : ℝ) * t) ^ 2 * m = (2 * B * r) ^ 2 * m := by
        calc ((ρ : ℝ) * t) ^ 2 * m = ρ ^ 2 * (t ^ 2 * m) := by ring
          _ = 4 * (r ^ 2 * (B ^ 2 * m)) := by rw [ht2, hr2]; ring
          _ = (2 * B * r) ^ 2 * m := by ring
      exact mul_right_cancel₀ hm'.ne' this
    exact (sq_eq_sq₀ (by positivity) (by positivity)).1 hsq
  have : (ρ : ℝ) * B * t = 2 * (r * B ^ 2) := by
    rw [mul_right_comm, hρt]
    ring
  have hrB : 0 ≤ r * B ^ 2 := by positivity
  linarith

end Tikhonov

end Cslib.MachineLearning
