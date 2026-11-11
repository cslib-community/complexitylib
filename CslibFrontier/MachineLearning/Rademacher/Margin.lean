/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Contraction
public import CslibFrontier.MachineLearning.Rademacher.Generalization
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product

/-!
# Margin generalization bounds via Rademacher complexity

For binary classification with real-valued scoring hypotheses `h : α → ℝ` and labels `y : Bool`
read as signs `signVal y ∈ {-1, +1}`, a labeled example `(x, y)` has signed margin
`signVal y * h x`. A nonpositive signed margin (`signVal y * h x ≤ 0`) counts as a margin error.

For `ρ > 0`, the *`ρ`-margin loss* `Φ_ρ(u) = min 1 (max 0 (1 - u / ρ))`
[MohriRostamizadehTalwalkar2018, Definition 5.5] interpolates linearly between `1` on `(-∞, 0]`
and `0` on `[ρ, ∞)`:

* `Φ_ρ(u) ∈ [0, 1]` for all `u`,
* `𝟙[u ≤ 0] ≤ Φ_ρ(u) ≤ 𝟙[u ≤ ρ]`, and
* `Φ_ρ` is `(1 / ρ)`-Lipschitz.

Combining the `[0, 1]` Rademacher generalization bounds
(`CslibFrontier.MachineLearning.Rademacher.Generalization`) for the induced margin-loss class
`{(x, y) ↦ Φ_ρ(signVal y * h x) | h ∈ H}` with Talagrand's contraction lemma
(`CslibFrontier.MachineLearning.Rademacher.Contraction`) yields the fixed-margin generalization
bounds of [MohriRostamizadehTalwalkar2018, Theorem 5.8, (5.39) and (5.40)]: on a finite domain `α`,
with probability at least `1 - δ` over `m > 0` independent draws from `D : PMF (α × Bool)`, every
hypothesis `h` in a uniformly bounded class `H : Set (α → ℝ)` satisfies

* `Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (2 / ρ) R_m(H) + √(log (1 / δ) / (2 m))`, and
* `Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (2 / ρ) R̂_{S_X}(H) + 3 √(log (2 / δ) / (2 m))`,

where `R_m(H)` is taken under the input marginal `D.map Prod.fst` and `S_X` is the unlabeled
sample `fun i => (S i).1`. Uniform boundedness of `H` supplies the `BddAbove` hypothesis required by
the real conditional supremum `⨆` in `rademacherAverage`.

## Main definitions

* `Cslib.MachineLearning.marginLoss`: the `ρ`-margin loss `Φ_ρ(u) = min 1 (max 0 (1 - u / ρ))`.
* `Cslib.MachineLearning.empiricalMarginLoss`: the empirical `ρ`-margin loss `R̂_{S, ρ}(h)`.
* `Cslib.MachineLearning.marginRisk`: the population `ρ`-margin loss under `D : PMF (α × Bool)`.
* `Cslib.MachineLearning.marginLossClass`: the composed class
  `{(x, y) ↦ Φ_ρ(signVal y * h x) | h ∈ H}`.

## Main results

* `Cslib.MachineLearning.marginLoss_mem_Icc`, `Cslib.MachineLearning.boole_le_marginLoss`,
  `Cslib.MachineLearning.marginLoss_le_boole`, `Cslib.MachineLearning.lipschitzWith_marginLoss`,
  `Cslib.MachineLearning.lipschitzWith_marginLoss_nnreal`: `[0, 1]` range, indicator sandwich, and
  `1 / ρ`-Lipschitz continuity of `marginLoss ρ`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_marginLossClass_le`,
  `Cslib.MachineLearning.rademacherComplexity_marginLossClass_le`: contraction of the `ρ`-margin
  loss class by `1 / ρ`.
* `Cslib.MachineLearning.rademacherComplexity_margin_bound`,
  `Cslib.MachineLearning.empiricalRademacherComplexity_margin_bound`: fixed-`ρ` margin bounds
  (5.39) and (5.40) [MohriRostamizadehTalwalkar2018, Theorem 5.8].
* `Cslib.MachineLearning.margin_bound_of_finset`: finite-class margin corollary via Massart's lemma.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Section 5.4, Definitions 5.5–5.6 and Theorem 5.8
* [P. L. Bartlett, S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and
  structural results*][BartlettMendelson2002], Section 3, Theorem 7
-/

public section

open Finset
open scoped BigOperators NNReal

namespace Cslib.MachineLearning

open Cslib.BitString

/-! ### The `ρ`-margin loss -/

/-- The **`ρ`-margin loss** `Φ_ρ(u) = min 1 (max 0 (1 - u / ρ))`
[MohriRostamizadehTalwalkar2018, Definition 5.5]. -/
noncomputable def marginLoss (ρ u : ℝ) : ℝ :=
  min 1 (max 0 (1 - u / ρ))

theorem marginLoss_def (ρ u : ℝ) : marginLoss ρ u = min 1 (max 0 (1 - u / ρ)) := by
  rw [marginLoss]

/-- The `ρ`-margin loss is nonnegative. -/
theorem marginLoss_nonneg (ρ u : ℝ) : 0 ≤ marginLoss ρ u :=
  le_min zero_le_one (le_max_left _ _)

/-- The `ρ`-margin loss is at most `1`. -/
theorem marginLoss_le_one (ρ u : ℝ) : marginLoss ρ u ≤ 1 :=
  min_le_left 1 _

/-- The `ρ`-margin loss takes values in `[0, 1]`. -/
theorem marginLoss_mem_Icc (ρ u : ℝ) : marginLoss ρ u ∈ Set.Icc 0 1 :=
  ⟨marginLoss_nonneg ρ u, marginLoss_le_one ρ u⟩

/-- On nonpositive margins `u ≤ 0` (`ρ > 0`), the `ρ`-margin loss equals `1`. -/
theorem marginLoss_of_nonpos {ρ u : ℝ} (hρ : 0 < ρ) (hu : u ≤ 0) : marginLoss ρ u = 1 := by
  have hdiv : u / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hρ.le
  rw [marginLoss_def, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- Beyond margin `ρ` (`ρ ≤ u`, `ρ > 0`), the `ρ`-margin loss vanishes. -/
theorem marginLoss_of_ge {ρ u : ℝ} (hρ : 0 < ρ) (hu : ρ ≤ u) : marginLoss ρ u = 0 := by
  have hdiv : 1 ≤ u / ρ := (one_le_div hρ).2 hu
  rw [marginLoss_def, max_eq_left (by linarith), min_eq_right zero_le_one]

/-- On `[0, ρ]` (`ρ > 0`), the `ρ`-margin loss is the linear ramp `1 - u / ρ`. -/
theorem marginLoss_of_mem_Icc {ρ u : ℝ} (hρ : 0 < ρ) (hu : u ∈ Set.Icc 0 ρ) :
    marginLoss ρ u = 1 - u / ρ := by
  have h0 : 0 ≤ u / ρ := div_nonneg hu.1 hρ.le
  have h1 : u / ρ ≤ 1 := (div_le_one hρ).2 hu.2
  rw [marginLoss_def, max_eq_right (by linarith), min_eq_right (by linarith)]

/-- **Zero-one domination** [MohriRostamizadehTalwalkar2018, Section 5.4]: for `ρ > 0`, the
`ρ`-margin loss dominates the nonpositive-margin indicator `𝟙[u ≤ 0]`. -/
theorem boole_le_marginLoss {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    (if u ≤ 0 then (1 : ℝ) else 0) ≤ marginLoss ρ u := by
  split_ifs with hu
  · rw [marginLoss_of_nonpos hρ hu]
  · exact marginLoss_nonneg ρ u

/-- **Margin-violation upper bound** [MohriRostamizadehTalwalkar2018, (5.37)]: for `ρ > 0`, the
`ρ`-margin loss is bounded above by the indicator `𝟙[u ≤ ρ]`. -/
theorem marginLoss_le_boole {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    marginLoss ρ u ≤ if u ≤ ρ then 1 else 0 := by
  split_ifs with hu
  · exact marginLoss_le_one ρ u
  · rw [marginLoss_of_ge hρ (le_of_not_ge hu)]

/-- For `ρ ≥ 0`, `marginLoss ρ` is `(1 / ρ)`-Lipschitz
[MohriRostamizadehTalwalkar2018, Section 5.4]. -/
theorem lipschitzWith_marginLoss {ρ : ℝ} (hρ : 0 ≤ ρ) :
    LipschitzWith (1 / ρ).toNNReal (marginLoss ρ) := by
  have hlin : LipschitzWith (1 / ρ).toNNReal (fun u : ℝ => 1 - u / ρ) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (one_div_nonneg.2 hρ),
      show (1 - x / ρ) - (1 - y / ρ) = (y - x) / ρ by ring, abs_div, abs_of_nonneg hρ,
      abs_sub_comm, div_eq_inv_mul, one_div]
  exact (hlin.const_max 0).const_min 1

/-- `NNReal`-parameterized form of `lipschitzWith_marginLoss`:
`LipschitzWith (1 / ρ) (marginLoss ρ)`. -/
theorem lipschitzWith_marginLoss_nnreal (ρ : ℝ≥0) :
    LipschitzWith (1 / ρ) (marginLoss ρ) := by
  have h := lipschitzWith_marginLoss ρ.coe_nonneg
  rwa [one_div, ← NNReal.coe_inv, Real.toNNReal_coe, ← one_div] at h

private theorem lipschitzWith_marginLoss_signVal_mul {ρ : ℝ} (hρ : 0 ≤ ρ) (y : Bool) :
    LipschitzWith (1 / ρ).toNNReal (fun u : ℝ => marginLoss ρ (signVal y * u)) := by
  have hsign : LipschitzWith 1 (fun u : ℝ => signVal y * u) := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_signVal, NNReal.coe_one]
  have h := (lipschitzWith_marginLoss hρ).comp hsign
  rwa [mul_one] at h

/-! ### Empirical and population margin losses -/

variable {α : Type*}

/-- The **empirical `ρ`-margin loss**
`R̂_{S, ρ}(h) = (1 / m) ∑ i, Φ_ρ (signVal (S i).2 * h (S i).1)` of a real-valued hypothesis
`h : α → ℝ` on a labeled sample `S : Fin m → α × Bool`
[MohriRostamizadehTalwalkar2018, Definition 5.6]. -/
noncomputable def empiricalMarginLoss (ρ : ℝ) (h : α → ℝ) {m : ℕ} (S : Fin m → α × Bool) : ℝ :=
  𝔼 i, marginLoss ρ (signVal (S i).2 * h (S i).1)

theorem empiricalMarginLoss_def (ρ : ℝ) (h : α → ℝ) {m : ℕ} (S : Fin m → α × Bool) :
    empiricalMarginLoss ρ h S = 𝔼 i, marginLoss ρ (signVal (S i).2 * h (S i).1) := by
  rw [empiricalMarginLoss]

theorem empiricalMarginLoss_nonneg (ρ : ℝ) (h : α → ℝ) {m : ℕ} (S : Fin m → α × Bool) :
    0 ≤ empiricalMarginLoss ρ h S :=
  Finset.expect_nonneg fun _ _ => marginLoss_nonneg _ _

theorem empiricalMarginLoss_le_one (ρ : ℝ) (h : α → ℝ) {m : ℕ} (S : Fin m → α × Bool) :
    empiricalMarginLoss ρ h S ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [empiricalMarginLoss]
  · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact Finset.expect_le Finset.univ_nonempty fun _ _ => marginLoss_le_one _ _

/-- The empirical `ρ`-margin loss is at most the fraction of sample points with signed margin at
most `ρ` [MohriRostamizadehTalwalkar2018, (5.37)]. -/
theorem empiricalMarginLoss_le_count_div {ρ : ℝ} (hρ : 0 < ρ) (h : α → ℝ) {m : ℕ}
    (S : Fin m → α × Bool) :
    empiricalMarginLoss ρ h S ≤
      ((Finset.univ.filter fun i : Fin m => signVal (S i).2 * h (S i).1 ≤ ρ).card : ℝ) / m := by
  classical
  rw [empiricalMarginLoss_def, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    Finset.card_filter, Nat.cast_sum]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg m)
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    marginLoss_le_boole hρ (signVal (S i).2 * h (S i).1)

/-- The **population `ρ`-margin loss** `E_{(x, y) ∼ D}[Φ_ρ(signVal y * h x)]` of `h : α → ℝ` under
`D : PMF (α × Bool)` on a finite domain `α`. -/
noncomputable def marginRisk [Fintype α] (D : PMF (α × Bool)) (ρ : ℝ) (h : α → ℝ) : ℝ :=
  ∑ p : α × Bool, (D p).toReal * marginLoss ρ (signVal p.2 * h p.1)

theorem marginRisk_def [Fintype α] (D : PMF (α × Bool)) (ρ : ℝ) (h : α → ℝ) :
    marginRisk D ρ h = ∑ p : α × Bool, (D p).toReal * marginLoss ρ (signVal p.2 * h p.1) := by
  rw [marginRisk]

theorem marginRisk_nonneg [Fintype α] (D : PMF (α × Bool)) (ρ : ℝ) (h : α → ℝ) :
    0 ≤ marginRisk D ρ h :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (marginLoss_nonneg _ _)

theorem marginRisk_le_one [Fintype α] (D : PMF (α × Bool)) (ρ : ℝ) (h : α → ℝ) :
    marginRisk D ρ h ≤ 1 :=
  Probability.PMF.sum_mul_le D _ _ fun _ => marginLoss_le_one _ _

/-- For `ρ > 0`, the population misclassification probability `Pr_D[signVal y * h x ≤ 0]` is at most
the population `ρ`-margin loss. -/
theorem marginError_le_marginRisk [Fintype α] (D : PMF (α × Bool)) {ρ : ℝ} (hρ : 0 < ρ)
    (h : α → ℝ) :
    (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal ≤ marginRisk D ρ h := by
  classical
  rw [Probability.PMF.toOuterMeasure_apply_toReal, marginRisk_def]
  refine Finset.sum_le_sum fun p _ => ?_
  have hdom := boole_le_marginLoss hρ (signVal p.2 * h p.1)
  by_cases hp : signVal p.2 * h p.1 ≤ 0
  · simp only [Set.mem_ofPred_eq, hp, ↓reduceIte] at hdom ⊢
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdom ENNReal.toReal_nonneg
  · simp only [Set.mem_ofPred_eq, hp, ↓reduceIte]
    exact mul_nonneg ENNReal.toReal_nonneg (marginLoss_nonneg _ _)

/-! ### The `ρ`-margin loss class and contraction -/

/-- The class of `ρ`-margin loss functions `(x, y) ↦ Φ_ρ (signVal y * h x)` induced by a
real-valued hypothesis class `H : Set (α → ℝ)`. -/
noncomputable def marginLossClass (ρ : ℝ) (H : Set (α → ℝ)) : Set (α × Bool → ℝ) :=
  (fun (h : α → ℝ) (p : α × Bool) => marginLoss ρ (signVal p.2 * h p.1)) '' H

theorem mem_marginLossClass {ρ : ℝ} {H : Set (α → ℝ)} {f : α × Bool → ℝ} :
    f ∈ marginLossClass ρ H ↔
      ∃ h ∈ H, (fun p : α × Bool => marginLoss ρ (signVal p.2 * h p.1)) = f := by
  rw [marginLossClass, Set.mem_image]

/-- Functions in `marginLossClass ρ H` take values in `[0, 1]`. -/
theorem mem_Icc_of_mem_marginLossClass {ρ : ℝ} {H : Set (α → ℝ)} {f : α × Bool → ℝ}
    (hf : f ∈ marginLossClass ρ H) (p : α × Bool) : f p ∈ Set.Icc 0 1 := by
  obtain ⟨h, -, rfl⟩ := mem_marginLossClass.1 hf
  exact marginLoss_mem_Icc ρ _

/-- **Contraction of `marginLossClass` (empirical)** [MohriRostamizadehTalwalkar2018, proof of
Theorem 5.8]: for `ρ ≥ 0` and a uniformly bounded class `H : Set (α → ℝ)`, the empirical Rademacher
complexity of `marginLossClass ρ H` on `S` is at most `(1 / ρ)` times that of `H` on the unlabeled
points `fun i => (S i).1`. -/
theorem empiricalRademacherComplexity_marginLossClass_le {ρ : ℝ} (hρ : 0 ≤ ρ)
    {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B) {m : ℕ} (S : Fin m → α × Bool) :
    empiricalRademacherComplexity (marginLossClass ρ H) S ≤
      (1 / ρ) * empiricalRademacherComplexity H (fun i => (S i).1) := by
  have h := empiricalRademacherComplexity_image_comp_le_of_map hH Prod.fst
    (fun p : α × Bool => lipschitzWith_marginLoss_signVal_mul hρ p.2) S
  rwa [Real.coe_toNNReal _ (one_div_nonneg.2 hρ)] at h

/-- **Contraction of `marginLossClass` (population)** [MohriRostamizadehTalwalkar2018, proof of
Theorem 5.8]: for `ρ ≥ 0` and a uniformly bounded class `H : Set (α → ℝ)` on a finite domain `α`,
the Rademacher complexity of `marginLossClass ρ H` under `D` is at most `(1 / ρ)` times that of `H`
under `D.map Prod.fst`. -/
theorem rademacherComplexity_marginLossClass_le [Fintype α] (D : PMF (α × Bool)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B) (m : ℕ) :
    rademacherComplexity D (marginLossClass ρ H) m ≤
      (1 / ρ) * rademacherComplexity (D.map Prod.fst) H m := by
  have h := rademacherComplexity_image_comp_le_of_map D hH Prod.fst
    (fun p : α × Bool => lipschitzWith_marginLoss_signVal_mul hρ p.2) m
  rwa [Real.coe_toNNReal _ (one_div_nonneg.2 hρ)] at h

/-! ### Margin generalization bounds -/

private theorem two_mul_le_two_div_mul {ρ x y : ℝ} (h : x ≤ (1 / ρ) * y) :
    2 * x ≤ 2 / ρ * y := by
  rw [div_eq_mul_one_div, mul_assoc]
  exact mul_le_mul_of_nonneg_left h zero_le_two

/-- Population `ρ`-margin risk generalization bound via `R_m(H)`. -/
theorem rademacherComplexity_marginRisk_bound [Fintype α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, empiricalMarginLoss ρ h S +
        2 / ρ * rademacherComplexity (D.map Prod.fst) H m +
          √(Real.log (1 / δ) / (2 * m)) < marginRisk D ρ h}).toReal ≤ δ := by
  have hmul := two_mul_le_two_div_mul (rademacherComplexity_marginLossClass_le D hρ.le hH m)
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (rademacherComplexity_generalization_bound D hm zero_lt_one (F := marginLossClass ρ H)
      (fun _ hf => mem_Icc_of_mem_marginLossClass hf) hδ)
  rintro S ⟨h, hh, hlt⟩
  refine ⟨fun p => marginLoss ρ (signVal p.2 * h p.1), mem_marginLossClass.2 ⟨h, hh, rfl⟩, ?_⟩
  rw [← empiricalMarginLoss_def, ← marginRisk_def, sub_zero, one_mul]
  linarith

/-- Data-dependent population `ρ`-margin risk generalization bound via `R̂_{S_X}(H)`. -/
theorem empiricalRademacherComplexity_marginRisk_bound [Fintype α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, empiricalMarginLoss ρ h S +
        2 / ρ * empiricalRademacherComplexity H (fun i => (S i).1) +
          3 * √(Real.log (2 / δ) / (2 * m)) < marginRisk D ρ h}).toReal ≤ δ := by
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (empiricalRademacherComplexity_generalization_bound D hm zero_lt_one (F := marginLossClass ρ H)
      (fun _ hf => mem_Icc_of_mem_marginLossClass hf) hδ)
  rintro S ⟨h, hh, hlt⟩
  have hmul := two_mul_le_two_div_mul (empiricalRademacherComplexity_marginLossClass_le hρ.le hH S)
  refine ⟨fun p => marginLoss ρ (signVal p.2 * h p.1), mem_marginLossClass.2 ⟨h, hh, rfl⟩, ?_⟩
  rw [← empiricalMarginLoss_def, ← marginRisk_def, sub_zero, one_mul]
  linarith

/-- **Margin generalization bound** [MohriRostamizadehTalwalkar2018, Theorem 5.8, (5.39)]: for a
uniformly bounded class `H : Set (α → ℝ)` on a finite domain `α`, margin `ρ > 0`, and `m > 0`
independent draws from `D : PMF (α × Bool)`, with probability at least `1 - δ` every `h ∈ H`
satisfies
`Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (2 / ρ) R_m(H) + √(log (1 / δ) / (2 m))`,
where `R_m(H)` is taken under the marginal `D.map Prod.fst`. -/
theorem rademacherComplexity_margin_bound [Fintype α] (D : PMF (α × Bool)) {m : ℕ} (hm : 0 < m)
    {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, empiricalMarginLoss ρ h S +
        2 / ρ * rademacherComplexity (D.map Prod.fst) H m +
          √(Real.log (1 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (rademacherComplexity_marginRisk_bound D hm hH hρ hδ)
  rintro S ⟨h, hh, hlt⟩
  exact ⟨h, hh, hlt.trans_le (marginError_le_marginRisk D hρ h)⟩

/-- **Data-dependent margin generalization bound** [MohriRostamizadehTalwalkar2018, Theorem 5.8,
(5.40)]: for a uniformly bounded class `H : Set (α → ℝ)` on a finite domain `α`, margin `ρ > 0`,
and `m > 0` independent draws from `D : PMF (α × Bool)`, with probability at least `1 - δ` every
`h ∈ H` satisfies
`Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (2 / ρ) R̂_{S_X}(H) + 3 √(log (2 / δ) / (2 m))`,
where `S_X` is the sequence of unlabeled inputs `fun i => (S i).1`. -/
theorem empiricalRademacherComplexity_margin_bound [Finite α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, empiricalMarginLoss ρ h S +
        2 / ρ * empiricalRademacherComplexity H (fun i => (S i).1) +
          3 * √(Real.log (2 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  have := Fintype.ofFinite α
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (empiricalRademacherComplexity_marginRisk_bound D hm hH hρ hδ)
  rintro S ⟨h, hh, hlt⟩
  exact ⟨h, hh, hlt.trans_le (marginError_le_marginRisk D hρ h)⟩

/-- **Finite-class margin bound** through Massart's lemma [MohriRostamizadehTalwalkar2018,
Theorems 3.7 and 5.8]: for a finite class `H : Finset (α → ℝ)` with values in `[-B, B]` (`B ≥ 0`),
margin `ρ > 0`, and `m > 0` independent draws from `D`, with probability at least `1 - δ` every
`h ∈ H` satisfies
`Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (2 B / ρ) √(2 log |H| / m) + √(log (1 / δ) / (2 m))`. -/
theorem margin_bound_of_finset [Finite α] (D : PMF (α × Bool)) {m : ℕ} (hm : 0 < m)
    {H : Finset (α → ℝ)} {B : ℝ} (hB : 0 ≤ B) (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, empiricalMarginLoss ρ h S +
        2 * B / ρ * √(2 * Real.log H.card / m) + √(Real.log (1 / δ) / (2 * m)) <
          (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  have := Fintype.ofFinite α
  have hR : rademacherComplexity (D.map Prod.fst) (H : Set (α → ℝ)) m ≤
      B * √(2 * Real.log H.card / m) :=
    rademacherComplexity_le_of_finset (D.map Prod.fst) hB hH m
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (rademacherComplexity_margin_bound D hm (H := (H : Set (α → ℝ))) hH hρ hδ)
  rintro S ⟨h, hh, hlt⟩
  refine ⟨h, hh, ?_⟩
  have hmul : 2 / ρ * rademacherComplexity (D.map Prod.fst) (H : Set (α → ℝ)) m ≤
      2 * B / ρ * √(2 * Real.log H.card / m) := by
    have hpos : 0 ≤ 2 / ρ := div_nonneg zero_le_two hρ.le
    calc 2 / ρ * rademacherComplexity (D.map Prod.fst) (H : Set (α → ℝ)) m
        ≤ 2 / ρ * (B * √(2 * Real.log H.card / m)) := mul_le_mul_of_nonneg_left hR hpos
      _ = 2 * B / ρ * √(2 * Real.log H.card / m) := by ring
  linarith

end Cslib.MachineLearning
