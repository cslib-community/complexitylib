/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.PACLearning.ERM
public import Complexity.MachineLearning.PACLearning.VCUpperBound
public import Complexity.MachineLearning.Rademacher.Generalization
public import Complexity.MachineLearning.Rademacher.GrowthFunction
import Complexity.Probability.PMF.Expect
import Complexity.Probability.Product

/-!
# Rademacher bounds for binary classification

For a binary concept class `C` on a finite domain `α` and a distribution `D` on labeled examples
`α × Bool`, the 0-1 losses `(x, y) ↦ 𝟙[h x ≠ y]` of the concepts `h ∈ C` form the class
`bitClass (lossClass C)` of `{0, 1}`-valued functions. Its empirical Rademacher complexity on a
labeled sample `S` is half that of the sign class `signClass C` on the unlabeled points of `S`
[MohriRostamizadehTalwalkar2018, Lemma 3.4]; taking expectations, its Rademacher complexity under
`D` is half that of `signClass C` under the marginal `D.map Prod.fst`. With the general Rademacher
generalization bound (`Complexity.MachineLearning.Rademacher.Generalization`) this gives, with
probability at least `1 - δ` over `m` independent examples, for every `h ∈ C`,

`err_D(h) ≤ err_S(h) + R_m(signClass C) + √(log (1 / δ) / (2 m))`

[MohriRostamizadehTalwalkar2018, Theorem 3.5], where `err_D(h)` is the probability that `h`
misclassifies an example drawn from `D` and `err_S(h)` is its empirical error on `S`. Bounding
the Rademacher complexity by the growth function or through Sauer's lemma gives the growth-function
and VC-dimension generalization bounds [MohriRostamizadehTalwalkar2018, Corollaries 3.9 and 3.19].

For an empirical risk minimizer `A` for `C`, the uniform bound at confidence `δ / 2` and the
Rademacher bound for a single comparator at confidence `δ / 2` give the agnostic guarantee
`err_D(A S) ≤ err_D(c) + R_m(signClass C) + √(2 log (2 / δ) / m)` for every `c ∈ C`, and thus the
VC-dimension rate `√(2 d log (e m / d) / m) + √(2 log (2 / δ) / m)` against the best concept of
`C`. The comparator bound is Hoeffding's inequality, obtained here from the generalization bound
for the singleton class `{-𝟙[c x ≠ y]}`, whose Rademacher complexity is `0`.

The domain is a finite type, so that distributions are probability mass functions and the finite
McDiarmid inequality applies; the source states the results for an arbitrary input space.
Probabilities are the outer measures of the product mass function `Probability.PMF.pi`, true errors
are `(D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal`, and empirical errors are
`empiricalMiscount h S / m`.

## Main definitions

* `Cslib.MachineLearning.bitClass`: the `{0, 1}`-valued functions `bitVal ℝ ∘ c` for `c ∈ C`.

## Main results

* `Cslib.MachineLearning.empiricalRademacherComplexity_bitClass_lossClass`,
  `Cslib.MachineLearning.rademacherComplexity_bitClass_lossClass`: the 0-1 loss class has half the
  (empirical) Rademacher complexity of the sign class [MohriRostamizadehTalwalkar2018, Lemma 3.4].
* `Cslib.MachineLearning.rademacherComplexity_classification_bound`,
  `Cslib.MachineLearning.empiricalRademacherComplexity_classification_bound`: the Rademacher
  bounds (3.17) and (3.18) for binary classification [MohriRostamizadehTalwalkar2018,
  Theorem 3.5].
* `Cslib.MachineLearning.growthFunction_classification_bound`: the growth-function bound
  [MohriRostamizadehTalwalkar2018, Corollary 3.9].
* `Cslib.MachineLearning.vc_classification_bound`: the VC-dimension bound
  [MohriRostamizadehTalwalkar2018, Corollary 3.19].
* `Cslib.MachineLearning.PACLearning.IsERM.rademacherComplexity_agnostic_bound`,
  `Cslib.MachineLearning.PACLearning.IsERM.vc_agnostic_bound`: empirical risk minimization is
  within `R_m(signClass C) + √(2 log (2 / δ) / m)`, respectively
  `√(2 d log (e m / d) / m) + √(2 log (2 / δ) / m)`, of the best concept of `C`.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Sections 3.1 to 3.3
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-! ### The 0-1 loss class -/

/-- The `{0, 1}`-valued functions `x ↦ bitVal ℝ (c x)` of a binary concept class `C`. Applied to
`lossClass C`, these are the 0-1 losses `(x, y) ↦ 𝟙[h x ≠ y]` of the concepts `h ∈ C`. -/
def bitClass (C : ConceptClass α Bool) : Set (α → ℝ) :=
  (fun c x => bitVal ℝ (c x)) '' C

theorem mem_bitClass {C : ConceptClass α Bool} {f : α → ℝ} :
    f ∈ bitClass C ↔ ∃ c ∈ C, (fun x => bitVal ℝ (c x)) = f := by
  rw [bitClass, Set.mem_image]

/-- The 0-1 losses of the concepts of `C` as functions on labeled examples. -/
theorem mem_bitClass_lossClass {C : ConceptClass α Bool} {f : α × Bool → ℝ} :
    f ∈ bitClass (lossClass C) ↔
      ∃ h ∈ C, (fun p : α × Bool => bitVal ℝ (decide (h p.1 ≠ p.2))) = f := by
  rw [mem_bitClass]
  constructor
  · rintro ⟨_, hl, rfl⟩
    obtain ⟨h, hh, rfl⟩ := mem_lossClass.1 hl
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, mem_lossClass.2 ⟨h, hh, rfl⟩, rfl⟩

/-- Functions of `bitClass C` take values in `[0, 1]`. -/
theorem mem_Icc_of_mem_bitClass {C : ConceptClass α Bool} {f : α → ℝ} (hf : f ∈ bitClass C)
    (x : α) : f x ∈ Set.Icc 0 1 := by
  obtain ⟨c, -, rfl⟩ := mem_bitClass.1 hf
  change bitVal ℝ (c x) ∈ Set.Icc 0 1
  cases c x <;> simp

/-- The 0-1 loss in terms of signs: `𝟙[a ≠ y] = 1 / 2 + (1 / 2) · signVal (!y) · signVal a`. -/
private theorem bitVal_decide_ne (a y : Bool) :
    bitVal ℝ (decide (a ≠ y)) = 1 / 2 + 1 / 2 * (signVal (!y) * signVal a) := by
  cases a <;> cases y <;> norm_num

/-- **The 0-1 loss class** [MohriRostamizadehTalwalkar2018, Lemma 3.4]: on a labeled sample `S`,
the empirical Rademacher complexity of the 0-1 losses of `C` is half that of `signClass C` on the
unlabeled points `x_i = (S i).1`. -/
theorem empiricalRademacherComplexity_bitClass_lossClass (C : ConceptClass α Bool) {m : ℕ}
    (S : Fin m → α × Bool) :
    empiricalRademacherComplexity (bitClass (lossClass C)) S =
      empiricalRademacherComplexity (signClass C) (fun i => (S i).1) / 2 := by
  have hsign : ∀ (f : signClass C) (i : Fin m), |(f : α → ℝ) (S i).1| ≤ 1 :=
    fun f i => abs_le_one_of_mem_signClass f.2 _
  have hloss : ∀ (f : bitClass (lossClass C)) (i : Fin m), |(f : α × Bool → ℝ) (S i)| ≤ 1 :=
    fun f i => by
      have := mem_Icc_of_mem_bitClass f.2 (S i)
      exact abs_le.2 ⟨by linarith [this.1], this.2⟩
  have haff := rademacherAverage_add_mul_signVal_mul hsign (fun _ => 1 / 2)
    (fun i => !(S i).2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [empiricalRademacherComplexity_def, empiricalRademacherComplexity_def, div_eq_inv_mul,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← haff]
  refine rademacherAverage_eq_of_forall_exists (B := 1) hloss ?_ ?_ ?_
  · intro f i
    have h1 := abs_le.1 (hsign f i)
    rw [abs_le]
    constructor <;> cases (S i).2 <;> simp only [Bool.not_false, Bool.not_true, signVal_true,
      signVal_false] <;> linarith [h1.1, h1.2]
  · rintro ⟨f, hf⟩
    obtain ⟨h, hh, rfl⟩ := mem_bitClass_lossClass.1 hf
    refine ⟨⟨fun x => signVal (h x), mem_signClass.2 ⟨h, hh, rfl⟩⟩, funext fun i => ?_⟩
    exact bitVal_decide_ne _ _
  · rintro ⟨f, hf⟩
    obtain ⟨h, hh, rfl⟩ := mem_signClass.1 hf
    refine ⟨⟨fun p => bitVal ℝ (decide (h p.1 ≠ p.2)), mem_bitClass_lossClass.2 ⟨h, hh, rfl⟩⟩,
      funext fun i => ?_⟩
    exact (bitVal_decide_ne _ _).symm

/-- The average 0-1 loss on a labeled sample is the empirical error `empiricalMiscount h S / m`. -/
theorem expect_bitVal_decide_ne {m : ℕ} (h : α → Bool) (S : Fin m → α × Bool) :
    𝔼 i, bitVal ℝ (decide (h (S i).1 ≠ (S i).2)) = (empiricalMiscount h S : ℝ) / m := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, empiricalMiscount, Finset.card_filter,
    Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : h (S i).1 = (S i).2 <;> simp [hi, bitVal]


/-- **The 0-1 loss class**, in expectation [MohriRostamizadehTalwalkar2018, Lemma 3.4 and the
remark after it]: under a distribution `D` on labeled examples, the Rademacher complexity of the
0-1 losses of `C` is half that of `signClass C` under the marginal distribution `D.map Prod.fst`
of the unlabeled points. -/
theorem rademacherComplexity_bitClass_lossClass [Fintype α] (D : PMF (α × Bool))
    (C : ConceptClass α Bool) (m : ℕ) :
    rademacherComplexity D (bitClass (lossClass C)) m =
      rademacherComplexity (D.map Prod.fst) (signClass C) m / 2 := by
  rw [rademacherComplexity_def, rademacherComplexity_def, Probability.PMF.pi_map,
    Probability.PMF.sum_map_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [empiricalRademacherComplexity_bitClass_lossClass, mul_div_assoc]

/-- The expected 0-1 loss under `D` is the probability that `h` misclassifies an example drawn
from `D`. -/
theorem sum_mul_bitVal_decide_ne [Fintype α] (D : PMF (α × Bool)) (h : α → Bool) :
    ∑ p, (D p).toReal * bitVal ℝ (decide (h p.1 ≠ p.2)) =
      (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal := by
  rw [Probability.PMF.toOuterMeasure_apply_toReal]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : h p.1 = p.2 <;> simp [hp, bitVal]

/-! ### Generalization bounds -/

/-- **Rademacher bound for binary classification** [MohriRostamizadehTalwalkar2018, Theorem 3.5,
(3.17)]: with probability at least `1 - δ` over `m > 0` independent examples from `D`, every
`h ∈ C` satisfies `err_D(h) ≤ err_S(h) + R_m(signClass C) + √(log (1 / δ) / (2 m))`, where the
Rademacher complexity is taken under the marginal `D.map Prod.fst`. The domain is finite. -/
theorem rademacherComplexity_classification_bound [Fintype α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) (C : ConceptClass α Bool) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ C, (empiricalMiscount h S : ℝ) / m +
        rademacherComplexity (D.map Prod.fst) (signClass C) m +
          √(Real.log (1 / δ) / (2 * m)) < (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal}).toReal ≤
      δ := by
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (rademacherComplexity_generalization_bound D hm zero_lt_one (F := bitClass (lossClass C))
      (fun f hf => mem_Icc_of_mem_bitClass hf) hδ)
  rintro S ⟨h, hh, hlt⟩
  refine ⟨fun p => bitVal ℝ (decide (h p.1 ≠ p.2)), mem_bitClass_lossClass.2 ⟨h, hh, rfl⟩, ?_⟩
  rw [expect_bitVal_decide_ne, sum_mul_bitVal_decide_ne, rademacherComplexity_bitClass_lossClass,
    sub_zero, one_mul]
  linarith

/-- **Data-dependent Rademacher bound for binary classification** [MohriRostamizadehTalwalkar2018,
Theorem 3.5, (3.18)]: with probability at least `1 - δ` over `m > 0` independent examples from
`D`, every `h ∈ C` satisfies
`err_D(h) ≤ err_S(h) + R̂_{S_X}(signClass C) + 3 √(log (2 / δ) / (2 m))`, where `S_X` is the
sequence of unlabeled points of `S`. The domain is finite. -/
theorem empiricalRademacherComplexity_classification_bound [Finite α] (D : PMF (α × Bool))
    {m : ℕ} (hm : 0 < m) (C : ConceptClass α Bool) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ C, (empiricalMiscount h S : ℝ) / m +
        empiricalRademacherComplexity (signClass C) (fun i => (S i).1) +
          3 * √(Real.log (2 / δ) / (2 * m)) < (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal}).toReal ≤
      δ := by
  have := Fintype.ofFinite α
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (empiricalRademacherComplexity_generalization_bound D hm zero_lt_one
      (F := bitClass (lossClass C)) (fun f hf => mem_Icc_of_mem_bitClass hf) hδ)
  rintro S ⟨h, hh, hlt⟩
  refine ⟨fun p => bitVal ℝ (decide (h p.1 ≠ p.2)), mem_bitClass_lossClass.2 ⟨h, hh, rfl⟩, ?_⟩
  rw [expect_bitVal_decide_ne, sum_mul_bitVal_decide_ne,
    empiricalRademacherComplexity_bitClass_lossClass, sub_zero, one_mul]
  linarith

/-- **Growth-function generalization bound** [MohriRostamizadehTalwalkar2018, Corollary 3.9]: with
probability at least `1 - δ` over `m > 0` independent examples from `D`, every `h ∈ C` satisfies
`err_D(h) ≤ err_S(h) + √(2 log Π_C(m) / m) + √(log (1 / δ) / (2 m))`. The domain is finite. -/
theorem growthFunction_classification_bound [Finite α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) (C : ConceptClass α Bool) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ C, (empiricalMiscount h S : ℝ) / m + √(2 * Real.log (growthFunction C m) / m) +
          √(Real.log (1 / δ) / (2 * m)) < (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal}).toReal ≤
      δ := by
  have := Fintype.ofFinite α
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (rademacherComplexity_classification_bound D hm C hδ)
  rintro S ⟨h, hh, hlt⟩
  refine ⟨h, hh, ?_⟩
  linarith [rademacherComplexity_signClass_le (D.map Prod.fst) C m]

/-- **VC-dimension generalization bound** [MohriRostamizadehTalwalkar2018, Corollary 3.19]: if
every finite set shattered by `C` has at most `d` points, then for `m ≥ d` and `m > 0`, with
probability at least `1 - δ` over `m` independent examples from `D`, every `h ∈ C` satisfies
`err_D(h) ≤ err_S(h) + √(2 d log (e m / d) / m) + √(log (1 / δ) / (2 m))`. The source assumes
`m ≥ d` implicitly through Corollary 3.18. The domain is finite. -/
theorem vc_classification_bound [Finite α] (D : PMF (α × Bool)) {C : ConceptClass α Bool}
    {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (hm : 0 < m)
    (hdm : d ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ C, (empiricalMiscount h S : ℝ) / m +
        √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) +
          √(Real.log (1 / δ) / (2 * m)) < (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal}).toReal ≤
      δ := by
  have := Fintype.ofFinite α
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (rademacherComplexity_classification_bound D hm C hδ)
  rintro S ⟨h, hh, hlt⟩
  refine ⟨h, hh, ?_⟩
  linarith [rademacherComplexity_signClass_le_vc (D.map Prod.fst) hC hdm]

/-! ### Empirical risk minimization -/

/-- **Hoeffding's upper tail for one concept**, from the Rademacher bound for the singleton class
`{-𝟙[c x ≠ y]}`: with probability at least `1 - δ`,
`err_S(c) ≤ err_D(c) + √(log (1 / δ) / (2 m))`. -/
private theorem empiricalMiscount_div_le [Finite α] (D : PMF (α × Bool)) {m : ℕ} (hm : 0 < m)
    (c : α → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal + √(Real.log (1 / δ) / (2 * m)) <
        (empiricalMiscount c S : ℝ) / m}).toReal ≤ δ := by
  have := Fintype.ofFinite α
  have hrange : ∀ f ∈ ({fun p => -bitVal ℝ (decide (c p.1 ≠ p.2))} : Set (α × Bool → ℝ)),
      ∀ z, f z ∈ Set.Icc (-1) 0 := by
    rintro f rfl z
    by_cases hz : c z.1 = z.2 <;> simp [hz, bitVal]
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (rademacherComplexity_generalization_bound D hm (by norm_num) hrange hδ)
  intro S hS
  refine ⟨_, rfl, ?_⟩
  simp only [Set.mem_ofPred_eq] at hS ⊢
  rw [Finset.expect_neg_distrib, expect_bitVal_decide_ne, rademacherComplexity_singleton]
  simp only [mul_neg, Finset.sum_neg_distrib, sum_mul_bitVal_decide_ne]
  linarith

/-- Empirical risk minimization against one comparator `c ∈ C`. -/
private theorem PACLearning.IsERM.rademacherComplexity_le_add [Fintype α] (D : PMF (α × Bool))
    {m : ℕ} (hm : 0 < m) {C : ConceptClass α Bool} {A : Learner α Bool m} (hA : IsERM A C)
    {c : α → Bool} (hc : c ∈ C) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal +
        rademacherComplexity (D.map Prod.fst) (signClass C) m + √(2 * Real.log (2 / δ) / m) <
          (D.toOuterMeasure {p | A S p.1 ≠ p.2}).toReal}).toReal ≤ δ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hε : √(2 * Real.log (2 / δ) / m) = 2 * √(Real.log (1 / (δ / 2)) / (2 * m)) := by
    rw [one_div_div, show 2 * Real.log (2 / δ) / m = 2 ^ 2 * (Real.log (2 / δ) / (2 * m)) by
      field_simp, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h₁ := rademacherComplexity_classification_bound D hm C (half_pos hδ)
  have h₂ := empiricalMiscount_div_le D hm c (half_pos hδ)
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono
      (s₂ := {S | ∃ h ∈ C, (empiricalMiscount h S : ℝ) / m +
        rademacherComplexity (D.map Prod.fst) (signClass C) m +
          √(Real.log (1 / (δ / 2)) / (2 * m)) < (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal} ∪
        {S | (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal + √(Real.log (1 / (δ / 2)) / (2 * m)) <
          (empiricalMiscount c S : ℝ) / m}) ?_)) ?_
  · intro S hS
    by_contra hS'
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hS hS'
    obtain ⟨hAC, hmin⟩ := hA S
    have hmis : (empiricalMiscount (A S) S : ℝ) / m ≤ (empiricalMiscount c S : ℝ) / m :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmin c hc) hm'.le
    linarith [hS'.1 (A S) hAC, hS'.2]
  · refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨Probability.PMF.toOuterMeasure_ne_top _ _,
      Probability.PMF.toOuterMeasure_ne_top _ _⟩) (MeasureTheory.measure_union_le _ _)).trans ?_
    rw [ENNReal.toReal_add (Probability.PMF.toOuterMeasure_ne_top _ _)
      (Probability.PMF.toOuterMeasure_ne_top _ _)]
    linarith

/-- **Agnostic learning by empirical risk minimization**: with probability at least `1 - δ` over
`m > 0` independent examples from `D`, an empirical risk minimizer `A` for `C` satisfies
`err_D(A S) ≤ err_D(c) + R_m(signClass C) + √(2 log (2 / δ) / m)` simultaneously for every
`c ∈ C`, that is, it is within this margin of the best concept of `C`. The Rademacher complexity
is taken under the marginal `D.map Prod.fst`. This combines (3.17) of
[MohriRostamizadehTalwalkar2018, Theorem 3.5] at confidence `δ / 2` with Hoeffding's upper tail
for a best concept at confidence `δ / 2`; compare the agnostic analysis of
[ShalevShwartzBenDavid2014, Chapter 26], whose constants differ. The domain is finite. -/
theorem PACLearning.IsERM.rademacherComplexity_agnostic_bound [Fintype α] (D : PMF (α × Bool))
    {m : ℕ} (hm : 0 < m) {C : ConceptClass α Bool} {A : Learner α Bool m} (hA : IsERM A C)
    {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ c ∈ C, (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal +
        rademacherComplexity (D.map Prod.fst) (signClass C) m + √(2 * Real.log (2 / δ) / m) <
          (D.toOuterMeasure {p | A S p.1 ≠ p.2}).toReal}).toReal ≤ δ := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
      MeasureTheory.measure_empty, ENNReal.toReal_zero]
    exact hδ.le
  obtain ⟨c₀, hc₀, hmin⟩ := Set.exists_min_image C
    (fun c => (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal) (Set.toFinite C) hne
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (IsERM.rademacherComplexity_le_add D hm hA hc₀ hδ)
  rintro S ⟨c, hc, hlt⟩
  change _ < _
  linarith [hmin c hc]

/-- **Agnostic VC bound for empirical risk minimization**: if every finite set shattered by `C`
has at most `d` points, then for `m ≥ d` and `m > 0`, with probability at least `1 - δ` over `m`
independent examples from `D`, an empirical risk minimizer `A` for `C` satisfies
`err_D(A S) ≤ err_D(c) + √(2 d log (e m / d) / m) + √(2 log (2 / δ) / m)` for every `c ∈ C`, an
excess error of `O(√((d log (m / d) + log (1 / δ)) / m))`. This combines
`PACLearning.IsERM.rademacherComplexity_agnostic_bound` with the VC bound on the Rademacher
complexity [MohriRostamizadehTalwalkar2018, Corollaries 3.8 and 3.18]. The domain is finite. -/
theorem PACLearning.IsERM.vc_agnostic_bound [Finite α] (D : PMF (α × Bool))
    {C : ConceptClass α Bool} {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    {m : ℕ} (hm : 0 < m) (hdm : d ≤ m) {A : Learner α Bool m} (hA : IsERM A C) {δ : ℝ}
    (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ c ∈ C, (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal +
        √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) + √(2 * Real.log (2 / δ) / m) <
          (D.toOuterMeasure {p | A S p.1 ≠ p.2}).toReal}).toReal ≤ δ := by
  have := Fintype.ofFinite α
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (hA.rademacherComplexity_agnostic_bound D hm hδ)
  rintro S ⟨c, hc, hlt⟩
  refine ⟨c, hc, ?_⟩
  linarith [rademacherComplexity_signClass_le_vc (D.map Prod.fst) hC hdm]

end Cslib.MachineLearning
