/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Basic
public import CslibFrontier.Probability.BoundedDifferences
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.BitString.Massart
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Rademacher generalization bounds

For a class `F` of functions from a finite domain `Z` into `[a, b]` and a sample `S` of `m`
independent draws from a distribution `D`, the population mean `∑ z, D z f z` of every `f ∈ F`
exceeds its empirical mean `𝔼 i, f (S i)` by at most twice the Rademacher complexity plus a
deviation term. With probability at least `1 - δ`, for all `f ∈ F`,

* `E_D f ≤ Ê_S f + 2 R_m(F) + (b - a) √(log (1 / δ) / (2 m))`, and
* `E_D f ≤ Ê_S f + 2 R̂_S(F) + 3 (b - a) √(log (2 / δ) / (2 m))`,

[MohriRostamizadehTalwalkar2018, Theorem 3.3] (stated there for `[0, 1]`-valued classes, the case
`a = 0`, `b = 1`); see also [ShalevShwartzBenDavid2014, Chapter 26], and cf.
[BartlettMendelson2002, Theorem 8], a variant for loss classes with a different normalization of the
Rademacher complexity and different constants.
The second bound is data-dependent: its complexity term can be computed from the sample.

The proof has two parts.

* **Symmetrization** [MohriRostamizadehTalwalkar2018, (3.8)–(3.13)]. The expected worst-case gap
  `Φ(S) = sup_{f ∈ F} (E_D f - Ê_S f)` is at most `2 R_m(F)`. Replace `E_D f` by the empirical
  mean on an independent ghost sample `S'`. Exchanging `S i` with `S' i` at the positions where a
  sign vector `σ` is `true` preserves the joint distribution and multiplies the `i`-th difference
  by the sign `σ_i`. Averaging over `σ` and splitting the supremum of the sum bounds the result
  by `R̂_{S'}(F) + R̂_S(F)`.
* **Concentration.** Changing one sample point changes `Φ` and `R̂_S(F)` by at most `(b - a) / m`,
  so McDiarmid's inequality (`Cslib.Probability.HasBoundedDifferences.pi_ge_mean_add`) bounds the
  probability that `Φ` exceeds its mean by `ε`, or that `R̂_S(F)` falls short of `R_m(F)` by `ε`,
  by `exp (-2 m ε² / (b - a)²)`.

Probabilities are the outer measures of the finite product distribution
`Cslib.Probability.PMF.pi`, and each theorem bounds the probability of the failure event by `δ`.

## Main results

* `Cslib.MachineLearning.sum_pi_mul_ciSup_sub_le_two_mul_rademacherComplexity`:
  **symmetrization**, `𝔼_S sup_f (E_D f - Ê_S f) ≤ 2 R_m(F)`.
* `Cslib.MachineLearning.hasBoundedDifferences_empiricalRademacherComplexity`: the empirical
  Rademacher complexity has bounded differences `(b - a) / m`.
* `Cslib.MachineLearning.rademacherComplexity_generalization_bound`: the bound with `R_m(F)`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_generalization_bound`: the data-dependent
  bound with `R̂_S(F)`.
* `Cslib.MachineLearning.rademacher_generalization_bound_of_finset`: a finite class with values in
  `[0, 1]`, through Massart's lemma.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Theorem 3.3
* [P. L. Bartlett, S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and
  structural results*][BartlettMendelson2002], Theorem 8 (a variant with a different
  normalization and constants)
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Chapter 26
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString

variable {Z : Type*}

/-! ### Boundedness helpers -/

/-- The gaps between population and empirical means over a bounded class are bounded above. -/
private theorem bddAbove_range_sub [Fintype Z] (D : PMF Z) {m : ℕ} (hm : 0 < m)
    {F : Set (Z → ℝ)} {B : ℝ} (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (S : Fin m → Z) :
    BddAbove (Set.range fun f : F =>
      ∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i)) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨B + B, ?_⟩
  rintro _ ⟨f, rfl⟩
  have h1 : ∑ z, (D z).toReal * (f : Z → ℝ) z ≤ B :=
    Probability.PMF.sum_mul_le D _ _ fun z => (le_abs_self _).trans (hF f f.2 z)
  have h2 : -B ≤ 𝔼 i, (f : Z → ℝ) (S i) :=
    Finset.le_expect Finset.univ_nonempty fun i _ => neg_le_of_abs_le (hF f f.2 _)
  dsimp only
  linarith

/-! ### Symmetrization -/

section Symmetrization

variable [Fintype Z]

/-- Averaged over the sample, the empirical mean is the population mean. -/
private theorem sum_pi_mul_expect (D : PMF Z) {m : ℕ} (hm : 0 < m) (f : Z → ℝ) :
    ∑ S : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S).toReal * 𝔼 i, f (S i) =
      ∑ z, (D z).toReal * f z := by
  have h := Probability.PMF.sum_pi_mul_sum (fun _ : Fin m => D) (fun _ z => f z)
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, mul_div_assoc', ← Finset.sum_div,
    h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  field_simp

/-- First symmetrization step: replace the population mean by the empirical mean on a ghost
sample `S'`. -/
private theorem ciSup_sub_le_sum (D : PMF Z) {m : ℕ} (hm : 0 < m) {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (S : Fin m → Z) :
    ⨆ f : F, (∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i)) ≤
      ∑ S' : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S').toReal *
        ⨆ f : F, 𝔼 i, ((f : Z → ℝ) (S' i) - (f : Z → ℝ) (S i)) := by
  set P := Probability.PMF.pi fun _ : Fin m => D
  rcases isEmpty_or_nonempty F with hFe | hFe
  · rw [Real.iSup_of_isEmpty]
    refine Finset.sum_nonneg fun S' _ => ?_
    rw [Real.iSup_of_isEmpty, mul_zero]
  refine ciSup_le fun f => ?_
  have hbdd (S' : Fin m → Z) :
      BddAbove (Set.range fun g : F => 𝔼 i, ((g : Z → ℝ) (S' i) - (g : Z → ℝ) (S i))) :=
    Fintype.bddAbove_range_expect _ (B := B + B) fun g i =>
      (le_abs_self _).trans ((abs_sub _ _).trans (by linarith [hF g g.2 (S' i), hF g g.2 (S i)]))
  calc ∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i)
      = ∑ S' : Fin m → Z, (P S').toReal * 𝔼 i, ((f : Z → ℝ) (S' i) - (f : Z → ℝ) (S i)) := by
        simp only [Finset.expect_sub_distrib, mul_sub, Finset.sum_sub_distrib,
          sum_pi_mul_expect D hm, ← Finset.sum_mul, Probability.PMF.sum_toReal, one_mul, P]
    _ ≤ _ := Finset.sum_le_sum fun S' _ =>
        mul_le_mul_of_nonneg_left (le_ciSup (hbdd S') f) ENNReal.toReal_nonneg

/-- Exchange the coordinates of two samples at the positions where `σ` is `true`. -/
private def swapAt {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → Z) × (Fin m → Z)) :
    (Fin m → Z) × (Fin m → Z) :=
  (fun i => if σ i then p.2 i else p.1 i, fun i => if σ i then p.1 i else p.2 i)

omit [Fintype Z] in
private theorem swapAt_involutive {m : ℕ} (σ : Fin m → Bool) :
    Function.Involutive (swapAt (Z := Z) σ) := by
  rintro ⟨x, y⟩
  simp only [swapAt, Prod.mk.injEq]
  constructor <;> funext i <;> cases σ i <;> rfl

-- `Probability.PMF.pi` is computed from the `Fintype` instance of its coordinate type.
set_option linter.unusedFintypeInType false in
/-- Exchanging coordinates of two independent samples preserves their joint weight. -/
private theorem weight_swapAt (D : PMF Z) {m : ℕ} (σ : Fin m → Bool)
    (p : (Fin m → Z) × (Fin m → Z)) :
    ((Probability.PMF.pi fun _ : Fin m => D) (swapAt σ p).1).toReal *
        ((Probability.PMF.pi fun _ : Fin m => D) (swapAt σ p).2).toReal =
      ((Probability.PMF.pi fun _ : Fin m => D) p.1).toReal *
        ((Probability.PMF.pi fun _ : Fin m => D) p.2).toReal := by
  simp only [Probability.PMF.pi_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [swapAt]
  cases σ i
  · rfl
  · exact mul_comm _ _

omit [Fintype Z] in
/-- Exchanging the coordinates where `σ` is `true` flips the sign of those differences. -/
private theorem expect_sub_swapAt {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → Z) × (Fin m → Z))
    (f : Z → ℝ) :
    𝔼 i, (f ((swapAt σ p).2 i) - f ((swapAt σ p).1 i)) =
      𝔼 i, signVal (σ i) * (f (p.2 i) - f (p.1 i)) := by
  refine Finset.expect_congr rfl fun i _ => ?_
  simp only [swapAt]
  cases σ i
  · simp only [Bool.false_eq_true, ite_false, signVal_false, one_mul]
  · simp only [ite_true, signVal_true]
    ring

omit [Fintype Z] in
/-- For a fixed sign vector, the swapped ghost-sample gap splits into two Rademacher
correlations. -/
private theorem ciSup_expect_sub_swapAt_le {m : ℕ} {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (σ : Fin m → Bool) (p : (Fin m → Z) × (Fin m → Z)) :
    ⨆ f : F, 𝔼 i, ((f : Z → ℝ) ((swapAt σ p).2 i) - (f : Z → ℝ) ((swapAt σ p).1 i)) ≤
      (⨆ f : F, 𝔼 i, signVal (σ i) * (f : Z → ℝ) (p.2 i)) +
        ⨆ f : F, 𝔼 i, signVal (!σ i) * (f : Z → ℝ) (p.1 i) := by
  rcases isEmpty_or_nonempty F with hFe | hFe
  · simp only [Real.iSup_of_isEmpty, add_zero, le_refl]
  refine ciSup_le fun f => ?_
  rw [expect_sub_swapAt]
  have hsplit : 𝔼 i, signVal (σ i) * ((f : Z → ℝ) (p.2 i) - (f : Z → ℝ) (p.1 i)) =
      𝔼 i, signVal (σ i) * (f : Z → ℝ) (p.2 i) +
        𝔼 i, signVal (!σ i) * (f : Z → ℝ) (p.1 i) := by
    rw [← Finset.expect_add_distrib]
    refine Finset.expect_congr rfl fun i _ => ?_
    rw [signVal_not]
    ring
  rw [hsplit]
  exact add_le_add
    (le_ciSup (bddAbove_range_expect_signVal_mul (fun (g : F) i => (g : Z → ℝ) (p.2 i))
      (fun g _ => hF g g.2 _) σ) f)
    (le_ciSup (bddAbove_range_expect_signVal_mul (fun (g : F) i => (g : Z → ℝ) (p.1 i))
      (fun g _ => hF g g.2 _) fun i => !σ i) f)

omit [Fintype Z] in
/-- Averaged over the signs, the swapped ghost-sample gap is at most the sum of the two empirical
Rademacher complexities. -/
private theorem expect_ciSup_swapAt_le {m : ℕ} {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (p : (Fin m → Z) × (Fin m → Z)) :
    𝔼 σ : Fin m → Bool,
        ⨆ f : F, 𝔼 i, ((f : Z → ℝ) ((swapAt σ p).2 i) - (f : Z → ℝ) ((swapAt σ p).1 i)) ≤
      empiricalRademacherComplexity F p.2 + empiricalRademacherComplexity F p.1 := by
  have hinv : Function.Involutive fun (σ : Fin m → Bool) i => !σ i :=
    fun σ => funext fun i => Bool.not_not _
  refine (Finset.expect_le_expect fun σ _ => ciSup_expect_sub_swapAt_le hF σ p).trans_eq ?_
  rw [Finset.expect_add_distrib, empiricalRademacherComplexity_def,
    empiricalRademacherComplexity_def, rademacherAverage_def, rademacherAverage_def]
  congr 1
  exact Fintype.expect_equiv (Function.Involutive.toPerm _ hinv) _ _ fun σ => rfl

/-- Second symmetrization step: the ghost-sample gap is at most twice the Rademacher
complexity. -/
private theorem sum_sum_ciSup_le (D : PMF Z) {m : ℕ} {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) :
    ∑ S : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S).toReal *
      ∑ S' : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S').toReal *
        ⨆ f : F, 𝔼 i, ((f : Z → ℝ) (S' i) - (f : Z → ℝ) (S i)) ≤
      2 * rademacherComplexity D F m := by
  set P := Probability.PMF.pi fun _ : Fin m => D
  set W : (Fin m → Z) × (Fin m → Z) → ℝ := fun p => (P p.1).toReal * (P p.2).toReal
  set G : (Fin m → Z) × (Fin m → Z) → ℝ :=
    fun p => ⨆ f : F, 𝔼 i, ((f : Z → ℝ) (p.2 i) - (f : Z → ℝ) (p.1 i))
  have hLHS : ∑ S : Fin m → Z, (P S).toReal * ∑ S' : Fin m → Z, (P S').toReal *
      ⨆ f : F, 𝔼 i, ((f : Z → ℝ) (S' i) - (f : Z → ℝ) (S i)) = ∑ p, W p * G p := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.mul_sum, mul_assoc, W, G]
  have hsym (σ : Fin m → Bool) : ∑ p, W p * G p = ∑ p, W p * G (swapAt σ p) :=
    (Fintype.sum_equiv (Function.Involutive.toPerm _ (swapAt_involutive σ)) _ _ fun p => by
      change W p * G (swapAt σ p) = W (swapAt σ p) * G (swapAt σ p)
      rw [show W (swapAt σ p) = W p from weight_swapAt D σ p]).symm
  have hexp : ∑ p, W p * G p = ∑ p, W p * 𝔼 σ : Fin m → Bool, G (swapAt σ p) := by
    calc ∑ p, W p * G p = 𝔼 σ : Fin m → Bool, ∑ p, W p * G p := (Fintype.expect_const _).symm
      _ = 𝔼 σ : Fin m → Bool, ∑ p, W p * G (swapAt σ p) :=
          Finset.expect_congr rfl fun σ _ => hsym σ
      _ = ∑ p, 𝔼 σ : Fin m → Bool, W p * G (swapAt σ p) := Finset.expect_sum_comm ..
      _ = ∑ p, W p * 𝔼 σ : Fin m → Bool, G (swapAt σ p) := by simp only [Finset.mul_expect]
  have hR : ∑ S : Fin m → Z, (P S).toReal * empiricalRademacherComplexity F S =
      rademacherComplexity D F m := (rademacherComplexity_def D F m).symm
  have hP : ∑ S : Fin m → Z, (P S).toReal = 1 := Probability.PMF.sum_toReal P
  calc _ = ∑ p, W p * G p := hLHS
    _ = ∑ p, W p * 𝔼 σ : Fin m → Bool, G (swapAt σ p) := hexp
    _ ≤ ∑ p, W p * (empiricalRademacherComplexity F p.2 + empiricalRademacherComplexity F p.1) :=
        Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (expect_ciSup_swapAt_le hF p) (by positivity)
    _ = 2 * rademacherComplexity D F m := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        have h1 : ∀ S : Fin m → Z, ∑ S' : Fin m → Z, W (S, S') *
            (empiricalRademacherComplexity F S' + empiricalRademacherComplexity F S) =
            (P S).toReal * rademacherComplexity D F m +
              (P S).toReal * empiricalRademacherComplexity F S := by
          intro S
          simp only [W, mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ← hR]
          rw [← Finset.sum_mul, hP, one_mul]
        simp only [h1, Finset.sum_add_distrib, ← Finset.sum_mul, hP, one_mul, hR]
        ring

/-- **Symmetrization** [MohriRostamizadehTalwalkar2018, (3.8)–(3.13)]: for a class bounded by
`B` and samples of size `m > 0`, the expected worst-case gap between population and empirical
means is at most twice the Rademacher complexity,
`𝔼_S sup_{f ∈ F} (E_D f - Ê_S f) ≤ 2 R_m(F)`. -/
theorem sum_pi_mul_ciSup_sub_le_two_mul_rademacherComplexity (D : PMF Z) {m : ℕ} (hm : 0 < m)
    {F : Set (Z → ℝ)} {B : ℝ} (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) :
    ∑ S : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S).toReal *
      ⨆ f : F, (∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i)) ≤
      2 * rademacherComplexity D F m :=
  (Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (ciSup_sub_le_sum D hm hF S)
    ENNReal.toReal_nonneg).trans (sum_sum_ciSup_le D hF)

end Symmetrization

/-! ### Bounded differences -/

/-- The empirical mean of a function with values in `[a, b]` has bounded differences
`(b - a) / m`. -/
private theorem hasBoundedDifferences_expect_apply {m : ℕ} {f : Z → ℝ} {a b : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc a b) :
    Probability.HasBoundedDifferences (fun S : Fin m → Z => 𝔼 i, f (S i))
      fun _ => (b - a) / m := by
  have h := Probability.hasBoundedDifferences_sum (α := fun _ : Fin m => Z)
    (score := fun _ z => f z / m) (c := fun _ => (b - a) / m) fun _ z w => by
      rw [← sub_div, abs_div, Nat.abs_cast]
      gcongr
      have hz := hf z
      have hw := hf w
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2, hw.1, hw.2]
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, Finset.sum_div] using h

/-- The worst-case gap between population and empirical means over a class with values in
`[a, b]` has bounded differences `(b - a) / m`. -/
private theorem hasBoundedDifferences_ciSup_sub [Fintype Z] (D : PMF Z) {m : ℕ} (hm : 0 < m)
    {F : Set (Z → ℝ)} {a b : ℝ} (hab : a ≤ b) (hF : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc a b) :
    Probability.HasBoundedDifferences (fun S : Fin m → Z =>
      ⨆ f : F, (∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i)))
      fun _ => (b - a) / m := by
  refine Probability.HasBoundedDifferences.ciSup (fun _ => div_nonneg (sub_nonneg.2 hab)
    (Nat.cast_nonneg m)) (fun f S i z => ?_) (bddAbove_range_sub D hm fun f hf z =>
      abs_le_max_abs_abs (hF f hf z).1 (hF f hf z).2)
  have := hasBoundedDifferences_expect_apply (m := m) (hF f f.2) S i z
  dsimp only at this ⊢
  rw [sub_sub_sub_cancel_left, abs_sub_comm]
  exact this

/-- The empirical Rademacher complexity of a class with values in `[a, b]` has bounded differences
`(b - a) / m` as a function of the sample [MohriRostamizadehTalwalkar2018, proof of Theorem 3.3]. -/
theorem hasBoundedDifferences_empiricalRademacherComplexity {m : ℕ} {F : Set (Z → ℝ)} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc a b) :
    Probability.HasBoundedDifferences (fun S : Fin m → Z => empiricalRademacherComplexity F S)
      fun _ => (b - a) / m := by
  have hc : ∀ _ : Fin m, 0 ≤ (b - a) / m := fun _ => div_nonneg (sub_nonneg.2 hab)
    (Nat.cast_nonneg m)
  have hB : ∀ f ∈ F, ∀ z, |f z| ≤ max |a| |b| := fun f hf z =>
    abs_le_max_abs_abs (hF f hf z).1 (hF f hf z).2
  simp only [empiricalRademacherComplexity_def, rademacherAverage_def]
  refine Probability.HasBoundedDifferences.expect hc fun σ =>
    Probability.HasBoundedDifferences.ciSup hc (fun f => ?_)
      fun S => bddAbove_range_expect_signVal_mul (fun (g : F) i => (g : Z → ℝ) (S i))
        (fun g _ => hB g g.2 _) σ
  have h := Probability.hasBoundedDifferences_sum (α := fun _ : Fin m => Z)
    (score := fun i z => signVal (σ i) * (f : Z → ℝ) z / m) (c := fun _ => (b - a) / m)
    fun i z w => by
      rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_signVal, one_mul, Nat.abs_cast]
      gcongr
      have hz := hF f f.2 z
      have hw := hF f f.2 w
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2, hw.1, hw.2]
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, Finset.sum_div] using h

/-! ### Generalization bounds -/

/-- `exp (-2 ε² / ((b - a)² / m)) ≤ δ` for the deviation `ε = (b - a) √(log (1 / δ) / (2 m))`. -/
private theorem exp_neg_two_mul_sq_le {m : ℕ} (hm : 0 < m) {a b δ : ℝ} (hab : a < b)
    (hδ : 0 < δ) :
    Real.exp (-2 * ((b - a) * √(Real.log (1 / δ) / (2 * m))) ^ 2 / ((b - a) ^ 2 / m)) ≤ δ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hba : 0 < b - a := sub_pos.2 hab
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · have hL : 0 ≤ Real.log (1 / δ) / (2 * m) :=
      div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)) (by positivity)
    rw [mul_pow, Real.sq_sqrt hL]
    have : -2 * ((b - a) ^ 2 * (Real.log (1 / δ) / (2 * m))) / ((b - a) ^ 2 / m) =
        Real.log δ := by
      rw [one_div, Real.log_inv]
      field_simp
    rw [this, Real.exp_log hδ]
  · have hL : Real.log (1 / δ) / (2 * m) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (by positivity)
        (by rw [div_le_one hδ]; exact hδ1.le)) (by positivity)
    rw [Real.sqrt_eq_zero'.2 hL]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero]
    exact hδ1.le

/-- `∑ i < m, ((b - a) / m)² = (b - a)² / m`. -/
private theorem sum_div_sq {m : ℕ} (hm : 0 < m) (c : ℝ) :
    ∑ _i : Fin m, (c / m) ^ 2 = c ^ 2 / m := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  field_simp

variable [Fintype Z]

/-- **Rademacher generalization bound** [MohriRostamizadehTalwalkar2018, Theorem 3.3, (3.3)]:
for a class `F` of functions with values in `[a, b]` and `m > 0` independent draws from `D`, the
probability that some `f ∈ F` has
`E_D f > Ê_S f + 2 R_m(F) + (b - a) √(log (1 / δ) / (2 m))` is at most `δ`. The source states
the case `[a, b] = [0, 1]`. -/
theorem rademacherComplexity_generalization_bound (D : PMF Z) {m : ℕ} (hm : 0 < m)
    {F : Set (Z → ℝ)} {a b : ℝ} (hab : a < b) (hF : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc a b) {δ : ℝ}
    (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ F, 𝔼 i, f (S i) + 2 * rademacherComplexity D F m +
        (b - a) * √(Real.log (1 / δ) / (2 * m)) < ∑ z, (D z).toReal * f z}).toReal ≤ δ := by
  set P := Probability.PMF.pi fun _ : Fin m => D
  set ε := (b - a) * √(Real.log (1 / δ) / (2 * m))
  set Φ : (Fin m → Z) → ℝ := fun S =>
    ⨆ f : F, (∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i))
  have hB : ∀ f ∈ F, ∀ z, |f z| ≤ max |a| |b| := fun f hf z =>
    abs_le_max_abs_abs (hF f hf z).1 (hF f hf z).2
  have hmean : ∑ S, (P S).toReal * Φ S ≤ 2 * rademacherComplexity D F m :=
    sum_pi_mul_ciSup_sub_le_two_mul_rademacherComplexity D hm hB
  have hε : 0 ≤ ε := mul_nonneg (sub_pos.2 hab).le (Real.sqrt_nonneg _)
  have htail := (hasBoundedDifferences_ciSup_sub D hm hab.le hF).pi_ge_mean_add (fun _ => D) hε
  rw [sum_div_sq hm] at htail
  have hsub : {S | ∃ f ∈ F, 𝔼 i, f (S i) + 2 * rademacherComplexity D F m + ε <
      ∑ z, (D z).toReal * f z} ⊆ {S | (∑ S', (P S').toReal * Φ S') + ε ≤ Φ S} := by
    rintro S ⟨f, hf, hlt⟩
    have := le_ciSup (bddAbove_range_sub D hm hB S) ⟨f, hf⟩
    dsimp only at this
    change (∑ S', (P S').toReal * Φ S') + ε ≤ Φ S
    linarith
  calc _ ≤ (P.toOuterMeasure {S | (∑ S', (P S').toReal * Φ S') + ε ≤ Φ S}).toReal :=
        ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
          (P.toOuterMeasure.mono hsub)
    _ ≤ Real.exp (-2 * ε ^ 2 / ((b - a) ^ 2 / m)) := htail
    _ ≤ δ := exp_neg_two_mul_sq_le hm hab hδ

/-- **Data-dependent Rademacher generalization bound** [MohriRostamizadehTalwalkar2018,
Theorem 3.3, (3.4)]: for a class `F` of functions with values in `[a, b]` and `m > 0` independent
draws from `D`, the probability that some `f ∈ F` has
`E_D f > Ê_S f + 2 R̂_S(F) + 3 (b - a) √(log (2 / δ) / (2 m))` is at most `δ`. The source states
the case `[a, b] = [0, 1]`. The proof combines the expected bound at confidence `δ / 2` with
McDiarmid's lower tail for `R̂_S(F)` at confidence `δ / 2`. -/
theorem empiricalRademacherComplexity_generalization_bound (D : PMF Z) {m : ℕ} (hm : 0 < m)
    {F : Set (Z → ℝ)} {a b : ℝ} (hab : a < b) (hF : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc a b) {δ : ℝ}
    (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ F, 𝔼 i, f (S i) + 2 * empiricalRademacherComplexity F S +
        3 * ((b - a) * √(Real.log (2 / δ) / (2 * m))) < ∑ z, (D z).toReal * f z}).toReal ≤
      δ := by
  set P := Probability.PMF.pi fun _ : Fin m => D
  set ε := (b - a) * √(Real.log (2 / δ) / (2 * m))
  set Φ : (Fin m → Z) → ℝ := fun S =>
    ⨆ f : F, (∑ z, (D z).toReal * (f : Z → ℝ) z - 𝔼 i, (f : Z → ℝ) (S i))
  have hB : ∀ f ∈ F, ∀ z, |f z| ≤ max |a| |b| := fun f hf z =>
    abs_le_max_abs_abs (hF f hf z).1 (hF f hf z).2
  have hmean : ∑ S, (P S).toReal * Φ S ≤ 2 * rademacherComplexity D F m :=
    sum_pi_mul_ciSup_sub_le_two_mul_rademacherComplexity D hm hB
  have hε : 0 ≤ ε := mul_nonneg (sub_pos.2 hab).le (Real.sqrt_nonneg _)
  have hexp : Real.exp (-2 * ε ^ 2 / ((b - a) ^ 2 / m)) ≤ δ / 2 := by
    have := exp_neg_two_mul_sq_le hm hab (half_pos hδ)
    rwa [one_div_div] at this
  have htail1 := (hasBoundedDifferences_ciSup_sub D hm hab.le hF).pi_ge_mean_add (fun _ => D) hε
  have htail2 := (hasBoundedDifferences_empiricalRademacherComplexity (m := m) hab.le
    hF).pi_le_mean_sub (fun _ => D) hε
  rw [sum_div_sq hm] at htail1 htail2
  rw [← rademacherComplexity_def] at htail2
  have hsub : {S | ∃ f ∈ F, 𝔼 i, f (S i) + 2 * empiricalRademacherComplexity F S + 3 * ε <
      ∑ z, (D z).toReal * f z} ⊆ {S | (∑ S', (P S').toReal * Φ S') + ε ≤ Φ S} ∪
        {S | empiricalRademacherComplexity F S ≤ rademacherComplexity D F m - ε} := by
    rintro S ⟨f, hf, hlt⟩
    by_contra hS
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hS
    have := le_ciSup (bddAbove_range_sub D hm hB S) ⟨f, hf⟩
    dsimp only at this
    change Φ S < (∑ S', (P S').toReal * Φ S') + ε ∧ _ at hS
    linarith [hS.1, hS.2]
  calc _ ≤ (P.toOuterMeasure ({S | (∑ S', (P S').toReal * Φ S') + ε ≤ Φ S} ∪
        {S | empiricalRademacherComplexity F S ≤ rademacherComplexity D F m - ε})).toReal :=
        ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
          (P.toOuterMeasure.mono hsub)
    _ ≤ (P.toOuterMeasure {S | (∑ S', (P S').toReal * Φ S') + ε ≤ Φ S}).toReal +
        (P.toOuterMeasure
          {S | empiricalRademacherComplexity F S ≤ rademacherComplexity D F m - ε}).toReal := by
        exact ENNReal.toReal_le_add (MeasureTheory.measure_union_le _ _)
          (Probability.PMF.toOuterMeasure_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)
    _ ≤ δ / 2 + δ / 2 := add_le_add (htail1.trans hexp) (htail2.trans hexp)
    _ = δ := add_halves δ

/-- **Generalization bound for a finite class** with values in `[0, 1]`, through Massart's
lemma: the probability that some `f ∈ F` has
`E_D f > Ê_S f + 2 √(2 log |F| / m) + √(log (1 / δ) / (2 m))` is at most `δ`
[MohriRostamizadehTalwalkar2018, Theorem 3.3 and Theorem 3.7]. This illustrates the method;
Hoeffding's inequality with a union bound gives the sharper `√(log (|F| / δ) / (2 m))`. -/
theorem rademacher_generalization_bound_of_finset (D : PMF Z) {m : ℕ} (hm : 0 < m)
    {F : Finset (Z → ℝ)} (hF : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc 0 1) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ F, 𝔼 i, f (S i) + 2 * √(2 * Real.log F.card / m) +
        √(Real.log (1 / δ) / (2 * m)) < ∑ z, (D z).toReal * f z}).toReal ≤ δ := by
  have hR : rademacherComplexity D (F : Set (Z → ℝ)) m ≤ √(2 * Real.log F.card / m) := by
    simpa only [one_mul] using rademacherComplexity_le_of_finset D zero_le_one
      (fun f hf z => abs_le.2 ⟨by linarith [(hF f hf z).1], (hF f hf z).2⟩) m
  refine le_trans (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure.mono ?_))
    (rademacherComplexity_generalization_bound D hm zero_lt_one (F := (F : Set (Z → ℝ))) hF hδ)
  rintro S ⟨f, hf, hlt⟩
  refine ⟨f, hf, ?_⟩
  rw [sub_zero, one_mul]
  linarith

end Cslib.MachineLearning
