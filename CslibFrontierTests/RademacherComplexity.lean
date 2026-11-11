/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.Rademacher.Classification
import CslibFrontier.MachineLearning.Rademacher.Generalization
import CslibFrontier.MachineLearning.Rademacher.GrowthFunction

/-! Checks for Rademacher complexity: a single function has complexity `0`; the two constants
`±1` on a one-point sample have complexity exactly `1`, against Massart's bound `√(2 log 2)`; the
finite-class generalization bound and the data-dependent bound give nontrivial guarantees for
explicit parameters; and the VC bounds apply to the class of all binary functions on `Bool`. For
binary classification, the 0-1 loss class of the two constant classifiers on one labeled point has
complexity exactly `1 / 2`, a single classifier gives Hoeffding's bound, and the VC and agnostic ERM
bounds give nontrivial guarantees for all binary classifiers on `Bool` with `65536` examples. -/

namespace CslibFrontierTests.RademacherComplexity

open Cslib.MachineLearning Cslib.BitString Cslib.MachineLearning.PACLearning
open scoped BigOperators

/-! ### A single function and the empty sample -/

example : empiricalRademacherComplexity {fun _ : Bool => (3 : ℝ)} ![true, false] = 0 :=
  empiricalRademacherComplexity_singleton _ _

example (F : Set (Bool → ℝ)) : empiricalRademacherComplexity F (Fin.elim0 : Fin 0 → Bool) = 0 := by
  rw [empiricalRademacherComplexity_def, rademacherAverage_def]
  simp

/-! ### Two constants on one point -/

/-- The constant functions `1` and `-1` on a one-point domain. -/
def pm : Set (Unit → ℝ) := {fun _ => 1, fun _ => -1}

theorem abs_le_one_of_mem_pm {f : Unit → ℝ} (hf : f ∈ pm) (z : Unit) : |f z| ≤ 1 := by
  rcases hf with rfl | rfl <;> simp

/-- On one sample point, the constants `±1` match every sign, so their empirical Rademacher
complexity is `1`. -/
theorem empiricalRademacherComplexity_pm : empiricalRademacherComplexity pm ![()] = 1 := by
  have : Nonempty pm := ⟨⟨fun _ => 1, Or.inl rfl⟩⟩
  have hbdd (σ : Fin 1 → Bool) := bddAbove_range_expect_signVal_mul
    (fun (f : pm) i => (f : Unit → ℝ) (![()] i)) (fun f _ => abs_le_one_of_mem_pm f.2 _) σ
  have h (σ : Fin 1 → Bool) :
      ⨆ f : pm, 𝔼 i, signVal (σ i) * (f : Unit → ℝ) (![()] i) = 1 := by
    refine le_antisymm (ciSup_le fun f => ?_) ?_
    · have hs := abs_le.1 (abs_signVal (σ 0)).le
      rcases f.2 with hf | hf
      · simp [hf, hs.2]
      · rw [Set.mem_singleton_iff] at hf
        simp only [hf, Matrix.cons_val_fin_one, mul_neg, mul_one, Finset.univ_unique,
          Fin.default_eq_zero, Finset.expect_singleton]
        linarith [hs.1]
    · cases h0 : σ 0
      · refine le_ciSup_of_le (hbdd σ) ⟨fun _ => 1, Or.inl rfl⟩ ?_
        simp [h0]
      · refine le_ciSup_of_le (hbdd σ) ⟨fun _ => -1, Or.inr rfl⟩ ?_
        simp [h0]
  rw [empiricalRademacherComplexity_def, rademacherAverage_def]
  simp only [h, Finset.expect_const, Finset.univ_nonempty]

/-- Massart's bound for `pm` is `√(2 log 2) ≈ 1.18`, close to the true value `1`. -/
example : empiricalRademacherComplexity pm ![()] ≤ √(2 * Real.log 2) := by
  have h := empiricalRademacherComplexity_le_of_finset (F := {fun _ => 1, fun _ => -1})
    zero_le_one (fun f hf z => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl <;> simp) ![()]
  have hcard : ({fun _ => 1, fun _ => -1} : Finset (Unit → ℝ)).card = 2 :=
    Finset.card_pair fun h => by
      have := congrFun h ()
      norm_num at this
  simpa [pm, hcard] using h

/-! ### A nonvacuous generalization bound -/

/-- Two `[0, 1]`-valued functions on `Bool`. -/
noncomputable def two : Finset (Bool → ℝ) := {fun _ => 0, fun b => (if b then 1 else 0 : ℝ)}

theorem card_two : two.card = 2 :=
  Finset.card_pair fun h => by simpa using (congrFun h true).symm

theorem mem_Icc_of_mem_two {f : Bool → ℝ} (hf : f ∈ two) (z : Bool) : f z ∈ Set.Icc 0 1 := by
  simp only [two, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · simp
  · cases z <;> simp

private theorem sqrt_le_of_le_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hy)

/-- With `100` samples, the probability that some function of `two` has population mean more than
`0.61` above its empirical mean is at most `1 / 20`. The range of the functions is `1`, so the
guarantee is nontrivial. -/
example (D : PMF Bool) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 100 => D).toOuterMeasure
      {S | ∃ f ∈ two, 𝔼 i, f (S i) + 61 / 100 < ∑ z, (D z).toReal * f z}).toReal ≤ 1 / 20 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog20 : Real.log (1 / (1 / 20)) ≤ 19 := by
    rw [one_div_one_div]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)]
  have h1 : √(2 * Real.log (two.card : ℝ) / (100 : ℕ)) ≤ 15 / 100 := by
    rw [card_two]
    refine sqrt_le_of_le_sq (by norm_num) ?_
    push_cast
    nlinarith
  have h2 : √(Real.log (1 / (1 / 20)) / (2 * (100 : ℕ))) ≤ 31 / 100 := by
    refine sqrt_le_of_le_sq (by norm_num) ?_
    push_cast
    nlinarith
  refine le_trans (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Cslib.Probability.PMF.pi fun _ : Fin 100 => D).toOuterMeasure.mono ?_))
    (rademacher_generalization_bound_of_finset D (by norm_num) (fun f hf => mem_Icc_of_mem_two hf)
      (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨f, hf, hlt⟩
  exact ⟨f, hf, by linarith⟩

/-- The data-dependent bound [MohriRostamizadehTalwalkar2018, Theorem 3.3, (3.4)] with `10000`
samples: the probability that some function of `two` has population mean more than `0.2` above its
empirical mean is at most `1 / 20`. The empirical complexity of `two` is computed from the sample
through Massart's lemma. -/
example (D : PMF Bool) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 10000 => D).toOuterMeasure
      {S | ∃ f ∈ two, 𝔼 i, f (S i) + 1 / 5 < ∑ z, (D z).toReal * f z}).toReal ≤ 1 / 20 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog40 : Real.log (2 / (1 / 20)) ≤ 39 := by
    norm_num only
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 40)]
  have hR (S : Fin 10000 → Bool) :
      empiricalRademacherComplexity (two : Set (Bool → ℝ)) S ≤ 2 / 100 := by
    refine (empiricalRademacherComplexity_le_of_finset zero_le_one (fun f hf z =>
      abs_le.2 ⟨by linarith [(mem_Icc_of_mem_two hf z).1], (mem_Icc_of_mem_two hf z).2⟩) S).trans ?_
    rw [one_mul, card_two]
    refine sqrt_le_of_le_sq (by norm_num) ?_
    push_cast
    nlinarith
  have hε : √(Real.log (2 / (1 / 20)) / (2 * (10000 : ℕ))) ≤ 5 / 100 := by
    refine sqrt_le_of_le_sq (by norm_num) ?_
    push_cast
    nlinarith
  refine le_trans (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Cslib.Probability.PMF.pi fun _ : Fin 10000 => D).toOuterMeasure.mono ?_))
    (empiricalRademacherComplexity_generalization_bound D (by norm_num) zero_lt_one
      (F := (two : Set (Bool → ℝ))) (fun f hf => mem_Icc_of_mem_two hf)
      (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨f, hf, hlt⟩
  refine ⟨f, hf, ?_⟩
  rw [sub_zero, one_mul]
  linarith [hR S]

/-! ### The VC bounds -/

/-- The VC bound with `d = 2` and `m = 100`: the empirical Rademacher complexity of every binary
class on `Bool` on `100` points is at most `√(4 log (50 e) / 100) < 1 / 2`. -/
example (C : ConceptClass Bool Bool) (S : Fin 100 → Bool) :
    empiricalRademacherComplexity (signClass C) S ≤ 1 / 2 := by
  refine (empiricalRademacherComplexity_signClass_le_vc (C := C) (d := 2)
    (fun W _ => by simpa using W.card_le_univ) (by norm_num) S).trans ?_
  have hlog2 : Real.log 2 < 7 / 10 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hlog : Real.log (Real.exp 1 * (100 : ℕ) / (2 : ℕ)) ≤ 1 + 6 * Real.log 2 := by
    rw [show Real.exp 1 * (100 : ℕ) / (2 : ℕ) = Real.exp 1 * 50 by push_cast; ring,
      Real.log_mul (Real.exp_pos 1).ne' (by norm_num), Real.log_exp]
    have : Real.log 50 ≤ Real.log 64 := Real.log_le_log (by norm_num) (by norm_num)
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    linarith
  refine sqrt_le_of_le_sq (by norm_num) ?_
  push_cast at hlog ⊢
  nlinarith

/-- Every set of booleans has at most two points, so the VC bound applies to every binary class on
`Bool` with `d = 2`. -/
example (C : ConceptClass Bool Bool) {m : ℕ} (S : Fin m → Bool) :
    empiricalRademacherComplexity (signClass C) S ≤ √(2 * (2 * Real.log (m + 1)) / m) := by
  have h := empiricalRademacherComplexity_signClass_le_add_one (C := C) (d := 2)
    (fun W _ => by simpa using W.card_le_univ) S
  simpa using h

/-- A single concept has empirical Rademacher complexity `0`. -/
example (c : Bool → Bool) {m : ℕ} (S : Fin m → Bool) :
    empiricalRademacherComplexity (signClass {c}) S = 0 := by
  rw [signClass_singleton]
  exact empiricalRademacherComplexity_singleton _ _

/-! ### Binary classification -/

/-- The two constant classifiers on `Unit`. -/
def consts : ConceptClass Unit Bool := {fun _ => false, fun _ => true}

theorem signClass_consts : signClass consts = pm := by
  ext f
  simp only [mem_signClass, consts, Set.mem_insert_iff, Set.mem_singleton_iff, pm]
  constructor
  · rintro ⟨c, rfl | rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, by funext; simp⟩

/-- [MohriRostamizadehTalwalkar2018, Lemma 3.4] on one labeled point: the 0-1 losses of the two
constant classifiers have empirical Rademacher complexity `1 / 2`, half that of `{±1}`. -/
example (y : Bool) :
    empiricalRademacherComplexity (bitClass (lossClass consts)) ![((), y)] = 1 / 2 := by
  rw [empiricalRademacherComplexity_bitClass_lossClass, signClass_consts]
  have : (fun i => (![((), y)] i).1) = ![()] := funext fun i => rfl
  rw [this, empiricalRademacherComplexity_pm]

/-- A single classifier: the 0-1 loss class has Rademacher complexity `0`. -/
example (D : PMF (Bool × Bool)) (c : Bool → Bool) (m : ℕ) :
    rademacherComplexity D (bitClass (lossClass {c})) m = 0 := by
  rw [rademacherComplexity_bitClass_lossClass, signClass_singleton, rademacherComplexity_singleton,
    zero_div]

/-- For a single classifier, (3.17) is Hoeffding's upper tail: `err_D(c) > err_S(c) +
√(log (1 / δ) / (2 m))` with probability at most `δ`. -/
example (D : PMF (Bool × Bool)) (c : Bool → Bool) {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    ((Cslib.Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | (empiricalMiscount c S : ℝ) / m + √(Real.log (1 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal}).toReal ≤ δ := by
  have h := rademacherComplexity_classification_bound D hm {c} hδ
  simp only [signClass_singleton, rademacherComplexity_singleton, add_zero, Set.mem_singleton_iff,
    exists_eq_left] at h
  exact h

/-- `√(2 (2 log (e m / 2)) / m) ≤ 1 / 32` for `m = 65536`. -/
theorem vc_term_le :
    √(2 * ((2 : ℕ) * Real.log (Real.exp 1 * (65536 : ℕ) / (2 : ℕ))) / (65536 : ℕ)) ≤ 1 / 32 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log (Real.exp 1 * (65536 : ℕ) / (2 : ℕ)) ≤ 16 := by
    rw [show Real.exp 1 * (65536 : ℕ) / (2 : ℕ) = Real.exp 1 * 2 ^ 15 by push_cast; ring,
      Real.log_mul (Real.exp_pos 1).ne' (by norm_num), Real.log_exp, Real.log_pow]
    push_cast
    linarith
  refine sqrt_le_of_le_sq (by norm_num) ?_
  push_cast at hlog ⊢
  nlinarith

/-- [MohriRostamizadehTalwalkar2018, Corollary 3.19] with `d = 2`, `m = 65536` and `δ = 1 / 20`:
with probability at least `19 / 20`, every binary classifier on `Bool` has true error at most its
empirical error plus `0.06`. -/
example (D : PMF (Bool × Bool)) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 65536 => D).toOuterMeasure
      {S | ∃ h : Bool → Bool, (empiricalMiscount h S : ℝ) / 65536 + 6 / 100 <
        (D.toOuterMeasure {p | h p.1 ≠ p.2}).toReal}).toReal ≤ 1 / 20 := by
  have hδ : √(Real.log (1 / (1 / 20)) / (2 * (65536 : ℕ))) ≤ 2 / 100 := by
    have : Real.log (1 / (1 / 20)) ≤ 19 := by
      rw [one_div_one_div]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)]
    refine sqrt_le_of_le_sq (by norm_num) ?_
    push_cast
    nlinarith
  refine le_trans (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Cslib.Probability.PMF.pi fun _ : Fin 65536 => D).toOuterMeasure.mono ?_))
    (vc_classification_bound D (C := Set.univ) (d := 2) (fun W _ => by simpa using W.card_le_univ)
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨h, hlt⟩
  refine ⟨h, Set.mem_univ h, ?_⟩
  have := vc_term_le
  push_cast at this hδ hlt ⊢
  linarith

/-- Agnostic learning by ERM with `d = 2`, `m = 65536` and `δ = 1 / 20`: with probability at least
`19 / 20`, an empirical risk minimizer over all binary classifiers on `Bool` has true error within
`0.08` of every classifier, in particular of a Bayes-optimal one. -/
example (D : PMF (Bool × Bool)) {A : Learner Bool Bool 65536} (hA : IsERM A Set.univ) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 65536 => D).toOuterMeasure
      {S | ∃ c : Bool → Bool, (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal + 8 / 100 <
        (D.toOuterMeasure {p | A S p.1 ≠ p.2}).toReal}).toReal ≤ 1 / 20 := by
  have hδ : √(2 * Real.log (2 / (1 / 20)) / (65536 : ℕ)) ≤ 4 / 100 := by
    have : Real.log (2 / (1 / 20)) ≤ 39 := by
      norm_num only
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 40)]
    refine sqrt_le_of_le_sq (by norm_num) ?_
    push_cast
    nlinarith
  refine le_trans (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
    ((Cslib.Probability.PMF.pi fun _ : Fin 65536 => D).toOuterMeasure.mono ?_))
    (hA.vc_agnostic_bound D (d := 2) (fun W _ => by simpa using W.card_le_univ) (by norm_num)
      (by norm_num) (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨c, hlt⟩
  refine ⟨c, Set.mem_univ c, ?_⟩
  have := vc_term_le
  push_cast at this hδ hlt ⊢
  linarith

/-- Empirical risk minimizers over all binary classifiers on `Bool` exist. -/
example : ∃ A : Learner Bool Bool 65536, IsERM A Set.univ := exists_isERM Set.univ_nonempty

end CslibFrontierTests.RademacherComplexity
