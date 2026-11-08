/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.MachineLearning.Rademacher.Generalization
import Complexity.MachineLearning.Rademacher.GrowthFunction

/-! Checks for Rademacher complexity: a single function has complexity `0`; the two constants
`±1` on a one-point sample have complexity exactly `1`, against Massart's bound `√(2 log 2)`; the
finite-class generalization bound gives a nontrivial guarantee for explicit parameters; and the
VC bound applies to the class of all binary functions on `Bool`. -/

namespace ComplexityTests.RademacherComplexity

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
    (generalization_bound_of_finset D (by norm_num) (fun f hf => mem_Icc_of_mem_two hf)
      (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨f, hf, hlt⟩
  exact ⟨f, hf, by linarith⟩

/-! ### The VC bound -/

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
  rw [signClass, Set.image_singleton]
  exact empiricalRademacherComplexity_singleton _ _

end ComplexityTests.RademacherComplexity
