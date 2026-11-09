/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PropertyTesting.Linearity
import Complexity.Foundations.BooleanAnalysis.HadamardTester
import Complexity.Foundations.BooleanAnalysis.Hypercontractivity.Derivative
import Complexity.Foundations.BooleanAnalysis.MirrorSets
import Complexity.Foundations.BooleanAnalysis.MultilinearExtension
import Complexity.Foundations.BooleanAnalysis.Noise
import Complexity.Foundations.Data.Finset.Expect

/-! # Boolean analysis on small cubes

Concrete instances of the Boolean analysis API, mostly on the cube `Fin 2 → Bool`. The
conjunction of two bits has BLR acceptance `5 / 8`, so linearity testing certifies a parity at
distance at most one, and that bound is attained. Its noise sensitivity `δ - δ ^ 2 / 2`, total
influence `1`, influence `1 / 2`, Fourier coefficient `-1 / 2` and multilinear extension
`z₀ z₁` are computed. Korten's mirror-set and light-patterns lemmas are applied to sets that
satisfy their hypotheses, and the Hadamard tester to honest tables at positive error. The
examples show that the hypotheses of these results are satisfiable and that the definitions
compute the values their docstrings describe.
-/

namespace ComplexityTests.BooleanAnalysisExamples

open Cslib Cslib.BitString Finset

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-! ### Fourier coefficients -/

-- The coefficient of a character is one on its own set and zero on any other.
example : fourierCoeff (chi ℝ ({0, 1} : Finset (Fin 2))) {0, 1} = 1 ∧
    fourierCoeff (chi ℝ ({0, 1} : Finset (Fin 2))) {1} = 0 := by
  refine ⟨?_, ?_⟩
  · rw [fourierCoeff_chi, ite_eq_left rfl]
  · rw [fourierCoeff_chi, ite_eq_right (by decide)]

-- The coefficient of the conjunction, read as signs, on both coordinates, from the definition.
example : fourierCoeff (fun x => signVal (and₂ x)) {0, 1} = -1 / 2 := by
  simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  simp [chi, and₂]

/-! ### Linearity testing -/

/-- The BLR test accepts the conjunction of two bits on `10` of the `16` pairs. -/
theorem blrAcceptance_and₂ : blrAcceptance and₂ = 5 / 8 := by
  simp only [blrAcceptance, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  simp only [and₂, Nat.reduceAdd, Fin.isValue, Fin.cons_zero, Fin.cons_one, Bool.and_self,
      bne_self_eq_false, Pi.add_apply, Bool.add_eq_xor, ↓reduceIte, Bool.and_true, Bool.bne_true,
      Bool.not_false, add_self_div_two, Bool.and_false, Bool.bne_false, Bool.false_eq_true,
      Bool.true_eq_false, add_zero, zero_div, one_div, zero_add]
  norm_num

-- Through the Fourier formula for the acceptance, the cubed coefficients sum to `1 / 4`;
-- `and₂` is not a parity, BLR soundness at `ε = 3 / 8` gives distance at most `1` to some parity,
-- and `parityOn ∅` attains that bound.
example (S : Finset (Fin 2)) :
    ∑ T, fourierCoeff (fun x => signVal (and₂ x)) T ^ 3 = 1 / 4 ∧
    and₂ ≠ parityOn S ∧
    (∃ T, hammingDist and₂ (parityOn T) ≤ 1) ∧
    hammingDist and₂ (parityOn ∅) = 1 := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · have h := blrAcceptance_eq_sum_fourierCoeff_pow_three and₂
    rw [blrAcceptance_and₂] at h
    linarith
  · intro h
    have h₁ := blrAcceptance_parityOn S
    rw [← h, blrAcceptance_and₂] at h₁
    norm_num at h₁
  · obtain ⟨T, hT⟩ := exists_hammingDist_parityOn_le_of_le_blrAcceptance
      (f := and₂) (ε := 3 / 8) (by rw [blrAcceptance_and₂]; norm_num)
    refine ⟨T, ?_⟩
    have h : (hammingDist and₂ (parityOn T) : ℝ) < 2 := by
      rw [Fintype.card_fin] at hT
      linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h)

-- The repeated tester reuses the same BLR local test and its checked acceptance probability.
example : ((PCP.HadamardTester.blrTest (Fin 2)).repeatAll 2).acceptProb and₂ = 25 / 64 := by
  rw [PCP.LocalTest.acceptProb_repeatAll, PCP.HadamardTester.acceptProb_blrTest,
    blrAcceptance_and₂]
  norm_num

-- Every parity is at distance at least 1/4, so the generic soundness bound gives (3/4)^2.
example : ((PCP.HadamardTester.blrTest (Fin 2)).repeatAll 2).acceptProb and₂ ≤ 9 / 16 := by
  have hdist : ∀ S : Finset (Fin 2), 1 ≤ hammingDist and₂ (parityOn S) := by decide
  have hfar (S : Finset (Fin 2)) :
      (1 / 4 : ℝ) ≤ (hammingDist and₂ (parityOn S) : ℝ) / 2 ^ Fintype.card (Fin 2) := by
    have h : (1 : ℝ) ≤ hammingDist and₂ (parityOn S) := by exact_mod_cast hdist S
    norm_num only [Fintype.card_fin]
    linarith
  have h := acceptProb_repeatAll_blrTest_le hfar 2
  norm_num at h ⊢
  exact h

-- This seed queries the two singletons and their sum: conjunction fails the BLR equation.
example :
    ((PCP.HadamardTester.blrTest (Fin 2)).decisionTree
      (![true, false], ![false, true])).eval and₂ = false := by decide

example :
    ((PCP.HadamardTester.blrTest (Fin 2)).decisionTree
      (![true, false], ![false, true])).eval (parityOn {0, 1}) = true := by decide

example :
    (((PCP.HadamardTester.blrTest (Fin 2)).repeatAll 2).decisionTree
      (fun _ => (![true, false], ![false, true]))).depth = 6 := by decide

-- On the empty cube the only table entry is still queried: constant true is nonlinear.
example :
    ((PCP.HadamardTester.blrTest (Fin 0)).decisionTree
      ((fun i => i.elim0), (fun i => i.elim0))).eval (fun _ => true) = false := by
  rw [PCP.LocalTest.eval_decisionTree]
  decide

/-! ### Noise sensitivity and influence -/

/-- The conjunction changes under noise of rate `δ` when both bits are `true` before or after
the noise: with probability `2 · 1/4 · (1 - (1 - δ) ^ 2)`. -/
theorem noiseSensitivity_and₂ (δ : ℝ) : noiseSensitivity δ and₂ = δ - δ ^ 2 / 2 := by
  simp only [noiseSensitivity, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique,
    bernoulliAverage_cons]
  simp only [and₂, Nat.reduceAdd, Fin.isValue, Fin.cons_zero, Fin.cons_one, Bool.and_self,
      Pi.add_apply, Bool.add_eq_xor, bne_self_eq_false, ne_eq, not_true_eq_false, ↓reduceIte,
      bernoulliAverage_const, mul_zero, Bool.bne_true, Bool.not_false, Bool.and_true, add_zero,
      Bool.and_false, Bool.false_eq_true, not_false_eq_true, mul_one, zero_add, Bool.bne_false,
      Bool.true_eq_false, sub_add_cancel]
  ring

/-- Each bit of the conjunction is pivotal on half of the inputs. -/
theorem influence_and₂ : influence 0 (fun x => signVal (and₂ x)) = 1 / 2 := by
  simp only [influence_signVal, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  simp [and₂, Function.update]

/-- The total influence of the conjunction is `1 / 2 + 1 / 2`. -/
theorem totalInfluence_and₂ : totalInfluence (fun x => signVal (and₂ x)) = 1 := by
  simp only [totalInfluence, Fin.sum_univ_two, influence_signVal, Fin.expect_univ_cons,
    Fintype.expect_bool, Fintype.expect_unique]
  simp only [and₂, Function.update, Fin.isValue, ↓reduceDIte, Nat.reduceAdd, Fin.cons_zero,
      Bool.not_false, one_ne_zero, Fin.cons_one, Bool.and_false, Bool.and_self, ↓reduceIte,
      Bool.and_true, Bool.true_eq_false, zero_add, one_div, Bool.not_true, Bool.false_eq_true,
      add_self_div_two, zero_ne_one, add_zero, zero_div]
  norm_num

-- `NS_δ ≤ δ I` on the conjunction and the `L⁴` norm of the derivative in its first bit.
example {δ : ℝ} (hδ : δ ≤ 1) :
    noiseSensitivity δ and₂ ≤ δ ∧
    lpNorm 4 (derivative 0 fun x => signVal (and₂ x)) = (1 / 2) ^ (4 : ℝ)⁻¹ :=
  ⟨by simpa [totalInfluence_and₂] using noiseSensitivity_le_mul_totalInfluence hδ and₂,
    by rw [lpNorm_derivative_signVal and₂ 0 (by norm_num), influence_and₂]⟩

/-! ### The Hadamard tester -/

-- Soundness at positive errors `ε = ε' = 1 / 32`: the honest tables for the solution
-- `(true, true)` of the equation `x₀ x₁ = 1` pass, so the tester certifies a solution.
example : ∃ x : Fin 2 → Bool,
    (hammingDist (hadamardCode (fun _ => true)) (hadamardCode x) : ℝ) / 2 ^ 2 ≤ 1 / 32 ∧
      (x 0 && x 1) = true := by
  obtain ⟨x, hx, he⟩ := exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance
    (f := hadamardCode (fun _ : Fin 2 => true))
    (g := hadamardCode (tensor (fun _ => true) (fun _ => true)))
    (A := fun _ : Unit => Pi.single ((0 : Fin 2), (1 : Fin 2)) true) (b := fun _ => true)
    (ε := 1 / 32) (ε' := 1 / 32) (by simp) (by simp)
    (by simp only [one_div, tensorTestAcceptance_hadamardCode]; norm_num)
    (by rw [equationTestAcceptance_hadamardCode (by simp)]; norm_num)
  refine ⟨x, by simpa using hx, ?_⟩
  simpa using he ()

/-! ### Random masks -/

-- Bernoulli mask averages: both coordinates selected with probability `p ^ 2`, expected weight `1`
-- at rate `1 / 3` on three coordinates, and union-difference conditional sampling rate `1 / 3`.
example (p : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    bernoulliAverage p (fun P : Fin 2 → Bool => if P 0 && P 1 then (1 : ℝ) else 0) = p ^ 2 ∧
    bernoulliAverage (1 / 3) (fun P : Fin 3 → Bool => (weight P : ℝ)) = 1 ∧
    conditionalSamplingRate (1 / 2) (1 / 2) = 1 / 3 ∧
    bernoulliAverage (1 / 2) (fun P : ι → Bool => bernoulliAverage (1 / 2) (fun Q =>
      if P i && !Q i then (1 : ℝ) else 0)) = 1 / 4 := by
  refine ⟨?_,
    by rw [bernoulliAverage_weight, Fintype.card_fin]; norm_num,
    by norm_num [conditionalSamplingRate],
    ?_⟩
  · simp only [Fin.isValue, Bool.and_eq_true, bernoulliAverage_cons, Nat.reduceAdd, Fin.cons_zero,
      Bool.false_eq_true, Fin.cons_one, false_and, ↓reduceIte, bernoulliAverage_const, mul_zero,
      true_and, mul_one, zero_add]
    ring
  · rw [bernoulliAverage_union_difference (1 / 2) (1 / 2) (1 / 3) (by norm_num)
      (fun _ D => if D i then (1 : ℝ) else 0)]
    have h (S : ι → Bool) : bernoulliAverage (1 / 3) (fun T => if (S i && T i) = true then
        (1 : ℝ) else 0) = 1 / 3 * if S i then 1 else 0 := by
      cases S i <;> simp [bernoulliAverage_const, bernoulliAverage_coordinate]
    simp only [h, bernoulliAverage_const_mul, bernoulliAverage_coordinate]
    norm_num

/-! ### Fibers, light patterns and mirror sets -/

/-- The half of the cube `Fin 2 → Bool` whose first bit is `false`. -/
def halfCube : Finset (Fin 2 → Bool) :=
  univ.filter fun x => x 0 = false

/-- The half cube contains the all-`false` point. -/
theorem halfCube_nonempty : halfCube.Nonempty :=
  ⟨fun _ => false, by simp [halfCube]⟩

/-- Half of the cube has min-entropy deficit one. -/
theorem uniformDeficit_halfCube : uniformDeficit halfCube = 1 := by
  have h : halfCube.card = 2 := by decide
  rw [uniformDeficit, h, Fintype.card_fin]
  norm_num

/-- Each point has uniform mass at most `2 ^ (1 - 2) = 1 / 2` on the half cube. -/
private theorem uniformMass_halfCube_le (x : Fin 2 → Bool) :
    uniformMass halfCube x ≤ (2 : ℝ) ^ ((1 : ℝ) - Fintype.card (Fin 2)) := by
  have h : halfCube.card = 2 := by decide
  rw [Fintype.card_fin, show (1 : ℝ) - (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
  unfold uniformMass
  split_ifs
  · rw [h]; norm_num
  · positivity

-- A function that flips with the first bit is `true` on half of every fiber freeing that bit.
example (x : Fin 2 → Bool) :
    coordinateDensity (univ.filter fun z : Fin 2 → Bool => z 0 = true) (Pi.single 0 true) x =
      1 / 2 :=
  coordinateDensity_filter_eq_one_half_of_update_not (fun z => z 0) 0 (by simp) _ x (by simp) true

-- The light-patterns lemma applies to the uniform distribution on half of the cube, at `k = 1`.
example : 63 / 64 ≤ bernoulliAverage (1 / 512) (fun s : Fin 2 → Bool =>
    if ((univ.filter fun z => coordinateMass (uniformMass halfCube) s z ≤
        (2 : ℝ) ^ (-(Fintype.card {i // s i = true} : ℝ) - 2 * 1 - 2)).card : ℝ) ≤
      (2 : ℝ) ^ ((Fintype.card {i // s i = true} : ℝ) - 1) then 1 else 0) :=
  le_bernoulliAverage_card_coordinateMass_le (uniformMass_nonneg halfCube)
    (sum_uniformMass halfCube_nonempty) le_rfl
    uniformMass_halfCube_le (by norm_num)
    (by norm_num)

-- The mirror-set lemma applies with `X = Y` the whole cube, every point of which is a density
-- limit, at `k = 1`, `p = 1 / 65536` and `q = 32768 k p = 1 / 2`.
example {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∃ Y' : Finset (ι → Bool), Y'.Nonempty ∧ uniformDeficit Y' ≤ 4 ∧
      ∀ y ∈ Y', IsDensityLimit univ (1 / 2) 194 y := by
  have hdef : uniformDeficit (univ : Finset (ι → Bool)) ≤ 1 := by
    rw [uniformDeficit_le_iff univ_nonempty, card_univ, Fintype.card_fun, Fintype.card_bool,
      Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp)
  have hlim (x : ι → Bool) (_ : x ∈ (univ : Finset (ι → Bool))) :
      IsDensityLimit univ (1 / 65536) 1 x := by
    have h (P : ι → Bool) : coordinateDensity univ P x = 1 := by
      simp [coordinateDensity_eq_expect]
    simp only [IsDensityLimit, h]
    rw [ite_eq_left (by norm_num), bernoulliAverage_const]
    norm_num
  obtain ⟨Y', -, hne, hY', hlim'⟩ := exists_mirror_set univ univ univ_nonempty le_rfl hdef
    (by norm_num) (q := 1 / 2) (by norm_num) le_rfl hlim
  exact ⟨Y', hne, by linarith, by simpa using hlim'⟩

/-! ### The harmonic mean transform -/

/-- A function on one bit with values `1` and `2`. -/
def oneTwo (x : Fin 1 → Bool) : ℝ :=
  if x 0 then 2 else 1

-- Selecting every coordinate gives the harmonic mean `4 / 3` of `1` and `2`, which is at most
-- their mean `3 / 2`.
example :
    harmonicTransform oneTwo (fun _ => true) = 4 / 3 ∧
    harmonicTransform oneTwo (fun _ => true) ≤ 3 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [harmonicTransform_full, Cslib.harmonicMean_of_pos (fun x => by
      unfold oneTwo; split_ifs <;> norm_num)]
    simp only [oneTwo, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
    norm_num
  · have h := harmonicTransform_le_expect (f := oneTwo)
      (fun x => by unfold oneTwo; split_ifs <;> norm_num) (fun _ => true)
    simp only [oneTwo, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique] at h
    norm_num at h
    exact h

/-! ### Multilinear extensions -/

/-- The multilinear extension of the conjunction is the product of the two variables. -/
theorem eval_multilinearExtension_and₂ (z : Fin 2 → ℚ) :
    MvPolynomial.eval z (multilinearExtension fun x => bitVal ℚ (and₂ x)) = z 0 * z 1 := by
  rw [multilinearExtension, map_sum, sum_eq_single (fun _ => true)]
  · simp [eval_indicatorPoly_apply, and₂, bitVal, Fin.prod_univ_two]
  · intro a _ ha
    have h : and₂ a = false := by
      revert ha
      decide +revert
    simp [h, bitVal]
  · simp

-- Off the cube, at `(1 / 2, 1 / 3)`, it takes the value `1 / 6`, and on the cube it agrees with
-- the conjunction.
example :
    MvPolynomial.eval ![1 / 2, 1 / 3] (multilinearExtension fun x => bitVal ℚ (and₂ x)) = 1 / 6 ∧
    MvPolynomial.eval (fun i => bitVal ℚ (![true, false] i))
      (multilinearExtension fun x => bitVal ℚ (and₂ x)) = 0 :=
  ⟨by rw [eval_multilinearExtension_and₂]; norm_num,
    by rw [eval_multilinearExtension]; simp [and₂, bitVal]⟩

end ComplexityTests.BooleanAnalysisExamples
