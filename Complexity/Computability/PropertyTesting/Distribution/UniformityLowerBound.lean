/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PropertyTesting.Distribution.Basic
public import Complexity.Probability.Collision
import Complexity.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Paninski's lower bound for uniformity testing

On a domain of even size `n`, every `k`-sample uniformity tester with proximity `δ ≤ 1 / 2` in
statistical distance satisfies `n ≤ 52 k² δ⁴` (`card_le_of_isTester_uniform`), so
`k = Ω(√n / δ²)` samples are necessary [Paninski][Paninski2008]. This matches the collision tester
(`Cslib.DistributionTesting.isTester_collisionTester`) up to the constant. At `δ = 1 / 2` it is
the birthday bound `4 n ≤ 13 k²` (`four_mul_card_le_of_isTester_uniform`).

The hard instances live on `Fin m × Bool`. For a sign vector `σ : Fin m → Bool`, Paninski's
distribution `paninski hε σ` puts mass `(1 ± ε) / (2 m)` on `(i, b)`, with the plus sign when
`b = σ i`; it is at distance `|ε| / 2` from uniform (`dist_paninski_uniform`). The mixture
`paninskiMixture m hε k` draws `σ` uniformly and then `k` samples from `paninski hε σ`. Its
collision probability satisfies the second-moment bound
`(2 m)^k ‖Q‖₂² ≤ cosh(k ε² / m)^m ≤ exp(k² ε⁴ / (2 m))`
(`collisionProbability_paninskiMixture_le`), so it is close to `k` uniform samples
(`dist_paninskiMixture_sq_le`). Le Cam's method
(`Cslib.DistributionTesting.one_third_le_dist_iid_bind`) then bounds `k`. At `ε = 1` each
`paninski hε σ` is uniform on a subset of half the domain, the instance of the birthday argument.
The constants `52` and `13` are the ones this proof gives; they are not optimized.

## Main definitions

* `Cslib.DistributionTesting.paninski`: Paninski's perturbations of the uniform distribution.
* `Cslib.DistributionTesting.paninskiMixture`: their uniform mixture over `k` samples.

## Main results

* `Cslib.DistributionTesting.collisionProbability_paninskiMixture_le`: the second-moment bound.
* `Cslib.DistributionTesting.le_of_isTester_uniform_prod`: the lower bound on `Fin m × Bool`.
* `Cslib.DistributionTesting.card_le_of_isTester_uniform`: the lower bound on even domains.
* `Cslib.DistributionTesting.four_mul_card_le_of_isTester_uniform`: the birthday bound.

## References

* [L. Paninski, *A coincidence-based test for uniformity given very sparsely sampled discrete
  data*][Paninski2008]
* [C. L. Canonne, *A Survey on Distribution Testing: Your Data is Big. But is it
  Blue?*][Canonne2020]
-/

public section

namespace Cslib.DistributionTesting

open Cslib.Probability.PMF Finset

section Paninski

variable {m : ℕ}

/-- Paninski's perturbation of the uniform distribution on `Fin m × Bool`: the point `(i, b)`
receives mass `(1 + ε) / (2 m)` when `b = σ i` and `(1 - ε) / (2 m)` otherwise. -/
noncomputable def paninskiWeight (ε : ℝ) (σ : Fin m → Bool) (y : Fin m × Bool) : ℝ :=
  (1 + if y.2 = σ y.1 then ε else -ε) / (2 * m)

/-- Paninski weights are nonnegative for `|ε| ≤ 1`. -/
theorem paninskiWeight_nonneg {ε : ℝ} (hε : |ε| ≤ 1) (σ : Fin m → Bool) (y : Fin m × Bool) :
    0 ≤ paninskiWeight ε σ y := by
  rw [abs_le] at hε
  unfold paninskiWeight
  refine div_nonneg ?_ (by positivity)
  split_ifs <;> linarith

private theorem sum_bool_ite_neg (c : Bool) (ε : ℝ) :
    ∑ b : Bool, (if b = c then ε else -ε) = 0 := by
  cases c <;> simp

/-- Paninski weights sum to one. -/
theorem sum_paninskiWeight [NeZero m] (ε : ℝ) (σ : Fin m → Bool) :
    ∑ y, paninskiWeight ε σ y = 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have h (i : Fin m) : ∑ b, paninskiWeight ε σ (i, b) = 1 / m := by
    simp only [paninskiWeight, ← sum_div, sum_add_distrib, sum_bool_ite_neg, sum_const, card_univ,
      Fintype.card_bool, nsmul_eq_mul]
    field_simp
    norm_num
  rw [Fintype.sum_prod_type]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Paninski's distribution on `Fin m × Bool` with bias `ε` along the sign vector `σ`. -/
noncomputable def paninski [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (σ : Fin m → Bool) :
    PMF (Fin m × Bool) :=
  PMF.ofFintype (fun y => ENNReal.ofReal (paninskiWeight ε σ y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => paninskiWeight_nonneg hε σ y,
      sum_paninskiWeight, ENNReal.ofReal_one])

/-- The masses of Paninski's distribution are its weights. -/
theorem paninski_apply_toReal [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (σ : Fin m → Bool)
    (y : Fin m × Bool) : (paninski hε σ y).toReal = paninskiWeight ε σ y := by
  rw [paninski, PMF.ofFintype_apply, ENNReal.toReal_ofReal (paninskiWeight_nonneg hε σ y)]

/-- Every Paninski distribution is at statistical distance `|ε| / 2` from uniform. -/
theorem dist_paninski_uniform [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (σ : Fin m → Bool) :
    dist (paninski hε σ) (uniformOfFintype (Fin m × Bool)) = |ε| / 2 := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have h (y : Fin m × Bool) : |(paninski hε σ y).toReal -
      (uniformOfFintype (Fin m × Bool) y).toReal| = |ε| / (2 * m) := by
    rw [paninski_apply_toReal, uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    unfold paninskiWeight
    push_cast
    rw [show (1 + (if y.2 = σ y.1 then ε else -ε)) / (2 * m) - ((m : ℝ) * 2)⁻¹ =
        (if y.2 = σ y.1 then ε else -ε) / (2 * m) by field_simp; ring,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * m)]
    split_ifs <;> simp
  rw [dist_eq]
  simp only [h, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- Paninski's mixture: draw a uniformly random sign vector `σ`, then `k` independent samples
from `paninski hε σ`. -/
noncomputable def paninskiMixture (m : ℕ) [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (k : ℕ) :
    PMF (Fin k → Fin m × Bool) :=
  (uniformOfFintype (Fin m → Bool)).bind fun σ => iid (paninski hε σ) k

/-- The inner product of two Paninski weight vectors. -/
theorem sum_paninskiWeight_mul [NeZero m] (ε : ℝ) (σ τ : Fin m → Bool) :
    ∑ y, paninskiWeight ε σ y * paninskiWeight ε τ y =
      (1 + ε ^ 2 / m * ∑ i, (if σ i = τ i then (1 : ℝ) else -1)) / (2 * m) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have h (i : Fin m) : ∑ b, paninskiWeight ε σ (i, b) * paninskiWeight ε τ (i, b) =
      (2 + 2 * ε ^ 2 * (if σ i = τ i then (1 : ℝ) else -1)) / (2 * m) ^ 2 := by
    rw [Fintype.sum_bool]
    unfold paninskiWeight
    dsimp only
    cases σ i <;> cases τ i <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false] <;>
      field_simp <;> ring
  rw [Fintype.sum_prod_type]
  simp only [h, ← sum_div, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- The mass of a sample tuple under Paninski's mixture is the average over sign vectors of the
product of the weights. -/
theorem paninskiMixture_apply_toReal [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) {k : ℕ}
    (x : Fin k → Fin m × Bool) :
    (paninskiMixture m hε k x).toReal =
      ∑ σ : Fin m → Bool, ((2 : ℝ) ^ m)⁻¹ * ∏ j, paninskiWeight ε σ (x j) := by
  rw [paninskiMixture, bind_apply_toReal]
  refine sum_congr rfl fun σ _ => ?_
  rw [uniformOfFintype_apply, iid_apply, ENNReal.toReal_prod, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  simp only [paninski_apply_toReal]

/-- The collision probability of Paninski's mixture as an average over pairs of sign vectors of
the `k`-th powers of the inner products of their weight vectors. -/
theorem collisionProbability_paninskiMixture [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (k : ℕ) :
    collisionProbability (paninskiMixture m hε k) =
      ((4 : ℝ) ^ m)⁻¹ * ∑ σ : Fin m → Bool, ∑ τ : Fin m → Bool,
        (∑ y, paninskiWeight ε σ y * paninskiWeight ε τ y) ^ k := by
  have hc : ((2 : ℝ) ^ m)⁻¹ ^ 2 = ((4 : ℝ) ^ m)⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hx (x : Fin k → Fin m × Bool) : (paninskiMixture m hε k x).toReal ^ 2 =
      ((4 : ℝ) ^ m)⁻¹ * ∑ σ : Fin m → Bool, ∑ τ : Fin m → Bool,
        ∏ j, (paninskiWeight ε σ (x j) * paninskiWeight ε τ (x j)) := by
    rw [paninskiMixture_apply_toReal, ← mul_sum, mul_pow, hc, pow_two, sum_mul_sum]
    simp only [prod_mul_distrib]
  rw [collisionProbability_eq_sum]
  simp only [hx]
  rw [← mul_sum]
  congr 1
  refine sum_comm.trans ?_
  refine sum_congr rfl fun σ _ => ?_
  refine sum_comm.trans ?_
  refine sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_pow]

private theorem one_add_pow_le_exp {k : ℕ} {x : ℝ} (hx : -1 ≤ x) :
    (1 + x) ^ k ≤ Real.exp (k * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) k

/-- The second-moment bound for Paninski's mixture: `(2m)^k ‖Q‖₂² ≤ exp(k² ε⁴ / (2m))`. -/
theorem collisionProbability_paninskiMixture_le [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (k : ℕ) :
    (2 * m : ℝ) ^ k * collisionProbability (paninskiMixture m hε k) ≤
      Real.exp (k ^ 2 * ε ^ 4 / (2 * m)) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hε2 : ε ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg ε]
  set lam : ℝ := k * ε ^ 2 / m with hlam
  have hterm (σ τ : Fin m → Bool) :
      (2 * m : ℝ) ^ k * (∑ y, paninskiWeight ε σ y * paninskiWeight ε τ y) ^ k ≤
        Real.exp (lam * ∑ i, if σ i = τ i then (1 : ℝ) else -1) := by
    have hS : -(m : ℝ) ≤ ∑ i, if σ i = τ i then (1 : ℝ) else -1 := by
      have h := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin m))) =>
        (show (-1 : ℝ) ≤ if σ i = τ i then 1 else -1 by split_ifs <;> norm_num)
      simpa using h
    have h2m : (2 * m : ℝ) ≠ 0 := by positivity
    rw [sum_paninskiWeight_mul, ← mul_pow, mul_div_assoc', mul_div_cancel_left₀ _ h2m]
    refine (one_add_pow_le_exp ?_).trans_eq ?_
    · have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ ε ^ 2 / m)
      rw [mul_neg, div_mul_cancel₀ _ hm.ne'] at this
      linarith
    · rw [hlam]
      congr 1
      ring
  have hpair (σ : Fin m → Bool) :
      ∑ τ : Fin m → Bool, Real.exp (lam * ∑ i, if σ i = τ i then (1 : ℝ) else -1) =
        (2 * Real.cosh lam) ^ m := by
    simp only [mul_sum, Real.exp_sum]
    refine (Fintype.prod_sum
      (fun i (b : Bool) => Real.exp (lam * if σ i = b then (1 : ℝ) else -1))).symm.trans ?_
    rw [show (2 * Real.cosh lam) ^ m = ∏ _i : Fin m, 2 * Real.cosh lam by
      rw [prod_const, card_univ, Fintype.card_fin]]
    refine prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool, Real.cosh_eq]
    cases σ i <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, 
        mul_one, mul_neg] <;> ring
  calc (2 * m : ℝ) ^ k * collisionProbability (paninskiMixture m hε k)
      = ((4 : ℝ) ^ m)⁻¹ * ∑ σ : Fin m → Bool, ∑ τ : Fin m → Bool,
          (2 * m : ℝ) ^ k * (∑ y, paninskiWeight ε σ y * paninskiWeight ε τ y) ^ k := by
        rw [collisionProbability_paninskiMixture, mul_left_comm]
        simp only [mul_sum]
    _ ≤ ((4 : ℝ) ^ m)⁻¹ * ∑ σ : Fin m → Bool, ∑ τ : Fin m → Bool,
          Real.exp (lam * ∑ i, if σ i = τ i then (1 : ℝ) else -1) := by
        gcongr with σ _ τ _
        exact hterm σ τ
    _ = Real.cosh lam ^ m := by
        simp only [hpair, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [mul_pow, show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
        field_simp
    _ ≤ Real.exp (lam ^ 2 / 2) ^ m :=
        pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) m
    _ = Real.exp (k ^ 2 * ε ^ 4 / (2 * m)) := by
        rw [← Real.exp_nat_mul, hlam]
        congr 1
        field_simp

/-- Paninski's mixture is close to `k` uniform samples when `k² ε⁴ ≪ m`. -/
theorem dist_paninskiMixture_sq_le [NeZero m] {ε : ℝ} (hε : |ε| ≤ 1) (k : ℕ) :
    4 * dist (iid (uniformOfFintype (Fin m × Bool)) k) (paninskiMixture m hε k) ^ 2 ≤
      Real.exp (k ^ 2 * ε ^ 4 / (2 * m)) - 1 := by
  have h := dist_uniform_sq_le (paninskiMixture m hε k)
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool] at h
  push_cast at h
  rw [mul_comm (m : ℝ) 2] at h
  rw [iid_uniformOfFintype, dist_comm]
  have h2 := collisionProbability_paninskiMixture_le (m := m) hε k
  linarith

/-- **Paninski's lower bound** on `Fin m × Bool`: every `k`-sample uniformity tester with proximity
`δ ≤ 1 / 2` satisfies `2 m ≤ 52 k² δ⁴`. -/
theorem le_of_isTester_uniform_prod [NeZero m] {k : ℕ}
    {T : (Fin k → Fin m × Bool) → PMF Bool} {δ : ℝ}
    (hT : IsTester T {uniformOfFintype (Fin m × Bool)} δ) (hδ : δ ≤ 1 / 2) :
    (2 * m : ℝ) ≤ 52 * k ^ 2 * δ ^ 4 := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  rcases le_or_gt δ 0 with hδ0 | hδ0
  · exfalso
    have h1 := hT.accept _ (Set.mem_singleton _)
    have h2 := hT.reject (uniformOfFintype (Fin m × Bool)) fun q hq => by
      rw [Set.mem_singleton_iff] at hq
      rw [hq, dist_self]
      exact hδ0
    linarith
  have hε : |2 * δ| ≤ 1 := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hfar : ∀ σ : Fin m → Bool, ∀ q ∈ ({uniformOfFintype (Fin m × Bool)} :
      Set (PMF (Fin m × Bool))), δ ≤ dist (paninski hε σ) q := by
    intro σ q hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq, dist_paninski_uniform, abs_of_pos (by linarith)]
    linarith
  have h3 : 1 / 3 ≤ dist (iid (uniformOfFintype (Fin m × Bool)) k) (paninskiMixture m hε k) :=
    one_third_le_dist_iid_bind hT (Set.mem_singleton _) (uniformOfFintype (Fin m → Bool))
      (fun σ => paninski hε σ) hfar
  have h4 := dist_paninskiMixture_sq_le (m := m) hε k
  set x := (k : ℝ) ^ 2 * (2 * δ) ^ 4 / (2 * m) with hx
  have hx0 : 0 ≤ x := by positivity
  have h5 : 13 / 9 ≤ Real.exp x := by nlinarith
  have hx4 : 4 / 13 ≤ x := by
    rcases lt_or_ge x 1 with hx1 | hx1
    · have h7 : 13 / 9 ≤ 1 / (1 - x) := h5.trans (Real.exp_bound_div_one_sub_of_interval hx0 hx1)
      rw [le_div_iff₀ (by linarith)] at h7
      linarith
    · linarith
  rw [hx, le_div_iff₀ (by positivity)] at hx4
  nlinarith

end Paninski

section Even

variable {α : Type*} [Fintype α]

/-- **Paninski's lower bound for uniformity testing**: on a domain of even size `n`, every
`k`-sample uniformity tester with proximity `δ ≤ 1 / 2` satisfies `n ≤ 52 k² δ⁴`. -/
theorem card_le_of_isTester_uniform [Nonempty α] (hα : Even (Fintype.card α)) {k : ℕ}
    {T : (Fin k → α) → PMF Bool} {δ : ℝ} (hT : IsTester T {uniformOfFintype α} δ)
    (hδ : δ ≤ 1 / 2) : (Fintype.card α : ℝ) ≤ 52 * k ^ 2 * δ ^ 4 := by
  obtain ⟨m, hm⟩ := hα
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact Fintype.card_ne_zero hm
  have : NeZero m := ⟨hm0⟩
  have hcard : Fintype.card α = Fintype.card (Fin m × Bool) := by
    rw [hm, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have h := le_of_isTester_uniform_prod (hT.comp_equiv_uniform (Fintype.equivOfCardEq hcard)) hδ
  rw [hm]
  push_cast
  linarith

/-- **Birthday lower bound**: distinguishing uniform from distributions at distance `1 / 2` (such as
uniform distributions on half of the domain) requires `4 n ≤ 13 k²` samples. -/
theorem four_mul_card_le_of_isTester_uniform [Nonempty α] (hα : Even (Fintype.card α)) {k : ℕ}
    {T : (Fin k → α) → PMF Bool} (hT : IsTester T {uniformOfFintype α} (1 / 2)) :
    4 * Fintype.card α ≤ 13 * k ^ 2 := by
  have h := card_le_of_isTester_uniform hα hT le_rfl
  norm_num at h
  exact_mod_cast (by linarith : (4 * Fintype.card α : ℝ) ≤ 13 * k ^ 2)

end Even

end Cslib.DistributionTesting
