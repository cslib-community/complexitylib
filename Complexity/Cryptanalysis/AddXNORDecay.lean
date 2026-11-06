/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORSpectrum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Decay of arbitrary-bit Add/XNOR correlation

[WangLvShenZhang2027], Theorem 5(ii–iv), PDF pp. 17–18. The eigenvalues
are identified as `1-i*cot(theta)`. For every observed bit below the word width
and every run length, the actual full-word signed correlation is bounded by
`bitDecay j ^ z`. For nonzero bits this is at most `(1 / sqrt 2) ^ z`.
The decay constants strictly decrease to `2 / pi`, with bit one uniquely extremal
and attaining its envelope at every run length divisible by four. Extremality
is asymptotic: it is not a run-by-run comparison of different bits. Bit zero
is admitted with decay constant one; the half-bit bound requires `1 ≤ j`.
-/

public section

open scoped BigOperators Topology

namespace Cslib.Cryptanalysis.AddXNOR

/-- Half-angle of an odd root of unity. -/
@[expose] noncomputable def carryAngle (N : ℕ) (k : Fin N) : ℝ :=
  (2 * k.val + 1) * Real.pi / (2 * N)

/-- Every spectral angle lies strictly between zero and pi. -/
theorem carryAngle_bounds (N : ℕ) (k : Fin N) :
    0 < carryAngle N k ∧ carryAngle N k < Real.pi := by
  have hk := k.isLt
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkr : (k.val : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hk)
  dsimp [carryAngle]
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mpr
    nlinarith [Real.pi_pos]

/-- Root in real-angle form, connecting the algebraic spectrum to trigonometry. -/
theorem carryRoot_angle (N : ℕ) (k : Fin N) :
    carryRoot N k = Complex.exp (Complex.I * (2 * carryAngle N k : ℝ)) := by
  unfold carryRoot carryAngle
  congr 1
  push_cast
  ring


/-- The eigenvalues in the exact trigonometric notation of Theorem 5(ii). -/
theorem carryEigenvalue_cot (N : ℕ) (k : Fin N) :
    carryEigenvalue N k =
      1 - Complex.I * (Real.cot (carryAngle N k) : ℂ) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (carryAngle_bounds N k).1
    (carryAngle_bounds N k).2
  have hsc : Complex.sin (carryAngle N k : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact_mod_cast hs.ne'
  unfold carryEigenvalue
  apply (div_eq_iff (sub_ne_zero.mpr (carryRoot_ne_one N k))).mpr
  rw [carryRoot_angle]
  have he : Complex.I * (2 * carryAngle N k : ℝ) =
      2 * (carryAngle N k : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.exp_mul_I, Complex.cos_two_mul_eq_one_sub, Complex.sin_two_mul]
  rw [Complex.ofReal_cot, Complex.cot_eq_cos_div_sin]
  field_simp
  linear_combination (norm := skip) (-2 * Complex.sin (carryAngle N k : ℂ)) *
    (Complex.sin_sq_add_cos_sq (carryAngle N k : ℂ))
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The exact magnitude of every eigenvalue. -/
theorem norm_carryEigenvalue (N : ℕ) (k : Fin N) :
    ‖carryEigenvalue N k‖ = 1 / Real.sin (carryAngle N k) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (carryAngle_bounds N k).1
    (carryAngle_bounds N k).2
  rw [carryEigenvalue, norm_div, norm_mul, norm_carryRoot,
    carryRoot_angle, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hh : 2 * carryAngle N k / 2 = carryAngle N k := by ring
  rw [hh, Real.norm_eq_abs, abs_of_pos (by positivity)]
  norm_num
  field_simp

/-- Exact spectral decay constant for bit j. -/
@[expose] noncomputable def bitDecay (j : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ j * Real.sin (Real.pi / (2 * (2 : ℝ) ^ j)))

/-- The decay constant is positive, including bit zero. -/
theorem bitDecay_pos (j : ℕ) : 0 < bitDecay j := by
  unfold bitDecay
  have hp : 0 < Real.pi / (2 * (2 : ℝ) ^ j) := by positivity
  have hq : Real.pi / (2 * (2 : ℝ) ^ j) < Real.pi := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have he : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith [Real.pi_pos]
  exact one_div_pos.mpr (mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi hp hq))

/-- The smallest spectral angle gives the largest eigenvalue magnitude. -/
theorem norm_carryEigenvalue_le (j : ℕ) (k : Fin (2 ^ j)) :
    ‖carryEigenvalue (2 ^ j) k‖ ≤ (2 : ℝ) ^ j * bitDecay j := by
  let N : ℝ := 2 ^ j
  let a := Real.pi / (2 * N)
  let b := carryAngle (2 ^ j) k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hk : (k.val : ℝ) < N := by dsimp [N]; exact_mod_cast k.isLt
  have hkn : (0 : ℝ) ≤ k.val := by positivity
  have hkb : (k.val : ℝ) + 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_of_lt k.isLt)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b, carryAngle, N]
    push_cast
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    nlinarith [Real.pi_pos]
  have hba : b ≤ Real.pi - a := by
    dsimp [a, b, carryAngle, N]
    push_cast
    apply (div_le_iff₀ (by positivity)).mpr
    have he : (Real.pi - Real.pi / (2 * (2 : ℝ) ^ j)) * (2 * (2 : ℝ) ^ j) =
        Real.pi * (2 * (2 : ℝ) ^ j - 1) := by field_simp
    rw [he]
    dsimp [N] at hkb
    nlinarith [Real.pi_pos]
  have hs : Real.sin a ≤ Real.sin b := by
    by_cases hb : b ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hb hab
    · rw [← Real.sin_pi_sub b]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith) (by linarith)
  have hap : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by
    dsimp [a]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_pos])
  rw [norm_carryEigenvalue]
  have he : (2 : ℝ) ^ j * bitDecay j = 1 / Real.sin a := by
    dsimp [bitDecay, a, N]
    field_simp
  rw [he]
  exact one_div_le_one_div_of_le hap hs

/-- The total spectral weight, obtained at run length zero. -/
theorem carryEigenvalue_weight_sum (j : ℕ) :
    (∑ k : Fin (2 ^ j), Complex.normSq (carryEigenvalue (2 ^ j) k)) = (2 : ℝ) ^ (2 * j) := by
  have h0 : (2 ^ j : ℂ) = (2 ^ j : ℂ)⁻¹ *
      ∑ k : Fin (2 ^ j), (Complex.normSq (carryEigenvalue (2 ^ j) k) : ℂ) := by
    simpa [Matrix.one_apply] using signedMatrix_pow_sum (2 ^ j) 0
  have he : (∑ k : Fin (2 ^ j), (Complex.normSq (carryEigenvalue (2 ^ j) k) : ℂ)) =
      (2 : ℂ) ^ (2 * j) := by
    field_simp at h0
    rw [Nat.mul_comm 2 j, pow_mul]
    exact h0.symm
  exact_mod_cast he

/-- Theorem 5(iii): every actual full-word run satisfies the explicit decay bound. -/
theorem abs_bitRunFactor_le (h j z : ℕ) :
    |(bitRunFactor ((h + 1) + j) j z : ℝ)| ≤ bitDecay j ^ z := by
  rw [← Complex.norm_ratCast, bitRunFactor_spectrum, norm_mul, norm_pow, norm_inv]
  have hn : ‖(2 ^ j : ℂ)‖ = (2 : ℝ) ^ j := by simp
  rw [hn]
  calc
    _ ≤ (2 ^ j : ℝ)⁻¹ ^ (z + 2) *
        ∑ k : Fin (2 ^ j), ‖(Complex.normSq (carryEigenvalue (2 ^ j) k) : ℂ) *
          carryEigenvalue (2 ^ j) k ^ z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2 ^ j : ℝ)⁻¹ ^ (z + 2) *
        ∑ k : Fin (2 ^ j), Complex.normSq (carryEigenvalue (2 ^ j) k) *
          ((2 : ℝ) ^ j * bitDecay j) ^ z := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Complex.normSq_nonneg _), norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_carryEigenvalue_le j k) z)
        (Complex.normSq_nonneg _)
    _ = bitDecay j ^ z := by
      rw [← Finset.sum_mul, carryEigenvalue_weight_sum]
      simp only [pow_add, mul_pow, inv_pow]
      field_simp
      ring

/-- The decay rates strictly decrease with the bit position. -/
theorem bitDecay_strictAnti : StrictAnti bitDecay := by
  apply strictAnti_nat_of_succ_lt
  intro j
  let x : ℝ := 2 ^ j
  let a := Real.pi / (4 * x)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have ha : 0 < a := by dsimp [a]; positivity
  have hap : a < Real.pi / 2 := by
    dsimp [a]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hcos : Real.cos a < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      (by linarith : a ≤ Real.pi) ha
  have hden : x * Real.sin (Real.pi / (2 * x)) <
      (2 * x) * Real.sin (Real.pi / (2 * (2 * x))) := by
    have he : Real.pi / (2 * x) = 2 * a := by dsimp [a]; ring
    have he' : Real.pi / (2 * (2 * x)) = a := by dsimp [a]; ring
    rw [he, he', Real.sin_two_mul]
    have hm := mul_lt_mul_of_pos_left hcos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hx) hsin)
    nlinarith
  have hpos : 0 < x * Real.sin (Real.pi / (2 * x)) := by
    have hp : 0 < Real.pi / (2 * x) := by positivity
    have hq : Real.pi / (2 * x) < Real.pi := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [Real.pi_pos]
    exact mul_pos hx (Real.sin_pos_of_pos_of_lt_pi hp hq)
  change 1 / ((2 : ℝ) ^ (j + 1) * _) < 1 / ((2 : ℝ) ^ j * _)
  rw [pow_succ]
  simpa only [x, mul_comm (2 : ℝ)] using one_div_lt_one_div_of_lt hpos hden

/-- Bit one's decay rate is exactly the source's half-bit-per-addition constant. -/
theorem bitDecay_one : bitDecay 1 = 1 / Real.sqrt 2 := by
  norm_num [bitDecay, Real.sin_pi_div_four]
  field_simp
  exact Real.sq_sqrt (by norm_num)

/-- Every nonzero bit is bounded by the bit-one decay rate. -/
theorem bitDecay_le_bit_one (j : ℕ) (hj : 1 ≤ j) : bitDecay j ≤ 1 / Real.sqrt 2 := by
  rw [← bitDecay_one]
  exact bitDecay_strictAnti.antitone hj

/-- Theorem 5(iv)'s uniform arbitrary-bit correlation bound. -/
theorem abs_bitRunFactor_le_bit_one (h j z : ℕ) (hj : 1 ≤ j) :
    |(bitRunFactor ((h + 1) + j) j z : ℝ)| ≤ (1 / Real.sqrt 2) ^ z :=
  (abs_bitRunFactor_le h j z).trans
    (pow_le_pow_left₀ (bitDecay_pos j).le (bitDecay_le_bit_one j hj) z)


/-- Bit one is the unique bit with this extremal decay constant. -/
theorem bitDecay_eq_bit_one_iff (j : ℕ) :
    bitDecay j = 1 / Real.sqrt 2 ↔ j = 1 := by
  rw [← bitDecay_one]
  exact bitDecay_strictAnti.injective.eq_iff

/-- Bit one attains its envelope at every run length divisible by four. -/
theorem abs_bitRunFactor_bit_one_four (h t : ℕ) :
    |(bitRunFactor (h + 2) 1 (4 * t) : ℝ)| = (1 / Real.sqrt 2) ^ (4 * t) := by
  rw [bitRunFactor_bit_one, runFactor_cos]
  have he : ((4 * t : ℕ) : ℝ) * (Real.pi / 4) = (t : ℝ) * Real.pi := by
    push_cast
    ring
  rw [he, Real.cos_nat_mul_pi, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, mul_one]
  rw [abs_of_nonneg (show 0 ≤ 1 / Real.sqrt 2 by positivity)]

/-- Every operator string satisfies the same uniform bound, with the exponent
counting its actual additions rather than its total length. -/
theorem abs_bitCorrelation_le_bit_one (h j : ℕ) (bs : List Bool) (hj : 1 ≤ j) :
    |(bitCorrelation ((h + 1) + j) j bs : ℝ)| ≤
      (1 / Real.sqrt 2) ^ bs.count false := by
  obtain ⟨zs, hz, hc⟩ := bitCorrelation_run_product ((h + 1) + j) j bs
  have hn : zs.sum = bs.count false := by
    rw [← runs_addition_count, hz]
    simp
  rw [hc, ← hn]
  clear hz hc hn
  induction zs with
  | nil => norm_num
  | cons z zs ih =>
    simp only [List.map_cons, List.prod_cons, Rat.cast_mul, abs_mul, List.sum_cons, pow_add]
    exact mul_le_mul (abs_bitRunFactor_le_bit_one h j z hj) ih (abs_nonneg _) (by positivity)

/-- The limiting decay constant is 2/pi. -/
theorem tendsto_bitDecay : Filter.Tendsto bitDecay Filter.atTop (nhds (2 / Real.pi)) := by
  have ha : Filter.Tendsto (fun j : ℕ => Real.pi / (2 * (2 : ℝ) ^ j))
      Filter.atTop (nhds 0) := by
    have hp := (tendsto_const_nhds (x := Real.pi / 2)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    convert hp using 1
    · funext j
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
      ring
    · simp
  have hs : Filter.Tendsto
      (fun j : ℕ => Real.sinc (Real.pi / (2 * (2 : ℝ) ^ j))) Filter.atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt.tendsto.comp ha)
  have hd := (tendsto_const_nhds (x := (2 : ℝ) / Real.pi)).div hs (by norm_num)
  convert hd using 1
  · funext j
    change bitDecay j = (2 / Real.pi) / Real.sinc (Real.pi / (2 * (2 : ℝ) ^ j))
    rw [Real.sinc_of_ne_zero (by positivity)]
    unfold bitDecay
    field_simp
  · simp

end Cslib.Cryptanalysis.AddXNOR
