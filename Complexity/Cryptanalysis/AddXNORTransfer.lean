/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORBits
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.GeomSum

/-!
# The signed carry transfer matrix

The transfer construction of [WangLvShenZhang2027], Theorem 5(ii), PDF pp. 17–18.
Rows are new low states and columns are old low states. Its signs are derived
from actual modular addition, not assumed transition probabilities.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- Signed transition matrix on the low j bits, in the source's orientation. -/
@[expose] def carryMatrix (j : ℕ) : Matrix (BitVec j) (BitVec j) ℚ :=
  fun t s => if t.toNat < s.toNat then -1 else 1

/-- Actual carry process on the low j bits. -/
@[expose] def lowTransfer (j : ℕ) (f : BitVec j → ℚ) (s : BitVec j) : ℚ :=
  𝔼 a : BitVec j, sign (BitVec.carry j s a false) * f (s + a)

/-- An addition overflows the low field exactly when the new field is smaller. -/
theorem carry_iff_wrap (j : ℕ) (s a : BitVec j) :
    BitVec.carry j s a false = decide ((s + a).toNat < s.toNat) := by
  rw [BitVec.carry_width]
  simp only [Bool.toNat_false, add_zero, BitVec.toNat_add]
  apply Bool.decide_congr
  have hs := s.isLt
  have ha := a.isLt
  by_cases h : s.toNat + a.toNat < 2 ^ j
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : (s.toNat + a.toNat) % 2 ^ j = s.toNat + a.toNat - 2 ^ j := by
      have hsum : s.toNat + a.toNat < 2 ^ j * 2 := by omega
      rw [Nat.mod_eq_sub_mod (by omega : 2 ^ j ≤ s.toNat + a.toNat)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [he]
    omega

/-- The actual carry update is precisely the normalized signed matrix update. -/
theorem lowTransfer_matrix (j : ℕ) (f : BitVec j → ℚ) (s : BitVec j) :
    lowTransfer j f s = 𝔼 t : BitVec j, carryMatrix j t s * f t := by
  unfold lowTransfer
  simp only [carry_iff_wrap, sign, decide_eq_true_eq]
  have hb : Function.Bijective (fun a : BitVec j => s + a) := by
    constructor
    · intro a b h
      exact add_left_cancel h
    · intro t
      exact ⟨t - s, by simp⟩
  exact Fintype.expect_bijective _ hb _ _ (fun _ => rfl)

private theorem split_bijective (h j : ℕ) : Function.Bijective
    (fun p : Fin (2 ^ h) × BitVec j =>
      BitVec.ofNat (h + j) (p.1.val * 2 ^ j + p.2.toNat)) := by
  have bound (hi : Fin (2 ^ h)) (lo : BitVec j) :
      hi.val * 2 ^ j + lo.toNat < 2 ^ (h + j) := by
    rw [pow_add]
    have hh := hi.isLt
    have hl := lo.isLt
    have hp := Nat.two_pow_pos j
    nlinarith
  have val (hi : Fin (2 ^ h)) (lo : BitVec j) :
      (BitVec.ofNat (h + j) (hi.val * 2 ^ j + lo.toNat)).toNat =
        hi.val * 2 ^ j + lo.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bound hi lo)]
  constructor
  · rintro ⟨hi, lo⟩ ⟨hi', lo'⟩ he
    have hn := congrArg BitVec.toNat he
    rw [val, val] at hn
    have hl := lo.isLt
    have hl' := lo'.isLt
    have hd : hi.val = hi'.val := by
      nlinarith
    exact Prod.ext (Fin.ext hd) (BitVec.eq_of_toNat_eq (by nlinarith [hn]))
  · intro w
    have hw := w.isLt
    rw [pow_add] at hw
    have hp := Nat.two_pow_pos j
    have hh : w.toNat / 2 ^ j < 2 ^ h := (Nat.div_lt_iff_lt_mul hp).mpr (by
      simpa only [Nat.mul_comm] using hw)
    refine ⟨(⟨w.toNat / 2 ^ j, hh⟩, BitVec.ofNat j w.toNat), ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [val, BitVec.toNat_ofNat]
    simpa only [Nat.mul_comm] using Nat.div_add_mod w.toNat (2 ^ j)

/-- Uniform full-width words have uniform low fields, with every high field averaged out. -/
theorem expect_low (h j : ℕ) (f : BitVec j → ℚ) :
    (𝔼 s : BitVec (h + j), f (s.setWidth j)) = 𝔼 t : BitVec j, f t := by
  rw [← Fintype.expect_bijective _ (split_bijective h j)
    (fun p => f ((BitVec.ofNat (h + j) (p.1.val * 2 ^ j + p.2.toNat)).setWidth j))
    _ (fun _ => rfl)]
  rw [show (Finset.univ : Finset (Fin (2 ^ h) × BitVec j)) =
    Finset.univ ×ˢ Finset.univ from Finset.univ_product_univ.symm, Finset.expect_product]
  have hl (hi : Fin (2 ^ h)) (lo : BitVec j) :
      (BitVec.ofNat (h + j) (hi.val * 2 ^ j + lo.toNat)).setWidth j = lo := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.add_mod, Nat.mod_eq_of_lt lo.isLt]
  simp only [hl, Finset.expect_const, Finset.univ_nonempty]

/-- Reduction of the full-word signed addition update to the true low-bit transfer. -/
theorem bitTransfer_add_low (h j : ℕ) (f : BitVec j → ℚ)
    (s : BitVec ((h + 1) + j)) :
    bitTransfer j false (fun t => f (t.setWidth j)) s =
      lowTransfer j f (s.setWidth j) := by
  unfold bitTransfer lowTransfer
  have hc (a : BitVec ((h + 1) + j)) :
      (carryWord s a).getLsbD j =
        BitVec.carry j (s.setWidth j) (a.setWidth j) false := by
    rw [carryWord_bit s a j (by omega)]
    simp only [BitVec.carry, BitVec.toNat_setWidth, Nat.mod_mod]
  simp only [Bool.false_eq_true, ↓reduceIte, step, hc]
  simp only [BitVec.setWidth_add _ _ (by omega : j ≤ (h + 1) + j)]
  have he := expect_low (h + 1) j
    (fun a => sign (BitVec.carry j (s.setWidth j) a false) * f (s.setWidth j + a))
  exact he

/-- Conditional signed correlation of z additions on the low field. -/
@[expose] def lowRun (j z : ℕ) : BitVec j → ℚ :=
  (lowTransfer j)^[z] (fun _ => 1)

/-- Every full-word conditional addition-run experiment reduces to the low field. -/
theorem bitCoefficients_additions_low (h j z : ℕ) (s : BitVec ((h + 1) + j)) :
    bitCoefficients j (List.replicate z false) s = lowRun j z (s.setWidth j) := by
  induction z generalizing s with
  | zero => rfl
  | succ z ih =>
    simp only [List.replicate_succ, bitCoefficients]
    have hf : bitCoefficients j (List.replicate z false) =
        (fun t : BitVec ((h + 1) + j) => lowRun j z (t.setWidth j)) := funext ih
    rw [hf, bitTransfer_add_low]
    exact (Function.iterate_succ_apply' (lowTransfer j) z (fun _ => 1))
      |> congrArg (fun f => f (s.setWidth j)) |>.symm

/-- Exact arbitrary-bit run correlation is independent of all bits above that bit. -/
theorem bitRunFactor_low (h j z : ℕ) :
    bitRunFactor ((h + 1) + j) j z = 𝔼 s : BitVec j, lowRun j z s := by
  rw [bitRunFactor, bitCorrelation_coefficients]
  simp only [bitCoefficients_additions_low]
  have he := expect_low (h + 1) j (lowRun j z)
  exact he

private theorem card_words (j : ℕ) : Fintype.card (BitVec j) = 2 ^ j := by
  exact (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)

/-- The normalized transpose acts on conditional (backward) correlations. -/
theorem lowTransfer_mulVec (j : ℕ) (f : BitVec j → ℚ) :
    lowTransfer j f = fun s => (2 ^ j : ℚ)⁻¹ * (carryMatrix j).transpose.mulVec f s := by
  funext s
  rw [lowTransfer_matrix, Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, card_words, Nat.cast_pow, Nat.cast_ofNat,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, div_eq_mul_inv, mul_comm]

/-- Powers of the actual signed transfer matrix evaluate every addition run. -/
theorem lowRun_matrix (j z : ℕ) :
    lowRun j z = fun s => (2 ^ j : ℚ)⁻¹ ^ z *
      ((carryMatrix j).transpose ^ z).mulVec (fun _ => 1) s := by
  induction z with
  | zero => simp [lowRun]
  | succ z ih =>
    rw [lowRun, Function.iterate_succ_apply']
    change lowTransfer j (lowRun j z) = _
    rw [lowTransfer_mulVec, ih]
    funext s
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← mul_assoc,
      ← Finset.sum_mul]
    rw [pow_succ', pow_succ']
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_assoc]
    congr 1
    funext t
    simp only [mul_one]
    apply Finset.sum_congr rfl
    intro u _
    ring

/-- The unsimplified matrix-power formula preceding the spectral expansion in
Theorem 5(ii). The formula is derived from the full-width word experiment. -/
theorem bitRunFactor_matrix (h j z : ℕ) :
    bitRunFactor ((h + 1) + j) j z =
      (2 ^ j : ℚ)⁻¹ ^ (z + 1) *
        ∑ s : BitVec j, ((carryMatrix j).transpose ^ z).mulVec (fun _ => 1) s := by
  rw [bitRunFactor_low, lowRun_matrix, Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, card_words, Nat.cast_pow, Nat.cast_ofNat,
    ← Finset.mul_sum, div_eq_mul_inv, pow_succ]
  ring

end Cslib.Cryptanalysis.AddXNOR
