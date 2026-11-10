/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# ML-KEM coefficient compression

FIPS 203 compresses a coefficient `x ∈ ℤ_q` to `d` bits and lifts it back by
`Compress_d(x) = ⌈(2^d / q) · x⌋ mod 2^d` and `Decompress_d(y) = ⌈(q / 2^d) · y⌋`
([NIST, Section 4.2.1][NISTFIPS203]), where `⌈r⌋` rounds to the nearest
integer with ties rounded up. Natural-number rounded division `roundDiv a b = ⌊(2a + b) / (2b)⌋`
implements `⌈a / b⌋`, so `compress` and `decompress` below are these two maps for every modulus
`q` and width `d`, written on canonical representatives.

The three facts used by K-PKE are proved for every positive modulus:

* `compress_decompress`: compression inverts decompression when `2^d < q`.
* `natAbs_valMinAbs_decompress_compress_sub_le`: the centered rounding error of
  `Decompress_d ∘ Compress_d` is at most `⌈q / 2^(d + 1)⌋`.
* `compress_one_decompress_one_add`: one-bit decoding tolerates any centered error of
  magnitude at most `B` when `4 * B + 2 < q`; this is the decoding step of K-PKE decryption.

## Main definitions

* `Cslib.Crypto.MLKEM.roundDiv`: rounded natural division `⌈a / b⌋`, ties up.
* `Cslib.Crypto.MLKEM.compress`, `Cslib.Crypto.MLKEM.decompress`: FIPS 203 coefficient maps.
* `Cslib.Crypto.MLKEM.compressPoly`, `Cslib.Crypto.MLKEM.decompressPoly`: coefficientwise maps
  on polynomials `Fin n → ZMod q`.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 4.2.1][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

/-- Rounded natural division `⌈a / b⌋ = ⌊(2a + b) / (2b)⌋`, with ties rounded up. -/
def roundDiv (a b : ℕ) : ℕ := (2 * a + b) / (2 * b)

/-- FIPS 203 compression `Compress_d(x) = ⌈(2^d / q) · x⌋ mod 2^d` of a coefficient modulo `q`,
computed on the canonical representative `x.val ∈ [0, q)`. -/
def compress (q d : ℕ) (x : ZMod q) : ZMod (2 ^ d) :=
  (roundDiv (2 ^ d * x.val) q : ZMod (2 ^ d))

/-- FIPS 203 decompression `Decompress_d(y) = ⌈(q / 2^d) · y⌋` of a `d`-bit value, computed on its
canonical representative `y.val ∈ [0, 2^d)`. -/
def decompress (q d : ℕ) (y : ZMod (2 ^ d)) : ZMod q :=
  (roundDiv (q * y.val) (2 ^ d) : ZMod q)

/-- Coefficientwise compression of a polynomial `f ∈ ℤ_q[X] / (X^n + 1)` in coefficient form. -/
def compressPoly {n : ℕ} (q d : ℕ) (f : Fin n → ZMod q) : Fin n → ZMod (2 ^ d) :=
  fun i => compress q d (f i)

/-- Coefficientwise decompression of a polynomial with `d`-bit coefficients. -/
def decompressPoly {n : ℕ} (q d : ℕ) (f : Fin n → ZMod (2 ^ d)) : Fin n → ZMod q :=
  fun i => decompress q d (f i)

@[simp] theorem compressPoly_apply {n : ℕ} (q d : ℕ) (f : Fin n → ZMod q) (i : Fin n) :
    compressPoly q d f i = compress q d (f i) :=
  rfl

@[simp] theorem decompressPoly_apply {n : ℕ} (q d : ℕ) (f : Fin n → ZMod (2 ^ d)) (i : Fin n) :
    decompressPoly q d f i = decompress q d (f i) :=
  rfl

/-- The defining inequalities of rounded division: `b · ⌈a / b⌋` is within `b / 2` of `a`. -/
theorem roundDiv_spec {a b : ℕ} (hb : 0 < b) :
    2 * b * roundDiv a b ≤ 2 * a + b ∧ 2 * a + b < 2 * b * roundDiv a b + 2 * b := by
  have h := Nat.div_add_mod (2 * a + b) (2 * b)
  have hlt := Nat.mod_lt (2 * a + b) (show 0 < 2 * b by omega)
  unfold roundDiv
  constructor <;> omega

/-- Rounded division is characterized by its defining inequalities. -/
theorem roundDiv_eq_of_le_of_lt {a b c : ℕ} (hle : 2 * b * c ≤ 2 * a + b)
    (hlt : 2 * a + b < 2 * b * c + 2 * b) : roundDiv a b = c := by
  unfold roundDiv
  have hb : 0 < 2 * b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · omega
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have e : c * (2 * b) = 2 * b * c := Nat.mul_comm _ _
    omega
  · have e : (c + 1) * (2 * b) = 2 * b * c + 2 * b := by ring
    omega

/-- **Compression inverts decompression** ([NIST, Section 4.2.1][NISTFIPS203]): whenever
`2^d < q`, `Compress_d(Decompress_d(y)) = y` for every `d`-bit value `y`. -/
theorem compress_decompress {q d : ℕ} (hd : 2 ^ d < q) (y : ZMod (2 ^ d)) :
    compress q d (decompress q d y) = y := by
  have ha : 0 < 2 ^ d := Nat.two_pow_pos d
  have hy : y.val + 1 ≤ 2 ^ d := ZMod.val_lt y
  obtain ⟨h₁, h₂⟩ := roundDiv_spec (a := q * y.val) ha
  have hqy : q * (y.val + 1) ≤ q * 2 ^ d := Nat.mul_le_mul_left q hy
  have hxq : roundDiv (q * y.val) (2 ^ d) < q := by
    by_contra hcon
    have := Nat.mul_le_mul_left (2 * 2 ^ d) (Nat.le_of_not_lt hcon)
    nlinarith
  unfold compress decompress
  rw [ZMod.val_natCast_of_lt hxq]
  have hc : roundDiv (2 ^ d * roundDiv (q * y.val) (2 ^ d)) q = y.val := by
    apply roundDiv_eq_of_le_of_lt <;> nlinarith
  rw [hc, ZMod.natCast_zmod_val]

/-- **Rounding error of compression**: for every positive modulus `q`, width `d` and coefficient
`x`, the centered representative of `Decompress_d(Compress_d(x)) - x` has magnitude at most
`⌈q / 2^(d + 1)⌋`. This is the standard error bound used in the correctness analysis of Kyber;
FIPS 203 itself only remarks that the error is small. -/
theorem natAbs_valMinAbs_decompress_compress_sub_le {q : ℕ} [NeZero q] (d : ℕ) (x : ZMod q) :
    (decompress q d (compress q d x) - x).valMinAbs.natAbs ≤ roundDiv q (2 ^ (d + 1)) := by
  have ha : 0 < 2 ^ d := Nat.two_pow_pos d
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hB : roundDiv q (2 ^ (d + 1)) = (q + 2 ^ d) / (2 * 2 ^ d) := by
    unfold roundDiv
    rw [pow_succ]
    have e₁ : 2 * q + 2 ^ d * 2 = 2 * (q + 2 ^ d) := by ring
    have e₂ : 2 * (2 ^ d * 2) = 2 * (2 * 2 ^ d) := by ring
    rw [e₁, e₂, Nat.mul_div_mul_left _ _ (by norm_num)]
  rw [hB]
  have hvq : x.val + 1 ≤ q := ZMod.val_lt x
  have hdiv : ∀ t : ℕ, 2 * 2 ^ d * t ≤ q + 2 ^ d → t ≤ (q + 2 ^ d) / (2 * 2 ^ d) :=
    fun t ht => (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
  -- It suffices to bound a natural number `t` whose signed version represents the difference.
  suffices h : ∃ t : ℕ, 2 * 2 ^ d * t ≤ q + 2 ^ d ∧
      (((t : ℤ) : ZMod q) = decompress q d (compress q d x) - x ∨
        ((-(t : ℤ) : ℤ) : ZMod q) = decompress q d (compress q d x) - x) by
    obtain ⟨t, ht, hz⟩ := h
    refine le_trans ?_ (hdiv t ht)
    rcases hz with hz | hz
    · refine le_trans (ZMod.natAbs_min_of_le_div_two q _ (t : ℤ) ?_
        (ZMod.natAbs_valMinAbs_le _)) (by simp)
      rw [ZMod.coe_valMinAbs, hz]
    · refine le_trans (ZMod.natAbs_min_of_le_div_two q _ (-(t : ℤ)) ?_
        (ZMod.natAbs_valMinAbs_le _)) (by simp)
      rw [ZMod.coe_valMinAbs, hz]
  obtain ⟨h₁, h₂⟩ := roundDiv_spec (a := 2 ^ d * x.val) hq
  set c := roundDiv (2 ^ d * x.val) q with hc
  have hv1 : 2 ^ d * (x.val + 1) ≤ 2 ^ d * q := Nat.mul_le_mul_left _ hvq
  have hca : c ≤ 2 ^ d := by
    by_contra hcon
    have := Nat.mul_le_mul_left (2 * q) (show 2 ^ d + 1 ≤ c by omega)
    nlinarith
  have hxv : (x.val : ZMod q) = x := ZMod.natCast_zmod_val x
  rcases Nat.lt_or_ge c (2 ^ d) with hlt | hge
  · -- No wrap-around: the compressed value is `c` itself.
    have hcval : (compress q d x).val = c := by
      change ((c : ℕ) : ZMod (2 ^ d)).val = c
      exact ZMod.val_natCast_of_lt hlt
    obtain ⟨h₃, h₄⟩ := roundDiv_spec (a := q * c) ha
    set x' := roundDiv (q * c) (2 ^ d) with hx'
    have hdec : decompress q d (compress q d x) = (x' : ZMod q) := by
      unfold decompress
      rw [hcval]
    rcases le_or_gt x.val x' with hvx | hvx
    · refine ⟨x' - x.val, ?_, Or.inl ?_⟩
      · have e : 2 * 2 ^ d * (x' - x.val) + 2 * 2 ^ d * x.val = 2 * 2 ^ d * x' := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hvx]
        nlinarith
      · rw [hdec, Int.cast_natCast, Nat.cast_sub hvx, hxv]
    · refine ⟨x.val - x', ?_, Or.inr ?_⟩
      · have e : 2 * 2 ^ d * (x.val - x') + 2 * 2 ^ d * x' = 2 * 2 ^ d * x.val := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hvx.le]
        nlinarith
      · rw [hdec, Int.cast_neg, Int.cast_natCast, Nat.cast_sub hvx.le, hxv, neg_sub]
  · -- Wrap-around: `c = 2^d`, so the compressed value and its decompression are `0`.
    have hceq : c = 2 ^ d := le_antisymm hca hge
    have hcval : (compress q d x).val = 0 := by
      change ((c : ℕ) : ZMod (2 ^ d)).val = 0
      rw [hceq, ZMod.natCast_self, ZMod.val_zero]
    have hdec : decompress q d (compress q d x) = 0 := by
      unfold decompress
      rw [hcval, Nat.mul_zero]
      have h0 : roundDiv 0 (2 ^ d) = 0 := by
        unfold roundDiv
        exact Nat.div_eq_of_lt (by omega)
      rw [h0, Nat.cast_zero]
    refine ⟨q - x.val, ?_, Or.inl ?_⟩
    · have e : 2 * 2 ^ d * (q - x.val) + 2 * 2 ^ d * x.val = 2 * 2 ^ d * q := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      rw [hceq] at h₁
      nlinarith
    · rw [hdec, Int.cast_natCast, Nat.cast_sub (show x.val ≤ q by omega), hxv, ZMod.natCast_self]

/-- `Decompress_1` sends the bit `0` to `0` and the bit `1` to `⌈q / 2⌋ = (q + 1) / 2`. -/
theorem decompress_one_eq (q : ℕ) (y : ZMod (2 ^ 1)) :
    decompress q 1 y = (((q + 1) / 2 * y.val : ℕ) : ZMod q) := by
  have hy : y.val < 2 := ZMod.val_lt y
  unfold decompress roundDiv
  congr 1
  change (2 * (q * y.val) + 2) / (2 * 2) = (q + 1) / 2 * y.val
  interval_cases y.val <;> omega

/-- Compression to one bit from an integer representative `t ∈ [0, q)`. -/
private theorem compress_one_of_intCast {q : ℕ} [NeZero q] (x : ZMod q) (t : ℤ) (ht0 : 0 ≤ t)
    (htq : t < q) (heq : (t : ZMod q) = x) :
    compress q 1 x = ((roundDiv (2 * t.toNat) q : ℕ) : ZMod (2 ^ 1)) := by
  unfold compress
  congr 2
  rw [← heq, pow_one]
  have : ((t : ZMod q).val : ℤ) = t := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt ht0 htq]
  omega

/-- **One-bit decoding with bounded error**: when `4 * B + 2 < q` and the centered representative
of `w` has magnitude at most `B`, `Compress_1(Decompress_1(y) + w) = y` for each bit `y`. -/
theorem compress_one_decompress_one_add {q B : ℕ} (hB : 4 * B + 2 < q) (y : ZMod (2 ^ 1))
    {w : ZMod q} (hw : w.valMinAbs.natAbs ≤ B) :
    compress q 1 (decompress q 1 y + w) = y := by
  have hq : NeZero q := ⟨by omega⟩
  have hy : y.val < 2 := ZMod.val_lt y
  have hwz : ((w.valMinAbs : ℤ) : ZMod q) = w := ZMod.coe_valMinAbs w
  have hzB : -(B : ℤ) ≤ w.valMinAbs ∧ w.valMinAbs ≤ B := by omega
  have hyv : y = ((y.val : ℕ) : ZMod (2 ^ 1)) := (ZMod.natCast_zmod_val y).symm
  have hmod : ∀ m : ℕ, ((m : ℕ) : ZMod (2 ^ 1)) = ((m % 2 : ℕ) : ZMod (2 ^ 1)) := by
    intro m
    rw [pow_one, ZMod.natCast_mod]
  rw [decompress_one_eq]
  interval_cases hv : y.val
  · -- Bit `0`: the coefficient is `w` itself.
    rw [Nat.mul_zero, Nat.cast_zero, zero_add, hyv, hmod]
    rcases le_or_gt 0 w.valMinAbs with hz0 | hz0
    · rw [compress_one_of_intCast w _ hz0 (by omega) hwz, hmod]
      congr 1
      have : roundDiv (2 * w.valMinAbs.toNat) q = 0 := by
        apply roundDiv_eq_of_le_of_lt <;> omega
      rw [this]
    · rw [compress_one_of_intCast w (w.valMinAbs + q) (by omega) (by omega)
        (by simp [hwz]), hmod]
      congr 1
      have : roundDiv (2 * (w.valMinAbs + q).toNat) q = 2 := by
        apply roundDiv_eq_of_le_of_lt <;> omega
      rw [this]
  · -- Bit `1`: the coefficient is `(q + 1) / 2 + z`, without wrap-around.
    rw [Nat.mul_one, hyv, hmod]
    have hh : 2 * ((q + 1) / 2) ≤ q + 1 ∧ q ≤ 2 * ((q + 1) / 2) := by omega
    rw [compress_one_of_intCast _ (((q + 1) / 2 : ℕ) + w.valMinAbs) (by omega) (by omega)
      (by rw [Int.cast_add, Int.cast_natCast, hwz]), hmod]
    congr 1
    have : roundDiv (2 * (((q + 1) / 2 : ℕ) + w.valMinAbs).toNat) q = 1 := by
      apply roundDiv_eq_of_le_of_lt <;> omega
    rw [this]

end Cslib.Crypto.MLKEM
