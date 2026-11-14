/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pătrașcu Power-of-Two Spillover Representation

This file formalizes the power-of-two spillover encoding of Mihai Pătrașcu, *Succincter*
([Patrascu2008, Lemma 3]), as specialized in Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei
Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Section 3.4,
Lemma 3.8 and Footnote 4]; [arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 11 /
printed p. 10).

Given a finite payload universe `Fin X` (`1 ≤ X`) and spillover parameter `r_sp ≥ 1`, we set
`M := memBits X r_sp` (`0` when `X ≤ r_sp`, and `⌊log₂(X / r_sp)⌋` otherwise) and
`K := spillUniv X r_sp := ⌈X / 2 ^ M⌉`. Because the memory-bit modulus `2 ^ M` is an exact power of
two, `encode` splits `x < X` into `(x / 2 ^ M, x % 2 ^ M) ∈ Fin K × Fin (2 ^ M)`, `decodeVal`
reconstructs `k * 2 ^ M + m` with exact round-trip identity, `K ≤ 2 * r_sp`, and the bit-redundancy
`M + log₂ K - log₂ X` is at most `2 / r_sp` bits (with multiplicative `ℕ`, `ℚ`, and `Nat.clog 2`
batch forms for `n` independent payloads at `r_sp = n`).

## Scope note

This module supplies the pure mathematical spillover primitive for the large-parameter-regime
dynamic dictionary of [LiLiangYuZhou2024, Section 5]. Word-RAM `O(1)` bit-shift and bit-mask
evaluation, variable-length adapter trees, strong history independence, dynamic resizing, and
super-polynomial key universes are not formalized here.

## Main definitions

* `Cslib.DataStructure.Dictionary.Spillover.memBits`: memory bit width `M`.
* `Cslib.DataStructure.Dictionary.Spillover.spillUniv`: spillover universe size `K = ⌈X / 2 ^ M⌉`.
* `Cslib.DataStructure.Dictionary.Spillover.encode`, `decodeVal`, `decode?`, `equiv`: spillover
  encoding, integer reconstruction, checked partial inverse, and exact subtype bijection.

## Main results

* `spillUniv_le_two_mul`, `le_spillUniv_of_le`, `lt_spillUniv_of_mul_two_pow_lt`: spillover
  universe bounds `r_sp ≤ K ≤ 2 * r_sp` (and strict `r_sp < K` when `r_sp * 2 ^ M < X`).
* `decodeVal_encode`, `encode_decodeVal`, `encode_injective`, `decode?_encode`,
  `decode?_eq_some_iff`: exact round-trip and injectivity laws.
* `mul_spillUniv_mul_two_pow_le`, `spillUniv_mul_two_pow_div_le_rat`,
  `memBits_add_logb_spillUniv_le`, `pow_spillUniv_mul_two_pow_le_three_mul`,
  `clog_mul_spillUniv_pow_add_le`: bit-redundancy bounds in `ℕ`, `ℚ`, `ℝ`, and `Nat.clog 2`.

## References

* [M. Pătrașcu, *Succincter*][Patrascu2008]
* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.Spillover

/-- Number of raw memory bits `M = ⌊log₂(X / r_sp)⌋` in the power-of-two spillover split of
`Fin X` with parameter `r_sp` (equals `0` when `X ≤ r_sp`, [LiLiangYuZhou2024, Footnote 4]). -/
@[expose]
def memBits (X r_sp : ℕ) : ℕ :=
  Nat.log 2 (X / r_sp)

/-- Spillover universe size `K = ⌈X / 2 ^ M⌉` for universe `X` and parameter `r_sp`. -/
@[expose]
def spillUniv (X r_sp : ℕ) : ℕ :=
  (X + 2 ^ memBits X r_sp - 1) / 2 ^ memBits X r_sp

@[simp]
theorem memBits_of_le {X r_sp : ℕ} (h : X ≤ r_sp) : memBits X r_sp = 0 := by
  dsimp only [memBits]
  rcases Nat.eq_zero_or_pos r_sp with rfl | hr
  · simp [Nat.le_zero.mp h]
  · have hdiv : X / r_sp ≤ 1 := Nat.div_le_of_le_mul (by omega)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdiv with h0 | h1
    · simp [h0]
    · simp [h1]

/-- `memBits X r_sp` equals `Nat.log 2 (X / r_sp)` definitionally. -/
theorem memBits_eq_log_div (X r_sp : ℕ) : memBits X r_sp = Nat.log 2 (X / r_sp) :=
  rfl

@[simp]
theorem spillUniv_of_le {X r_sp : ℕ} (h : X ≤ r_sp) : spillUniv X r_sp = X := by
  simp [spillUniv, memBits_of_le h]

/-- `K * 2 ^ M` covers `X`. -/
theorem le_spillUniv_mul_two_pow (X r_sp : ℕ) :
    X ≤ spillUniv X r_sp * 2 ^ memBits X r_sp := by
  have hP : 0 < 2 ^ memBits X r_sp := Nat.two_pow_pos _
  have hmod := Nat.div_add_mod (X + 2 ^ memBits X r_sp - 1) (2 ^ memBits X r_sp)
  have hlt : (X + 2 ^ memBits X r_sp - 1) % 2 ^ memBits X r_sp < 2 ^ memBits X r_sp :=
    Nat.mod_lt _ hP
  dsimp only [spillUniv]
  rw [Nat.mul_comm]
  omega

/-- `K * 2 ^ M` overshoots `X` by strictly less than `2 ^ M`. -/
theorem spillUniv_mul_two_pow_lt (X r_sp : ℕ) :
    spillUniv X r_sp * 2 ^ memBits X r_sp < X + 2 ^ memBits X r_sp := by
  have hP : 0 < 2 ^ memBits X r_sp := Nat.two_pow_pos _
  have hle := Nat.div_mul_le_self (X + 2 ^ memBits X r_sp - 1) (2 ^ memBits X r_sp)
  dsimp only [spillUniv]
  omega

theorem spillUniv_pos {X : ℕ} (hX : 1 ≤ X) (r_sp : ℕ) : 0 < spillUniv X r_sp := by
  by_contra h
  have h0 : spillUniv X r_sp = 0 := Nat.eq_zero_of_not_pos h
  have hle := le_spillUniv_mul_two_pow X r_sp
  rw [h0, zero_mul] at hle
  omega

theorem encode_div_lt {X : ℕ} (r_sp : ℕ) (x : Fin X) :
    x.val / 2 ^ memBits X r_sp < spillUniv X r_sp := by
  have hcov := le_spillUniv_mul_two_pow X r_sp
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact lt_of_lt_of_le x.isLt hcov)

/-- Encode `x : Fin X` into spillover index `k = x / 2 ^ M` and memory word `m = x % 2 ^ M`. -/
@[expose]
def encode {X : ℕ} (r_sp : ℕ) (x : Fin X) :
    Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp) :=
  (⟨x.val / 2 ^ memBits X r_sp, encode_div_lt r_sp x⟩,
   ⟨x.val % 2 ^ memBits X r_sp, Nat.mod_lt x.val (Nat.two_pow_pos _)⟩)

/-- Reconstruct the raw natural number `k * 2 ^ M + m` from a `(k, m)` spillover pair. -/
@[expose]
def decodeVal {X r_sp : ℕ} : Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp) → ℕ
  | (k, m) => k.val * 2 ^ memBits X r_sp + m.val

/-- Checked partial inverse of `encode`, returning `some x` when `k * 2 ^ M + m < X`. -/
@[expose]
def decode? {X : ℕ} (r_sp : ℕ)
    (km : Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp)) : Option (Fin X) :=
  if h : decodeVal km < X then some ⟨decodeVal km, h⟩ else none

@[simp]
theorem decodeVal_encode {X : ℕ} (r_sp : ℕ) (x : Fin X) :
    decodeVal (encode r_sp x) = x.val := by
  dsimp only [encode, decodeVal]
  rw [Nat.mul_comm, Nat.div_add_mod]

theorem decodeVal_injective (X r_sp : ℕ) :
    Function.Injective (decodeVal (X := X) (r_sp := r_sp)) := by
  rintro ⟨k₁, m₁⟩ ⟨k₂, m₂⟩ h
  dsimp only [decodeVal] at h
  have hdiv : k₁.val = k₂.val := by
    have h1 : (k₁.val * 2 ^ memBits X r_sp + m₁.val) / 2 ^ memBits X r_sp = k₁.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _),
        Nat.div_eq_zero_iff.mpr (.inr m₁.isLt), add_zero]
    have h2 : (k₂.val * 2 ^ memBits X r_sp + m₂.val) / 2 ^ memBits X r_sp = k₂.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _),
        Nat.div_eq_zero_iff.mpr (.inr m₂.isLt), add_zero]
    rw [← h1, ← h2, h]
  ext
  · exact hdiv
  · dsimp only
    rw [hdiv] at h
    omega

@[simp]
theorem encode_decodeVal {X r_sp : ℕ}
    (km : Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp)) (h : decodeVal km < X) :
    encode r_sp ⟨decodeVal km, h⟩ = km :=
  decodeVal_injective X r_sp (decodeVal_encode r_sp ⟨decodeVal km, h⟩)

theorem encode_injective {X : ℕ} (r_sp : ℕ) :
    Function.Injective (encode (X := X) r_sp) := fun x₁ x₂ h =>
  Fin.ext (by simpa using congrArg decodeVal h)

@[simp]
theorem decode?_encode {X : ℕ} (r_sp : ℕ) (x : Fin X) :
    decode? r_sp (encode r_sp x) = some x := by
  simp [decode?, x.isLt]

theorem decode?_eq_some_iff {X : ℕ} (r_sp : ℕ)
    (km : Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp)) (x : Fin X) :
    decode? r_sp km = some x ↔ encode r_sp x = km := by
  constructor
  · intro h
    dsimp only [decode?] at h
    split_ifs at h with hlt
    · injection h with hx
      rw [← hx]
      exact encode_decodeVal km hlt
  · rintro rfl
    exact decode?_encode r_sp x

/-- Exact bijection between `Fin X` and valid spillover pairs `{km // decodeVal km < X}`. -/
def equiv (X r_sp : ℕ) :
    Fin X ≃ { km : Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp) // decodeVal km < X } where
  toFun x := ⟨encode r_sp x, by simp [x.isLt]⟩
  invFun km := ⟨decodeVal km.1, km.2⟩
  left_inv x := Fin.ext (decodeVal_encode r_sp x)
  right_inv km := Subtype.ext (encode_decodeVal km.1 km.2)

@[simp]
theorem coe_equiv {X r_sp : ℕ} (x : Fin X) :
    (equiv X r_sp x).1 = encode r_sp x := by
  simp [equiv]

@[simp]
theorem val_equiv_symm {X r_sp : ℕ}
    (km : { km : Fin (spillUniv X r_sp) × Fin (2 ^ memBits X r_sp) // decodeVal km < X }) :
    ((equiv X r_sp).symm km).val = decodeVal km.1 := by
  simp [equiv]

/-! ### Spillover universe and bit-redundancy bounds (Lemma 3.8) -/

private theorem mul_two_pow_memBits_le {X r_sp : ℕ} (hr : r_sp ≤ X) :
    r_sp * 2 ^ memBits X r_sp ≤ X := by
  rcases Nat.eq_zero_or_pos r_sp with rfl | hr0
  · simp
  · rw [memBits_eq_log_div]
    have hpos : X / r_sp ≠ 0 := Nat.ne_of_gt (Nat.div_pos hr hr0)
    exact (Nat.mul_comm _ _).trans_le
      ((Nat.mul_le_mul_right r_sp (Nat.pow_log_le_self 2 hpos)).trans (Nat.div_mul_le_self X r_sp))

/-- When `r_sp ≤ X`, `r_sp ≤ spillUniv X r_sp`. -/
theorem le_spillUniv_of_le {X r_sp : ℕ} (hrX : r_sp ≤ X) :
    r_sp ≤ spillUniv X r_sp := by
  have h1 := mul_two_pow_memBits_le hrX
  have h2 := le_spillUniv_mul_two_pow X r_sp
  exact Nat.le_of_mul_le_mul_right (h1.trans h2) (Nat.two_pow_pos _)

/-- When `r_sp * 2 ^ M < X` (for `r_sp ≤ X`, i.e. when `X ≠ r_sp * 2 ^ M`),
`r_sp < spillUniv X r_sp`. -/
theorem lt_spillUniv_of_mul_two_pow_lt {X r_sp : ℕ} (h : r_sp * 2 ^ memBits X r_sp < X) :
    r_sp < spillUniv X r_sp := by
  have hcov := le_spillUniv_mul_two_pow X r_sp
  exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le h hcov)

/-- Upper bound `K ≤ 2 * r_sp` in Lemma 3.8. -/
theorem spillUniv_le_two_mul {X r_sp : ℕ} (hr : 1 ≤ r_sp) :
    spillUniv X r_sp ≤ 2 * r_sp := by
  by_cases hXr : X ≤ r_sp
  · rw [spillUniv_of_le hXr]; omega
  · have hlog : X / r_sp < 2 ^ (memBits X r_sp + 1) := by
      rw [memBits_eq_log_div]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two (X / r_sp)
    have hXlt : X < 2 * r_sp * 2 ^ memBits X r_sp := by
      have hdiv := Nat.div_add_mod X r_sp
      have hmod : X % r_sp < r_sp := Nat.mod_lt X hr
      rw [Nat.pow_succ'] at hlog
      nlinarith
    have hP : 0 < 2 ^ memBits X r_sp := Nat.two_pow_pos _
    dsimp only [spillUniv]
    refine Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul ?_)
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 ^ memBits X r_sp)]
    omega

/-- Exact multiplicative `ℕ` redundancy bound: `r_sp * (K * 2 ^ M) ≤ (r_sp + 1) * X`. -/
theorem mul_spillUniv_mul_two_pow_le {X r_sp : ℕ} (hr : 1 ≤ r_sp) :
    r_sp * (spillUniv X r_sp * 2 ^ memBits X r_sp) ≤ (r_sp + 1) * X := by
  by_cases hXr : X ≤ r_sp
  · rw [spillUniv_of_le hXr, memBits_of_le hXr]; nlinarith
  · have hle : r_sp * 2 ^ memBits X r_sp ≤ X := mul_two_pow_memBits_le (Nat.le_of_not_ge hXr)
    have hlt := spillUniv_mul_two_pow_lt X r_sp
    nlinarith

/-- Rational ratio form of Lemma 3.8: `(K * 2 ^ M) / X ≤ 1 + 1 / r_sp`. -/
theorem spillUniv_mul_two_pow_div_le_rat {X r_sp : ℕ} (hX : 1 ≤ X) (hr : 1 ≤ r_sp) :
    ((spillUniv X r_sp * 2 ^ memBits X r_sp : ℕ) : ℚ) / X ≤ 1 + 1 / r_sp := by
  have hX0 : (0 : ℚ) < X := by positivity
  have hr0 : (0 : ℚ) < r_sp := by positivity
  have hnat : (r_sp : ℚ) * (spillUniv X r_sp * 2 ^ memBits X r_sp : ℕ) ≤
      ((r_sp : ℚ) + 1) * X := by exact_mod_cast mul_spillUniv_mul_two_pow_le (X := X) hr
  rw [div_le_iff₀ hX0]
  have hcalc : (1 + 1 / (r_sp : ℚ)) * X * r_sp = ((r_sp : ℚ) + 1) * X := by
    field_simp
  nlinarith

/-- When `X ≤ r_sp`, the spillover representation incurs zero bit redundancy (`Footnote 4`). -/
theorem memBits_add_logb_spillUniv_eq_of_le {X r_sp : ℕ} (hXr : X ≤ r_sp) :
    (memBits X r_sp : ℝ) + Real.logb 2 (spillUniv X r_sp) = Real.logb 2 X := by
  simp [memBits_of_le hXr, spillUniv_of_le hXr]

/-- Logarithmic bit-redundancy bound (`Lemma 3.8` of Li–Liang–Yu–Zhou 2024; `Lemma 3` of
Pătrașcu 2008): `M + log₂ K ≤ log₂ X + 2 / r_sp`. -/
theorem memBits_add_logb_spillUniv_le {X r_sp : ℕ} (hX : 1 ≤ X) (hr : 1 ≤ r_sp) :
    (memBits X r_sp : ℝ) + Real.logb 2 (spillUniv X r_sp) ≤ Real.logb 2 X + 2 / (r_sp : ℝ) := by
  have hKpos : (0 : ℝ) < spillUniv X r_sp := by exact_mod_cast spillUniv_pos hX r_sp
  have hXpos : (0 : ℝ) < X := by positivity
  have hrpos : (0 : ℝ) < r_sp := by positivity
  have h2Mpos : (0 : ℝ) < (2 : ℝ) ^ memBits X r_sp := by positivity
  have hlhs : (memBits X r_sp : ℝ) + Real.logb 2 (spillUniv X r_sp) =
      Real.logb 2 ((spillUniv X r_sp : ℝ) * (2 : ℝ) ^ memBits X r_sp) := by
    rw [Real.logb_mul hKpos.ne' h2Mpos.ne', Real.logb_two_pow]
    ring
  have hprod_le : (spillUniv X r_sp : ℝ) * (2 : ℝ) ^ memBits X r_sp ≤
      X * (1 + 1 / (r_sp : ℝ)) := by
    have hnat : (r_sp : ℝ) * ((spillUniv X r_sp : ℝ) * (2 : ℝ) ^ memBits X r_sp) ≤
        ((r_sp : ℝ) + 1) * X := by exact_mod_cast mul_spillUniv_mul_two_pow_le (X := X) hr
    have hcalc : X * (1 + 1 / (r_sp : ℝ)) * r_sp = ((r_sp : ℝ) + 1) * X := by
      field_simp
    nlinarith
  have hlog1 : Real.log (1 + 1 / (r_sp : ℝ)) ≤ 1 / (r_sp : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (r_sp : ℝ))
    linarith
  have hlogb : Real.logb 2 (1 + 1 / (r_sp : ℝ)) ≤ 2 / (r_sp : ℝ) := by
    rw [Real.logb, div_le_div_iff₀ (Real.log_pos (by norm_num)) hrpos]
    have hmul : Real.log (1 + 1 / (r_sp : ℝ)) * r_sp ≤ 1 := by
      calc Real.log (1 + 1 / (r_sp : ℝ)) * r_sp
          ≤ (1 / (r_sp : ℝ)) * r_sp := mul_le_mul_of_nonneg_right hlog1 hrpos.le
        _ = 1 := one_div_mul_cancel hrpos.ne'
    linarith [Real.log_two_gt_d9]
  calc (memBits X r_sp : ℝ) + Real.logb 2 (spillUniv X r_sp)
      = Real.logb 2 ((spillUniv X r_sp : ℝ) * (2 : ℝ) ^ memBits X r_sp) := hlhs
    _ ≤ Real.logb 2 (X * (1 + 1 / (r_sp : ℝ))) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hprod_le
    _ = Real.logb 2 X + Real.logb 2 (1 + 1 / (r_sp : ℝ)) :=
        Real.logb_mul hXpos.ne' (by positivity)
    _ ≤ Real.logb 2 X + 2 / (r_sp : ℝ) := by linarith

/-- Batch `ℕ` bound across `n` payloads at spillover parameter `r_sp = n`:
`(K * 2 ^ M) ^ n ≤ 3 * X ^ n` (since `(1 + 1 / n) ^ n ≤ e < 3`). -/
theorem pow_spillUniv_mul_two_pow_le_three_mul {X n : ℕ} (hn : 1 ≤ n) :
    (spillUniv X n * 2 ^ memBits X n) ^ n ≤ 3 * X ^ n := by
  have hnR : (0 : ℝ) < n := by positivity
  have h1n : (1 + 1 / (n : ℝ)) ^ n ≤ 3 := by
    calc (1 + 1 / (n : ℝ)) ^ n
        = (1 / (n : ℝ) + 1) ^ n := by ring
      _ ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp (1 / (n : ℝ))) n
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hpow_nat : (n + 1) ^ n ≤ 3 * n ^ n := by
    have hR : ((n : ℝ) + 1) ^ n ≤ 3 * (n : ℝ) ^ n := by
      have heq : ((n : ℝ) + 1) ^ n = (1 + 1 / (n : ℝ)) ^ n * (n : ℝ) ^ n := by
        rw [← mul_pow]; congr 1; field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right h1n (by positivity)
    exact_mod_cast hR
  have hstep := Nat.pow_le_pow_left (mul_spillUniv_mul_two_pow_le (X := X) hn) n
  have hbound : n ^ n * (spillUniv X n * 2 ^ memBits X n) ^ n ≤ n ^ n * (3 * X ^ n) :=
    calc n ^ n * (spillUniv X n * 2 ^ memBits X n) ^ n
        = (n * (spillUniv X n * 2 ^ memBits X n)) ^ n := (Nat.mul_pow _ _ _).symm
      _ ≤ ((n + 1) * X) ^ n := hstep
      _ = (n + 1) ^ n * X ^ n := Nat.mul_pow _ _ _
      _ ≤ 3 * n ^ n * X ^ n := Nat.mul_le_mul_right _ hpow_nat
      _ = n ^ n * (3 * X ^ n) := by ring
  exact Nat.le_of_mul_le_mul_left hbound (Nat.pow_pos hn)

private theorem clog_two_mul_two_pow {a : ℕ} (ha : 1 ≤ a) (m : ℕ) :
    Nat.clog 2 (a * 2 ^ m) = Nat.clog 2 a + m := by
  refine le_antisymm ?_ ?_
  · rw [Nat.clog_le_iff_le_pow Nat.one_lt_two, Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog Nat.one_lt_two a)
  · rcases eq_or_lt_of_le ha with rfl | hlt
    · simp
    · have hcpos : 0 < Nat.clog 2 a := Nat.clog_pos Nat.one_lt_two hlt
      have hsub : Nat.clog 2 a - 1 + m < Nat.clog 2 (a * 2 ^ m) := by
        rw [Nat.lt_clog_iff_pow_lt Nat.one_lt_two, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right (Nat.pow_pred_clog_lt_self Nat.one_lt_two hlt)
          (Nat.two_pow_pos m)
      omega

/-- Ceiling-logarithm batch bound: combining a header factor `A ≥ 1` (such as `C(U', n)`) with `n`
spillovers of universe `K = spillUniv X n` and `n * M` memory bits adds at most `2` bits over the
exact information-theoretic ceiling `⌈log₂ (A * X ^ n)⌉`. -/
theorem clog_mul_spillUniv_pow_add_le {A X n : ℕ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hn : 1 ≤ n) :
    Nat.clog 2 (A * spillUniv X n ^ n) + n * memBits X n ≤ Nat.clog 2 (A * X ^ n) + 2 := by
  have hAK : 1 ≤ A * spillUniv X n ^ n :=
    Nat.mul_pos hA (Nat.pow_pos (spillUniv_pos hX n))
  have hAX : 1 ≤ A * X ^ n := Nat.mul_pos hA (Nat.pow_pos hX)
  rw [← clog_two_mul_two_pow hAK (n * memBits X n), ← clog_two_mul_two_pow hAX 2]
  refine Nat.clog_mono_right 2 ?_
  calc A * spillUniv X n ^ n * 2 ^ (n * memBits X n)
      = A * (spillUniv X n * 2 ^ memBits X n) ^ n := by
        rw [Nat.pow_mul', Nat.mul_assoc, ← Nat.mul_pow]
    _ ≤ A * (3 * X ^ n) := Nat.mul_le_mul_left A (pow_spillUniv_mul_two_pow_le_three_mul hn)
    _ ≤ A * X ^ n * 2 ^ 2 := by ring_nf; omega

end Cslib.DataStructure.Dictionary.Spillover
