/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.Garbling.Arithmetic.AffineLabel
public import Complexity.Languages.Probabilistic.Sharing
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic

/-!
# Bit composition for arithmetic garbling over `ℤ/p^k`

Mixed garbling schemes convert between Boolean wires and arithmetic wires over `ℤ/p^k`. Li and
Liu [LiLiu2024] write `x : ℤ/p^k` with `k` base-`p` digits and each digit with
`⌈log₂ p⌉` bits (bit decomposition `bitDecomp`); bit composition `bitComp` maps a bit array back
to `∑ i j, p ^ i * 2 ^ j * z i j`. Composition inverts decomposition (`bitComp_bitDecomp`), and is
`ℤ/p^k`-linear in the bits, which is what makes it cheap to garble.

The gadget for a public linear function `z ↦ ∑ i, c i * z i` of bits (`linCompTable`,
`linCompEval`) gives the evaluator the affine label of the output under key `∑ i, b i` and
slope `s`. For each input bit `i` and each row `ρ : Bool` (the point-and-permute colour, encoding
the bit `ρ xor α i` for the wire's permutation bit `α i`), the garbler publishes
`(c i * β) • s + b i + pad i β` with `β = ρ xor α i`, where `pad i β` is the one-time pad that
the label of bit `β` on wire `i` unlocks (a random-oracle output in [LiLiu2024]). The evaluator
holding the labels of `z` reads the row of colour `z i xor α i` of each table, removes the pad it
can compute, and adds the results (`linCompEval_linCompTable`).

What the evaluator sees once the pads are removed are the values `(c i * z i) • s + b i`. When the
key `b` is a uniform additive sharing of the output key, these values are a uniform additive
sharing of the output label; they reveal nothing about `z` beyond the output label
(`eval_activeShares`). Hiding the inactive rows is the job of the pads and is not formalized here.

## Main definitions

* `Cslib.Crypto.Garbling.Arithmetic.digit`: the base-`b` digits of a natural number.
* `Cslib.Crypto.Garbling.Arithmetic.bitDecomp`, `Cslib.Crypto.Garbling.Arithmetic.bitComp`:
  bit decomposition and bit composition over `ℤ/p^k`.
* `Cslib.Crypto.Garbling.Arithmetic.linCompTable`,
  `Cslib.Crypto.Garbling.Arithmetic.linCompEval`: the linear bit-composition gadget.
* `Cslib.Crypto.Garbling.Arithmetic.activeShares`: the unpadded active rows.

## Main results

* `Cslib.Crypto.Garbling.Arithmetic.sum_digit_mul_pow`: `∑ i < k, b ^ i * digit b x i =
  x % b ^ k`.
* `Cslib.Crypto.Garbling.Arithmetic.bitComp_bitDecomp`: composition inverts decomposition.
* `Cslib.Crypto.Garbling.Arithmetic.linCompEval_linCompTable`: correctness of the gadget.
* `Cslib.Crypto.Garbling.Arithmetic.eval_activeShares`: the active rows are a uniform sharing of
  the output label.

## References

* [H. Li, T. Liu, *How to Garble Mixed Circuits that Combine Boolean and Arithmetic
  Computations*][LiLiu2024]
-/

public section

namespace Cslib.Crypto.Garbling.Arithmetic

open Probability

/-! ### Digits and bits -/

/-- The `i`-th base-`b` digit of `x`, least significant first. -/
@[expose] def digit (b x i : ℕ) : ℕ := x / b ^ i % b

theorem digit_lt {b : ℕ} (hb : 0 < b) (x i : ℕ) : digit b x i < b := Nat.mod_lt _ hb

/-- The first `k` base-`b` digits of `x` recover `x` modulo `b ^ k`. -/
theorem sum_digit_mul_pow (b x k : ℕ) :
    ∑ i ∈ Finset.range k, b ^ i * digit b x i = x % b ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, digit, Nat.mod_pow_succ]

/-- The bit `j` of `x` is its base-`2` digit `j`. -/
theorem toNat_testBit_eq_digit (x j : ℕ) : (x.testBit j).toNat = digit 2 x j := by
  rw [digit, Nat.toNat_testBit]

/-- The number of bits of a base-`p` digit: `⌈log₂ p⌉`. -/
@[expose] def digitWidth (p : ℕ) : ℕ := Nat.clog 2 p

theorem lt_two_pow_digitWidth {p x : ℕ} (hx : x < p) : x < 2 ^ digitWidth p :=
  hx.trans_le (Nat.le_pow_clog one_lt_two p)

/-- The bits of a base-`p` digit `x < p` recover it. -/
theorem sum_testBit_mul_pow {p x : ℕ} (hx : x < p) :
    ∑ j : Fin (digitWidth p), 2 ^ (j : ℕ) * (x.testBit j).toNat = x := by
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ j * (x.testBit j).toNat)]
  simp only [toNat_testBit_eq_digit]
  rw [sum_digit_mul_pow, Nat.mod_eq_of_lt (lt_two_pow_digitWidth hx)]

variable {p k : ℕ}

/-- **Bit decomposition** over `ℤ/p^k`: bit `j` of base-`p` digit `i` of `x`. -/
@[expose] def bitDecomp (p k : ℕ) (x : ZMod (p ^ k)) : Fin k → Fin (digitWidth p) → Bool :=
  fun i j => (digit p x.val i).testBit j

/-- **Bit composition** over `ℤ/p^k`: `∑ i j, p ^ i * 2 ^ j * z i j`. It is defined for every bit
array, including those whose digits are not below `p`. -/
@[expose] def bitComp (p k : ℕ) (z : Fin k → Fin (digitWidth p) → Bool) : ZMod (p ^ k) :=
  ∑ i : Fin k, ∑ j : Fin (digitWidth p), ((p ^ (i : ℕ) * 2 ^ (j : ℕ) * (z i j).toNat : ℕ) :
    ZMod (p ^ k))

/-- **Composition inverts decomposition** on `ℤ/p^k`. -/
theorem bitComp_bitDecomp [NeZero p] (x : ZMod (p ^ k)) : bitComp p k (bitDecomp p k x) = x := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdigit (i : Fin k) :
      ∑ j : Fin (digitWidth p), p ^ (i : ℕ) * 2 ^ (j : ℕ) * ((digit p x.val i).testBit j).toNat =
        p ^ (i : ℕ) * digit p x.val i := by
    simp only [mul_assoc, ← Finset.mul_sum, sum_testBit_mul_pow (digit_lt hp x.val i)]
  simp only [bitComp, bitDecomp, ← Nat.cast_sum, hdigit]
  rw [Fin.sum_univ_eq_sum_range (fun i => p ^ i * digit p x.val i), sum_digit_mul_pow,
    Nat.mod_eq_of_lt (ZMod.val_lt x), ZMod.natCast_zmod_val]

/-! ### The linear bit-composition gadget -/

variable {R ι σ : Type} [CommRing R]

/-- The garbled tables for the linear function with coefficients `c`, target slope `s`, key
shares `b` and permutation bits `α`: row `ρ` of table `i` holds `(c i * β) • s + b i + pad i β`
for the bit `β = ρ xor α i` it encodes. -/
@[expose] def linCompTable (c : σ → R) (s : ι → R) (b : σ → ι → R) (α : σ → Bool)
    (pad : σ → Bool → ι → R) : σ → Bool → ι → R :=
  fun i ρ => (c i * (ρ ^^ α i).toNat) • s + b i + pad i (ρ ^^ α i)

variable [Fintype σ]

/-- The evaluator, holding for each wire `i` its colour `colour i` and the pad `pad i` that its
label unlocks: the sum of the unpadded rows named by the colours. -/
@[expose] def linCompEval (tbl : σ → Bool → ι → R) (colour : σ → Bool) (pad : σ → ι → R) : ι → R :=
  ∑ i, (tbl i (colour i) - pad i)

/-- **Correctness**: the evaluator holding the labels of `z`, with colours `z i xor α i` and pads
`pad i (z i)`, obtains the affine label of `∑ i, c i * z i` under key `∑ i, b i`. -/
theorem linCompEval_linCompTable (c : σ → R) (s : ι → R) (b : σ → ι → R) (α : σ → Bool)
    (pad : σ → Bool → ι → R) (z : σ → Bool) :
    linCompEval (linCompTable c s b α pad) (fun i => z i ^^ α i) (fun i => pad i (z i)) =
      affineLabel (∑ i, b i) s (∑ i, c i * (z i).toNat) := by
  simp only [linCompEval, linCompTable, Bool.xor_assoc, Bool.xor_self, Bool.xor_false,
    add_sub_cancel_right, Finset.sum_add_distrib, affineLabel, Finset.sum_smul]
  exact add_comm _ _

/-- The unpadded active rows: what the evaluator learns from the tables on input `z`. -/
@[expose] def activeShares (c : σ → R) (s : ι → R) (z : σ → Bool) (b : σ → ι → R) : σ → ι → R :=
  fun i => (c i * (z i).toNat) • s + b i

/-- The active rows add up to the output label. -/
theorem sum_activeShares (c : σ → R) (s : ι → R) (z : σ → Bool) (b : σ → ι → R) :
    ∑ i, activeShares c s z b i = affineLabel (∑ i, b i) s (∑ i, c i * (z i).toNat) := by
  simp only [activeShares, Finset.sum_add_distrib, affineLabel, Finset.sum_smul]
  exact add_comm _ _

variable [Fintype R] [Fintype ι] [DecidableEq ι]

/-- **Perfect privacy of the active rows**: if the key shares `b` are a uniform additive sharing
of the output key `key`, the active rows on input `z` are a uniform additive sharing of the output
label; their distribution depends on `z` only through `∑ i, c i * z i`. -/
theorem eval_activeShares {m : ℕ} [NeZero m] (c : Fin m → R) (s : ι → R) (z : Fin m → Bool)
    (key : ι → R) :
    (do
      let b ← ProbComp.sampleAdditiveShares m key
      return activeShares c s z b : ProbComp (Fin m → ι → R)).eval =
      (ProbComp.sampleAdditiveShares m (affineLabel key s (∑ i, c i * (z i).toNat))).eval := by
  set v : Fin m → ι → R := fun i => (c i * (z i).toNat) • s
  have hshift : (fun b => activeShares c s z b) = fun b => v + b := rfl
  apply ProbComp.eq_eval_sampleAdditiveShares_of_sum_of_map_init
  · intro t ht
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    rw [sum_activeShares, ProbComp.sum_sampleAdditiveShares key hb]
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.sampleAdditiveShares,
      ProbComp.eval_map, ProbComp.eval_uniform, hshift]
    have hcomp : (ProbComp.initOfShares m ∘ fun b => v + b) ∘ ProbComp.completeShares m key =
        Equiv.addLeft (ProbComp.initOfShares m v) := by
      funext init
      simp only [Function.comp_apply, Equiv.coe_addLeft]
      funext k
      simp [ProbComp.initOfShares]
    change PMF.map _ ((PMF.map _ _).bind (PMF.pure ∘ fun b => v + b)) = _
    rw [PMF.bind_pure_comp, PMF.map_comp, PMF.map_comp]
    rw [hcomp, PMF.uniformOfFintype_map_equiv]

end Cslib.Crypto.Garbling.Arithmetic
