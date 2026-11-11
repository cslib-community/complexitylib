/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Design
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Foundations.Data.BitString.Parity.SubsetSum
import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# The bit-indexed polynomial design

Carmosino, Impagliazzo, Kabanets and Kolokolova's AC⁰[p] construction of Nisan–Wigderson designs
(Def 3.4, Lemma 3.5, §3.1 and the proof of Theorem 3.6, pp. 10:10–10:12)
[CarmosinoImpagliazzoKabanetsKolokolova2016] indexes the blocks by bit strings. The string
`i : BitString ℓ` names the polynomial `A_i(x) = ∑_t i_t x^t` with coefficients `0` and `1`
(`Cslib.Crypto.PRG.NisanWigderson.bitPoly`). The universe is split into `n` rows, each a copy of
the field `F`. Block `i` takes, from row `j`, the cell in the column numbered by `A_i(r_j)`, for
fixed distinct points `r_j ∈ F`. Distinct strings give distinct polynomials of degree less than `ℓ`,
which agree at fewer than `ℓ` points, so two blocks share at most `ℓ - 1` cells. The cells are
numbered row-major, so the bits of a seed in block `i`, in increasing order of position, are read
row by row (`Cslib.Crypto.PRG.NisanWigderson.Design.restrict_bitPolynomial`).

Unlike `Cslib.Crypto.PRG.NisanWigderson.Design.polynomial`, which numbers points and blocks in some
unspecified order, every numbering here is explicit. That is what lets a circuit compute the design.
Over a field of characteristic two with an additive encoding by bits, each bit of `A_i(r_j)` is a
parity of the bits of `i` over a set fixed by `r_j`
(`Cslib.Crypto.PRG.NisanWigderson.bits_bitPoly_eq_parityOn`); this is the linear map of the proof of
Theorem 3.6, which uses the hard-coded matrix `r_j ^ t`.

The instance `Cslib.Crypto.PRG.NisanWigderson.Design.binaryPolynomial n ℓ` uses the explicit binary
field `Cslib.BinaryField e` with `e = binaryFieldDegree n = max 1 ⌈log₂ n⌉`. So `n ≤ 2 ^ e ≤ 2 n`
(`Cslib.Crypto.PRG.NisanWigderson.le_two_pow_binaryFieldDegree`,
`Cslib.Crypto.PRG.NisanWigderson.two_pow_binaryFieldDegree_le`), and the points `r_j` are the field
elements numbered `j < n`. Its seed has `n · 2 ^ e ≤ 2 n²` bits
(`Cslib.Crypto.PRG.NisanWigderson.Design.seedLength_binaryPolynomial_le`).

This differs from the source in these ways:

* only characteristic two is built (the field is `BinaryField e`, with `n ≤ |F| ≤ 2 n`);
* the universe has `n · |F| ≤ 2 n²` cells, not `n²`;
* two blocks share at most `ℓ - 1` cells (the source states `ℓ`);
* block `i` is numbered by `BitString.equivFin`, least significant bit first.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.bitPoly`: the polynomial with the bits of `i` as coefficients,
  evaluated at `x`.
* `Cslib.Crypto.PRG.NisanWigderson.bitPolyBlock`: block `i`, one cell per row.
* `Cslib.Crypto.PRG.NisanWigderson.Design.bitPolynomial`: the bit-indexed polynomial design for
  given points `r : Fin n ↪ F` and column numbering `num : F ≃ Fin q`.
* `Cslib.Crypto.PRG.NisanWigderson.binaryFieldDegree`: `max 1 ⌈log₂ n⌉`.
* `Cslib.Crypto.PRG.NisanWigderson.binaryFieldNum`,
  `Cslib.Crypto.PRG.NisanWigderson.binaryFieldPoints`: the numbering of `BinaryField e` by bits
  and the points numbered `0, …, n - 1`.
* `Cslib.Crypto.PRG.NisanWigderson.Design.binaryPolynomial`: the instance over
  `BinaryField (binaryFieldDegree n)`.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.mem_bitPolyBlock`: the cells of block `i`.
* `Cslib.Crypto.PRG.NisanWigderson.card_bitPolyBlock_inter_le`: distinct blocks share at most
  `ℓ - 1` cells.
* `Cslib.Crypto.PRG.NisanWigderson.Design.restrict_bitPolynomial`: the bits of a seed in block `i`,
  row by row.
* `Cslib.Crypto.PRG.NisanWigderson.bits_bitPoly_eq_parityOn`: each bit of `A_i(r)` is a parity of
  `i`.
* `Cslib.Crypto.PRG.NisanWigderson.Design.binaryPolynomial_eq`: the binary instance unfolded, so
  that the general results apply to it.
* `Cslib.Crypto.PRG.NisanWigderson.Design.restrict_binaryPolynomial`: the reading for the binary
  instance, with each column given by the bits of its number.
* `Cslib.Crypto.PRG.NisanWigderson.Design.seedLength_binaryPolynomial_le`: the seed has at most
  `2 n²` bits.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016], Def 3.4, Lemma 3.5, §3.1, Theorem 3.6
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset

variable {F : Type*} [Field F] {ℓ n q : ℕ}

/-- The polynomial `A_i(x) = ∑_t i_t x ^ t` whose coefficients are the bits of `i`, evaluated at
`x` [CarmosinoImpagliazzoKabanetsKolokolova2016, proof of Theorem 3.6]. -/
@[expose] def bitPoly (i : BitString ℓ) (x : F) : F :=
  ∑ t, if i t then x ^ (t : ℕ) else 0

/-- `bitPoly i` is the polynomial of `polynomialBlock` with coefficients `1` where `i` is true and
`0` elsewhere. -/
theorem bitPoly_eq_sum_mul (i : BitString ℓ) (x : F) :
    bitPoly i x = ∑ t, (if i t then 1 else 0) * x ^ (t : ℕ) := by
  simp only [bitPoly, ite_mul, one_mul, zero_mul]

/-- The coefficients `1` where `i` is true and `0` elsewhere determine `i`. -/
private theorem bitCoeff_injective :
    Function.Injective fun (i : BitString ℓ) (t : Fin ℓ) => (if i t then 1 else 0 : F) := by
  intro i i' h
  funext t
  have := congrFun h t
  cases hi : i t <;> cases hi' : i' t <;> simp_all

/-- **Each bit of `A_i(x)` is a parity of `i`.** For an additive encoding of `F` by bits, bit `c`
of `bitPoly i x` is the parity of `i` on the exponents `t` for which bit `c` of `x ^ t` is set. In
a circuit this is one parity gate per bit, with the set fixed by `x`
[CarmosinoImpagliazzoKabanetsKolokolova2016, proof of Theorem 3.6]. -/
theorem bits_bitPoly_eq_parityOn {e : ℕ} (bits : F ≃+ BitString e) (i : BitString ℓ) (x : F)
    (c : Fin e) : bits (bitPoly i x) c = parityOn {t : Fin ℓ | bits (x ^ (t : ℕ)) c = true} i :=
  BitString.map_sum_ite_eq_parityOn ((Pi.evalAddMonoidHom _ c).comp bits.toAddMonoidHom) _ i

section Design

variable (r : Fin n → F) (num : F ≃ Fin q)

/-- Distinct rows give distinct cells: the cell of row `j` in block `i` is `(j, num (A_i(r_j)))`,
numbered row-major. -/
private theorem bitPolyCell_injective (i : BitString ℓ) :
    Function.Injective fun j : Fin n => finProdFinEquiv (j, num (bitPoly i (r j))) :=
  fun _ _ h => congrArg Prod.fst (finProdFinEquiv.injective h)

/-- Block `i` of the bit-indexed polynomial design: from each row `j < n`, the cell in the column
numbered by `A_i(r_j)`. Cells are numbered row-major, so `(j, v)` is cell `v + q j`. -/
def bitPolyBlock (i : BitString ℓ) : Finset (Fin (n * q)) :=
  univ.map ⟨_, bitPolyCell_injective r num i⟩

variable {r num}

/-- A cell `(j, v)` lies in block `i` when its column `v` is the number of `A_i(r_j)`. -/
theorem mem_bitPolyBlock {i : BitString ℓ} {p : Fin (n * q)} :
    p ∈ bitPolyBlock r num i ↔
      (finProdFinEquiv.symm p).2 = num (bitPoly i (r (finProdFinEquiv.symm p).1)) := by
  simp only [bitPolyBlock, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, rfl⟩
    simp
  · intro h
    exact ⟨_, by rw [← h, Prod.mk.eta, Equiv.apply_symm_apply]⟩

/-- Each block has one cell in each of the `n` rows. -/
@[simp]
theorem card_bitPolyBlock (i : BitString ℓ) : #(bitPolyBlock r num i) = n := by
  rw [bitPolyBlock, card_map, card_univ, Fintype.card_fin]

/-- **Distinct blocks share at most `ℓ - 1` cells**, for distinct points `r_j`. A shared cell in
row `j` is a point `r_j` where the two polynomials agree. The polynomials are distinct and of
degree less than `ℓ`, so this holds for at most `ℓ - 1` points (`card_polynomialBlock_inter_le`)
[CarmosinoImpagliazzoKabanetsKolokolova2016, Lemma 3.5]. -/
theorem card_bitPolyBlock_inter_le (hr : Function.Injective r) {i i' : BitString ℓ}
    (h : i ≠ i') : #(bitPolyBlock r num i ∩ bitPolyBlock r num i') ≤ ℓ - 1 := by
  classical
  have := Fintype.ofEquiv _ num.symm
  refine le_trans ?_ (card_polynomialBlock_inter_le (F := F) (bitCoeff_injective.ne h))
  refine card_le_card_of_injOn
    (fun p => (r (finProdFinEquiv.symm p).1, num.symm (finProdFinEquiv.symm p).2))
    (fun p hp => ?_) (fun p hp p' hp' hpp' => ?_)
  · rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe, mem_bitPolyBlock, mem_bitPolyBlock] at hp
    rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe, mem_polynomialBlock, mem_polynomialBlock]
    dsimp only
    rw [← bitPoly_eq_sum_mul, ← bitPoly_eq_sum_mul, hp.1, Equiv.symm_apply_apply]
    exact ⟨rfl, num.injective (hp.1.symm.trans hp.2)⟩
  · simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hpp'
    exact finProdFinEquiv.symm.injective (Prod.ext (hr hpp'.1) hpp'.2)

/-- **The bit-indexed polynomial design**
[CarmosinoImpagliazzoKabanetsKolokolova2016, §3.1 and the proof of Theorem 3.6]: an
`(n q, n, ℓ - 1)`-design with `2 ^ ℓ` blocks. Block `i < 2 ^ ℓ` is `bitPolyBlock r num` of the bit
string numbered `i` by `BitString.equivFin` (least significant bit first). -/
def Design.bitPolynomial (ℓ : ℕ) (r : Fin n ↪ F) (num : F ≃ Fin q) :
    Design (n * q) n (ℓ - 1) (2 ^ ℓ) where
  block i := bitPolyBlock r num ((BitString.equivFin ℓ).symm i)
  card_block _ := card_bitPolyBlock _
  card_inter_le h :=
    card_bitPolyBlock_inter_le r.injective ((BitString.equivFin ℓ).symm.injective.ne h)

variable {r : Fin n ↪ F}

/-- Block `i` of `Design.bitPolynomial` is `bitPolyBlock` of the bit string numbered `i`. -/
theorem Design.block_bitPolynomial (i : Fin (2 ^ ℓ)) :
    (Design.bitPolynomial ℓ r num).block i =
      bitPolyBlock r num ((BitString.equivFin ℓ).symm i) := by
  unfold Design.bitPolynomial
  rfl

/-- **Reading a seed in block `i`**: its bit in row `j` is the seed's bit in that row, in the column
numbered by `A_i(r_j)`. The cells are numbered row-major, so increasing position is increasing row.
-/
theorem Design.restrict_bitPolynomial {α : Type*} (i : Fin (2 ^ ℓ)) (z : Fin (n * q) → α)
    (j : Fin n) :
    (Design.bitPolynomial ℓ r num).restrict i z j =
      z (finProdFinEquiv (j, num (bitPoly ((BitString.equivFin ℓ).symm i) (r j)))) := by
  set f : Fin n → Fin (n * q) :=
    fun j => finProdFinEquiv (j, num (bitPoly ((BitString.equivFin ℓ).symm i) (r j)))
  have hmono : StrictMono f := by
    intro j j' hjj'
    simp only [f, Fin.lt_def, finProdFinEquiv_apply_val]
    have hq := (num (bitPoly ((BitString.equivFin ℓ).symm i) (r j))).isLt
    have hjj : q * (j : ℕ) + q ≤ q * j' := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left q hjj'
    omega
  have hmem (j : Fin n) : f j ∈ (Design.bitPolynomial ℓ r num).block i := by
    rw [Design.block_bitPolynomial, bitPolyBlock, mem_map]
    exact ⟨j, mem_univ _, rfl⟩
  rw [Design.restrict_apply, ← orderEmbOfFin_unique _ hmem hmono]

end Design

/-! ### The instance over the explicit binary field -/

/-- The degree `e = max 1 ⌈log₂ n⌉` of the binary field for `n` rows: the least positive `e` with
`n ≤ 2 ^ e`. -/
def binaryFieldDegree (n : ℕ) : ℕ :=
  max 1 (Nat.clog 2 n)

theorem binaryFieldDegree_ne_zero (n : ℕ) : binaryFieldDegree n ≠ 0 :=
  (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

/-- The field has at least `n` elements. -/
theorem le_two_pow_binaryFieldDegree (n : ℕ) : n ≤ 2 ^ binaryFieldDegree n :=
  (Nat.le_pow_clog one_lt_two n).trans (Nat.pow_le_pow_right two_pos (le_max_right _ _))

/-- The field has at most `2 n` elements, for `n ≥ 1`. -/
theorem two_pow_binaryFieldDegree_le (hn : 1 ≤ n) : 2 ^ binaryFieldDegree n ≤ 2 * n := by
  rcases hn.eq_or_lt with rfl | hn
  · simp [binaryFieldDegree, Nat.clog_one_right]
  rw [binaryFieldDegree, max_eq_right (Nat.clog_pos one_lt_two hn)]
  exact Nat.pow_clog_le_mul one_lt_two (by omega)

/-- The degree is at most `n`, for `n ≥ 1`. -/
theorem binaryFieldDegree_le_self (hn : 1 ≤ n) : binaryFieldDegree n ≤ n :=
  max_le hn (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)

/-- The numbering `BinaryField e ≃ Fin (2 ^ e)` of the field elements by their bits, least
significant first. -/
noncomputable def binaryFieldNum {e : ℕ} (he : e ≠ 0) : BinaryField e ≃ Fin (2 ^ e) :=
  (BinaryField.equivBits he).toEquiv.trans (BitString.equivFin e)

/-- The points `r_j`, `j < n`: the elements of `BinaryField (binaryFieldDegree n)` numbered `j`. -/
noncomputable def binaryFieldPoints (n : ℕ) : Fin n ↪ BinaryField (binaryFieldDegree n) :=
  (Fin.castLEEmb (le_two_pow_binaryFieldDegree n)).trans
    (binaryFieldNum (binaryFieldDegree_ne_zero n)).symm.toEmbedding

/-- **The bit-indexed polynomial design over the explicit binary field**
[CarmosinoImpagliazzoKabanetsKolokolova2016, §3.1]: an
`(n 2 ^ e, n, ℓ - 1)`-design with `2 ^ ℓ` blocks, `e = binaryFieldDegree n`. Its points are the
field elements numbered `0, …, n - 1`, and its columns are numbered by the bits of the field
elements. -/
noncomputable def Design.binaryPolynomial (n ℓ : ℕ) :
    Design (n * 2 ^ binaryFieldDegree n) n (ℓ - 1) (2 ^ ℓ) :=
  .bitPolynomial ℓ (binaryFieldPoints n) (binaryFieldNum (binaryFieldDegree_ne_zero n))

/-- The binary instance is the bit-indexed polynomial design at its points and column numbering. -/
theorem Design.binaryPolynomial_eq (n ℓ : ℕ) :
    Design.binaryPolynomial n ℓ =
      .bitPolynomial ℓ (binaryFieldPoints n) (binaryFieldNum (binaryFieldDegree_ne_zero n)) := by
  unfold Design.binaryPolynomial
  rfl

/-- **Reading a seed in block `i` of the binary instance.** Row `j` contributes the cell whose
column `v` has the bits of `A_i(r_j)`. Bit `c` of `A_i(r_j)` is the parity of `i` on the exponents
`t` with bit `c` of `r_j ^ t` set (`bits_bitPoly_eq_parityOn`). So the bit is the seed bit of the
unique column `v` that has, for every `c`, bit `c` equal to that parity. -/
theorem Design.restrict_binaryPolynomial {α : Type*} (i : BitString ℓ)
    (z : Fin (n * 2 ^ binaryFieldDegree n) → α) (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n))
    (hv : ∀ c, (BitString.equivFin _).symm v c =
      parityOn {t : Fin ℓ | BinaryField.equivBits (binaryFieldDegree_ne_zero n)
        (binaryFieldPoints n j ^ (t : ℕ)) c = true} i) :
    (Design.binaryPolynomial n ℓ).restrict (BitString.equivFin ℓ i) z j =
      z (finProdFinEquiv (j, v)) := by
  rw [Design.binaryPolynomial, Design.restrict_bitPolynomial, Equiv.symm_apply_apply]
  congr 3
  rw [← (BitString.equivFin _).apply_symm_apply v, binaryFieldNum, Equiv.trans_apply]
  congr 1
  funext c
  rw [hv, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, bits_bitPoly_eq_parityOn]

/-- **The seed of the binary instance has at most `2 n²` bits.** -/
theorem Design.seedLength_binaryPolynomial_le (n : ℕ) :
    n * 2 ^ binaryFieldDegree n ≤ 2 * n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc n * 2 ^ binaryFieldDegree n ≤ n * (2 * n) :=
        Nat.mul_le_mul_left n (two_pow_binaryFieldDegree_le hn)
    _ = 2 * n ^ 2 := by ring

end Cslib.Crypto.PRG.NisanWigderson
