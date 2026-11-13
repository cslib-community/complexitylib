/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.ZMod.Basic

/-!
# One-hot vectors and truth-table products

The algebra behind the lookup-table garbling of Heath, Kolesnikov and Ng [HeathKolesnikovNg2024].
A lookup table with rows indexed by `ι` and outputs indexed by `κ` is a truth table
`T : ι → κ → Bool`. Multiplying its transpose by the one-hot vector of an index `x` selects row
`x` (`tableMulBits_oneHot`, [HeathKolesnikovNg2024], Lemma 1, a fact credited there to
[HeathKolesnikov2021]).

With Free-XOR labels [KolesnikovSchneider2008] the label of bit `b` on a wire with zero-label
`G` is `G + bitOffset Δ b` for a global offset `Δ`. The labelled product `tableMul T X` sums, for
each output `u`, the labels `X j` of the rows with `T j u = true`. It is additive in the labels,
and in characteristic two it commutes with offsets (`tableMul_bitOffset`). Consequently, if the
evaluator holds Free-XOR labels of the one-hot vector of `x`, the product of its labels is a
Free-XOR label of row `x`, whose zero-label is the product of the zero-labels
(`tableMul_oneHotLabels`, the display after Lemma 1 of [HeathKolesnikovNg2024]). Only one row
carries the offset, so this form holds in every additive commutative group.

## Main definitions

* `Cslib.Crypto.Garbling.bitOffset`: the multiple of the global offset selected by a bit.
* `Cslib.Crypto.Garbling.oneHot`: the one-hot vector of an index.
* `Cslib.Crypto.Garbling.tableMulBits`, `Cslib.Crypto.Garbling.tableMul`: transposed
  truth-table products on bits and on labels.

## Main results

* `Cslib.Crypto.Garbling.tableMulBits_oneHot`: the product with a one-hot vector selects a row.
* `Cslib.Crypto.Garbling.tableMul_bitOffset`: Free-XOR linearity of the labelled product.
* `Cslib.Crypto.Garbling.tableMul_oneHotLabels`: one-hot labels give labels of the selected row.

## References

* [D. Heath, V. Kolesnikov, *One Hot Garbling*][HeathKolesnikov2021]
* [D. Heath, V. Kolesnikov, L. K. L. Ng, *Garbled Circuit Lookup Tables with Logarithmic Number
  of Ciphertexts*][HeathKolesnikovNg2024]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

variable {ι κ L : Type}

/-- The multiple of the global offset selected by a bit: `Δ` for `true` and `0` for `false`.
With Free-XOR, the label of bit `b` on a wire with zero-label `G` is `G + bitOffset Δ b`. -/
def bitOffset [Zero L] (Δ : L) (b : Bool) : L := if b then Δ else 0

@[simp] theorem bitOffset_true [Zero L] (Δ : L) : bitOffset Δ true = Δ := rfl

@[simp] theorem bitOffset_false [Zero L] (Δ : L) : bitOffset Δ false = 0 := rfl

/-- For an element `Δ` of order at most two, the offset selected by a sum of bits is the sum of
the offsets. -/
theorem bitOffset_add_of_add_self [AddCommMonoid L] {Δ : L} (hΔ : Δ + Δ = 0) (a b : Bool) :
    bitOffset Δ (a + b) = bitOffset Δ a + bitOffset Δ b := by
  cases a <;> cases b
  · exact (add_zero _).symm
  · exact (zero_add _).symm
  · exact (add_zero _).symm
  · exact hΔ.symm

/-- In characteristic two, the offset selected by a sum of bits is the sum of the offsets. -/
theorem bitOffset_add [AddCommGroup L] [Module (ZMod 2) L] (Δ : L) (a b : Bool) :
    bitOffset Δ (a + b) = bitOffset Δ a + bitOffset Δ b :=
  bitOffset_add_of_add_self (ZModModule.add_self Δ) a b

/-- In characteristic two, `bitOffset Δ` is an additive map from `Bool` with `+ = xor`. -/
def bitOffsetHom [AddCommGroup L] [Module (ZMod 2) L] (Δ : L) : Bool →+ L where
  toFun := bitOffset Δ
  map_zero' := rfl
  map_add' := bitOffset_add Δ

/-- The one-hot vector of `x`: `true` exactly at `x`. -/
def oneHot [DecidableEq ι] (x : ι) : ι → Bool := fun j => decide (j = x)

@[simp] theorem oneHot_self [DecidableEq ι] (x : ι) : oneHot x x = true := decide_eq_true rfl

theorem oneHot_of_ne [DecidableEq ι] {x j : ι} (h : j ≠ x) : oneHot x j = false :=
  decide_eq_false h

/-- Transposed truth-table product on bits: output `u` is the sum over GF(2) of `v j && T j u`.
On a one-hot vector it reads one row of `T`. -/
def tableMulBits [Fintype ι] (T : ι → κ → Bool) (v : ι → Bool) : κ → Bool :=
  fun u => ∑ j, (v j && T j u)

/-- Transposed truth-table product on labels: output `u` is the sum of the labels `X j` over the
rows `j` with `T j u = true`. -/
def tableMul [Fintype ι] [AddCommMonoid L] (T : ι → κ → Bool) (X : ι → L) : κ → L :=
  fun u => ∑ j, if T j u then X j else 0

/-- **One-hot selection** ([HeathKolesnikovNg2024], Lemma 1): the transposed truth table times the
one-hot vector of `x` is row `x`. -/
theorem tableMulBits_oneHot [Fintype ι] [DecidableEq ι] (T : ι → κ → Bool) (x : ι) :
    tableMulBits T (oneHot x) = T x := by
  funext u
  simp only [tableMulBits]
  rw [Finset.sum_eq_single x (fun j _ hj => by rw [oneHot_of_ne hj]; rfl)
    (fun h => absurd (Finset.mem_univ x) h), oneHot_self, Bool.true_and]

/-- The labelled product is additive in the labels. -/
theorem tableMul_add [Fintype ι] [AddCommMonoid L] (T : ι → κ → Bool) (X Y : ι → L) :
    tableMul T (X + Y) = tableMul T X + tableMul T Y := by
  funext u
  simp only [tableMul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · exact (add_zero 0).symm

/-- **Free-XOR linearity**: in characteristic two, the product of a table with the offsets of a
bit vector `v` is the offset of the product of the table with `v`. -/
theorem tableMul_bitOffset [Fintype ι] [AddCommGroup L] [Module (ZMod 2) L] (T : ι → κ → Bool)
    (Δ : L) (v : ι → Bool) :
    tableMul T (fun j => bitOffset Δ (v j)) = fun u => bitOffset Δ (tableMulBits T v u) := by
  funext u
  change _ = bitOffsetHom Δ (∑ j, (v j && T j u))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (if T j u then bitOffset Δ (v j) else 0) = bitOffset Δ (v j && T j u)
  cases T j u <;> cases v j <;> rfl

/-- **One-hot selection on labels** (the display after Lemma 1 of [HeathKolesnikovNg2024]). If the
evaluator holds Free-XOR labels of the one-hot vector of `x` with zero-labels `G`, then output `u`
of the product of its labels is the label of bit `T x u` with zero-label `tableMul T G u`. -/
theorem tableMul_oneHotLabels [Fintype ι] [DecidableEq ι] [AddCommGroup L] (T : ι → κ → Bool)
    (G : ι → L) (Δ : L) (x : ι) :
    tableMul T (fun j => G j + bitOffset Δ (oneHot x j)) =
      fun u => tableMul T G u + bitOffset Δ (T x u) := by
  have hsplit : (fun j => G j + bitOffset Δ (oneHot x j)) =
      G + fun j => bitOffset Δ (oneHot x j) := rfl
  rw [hsplit, tableMul_add]
  funext u
  refine congrArg (tableMul T G u + ·) ?_
  simp only [tableMul]
  rw [Finset.sum_eq_single x (fun j _ hj => by rw [oneHot_of_ne hj, bitOffset_false, ite_self])
    (fun h => absurd (Finset.mem_univ x) h), oneHot_self, bitOffset_true]
  cases T x u <;> rfl

end Cslib.Crypto.Garbling
