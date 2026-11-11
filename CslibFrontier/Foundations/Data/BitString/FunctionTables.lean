/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.Fintype.RestrictInjective
import Mathlib.Data.Fintype.BigOperators

/-!
# Truth tables read from a random string

A family of Boolean functions `f v : BooleanFunction (ℓ v)`, one for each `v : Fin n`, can be read
from a string of bits laid out in blocks of width `B`: the table of `f v` occupies the bits
`v * B + equivFin y` for the inputs `y` of `f v`, numbered by `BitString.equivFin`
(`BitString.decodeTables`). Positions past the end of the string read `false`, so every list
decodes to some family.

When every table fits in its block (`2 ^ ℓ v ≤ B`) and the blocks fit in the string (`n * B ≤ p`),
decoding a uniformly random string of `p` bits gives a uniformly random family: each family is
decoded from exactly `2 ^ p / 2 ^ (∑ v, 2 ^ ℓ v)` strings. In counting form, a set `S` of families
is hit by `#S * 2 ^ p / 2 ^ (∑ v, 2 ^ ℓ v)` strings (`BitString.card_filter_decodeTables_mem_mul`).
This turns a count of bad families into a count of bad random strings, which is what a randomized
reduction that samples functions from its random bits needs.

The proof is the library's count of functions by a property of their restriction along an
injection (`Nat.card_subtype_comp_injective_mul`), applied to the positions of the tables
(`BitString.tablePos`).

## Main definitions

* `Cslib.BitString.decodeTables`: the family of truth tables read from a list of bits.
* `Cslib.BitString.tablePos`: the position of an entry of a table in the block layout.

## Main results

* `Cslib.BitString.card_functionTables`: there are `2 ^ (∑ v, 2 ^ ℓ v)` families of tables.
* `Cslib.BitString.card_filter_decodeTables_mem_mul`: decoding a random string hits a set of
  families in proportion to its size.
* `Cslib.BitString.mul_card_filter_decodeTables_mem_le`: the same as an inequality: rare families
  are decoded from rare strings.
-/

public section

namespace Cslib.BitString

open Finset

variable {n : ℕ}

/-- **Truth tables read from a list of bits**, in blocks of width `B`: the table of `v` is read
from the bits `v * B + equivFin y`, for the inputs `y` of `v`'s function in the order
`BitString.equivFin`. Missing bits read `false`, so every list decodes. -/
def decodeTables (B : ℕ) (ℓ : Fin n → ℕ) (r : List Bool) : (v : Fin n) → BooleanFunction (ℓ v) :=
  fun v y => r.getD (v * B + equivFin (ℓ v) y) false

/-- Entry `y` of the table of `v` is bit `v * B + equivFin y` of the list, or `false` past its
end. -/
@[simp]
theorem decodeTables_apply (B : ℕ) (ℓ : Fin n → ℕ) (r : List Bool) (v : Fin n)
    (y : BitString (ℓ v)) : decodeTables B ℓ r v y = r.getD (v * B + equivFin (ℓ v) y) false := by
  simp only [decodeTables]

/-- Two numbers written as `q * B + r` with `r < B` agree only when both parts do. -/
private theorem eq_of_mul_add_eq {B q q' r r' : ℕ} (hr : r < B) (hr' : r' < B)
    (h : q * B + r = q' * B + r') : q = q' ∧ r = r' := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hr
  obtain ⟨hd, hm⟩ := (Nat.div_mod_unique hB (a := q * B + r) (d := q) (c := r)).2 ⟨by ring, hr⟩
  obtain ⟨hd', hm'⟩ :=
    (Nat.div_mod_unique hB (a := q * B + r) (d := q') (c := r')).2 ⟨by rw [h]; ring, hr'⟩
  exact ⟨hd.symm.trans hd', hm.symm.trans hm'⟩

/-- **The position of a table entry** in the block layout of `decodeTables`: entry `y` of the table
of `v` is bit `v * B + equivFin y` of a string of `p` bits. -/
def tablePos {B p : ℕ} {ℓ : Fin n → ℕ} (hℓ : ∀ v, 2 ^ ℓ v ≤ B) (hp : n * B ≤ p) :
    (Σ v : Fin n, BitString (ℓ v)) ↪ Fin p where
  toFun x := ⟨x.1 * B + equivFin (ℓ x.1) x.2, by
    have hy := (equivFin (ℓ x.1) x.2).isLt
    have hv : (x.1 : ℕ) * B + B ≤ n * B := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right B x.1.isLt
    have := hℓ x.1
    omega⟩
  inj' := by
    rintro ⟨v, y⟩ ⟨v', y'⟩ h
    simp only [Fin.mk.injEq] at h
    obtain ⟨hv, hy⟩ := eq_of_mul_add_eq ((equivFin (ℓ v) y).isLt.trans_le (hℓ v))
      ((equivFin (ℓ v') y').isLt.trans_le (hℓ v')) h
    obtain rfl : v = v' := Fin.ext hv
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact (equivFin (ℓ v)).injective (Fin.ext hy)

/-- Entry `y` of the table of `v` sits at position `v * B + equivFin y`. -/
@[simp]
theorem tablePos_apply {B p : ℕ} {ℓ : Fin n → ℕ} (hℓ : ∀ v, 2 ^ ℓ v ≤ B) (hp : n * B ≤ p)
    (x : Σ v : Fin n, BitString (ℓ v)) :
    (tablePos hℓ hp x : ℕ) = x.1 * B + equivFin (ℓ x.1) x.2 := by
  simp only [tablePos]
  rfl

/-- Decoding the bits of a string of length `p` reads them at the positions `tablePos`. -/
theorem decodeTables_ofFn {B p : ℕ} {ℓ : Fin n → ℕ} (hℓ : ∀ v, 2 ^ ℓ v ≤ B) (hp : n * B ≤ p)
    (r : Fin p → Bool) :
    decodeTables B ℓ (List.ofFn r) = Equiv.piCurry (fun v (_ : BitString (ℓ v)) => Bool)
      (r ∘ tablePos hℓ hp) := by
  funext v y
  have hlt := (tablePos hℓ hp ⟨v, y⟩).isLt
  rw [tablePos_apply] at hlt
  simp only [decodeTables_apply, List.getD_eq_getElem?_getD, List.length_ofFn, hlt, getElem?_pos,
    List.getElem_ofFn, Option.getD_some, Equiv.piCurry_apply, Sigma.curry, Function.comp_apply]
  rfl

/-- There are `2 ^ (∑ v, 2 ^ ℓ v)` families of truth tables. -/
theorem card_functionTables (ℓ : Fin n → ℕ) :
    Fintype.card ((v : Fin n) → BooleanFunction (ℓ v)) = 2 ^ (∑ v, 2 ^ ℓ v) := by
  simp [Fintype.card_pi, Finset.prod_pow_eq_pow_sum]

/-- **Decoding a random string hits a set of families in proportion to its size.** If every table
fits in a block of width `B` and the `n` blocks fit in `p` bits, the strings `r` of `p` bits whose
decoding lies in `S` are a `#S / 2 ^ (∑ v, 2 ^ ℓ v)` fraction of all `2 ^ p` strings. -/
theorem card_filter_decodeTables_mem_mul {B p : ℕ} {ℓ : Fin n → ℕ} (hℓ : ∀ v, 2 ^ ℓ v ≤ B)
    (hp : n * B ≤ p) (S : Finset ((v : Fin n) → BooleanFunction (ℓ v))) :
    #{r : Fin p → Bool | decodeTables B ℓ (List.ofFn r) ∈ S} * 2 ^ (∑ v, 2 ^ ℓ v) =
      #S * 2 ^ p := by
  classical
  let c := Equiv.piCurry fun v (_ : BitString (ℓ v)) => Bool
  have key := Nat.card_subtype_comp_injective_mul (tablePos hℓ hp) (tablePos hℓ hp).injective
    (· ∈ S.map c.symm.toEmbedding)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, filter_univ_mem, card_map,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_sigma] at key
  rw [← key]
  congr 2
  ext r
  simp only [mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.symm_symm,
    decodeTables_ofFn hℓ hp, c]

/-- **Rare families are decoded from rare strings.** If at most a `b / a` fraction of the
families lie in `S`, then at most a `b / a` fraction of the strings of `p` bits decode into `S`. -/
theorem mul_card_filter_decodeTables_mem_le {B p a b : ℕ} {ℓ : Fin n → ℕ}
    (hℓ : ∀ v, 2 ^ ℓ v ≤ B) (hp : n * B ≤ p) {S : Finset ((v : Fin n) → BooleanFunction (ℓ v))}
    (hS : a * #S ≤ b * Fintype.card ((v : Fin n) → BooleanFunction (ℓ v))) :
    a * #{r : Fin p → Bool | decodeTables B ℓ (List.ofFn r) ∈ S} ≤ b * 2 ^ p := by
  rw [card_functionTables] at hS
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos (∑ v, 2 ^ ℓ v))
  calc a * #{r : Fin p → Bool | decodeTables B ℓ (List.ofFn r) ∈ S} * 2 ^ (∑ v, 2 ^ ℓ v)
      = a * #S * 2 ^ p := by rw [mul_assoc, card_filter_decodeTables_mem_mul hℓ hp, mul_assoc]
    _ ≤ b * 2 ^ (∑ v, 2 ^ ℓ v) * 2 ^ p := Nat.mul_le_mul_right _ hS
    _ = b * 2 ^ p * 2 ^ (∑ v, 2 ^ ℓ v) := by ring

end Cslib.BitString
