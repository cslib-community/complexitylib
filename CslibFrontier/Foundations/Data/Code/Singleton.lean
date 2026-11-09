/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The Singleton bound

Two distinct codewords of a code of minimum distance at least `d` differ on at least `d`
coordinates, so they already differ on any set `S` of coordinates that leaves out fewer than `d`
of them: the codewords are determined by their letters on `S`
(`Cslib.Code.injOn_restrict_of_card_lt_add`). Taking `n - d + 1` coordinates, a code of length `n`
and minimum distance at least `d` over an alphabet of `q` letters has at most `q ^ (n - d + 1)`
codewords: the **Singleton bound** (`Cslib.Code.card_le_pow_of_le_minDist`) [Singleton1964],
[GuruswamiRudraSudan2019]. For a nonzero linear code over a field the same restriction is an
injective linear map, so the dimension `k` satisfies `k + d ≤ n + 1`
(`Cslib.Code.finrank_add_le_card_add_one`). Codes meeting this bound, such as Reed–Solomon codes,
are *maximum distance separable*.

## Main results

* `Cslib.Code.injOn_restrict_of_card_lt_add`: codewords are determined by any `n - d + 1`
  coordinates.
* `Cslib.Code.card_le_pow_of_le_minDist`: the Singleton bound.
* `Cslib.Code.finrank_add_le_card_add_one`: the Singleton bound for linear codes.

## References

* [R. C. Singleton, *Maximum distance q-nary codes*][Singleton1964]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset

section Restrict

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, DecidableEq (β i)]

/-- The codewords of a code of minimum distance at least `d` are determined by their letters on any
set `S` of coordinates that leaves out fewer than `d` coordinates. -/
theorem injOn_restrict_of_card_lt_add {C : Set (∀ i, β i)} {d : ℕ} (hd : (d : ℕ∞) ≤ minDist C)
    {S : Finset ι} (hS : Fintype.card ι < #S + d) : C.InjOn S.restrict := by
  classical
  intro x hx y hy hxy
  by_contra hne
  -- the codewords differ only outside `S`
  have hsub : ({i | x i ≠ y i} : Finset ι) ⊆ univ \ S := fun i hi =>
    mem_sdiff.2 ⟨mem_univ i, fun hiS => (mem_filter.1 hi).2 (congrFun hxy ⟨i, hiS⟩)⟩
  have hdist : hammingDist x y ≤ Fintype.card ι - #S :=
    (card_le_card hsub).trans_eq (card_univ_sdiff S)
  have := Nat.cast_le.1 (le_minDist_iff.1 hd x hx y hy hne)
  have := card_le_univ S
  omega

end Restrict

variable {ι : Type*} [Fintype ι]

/-- **The Singleton bound** [Singleton1964]: a code of length `n` and minimum distance at least `d`
over an alphabet of `q` letters has at most `q ^ (n - d + 1)` codewords. -/
theorem card_le_pow_of_le_minDist {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {C : Finset (ι → α)} {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) :
    #C ≤ Fintype.card α ^ (Fintype.card ι - d + 1) := by
  classical
  have hq : 0 < Fintype.card α := Fintype.card_pos
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · calc #C ≤ Fintype.card (ι → α) := card_le_univ C
      _ = Fintype.card α ^ Fintype.card ι := Fintype.card_fun
      _ ≤ _ := Nat.pow_le_pow_right hq (by omega)
  -- restrict to `min n (n - d + 1)` coordinates
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset ι))
    (n := min (Fintype.card ι) (Fintype.card ι - d + 1)) (by rw [card_univ]; exact min_le_left _ _)
  have hinj := injOn_restrict_of_card_lt_add hd (S := S) (by omega)
  calc #C = #(C.image S.restrict) := (card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (S → α) := card_le_univ _
    _ = Fintype.card α ^ #S := by rw [Fintype.card_fun, Fintype.card_coe]
    _ ≤ _ := Nat.pow_le_pow_right hq (by omega)

/-- **The Singleton bound for linear codes**: a nonzero linear code of length `n` over a field,
with dimension `k` and minimum distance at least `d`, satisfies `k + d ≤ n + 1`. -/
theorem finrank_add_le_card_add_one {F : Type*} [Field F] [DecidableEq F]
    {C : Submodule F (ι → F)} (hC : C ≠ ⊥) {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → F))) :
    Module.finrank F C + d ≤ Fintype.card ι + 1 := by
  -- a nonzero codeword has weight at most `n`, so `d ≤ n`
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
  have hdn : d ≤ Fintype.card ι :=
    (Nat.cast_le.1 (hd.trans (minDist_le_hammingDist hx C.zero_mem hx0))).trans
      hammingDist_le_card_fintype
  have hC' := Submodule.finrank_le C
  rw [Module.finrank_fintype_fun_eq_card] at hC'
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · omega
  -- restrict to `n - d + 1` coordinates
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset ι))
    (n := Fintype.card ι - d + 1) (by rw [card_univ]; omega)
  have hinj := injOn_restrict_of_card_lt_add hd (S := S) (by omega)
  let f : C →ₗ[F] S → F := (LinearMap.funLeft F F ((↑) : S → ι)).comp C.subtype
  have hf : Function.Injective f := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  omega

end Cslib.Code
