/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Affine
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Affine dispersers

A Boolean function `f` on `n` bits is an *affine disperser for dimension `d`* when it is
nonconstant on the image of every injective affine map from `BitString d`
(`Cslib.BitString.IsAffineDisperser`), informally on every affine subspace of dimension `d`.
Dispersers for dimension `d` are dispersers for every larger dimension
(`Cslib.BitString.IsAffineDisperser.mono`), and no function is a disperser for dimension `0`
(`Cslib.BitString.not_isAffineDisperser_zero`).

Affine dispersers exist for every dimension `d` with `n (d + 1) + 1 < 2 ^ d`
(`Cslib.BitString.exists_isAffineDisperser`), for instance for `n = 100` and `d = 11`. There are at
most `2 ^ (n (d + 1))` affine maps from `BitString d` to `BitString n`
(`Cslib.BitString.card_isAffine_le`), and at most `2 · 2 ^ (2 ^ n - 2 ^ d)` functions are constant
on the image of each injective one (`Cslib.BitString.card_const_on_range_le`); together these are
fewer than the `2 ^ 2 ^ n` functions on `n` bits.

## Main definitions

* `Cslib.BitString.IsAffineDisperser`: affine dispersers for dimension `d`.

## Main results

* `Cslib.BitString.IsAffineDisperser.mono`: dispersers for smaller dimension are dispersers for
  larger dimension.
* `Cslib.BitString.not_isAffineDisperser_zero`: no function is an affine disperser for dimension
  `0`.
* `Cslib.BitString.exists_isAffineDisperser`: affine dispersers exist for every dimension `d`
  with `n (d + 1) + 1 < 2 ^ d`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- `f` is an affine disperser for dimension `d`: it is nonconstant on the image of every
injective affine map from `BitString d`. By `Cslib.BitString.IsAffine.finrank_direction_map_top`
each such image is an affine subspace of dimension `d`, so nonconstancy on `d`-dimensional affine
subspaces suffices (`Cslib.BitString.isAffineDisperser_of_forall_exists_ne`). -/
def IsAffineDisperser {n : ℕ} (f : BitString n → Bool) (d : ℕ) : Prop :=
  ∀ g : BitString d → BitString n, IsAffine g → Function.Injective g → ∃ x y, f (g x) ≠ f (g y)

/-- Dispersers for dimension `d` are dispersers for every larger dimension. -/
theorem IsAffineDisperser.mono {n d d' : ℕ} {f : BitString n → Bool}
    (hf : IsAffineDisperser f d) (h : d ≤ d') : IsAffineDisperser f d' := by
  intro g hg hinj
  obtain ⟨x, y, hxy⟩ := hf (g ∘ zeroExtend) (hg.comp isAffine_zeroExtend)
    (hinj.comp (zeroExtend_injective h))
  exact ⟨_, _, hxy⟩

/-- No function is an affine disperser for dimension `0`: it is constant on every point. -/
theorem not_isAffineDisperser_zero {n : ℕ} (f : BitString n → Bool) :
    ¬ IsAffineDisperser f 0 := by
  intro hf
  obtain ⟨x, y, hxy⟩ := hf (fun _ => 0) (isAffine_const (β := BitString n)
    (fun b => funext fun i => BooleanRing.add_self (b i)) 0)
    (fun x y _ => Subsingleton.elim x y)
  exact hxy rfl

/-- At most `2 · 2 ^ (2 ^ n - 2 ^ d)` functions on `n` bits are constant on the image of an
injective map from `BitString d`. -/
theorem card_const_on_range_le {d n : ℕ} {g : BitString d → BitString n}
    (hg : Function.Injective g) :
    (univ.filter fun f : BitString n → Bool => ∀ x y, f (g x) = f (g y)).card ≤
      2 * 2 ^ (2 ^ n - 2 ^ d) := by
  classical
  calc _ ≤ (univ : Finset (Bool × ({p // p ∉ Set.range g} → Bool))).card :=
        card_le_card_of_injOn (fun f => (f (g 0), fun p => f p.1)) (fun _ _ => mem_univ _)
          fun f hf f' hf' h => by
            simp only [Prod.mk.injEq] at h
            funext p
            by_cases hp : p ∈ Set.range g
            · obtain ⟨x, rfl⟩ := hp
              rw [(mem_filter.1 hf).2 x 0, (mem_filter.1 hf').2 x 0, h.1]
            · exact congrFun h.2 ⟨p, hp⟩
    _ = 2 * 2 ^ (2 ^ n - 2 ^ d) := by
      rw [card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Set.card_range_of_injective hg]
      simp

/-- **Affine dispersers exist** for every dimension `d` with `n (d + 1) + 1 < 2 ^ d`: fewer
functions on `n` bits are constant on the image of some injective affine map from `BitString d`
than there are functions. -/
theorem exists_isAffineDisperser {n d : ℕ} (h : n * (d + 1) + 1 < 2 ^ d) :
    ∃ f : BitString n → Bool, IsAffineDisperser f d := by
  classical
  by_contra hno
  push Not at hno
  set A := univ.filter fun g : BitString d → BitString n => IsAffine g ∧ Function.Injective g
  have hsub : (univ : Finset (BitString n → Bool)) ⊆
      A.biUnion fun g => univ.filter fun f => ∀ x y, f (g x) = f (g y) := by
    intro f _
    have := hno f
    unfold IsAffineDisperser at this
    push Not at this
    obtain ⟨g, hg, hinj, hconst⟩ := this
    exact mem_biUnion.2 ⟨g, mem_filter.2 ⟨mem_univ _, hg, hinj⟩, mem_filter.2 ⟨mem_univ _, hconst⟩⟩
  have hcard := (card_le_card hsub).trans (card_biUnion_le_card_mul A _ (2 * 2 ^ (2 ^ n - 2 ^ d))
    fun g hg => card_const_on_range_le (mem_filter.1 hg).2.2)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hcard
  rcases A.eq_empty_or_nonempty with hA | ⟨g, hg⟩
  · rw [hA, card_empty, zero_mul] at hcard
    exact absurd hcard (Nat.not_le.2 (Nat.two_pow_pos _))
  · have hdn : 2 ^ d ≤ 2 ^ n := by
      have := Fintype.card_le_of_injective g (mem_filter.1 hg).2.2
      simpa [Fintype.card_fun] using this
    have hA : A.card ≤ 2 ^ (n * (d + 1)) := (card_le_card fun g hg =>
      mem_filter.2 ⟨mem_univ _, (mem_filter.1 hg).2.1⟩).trans (card_isAffine_le d n)
    have hlt : A.card * (2 * 2 ^ (2 ^ n - 2 ^ d)) < 2 ^ 2 ^ n :=
      calc A.card * (2 * 2 ^ (2 ^ n - 2 ^ d)) ≤ 2 ^ (n * (d + 1)) * (2 * 2 ^ (2 ^ n - 2 ^ d)) :=
            Nat.mul_le_mul_right _ hA
        _ = 2 ^ (n * (d + 1) + 1 + (2 ^ n - 2 ^ d)) := by rw [pow_add, pow_add, pow_one]; ring
        _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Cslib.BitString
