/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Reed–Solomon designs

A *design* with parameters `m` and `a` is a family of sets of size `m` whose pairwise
intersections have size at most `a` (`Cslib.IsDesign`), as in the generator of Nisan and Wigderson
[NisanWigderson1994]. The family may be indexed by any type and its sets may lie in any type;
`Cslib.Crypto.PRG.NisanWigderson.Design` is the same notion bundled for families indexed by
`Fin m` of subsets of `Fin ℓ`.

For a prime `q`, a number of points `m ≤ q` and a degree bound `k`, the graphs of the polynomials
of degree less than `k` over `ZMod q`, restricted to the first `m` points, form a design
(`Cslib.rsDesign`): the graph of a polynomial `p` is `{(a, p(a)) : a < m}`, of size `m`, and two
distinct polynomials of degree less than `k` agree at no more than `k - 1` points. A polynomial of
degree less than `k` is given by its `k` coefficients, so the family is indexed by
`Fin k → ZMod q` and has `q ^ k` sets (`ZMod.card`), all inside a set of `m * q` points.

## Main definitions

* `Cslib.IsDesign`: sets of a fixed size with pairwise intersections of bounded size.
* `Cslib.rsDesign`: the graphs of the polynomials of degree less than `k` over `ZMod q`.

## Main results

* `Cslib.isDesign_rsDesign`: for a prime `q` and `m ≤ q`, the graphs form a design with sets of
  size `m` and intersections of size at most `k - 1`.

## References

* [N. Nisan, A. Wigderson, *Hardness vs Randomness*][NisanWigderson1994]: designs, and their
  construction from the graphs of polynomials of low degree
-/

@[expose] public section

namespace Cslib

open Finset Polynomial

/-- A *design* with parameters `m` and `a`: every set `S i` has `m` elements, and two distinct
sets share at most `a` elements. -/
def IsDesign {ι α : Type*} [DecidableEq α] (S : ι → Finset α) (m a : ℕ) : Prop :=
  (∀ i, #(S i) = m) ∧ ∀ i j, i ≠ j → #(S i ∩ S j) ≤ a

/-- The **Reed–Solomon design**: the graph `{(a, p(a)) : a < m}` of the polynomial `p` over
`ZMod q` with coefficients `c`, of degree less than `k`, restricted to the first `m` points. The
family is indexed by the `q ^ k` coefficient vectors `c : Fin k → ZMod q`. -/
noncomputable def rsDesign (q m k : ℕ) (c : Fin k → ZMod q) : Finset (Fin m × ZMod q) :=
  univ.map ⟨fun a : Fin m => (a, (ofFn k c).eval ((a : ℕ) : ZMod q)),
    fun _ _ h => (Prod.ext_iff.1 h).1⟩

/-- **The Reed–Solomon design is a design**: for a prime `q` and `m ≤ q`, the graphs over the
first `m` points of the polynomials of degree less than `k` over `ZMod q` have `m` elements, and
two of them share at most `k - 1` elements, since two distinct polynomials of degree less than `k`
agree at no more than `k - 1` points. -/
theorem isDesign_rsDesign {q m k : ℕ} [Fact q.Prime] (hm : m ≤ q) :
    IsDesign (rsDesign q m k) m (k - 1) := by
  refine ⟨fun c => by rw [rsDesign, card_map, card_univ, Fintype.card_fin], fun c c' hne => ?_⟩
  -- The points at which the two polynomials agree.
  set D : Finset (Fin m) :=
    {a | (ofFn k c).eval ((a : ℕ) : ZMod q) = (ofFn k c').eval ((a : ℕ) : ZMod q)}
  have hsub : rsDesign q m k c ∩ rsDesign q m k c' ⊆
      D.image fun a => (a, (ofFn k c).eval ((a : ℕ) : ZMod q)) := by
    intro x hx
    obtain ⟨hx, hx'⟩ := mem_inter.1 hx
    obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    obtain ⟨a', -, h⟩ := mem_map.1 hx'
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    exact mem_image.2 ⟨a', mem_filter.2 ⟨mem_univ _, h.symm⟩, rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  by_contra hlt
  have hinj : Function.Injective fun a : Fin m => ((a : ℕ) : ZMod q) := fun a b h => by
    have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
    rw [Nat.mod_eq_of_lt (a.2.trans_le hm), Nat.mod_eq_of_lt (b.2.trans_le hm)] at h'
    exact Fin.ext h'
  -- The difference of the two polynomials has at least `k` roots.
  have hzero : ofFn k (c - c') = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (s := D.image fun a : Fin m => ((a : ℕ) : ZMod q)) ((ofFn_degree_lt _).trans_le ?_)
      fun x hx => ?_
    · rw [card_image_of_injective _ hinj]
      exact_mod_cast (by omega : k ≤ #D)
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      rw [map_sub, eval_sub, (mem_filter.1 ha).2, sub_self]
  exact hne (sub_eq_zero.1 (injective_ofFn k (hzero.trans (ofFn_zero k).symm)))

end Cslib
