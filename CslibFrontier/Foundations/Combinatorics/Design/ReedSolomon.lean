/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Reed–Solomon designs

A *design* with parameters `m` and `a` is a family of sets of size `m` whose pairwise
intersections have size at most `a` (`Cslib.IsDesign`), as in the generator of Nisan and Wigderson
[NisanWigderson1994]. The family may be indexed by any type and its sets may lie in any type;
`Cslib.Crypto.PRG.NisanWigderson.Design` is the same notion bundled for families indexed by
`Fin m` of subsets of `Fin ℓ`.

Over a finite field `F`, the graphs of two distinct polynomials of degree less than `k`
(`Cslib.polynomialBlock`) share at most `k - 1` points (`Cslib.card_polynomialBlock_inter_le`),
since their difference has at most `k - 1` roots; these graphs are the blocks of the
Nisan–Wigderson design `Cslib.Crypto.PRG.NisanWigderson.Design.polynomial`.

For a prime `q`, a number of points `m ≤ q` and a degree bound `k`, the graphs of the polynomials
of degree less than `k` over `ZMod q`, restricted to the first `m` points, form a design
(`Cslib.rsDesign`): the graph of a polynomial `p` is `{(a, p(a)) : a < m}`, of size `m`, and it
lies inside `polynomialBlock` through the embedding of `Fin m` in `ZMod q`. A polynomial of
degree less than `k` is given by its `k` coefficients, so the family is indexed by
`Fin k → ZMod q` and has `q ^ k` sets (`ZMod.card`), all inside a set of `m * q` points.

## Main definitions

* `Cslib.IsDesign`: sets of a fixed size with pairwise intersections of bounded size.
* `Cslib.polynomialBlock`: the graph of a polynomial over a finite field, given by its
  coefficients.
* `Cslib.rsDesign`: the graphs of the polynomials of degree less than `k` over `ZMod q`.

## Main results

* `Cslib.card_polynomialBlock_inter_le`: the graphs of two distinct polynomials of degree less
  than `k` share at most `k - 1` points.
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

section Polynomial

variable (F : Type*) [Field F] [Fintype F] (k : ℕ)

/-- The graph `{(x, c₀ + c₁ x + ⋯ + cₖ₋₁ x ^ (k - 1)) | x ∈ F}` of the polynomial over `F` with
coefficients `c : Fin k → F`, a block of the Nisan–Wigderson design `Design.polynomial F k`. -/
def polynomialBlock (c : Fin k → F) : Finset (F × F) :=
  univ.map ⟨fun x => (x, ∑ i, c i * x ^ (i : ℕ)), fun _ _ h => congrArg Prod.fst h⟩

variable {F k}

@[simp]
theorem mem_polynomialBlock {c : Fin k → F} {p : F × F} :
    p ∈ polynomialBlock F k c ↔ p.2 = ∑ i, c i * p.1 ^ (i : ℕ) := by
  rw [polynomialBlock, mem_map]
  constructor
  · rintro ⟨x, -, rfl⟩
    rfl
  · exact fun h => ⟨p.1, mem_univ _, Prod.ext rfl h.symm⟩

/-- The graph of a polynomial over `F` has one point above each `x ∈ F`. -/
@[simp]
theorem card_polynomialBlock (c : Fin k → F) : #(polynomialBlock F k c) = Fintype.card F := by
  rw [polynomialBlock, card_map, card_univ]

variable [DecidableEq F]

/-- The graphs of two distinct polynomials over `F` of degree less than `k` share at most `k - 1`
points: the difference of the polynomials is nonzero and has degree less than `k`, so it has at most
`k - 1` roots [NisanWigderson1994]. -/
theorem card_polynomialBlock_inter_le {c d : Fin k → F} (hcd : c ≠ d) :
    #(polynomialBlock F k c ∩ polynomialBlock F k d) ≤ k - 1 := by
  have heval (c : Fin k → F) (x : F) :
      ((degreeLTEquiv F k).symm c : F[X]).eval x = ∑ i, c i * x ^ (i : ℕ) := by
    rw [eval_eq_sum_degreeLTEquiv ((degreeLTEquiv F k).symm c).2, Subtype.coe_eta,
      LinearEquiv.apply_symm_apply]
  set P : F[X] := ↑((degreeLTEquiv F k).symm c)
  set Q : F[X] := ↑((degreeLTEquiv F k).symm d)
  set s : Finset F := {x | P.eval x = Q.eval x}
  have hs : #(polynomialBlock F k c ∩ polynomialBlock F k d) ≤ #s := by
    refine card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp p' hp' h => ?_)
    · rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe, mem_polynomialBlock,
        mem_polynomialBlock] at hp
      rw [mem_coe, mem_filter, heval, heval, ← hp.1, ← hp.2]
      exact ⟨mem_univ _, rfl⟩
    · rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe, mem_polynomialBlock] at hp hp'
      exact Prod.ext h (by rw [hp.1, hp'.1, h])
  refine hs.trans (Nat.le_sub_one_of_lt (lt_of_not_ge fun hks => hcd ?_))
  refine (degreeLTEquiv F k).symm.injective (Subtype.ext ?_)
  refine eq_of_degree_sub_lt_of_eval_finset_eq s ?_ fun x hx => (mem_filter.1 hx).2
  refine (mem_degreeLT.1 (Submodule.sub_mem _ (Subtype.prop _) (Subtype.prop _))).trans_le ?_
  exact_mod_cast hks

end Polynomial

/-- The **Reed–Solomon design**: the graph `{(a, p(a)) : a < m}` of the polynomial `p` over
`ZMod q` with coefficients `c`, of degree less than `k`, restricted to the first `m` points. The
family is indexed by the `q ^ k` coefficient vectors `c : Fin k → ZMod q`. -/
noncomputable def rsDesign (q m k : ℕ) (c : Fin k → ZMod q) : Finset (Fin m × ZMod q) :=
  univ.map ⟨fun a : Fin m => (a, ∑ i, c i * ((a : ℕ) : ZMod q) ^ (i : ℕ)),
    fun _ _ h => (Prod.ext_iff.1 h).1⟩

/-- **The Reed–Solomon design is a design**: for a prime `q` and `m ≤ q`, the graphs over the
first `m` points of the polynomials of degree less than `k` over `ZMod q` have `m` elements, and
two of them share at most `k - 1` elements, by `card_polynomialBlock_inter_le` through the
embedding of `Fin m` in `ZMod q`. -/
theorem isDesign_rsDesign {q m k : ℕ} [Fact q.Prime] (hm : m ≤ q) :
    IsDesign (rsDesign q m k) m (k - 1) := by
  refine ⟨fun c => by rw [rsDesign, card_map, card_univ, Fintype.card_fin], fun c c' hne => ?_⟩
  set φ : Fin m × ZMod q → ZMod q × ZMod q := fun x => (((x.1 : ℕ) : ZMod q), x.2) with hφ
  have hinj : Set.InjOn φ ↑(rsDesign q m k c ∩ rsDesign q m k c') := by
    rintro ⟨a, b⟩ - ⟨a', b'⟩ - h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
    rw [Nat.mod_eq_of_lt (a.2.trans_le hm), Nat.mod_eq_of_lt (a'.2.trans_le hm)] at h'
    exact Prod.ext (Fin.ext h') h2
  have hmaps : ∀ c'' : Fin k → ZMod q, ∀ x ∈ rsDesign q m k c'',
      φ x ∈ polynomialBlock (ZMod q) k c'' := fun c'' x hx => by
    obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    exact mem_polynomialBlock.2 rfl
  refine (card_le_card_of_injOn φ (fun x hx => ?_) hinj).trans (card_polynomialBlock_inter_le hne)
  rw [mem_coe, mem_inter] at hx ⊢
  exact ⟨hmaps c x hx.1, hmaps c' x hx.2⟩

end Cslib
