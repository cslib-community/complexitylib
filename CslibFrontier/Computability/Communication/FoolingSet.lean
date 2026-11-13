/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Rectangle

/-!
# Fooling sets

A *fooling set* for `f : X → Y → Z` with value `z` is a finite set `S` of pairs of inputs on which
`f` is `z`, such that for any two distinct pairs `(x₁, y₁)` and `(x₂, y₂)` of `S`, `f x₁ y₂ ≠ z`
or `f x₂ y₁ ≠ z` (`IsFoolingSet`) [Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]. A
rectangle on which `f` is constantly `z` contains at most one pair of `S`. So a protocol computing
`f` has at least `|S|` leaves labelled `z` (`IsFoolingSet.card_le`), and at least one leaf more
when `f` takes another value somewhere: then `|S| < 2 ^ d` for every protocol sending `d` bits
(`IsFoolingSet.card_lt_two_pow`). In particular a fooling set of `2 ^ n` pairs for a function that
is not constantly `z` forces `n + 1` bits (`IsFoolingSet.succ_le_ecomplexity`).

## Main definitions

* `Cslib.Communication.IsFoolingSet`: fooling sets.

## Main results

* `Cslib.Communication.IsFoolingSet.card_le_tilingNumber`: the arbitrary tiling bound.
* `Cslib.Communication.IsFoolingSet.card_le`: a fooling set for value `z` is at most the number
  of leaves labelled `z`.
* `Cslib.Communication.IsFoolingSet.card_lt_two_pow`: the fooling-set bound.
* `Cslib.Communication.IsFoolingSet.succ_le_ecomplexity`: the fooling-set bound on communication
  complexity.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X Y Z : Type*}

/-- A *fooling set* for `f` with value `z`: a finite set `S` of pairs of inputs on which `f` is
`z`, such that two pairs `(x₁, y₁)` and `(x₂, y₂)` of `S` with `f x₁ y₂ = z` and `f x₂ y₁ = z` are
equal. -/
def IsFoolingSet (f : X → Y → Z) (z : Z) (S : Finset (X × Y)) : Prop :=
  (∀ q ∈ S, f q.1 q.2 = z) ∧ ∀ q ∈ S, ∀ q' ∈ S, f q.1 q'.2 = z → f q'.1 q.2 = z → q = q'

namespace IsFoolingSet

variable {f : X → Y → Z} {z : Z} {S : Finset (X × Y)} {p : Protocol X Y Z}

/-- A finite cover of a fooling set by monochromatic rectangles has at least as many
pieces as the fooling set. The cover may overlap and need only cover the set itself.
The shared injection is extracted from András Z. Salamon's nondeterministic-cover proof. -/
theorem card_le_cover {κ : Type*} [Fintype κ] (hS : IsFoolingSet f z S)
    (A : κ → Set X) (B : κ → Set Y)
    (hmono : ∀ i, ∀ x ∈ A i, ∀ y ∈ B i, f x y = z)
    (hcover : ∀ q ∈ S, ∃ i, q.1 ∈ A i ∧ q.2 ∈ B i) : #S ≤ Fintype.card κ := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rw [card_eq_zero.2 (eq_empty_of_forall_notMem fun q hq =>
      (hcover q hq).elim fun i _ => hκ.elim i)]
    exact Nat.zero_le _
  choose! g hg using hcover
  rw [← card_univ]
  refine card_le_card_of_injOn g (by intro _ _; exact mem_univ _) ?_
  intro q hq q' hq' hqq
  refine hS.2 q hq q' hq' ?_ ?_
  · exact hmono (g q) _ (hg q hq).1 _ (by rw [hqq]; exact (hg q' hq').2)
  · exact hmono (g q) _ (by rw [hqq]; exact (hg q' hq').1) _ (hg q hq).2

/-- A fooling set injects into the pieces labelled `z` of every arbitrary monochromatic tiling. -/
theorem card_le_partition [DecidableEq Z] (hS : IsFoolingSet f z S)
    {p : RectanglePartition X Y Z} (hp : p.run = f) : #S ≤ #{i | p.output i = z} := by
  classical
  have h := hS.card_le_cover
    (fun i : {i : Fin p.size // p.output i = z} => p.alice i.val)
    (fun i => p.bob i.val)
    (fun i x hx y hy => by rw [← hp, RectanglePartition.run_eq_output hx hy, i.property])
    (fun q hq => ⟨⟨p.part q.1 q.2, by
      rw [← RectanglePartition.run_eq_output_part, hp, hS.1 q hq]⟩, p.part_mem q.1 q.2⟩)
  simpa only [Fintype.card_subtype] using h

/-- A fooling set bounds the minimum over arbitrary monochromatic tilings
[AroraBarak07, Lemma 12.8]. -/
theorem card_le_tilingNumber (hS : IsFoolingSet f z S) : (#S : ℕ∞) ≤ tilingNumber f := by
  classical
  refine le_tilingNumber_iff.mpr fun p hp => ?_
  exact_mod_cast (hS.card_le_partition hp).trans
    ((card_le_univ _).trans_eq (card_fin p.size))

/-- A protocol computing `f` reaches distinct leaves labelled `z` on the pairs of a fooling set
for `f` with value `z`. -/
theorem card_le [DecidableEq Z] (hS : IsFoolingSet f z S) (hp : p.run = f) :
    #S ≤ #{i | p.leafOutput i = z} :=
  hS.card_le_partition (p.run_toRectanglePartition.trans hp)

/-- **The fooling-set bound.** If `f` takes a value other than `z`, a fooling set for `f` with
value `z` has fewer than `2 ^ d` pairs, for every protocol computing `f` with `d` bits. -/
theorem card_lt_two_pow (hS : IsFoolingSet f z S) (hp : p.run = f) (hz : ∃ x y, f x y ≠ z) :
    #S < 2 ^ p.depth := by
  classical
  obtain ⟨x, y, hxy⟩ := hz
  have hlt : #{i | p.leafOutput i = z} < p.leafCount := by
    refine (card_lt_card (filter_ssubset.mpr ⟨p.leaf x y, mem_univ _, ?_⟩)).trans_eq ?_
    · rwa [← Protocol.run_eq_leafOutput_leaf, hp]
    · exact card_fin p.leafCount
  exact (hS.card_le hp).trans_lt (hlt.trans_le p.leafCount_le_two_pow_depth)

/-- **The fooling-set bound on communication complexity.** A fooling set of at least `2 ^ n`
pairs for a function `f` that is not constantly `z` forces `n + 1` bits. -/
theorem succ_le_ecomplexity (hS : IsFoolingSet f z S) (hz : ∃ x y, f x y ≠ z) {n : ℕ}
    (hn : 2 ^ n ≤ #S) : (n + 1 : ℕ∞) ≤ Protocol.ecomplexityFun f := by
  refine Protocol.le_ecomplexityFun_iff.mpr fun p hp => ?_
  have h := hn.trans_lt (hS.card_lt_two_pow hp hz)
  exact_mod_cast (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp h

end IsFoolingSet

end Cslib.Communication
