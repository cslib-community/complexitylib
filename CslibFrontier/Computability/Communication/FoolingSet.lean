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

/-- A protocol computing `f` reaches distinct leaves labelled `z` on the pairs of a fooling set
for `f` with value `z`. -/
theorem card_le [DecidableEq Z] (hS : IsFoolingSet f z S) (hp : p.run = f) :
    #S ≤ #{i | p.leafOutput i = z} := by
  refine card_le_card_of_injOn (fun q => p.leaf q.1 q.2) (fun q hq => ?_) fun q hq q' hq' h => ?_
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [← Protocol.run_eq_leafOutput_leaf, hp, hS.1 q hq]
  · have h : p.leaf q.1 q.2 = p.leaf q'.1 q'.2 := h
    have h₁ : f q.1 q'.2 = z := by
      have hy : q'.2 ∈ p.leafBob (p.leaf q.1 q.2) := h ▸ Protocol.mem_leafBob_leaf
      rw [← hp, Protocol.run_eq_leafOutput Protocol.mem_leafAlice_leaf hy,
        ← Protocol.run_eq_leafOutput_leaf, hp, hS.1 q hq]
    have h₂ : f q'.1 q.2 = z := by
      have hy : q.2 ∈ p.leafBob (p.leaf q'.1 q'.2) := h ▸ Protocol.mem_leafBob_leaf
      rw [← hp, Protocol.run_eq_leafOutput Protocol.mem_leafAlice_leaf hy,
        ← Protocol.run_eq_leafOutput_leaf, hp, hS.1 q' hq']
    exact hS.2 q hq q' hq' h₁ h₂

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
