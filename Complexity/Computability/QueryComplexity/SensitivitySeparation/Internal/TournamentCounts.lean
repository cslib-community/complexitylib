/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Tournament
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-!
# Superquadratic sensitivity separation: tournament counts

Counts the directed edges inside a vertex set of a tournament: a set `I` spans exactly
`I.card.choose 2` internal edges, and this number equals the sum of the internal outdegrees.
Consequently a set in which every vertex has internal outdegree at most one has at most three
vertices; this bounds the number of gate candidates in the recursive construction.

## Main definitions

* `Tournament.internalEdges`: the directed edges with both endpoints in a given set.

## Main results

* `Tournament.card_internalEdges`: a set `I` spans `I.card.choose 2` internal edges.
* `Tournament.sum_outdegree_eq`: the internal outdegrees sum to the number of internal edges.
* `Tournament.card_le_three_of_outdegree_le_one`: internal outdegrees at most one force at most
  three vertices.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal.Tournament
variable {k : ℕ} (T : Tournament k)

open scoped Classical in
/-- Directed edges whose two endpoints both belong to the given vertex set. -/
def internalEdges (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => T.Adj p.1 p.2

open scoped Classical in
/-- A vertex set `I` spans exactly `I.card.choose 2` internal directed edges. -/
theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

open scoped Classical in
/-- The sum over `i ∈ I` of the number of outgoing neighbors of `i` in `I` equals the number of
internal edges of `I`. -/
theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

open scoped Classical in
/-- If every vertex of `I` has at most one outgoing neighbor in `I`, then `I` has at most `3`
vertices. -/
theorem card_le_three_of_outdegree_le_one (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by
  have hsum := Finset.sum_le_sum h
  have hc : I.card.choose 2 ≤ I.card := by
    rw [← T.card_internalEdges, ← T.sum_outdegree_eq]
    simpa only [Finset.sum_const_nat, mul_one] using hsum
  have hdouble : I.card * (I.card - 1) ≤ 2 * I.card + 1 := by grind [Nat.choose_two_right]
  by_contra hn
  have h4 : 4 ≤ I.card := by omega
  have ht : I.card - 1 + 1 = I.card := by omega
  nlinarith

end Internal.Tournament

end

end Cslib.QueryComplexity.SensitivitySeparation
