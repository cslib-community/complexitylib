/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion
import Mathlib.Data.Fintype.Sum

/-!
# Sizes of the child networks

The child networks of a mode splitting (`TensorNetwork.ModeSplitting.child`, §D.4.6 of
[OpenAI2026ETH], p. 63) keep the invariants of the recursion:

* an old vertex keeps its degree (`ModeSplitting.card_child_src_inl`);
* a packet vertex has one port for each port of its group in its packet
  (`ModeSplitting.card_child_tgt_inr`), so at most `2 L` ports when no two edges share a slot of a
  packet of `L` slots (`ModeSplitting.card_child_tgt_inr_le`): the manuscript's
  "a new packet vertex has at most `2L ⩽ Δ` ports";
* the child has one edge per port of its group (`ModeSplitting.card_edges_child`), so with at most
  `c M / r` ports per group on each side (Lemma D.3 (3)) it has at most `2 c M / r` edges
  (`ModeSplitting.mul_card_edges_child_le`): the manuscript's "at most `6M / r < M / 8` edges".

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting.card_child_src_inl`: old degrees are
  unchanged.
* `Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting.card_child_tgt_inr_le`: packet degrees are
  at most `2 L`.
* `Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting.mul_card_edges_child_le`: the edge bound.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.3 (pp. 58–59) and
  §D.4.6 (p. 63).
-/

public section

namespace Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting

open Finset

variable {R V E G P M : Type*} [CommRing R] [Fintype M] {N : TensorNetwork R Bool V E}
  {W : Matrix E E R} (S : N.ModeSplitting W G P M) [Fintype E] [DecidableEq E] [DecidableEq P]
  [DecidableEq G] [DecidableEq M] [DecidableEq V]

/-- Counting the elements of a sum type with a property. -/
private theorem card_filter_sum {A B : Type*} [Fintype A] [Fintype B] (p : A ⊕ B → Prop)
    [DecidablePred p] :
    #{x | p x} = #{a | p (.inl a)} + #{b | p (.inr b)} := by
  rw [← Fintype.card_subtype, Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum,
    Fintype.card_subtype, Fintype.card_subtype]

/-- Counting the elements of a subtype with a property. -/
private theorem card_filter_subtype {A : Type*} [Fintype A] (Q : A → Prop) [DecidablePred Q]
    (f : A → Prop) [DecidablePred f] : #{e : {e // Q e} | f e.1} = #{e | Q e ∧ f e} := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter Q f),
    Fintype.card_subtype]

/-- **Old degrees are unchanged.** In a child, an old vertex has one port for each edge of `N`
at it. -/
theorem card_child_src_inl (β : M → ℕ) (g : G) (v : {v // S.group v = g}) :
    #{x | (S.child β g).src x = .inl v} = #{e | N.src e = v.1} + #{e | N.tgt e = v.1} := by
  rw [card_filter_sum]
  congr 1
  · simp only [child_src_inl, Sum.inl.injEq, Subtype.ext_iff]
    rw [card_filter_subtype (fun e => S.group (N.src e) = g) (fun e => N.src e = v.1)]
    exact congrArg card (filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨h ▸ v.2, h⟩⟩)
  · simp only [child_src_inr, Sum.inl.injEq, Subtype.ext_iff]
    rw [card_filter_subtype (fun e => S.group (N.tgt e) = g) (fun e => N.tgt e = v.1)]
    exact congrArg card (filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨h ▸ v.2, h⟩⟩)

/-- Every edge of a child ends at a packet vertex. -/
theorem card_child_tgt_inl (β : M → ℕ) (g : G) (v : {v // S.group v = g}) :
    #{x | (S.child β g).tgt x = .inl v} = 0 := by
  rw [card_filter_sum]
  simp

/-- Every edge of a child starts at an old vertex. -/
theorem card_child_src_inr (β : M → ℕ) (g : G) (q : P) :
    #{x | (S.child β g).src x = .inr q} = 0 := by
  rw [card_filter_sum]
  simp

/-- A packet vertex of a child has one port for each port of its group in its packet. -/
theorem card_child_tgt_inr (β : M → ℕ) (g : G) (q : P) :
    #{x | (S.child β g).tgt x = .inr q} =
      #{e | S.group (N.src e) = g ∧ S.packet e = q} +
        #{e | S.group (N.tgt e) = g ∧ S.packet e = q} := by
  rw [card_filter_sum]
  simp only [child_tgt_inl, child_tgt_inr, Sum.inr.injEq]
  rw [card_filter_subtype (fun e => S.group (N.src e) = g) (fun e => S.packet e = q),
    card_filter_subtype (fun e => S.group (N.tgt e) = g) (fun e => S.packet e = q)]

omit [DecidableEq E] [DecidableEq G] [DecidableEq M] [DecidableEq V] in
/-- At most `L` edges lie in a packet of `L` slots when no two share a slot. -/
private theorem card_packet_le {a : ℕ} {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a)
    (hinj : ∀ e e', S.packet e = S.packet e' → slot e = slot e' → e = e') (q : P)
    (f : E → Prop) [DecidablePred f] : #{e | f e ∧ S.packet e = q} ≤ 2 ^ a := by
  calc #{e | f e ∧ S.packet e = q} ≤ #(range (2 ^ a)) :=
        card_le_card_of_injOn slot (fun e _ => by simpa using hslot e) fun e he e' he' h => by
          simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at he he'
          exact hinj e e' (he.2.trans he'.2.symm) h
    _ = 2 ^ a := card_range _

/-- **Packet degrees are at most `2 L`** in a child, for packets of `L = 2 ^ a` slots with no two
edges in the same slot of a packet. -/
theorem card_child_tgt_inr_le {a : ℕ} {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a)
    (hinj : ∀ e e', S.packet e = S.packet e' → slot e = slot e' → e = e') (β : M → ℕ) (g : G)
    (q : P) : #{x | (S.child β g).tgt x = .inr q} ≤ 2 * 2 ^ a := by
  rw [card_child_tgt_inr, two_mul]
  exact add_le_add (S.card_packet_le hslot hinj q _) (S.card_packet_le hslot hinj q _)

omit [DecidableEq E] [DecidableEq P] [DecidableEq M] [DecidableEq V] in
/-- **The edge bound.** If, in the group `g`, the rows have at most `c M / r` ports and so do the
columns, then the child of `g` has at most `2 c M / r` edges. With Lemma D.3 (3), `c = 3` and
`r = 64`, this is the manuscript's `6M / r < M / 8`. -/
theorem mul_card_edges_child_le {r c : ℕ} (g : G)
    (hrow : r * #{e | S.group (N.src e) = g} ≤ c * Fintype.card E)
    (hcol : r * #{e | S.group (N.tgt e) = g} ≤ c * Fintype.card E) :
    r * Fintype.card ({e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g}) ≤
      2 * c * Fintype.card E := by
  rw [card_edges_child, mul_add]
  linarith

end Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting
