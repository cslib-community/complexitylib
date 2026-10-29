/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import ComplexityTests.PCPNumbering
import Complexity.Computability.PCP.Encoded.AssignmentTester.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime

/-! Tests for exact gadget enumeration, numbering, soundness, and composition certificates. -/

namespace ComplexityTests.PCPEncodedComposition

open Cslib Cslib.PCP Cslib.PCP.HadamardTester Cslib.PCP.Encoded Turing.MultiTapeTM
open ComplexityTests.PCPNumbering

attribute [local instance] HadamardTester.instFinEnumBool Rand.finEnum

-- The complete empty-alphabet gadget is small enough to evaluate: 8 coins, 17 queries.
private def emptyAlphabet : Numbering (Fin 0) := ⟨0, Equiv.refl _⟩
private def emptyCoins : List (Rand (Fin 0)) :=
  List.ofFn (numberCoins emptyAlphabet).2.symm
private def emptyGraph : Graph (Fin 0 → Fin 0 → Bool) :=
  ⟨2, [⟨0, 1, fun _ _ => false⟩]⟩

-- All queries for one coin precede the next coin; the original edge index is retained.
example : (emptyGraph.composeEnumeration (numberSlots emptyAlphabet).2 emptyCoins queries
    (nodup_coins _) nodup_queries (mem_coins _) mem_queries).equiv
      ⟨17, by rw [Graph.length_edges_compose]; decide⟩ =
        ((⟨0, by decide⟩, emptyCoins[1]), queries[0]) := rfl

example : (numberSlots emptyAlphabet).1 = 11 := by decide
example : emptyCoins.length = 8 := by decide
example : queries.length = 17 := by decide
example : (emptyGraph.compose (numberSlots emptyAlphabet).2 emptyCoins queries).vertices =
    33 := by decide
example : (emptyGraph.compose (numberSlots emptyAlphabet).2 emptyCoins queries).edges.length =
    136 := by
  rw [Graph.length_edges_compose]
  decide
example : ((emptyGraph.compose (numberSlots emptyAlphabet).2 emptyCoins queries).edges.map
    (fun e => (e.src, e.dst))).head? = some (3, 1) := by decide
example : ((emptyGraph.compose (numberSlots emptyAlphabet).2 emptyCoins queries).edges.map
    (fun e => (e.src, e.dst))).getLast? = some (10, 1) := by decide
example : (emptyGraph.compose (numberSlots emptyAlphabet).2 emptyCoins queries).isWellFormed =
    true := by decide

example : ((Graph.mk 0 emptyGraph.edges).compose (numberSlots emptyAlphabet).2 emptyCoins
    queries).isWellFormed = false := by decide

-- Nonempty-alphabet correctness is instantiated with the actual complete coin enumeration.
-- The Bool construction has 2^113 coins; the test uses its enumeration proof without running it.
private def boolAlphabet : Numbering Bool := ⟨2, finTwoEquiv.symm⟩
private def boolCoins : List (Rand Bool) := List.ofFn (numberCoins boolAlphabet).2.symm

-- One actual Bool gadget per old edge, retaining a loop and two parallel edges.
private def boolGraph : Graph (Bool → Bool → Bool) :=
  ⟨2, [⟨0, 0, fun a b => a == b⟩, ⟨0, 1, fun a b => a == b⟩,
    ⟨0, 1, fun _ _ => false⟩]⟩

private def oneCoin : Rand Bool :=
  ((0, 0), (0, 0), (0, 0, 0, 0, 0), (0, 0), (1, id, 0))

private def boolGadgets := boolGraph.compose (numberSlots boolAlphabet).2 [oneCoin] queries

example : boolGadgets.edges.length = 51 := by
  rw [boolGadgets, Graph.length_edges_compose]
  decide

-- The loop queries vertex zero's table; the parallel edges query vertex one's same table.
example : (boolGadgets.edges.map Edge.dst).getD 14 0 = 2 := by decide
example : (boolGadgets.edges.map Edge.dst).getD 31 0 =
    (numberSlots boolAlphabet).1 + 2 := by decide
example : (boolGadgets.edges.map Edge.dst).getD 48 0 =
    (numberSlots boolAlphabet).1 + 2 := by decide
example : (boolGadgets.edges.map Edge.src).getD 17 0 =
    (boolGadgets.edges.map Edge.src).getD 0 0 + (numberSlots boolAlphabet).1 := by decide
example : boolGadgets.isWellFormed = true := by decide

-- The third edge rejects every assignment; the fixture is genuinely unsatisfiable.
private theorem boolGraph_not_satisfiable : ¬ (boolGraph.toGraph id).Satisfiable := by
  rintro ⟨σ, hσ⟩
  exact Bool.false_ne_true (hσ ⟨2, by decide⟩)

example : ¬ ((boolGraph.compose (numberSlots boolAlphabet).2 boolCoins queries).toGraph
    Graph.composeEval).Satisfiable := by
  intro h
  exact boolGraph_not_satisfiable ((Graph.satisfiable_compose_iff _ _ _ boolGraph
    (nodup_coins _) nodup_queries (mem_coins _) mem_queries).mp h)

example : 0 < ((boolGraph.compose (numberSlots boolAlphabet).2 boolCoins queries).toGraph
    Graph.composeEval).unsatVal := by
  have hgap := (boolGraph.toGraph id).unsatVal_pos_iff.mpr boolGraph_not_satisfiable
  exact (div_pos hgap (by norm_num : (0 : ℝ) < 476)).trans_le
    (Graph.le_unsatVal_compose _ _ _ boolGraph (nodup_coins _) nodup_queries (mem_coins _)
      mem_queries)

example : ComputableInPolyTime
    (Graph.compose (numberSlots boolAlphabet).2 boolCoins queries)
    (Graph.encoding (encPi (encPi encBool)))
    (Graph.encoding (encPair (encPi (encPi encBool))
      (encPair (encFinEnum (Rand Bool)) (encFinEnum Query)))) := by fun_prop

-- The composed descriptors normalize to fixed tables over the 17-query answer alphabet.
example : ComputableInPolyTime
    (fun g : Graph (Bool → Bool → Bool) =>
      g.composeTabulated (numberSlots boolAlphabet).2 boolCoins queries)
    (Graph.encoding (encPi (encPi encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by
  polytime

-- A captured graph may use an arbitrary outer representation; its certificate is still required.
example {Input : Type} (input : Input ↪ List Bool) (graph : Input → Graph (Bool → Bool → Bool))
    (hgraph : ComputableInPolyTime graph input (Graph.encoding (encPi (encPi encBool)))) :
    ComputableInPolyTime
      (fun x => (graph x).composeTabulated (numberSlots boolAlphabet).2 boolCoins queries)
      input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hgraph; polytime)
  polytime

end ComplexityTests.PCPEncodedComposition
