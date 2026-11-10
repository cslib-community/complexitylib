/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import CslibFrontier.Computability.PCP.Encoded.SelectedComposition
import CslibFrontier.Tactic.PolyTime

/-! Complete constructive enumeration, exact graph semantics, and encoding inference clients. -/

namespace CslibFrontierTests.PCPEncodedSelectedComposition

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.HadamardTester Turing.MultiTapeTM

-- The complete empty-alphabet gadget has 40 selected coins and 6 queries.
-- We evaluate its endpoints, not the enormous encoded answer tables.
private def emptyGraph : Graph (Fin 0 → Fin 0 → Bool) :=
  ⟨2, [⟨0, 1, fun _ _ => false⟩]⟩

example : emptyGraph.composeSelectedEnumerated.vertices = 129 := by decide
example : emptyGraph.composeSelectedEnumerated.edges.length = 240 := by
  rw [Graph.length_edges_composeSelectedEnumerated]
  decide
example : emptyGraph.composeSelectedEnumerated.WellFormed := by
  apply Graph.WellFormed.composeSelectedEnumerated
  simp [Graph.WellFormed, emptyGraph]

/-- info: (240, 129, true) -/
#guard_msgs in
#eval (emptyGraph.composeSelectedEnumerated.edges.length,
  emptyGraph.composeSelectedEnumerated.vertices, emptyGraph.composeSelectedEnumerated.isWellFormed)

/-- info: false -/
#guard_msgs in
#eval (Graph.mk 0 emptyGraph.edges).composeSelectedEnumerated.isWellFormed

private def falseLoop : Graph (Unit → Unit → Bool) :=
  ⟨1, [⟨0, 0, fun _ _ => false⟩]⟩

example : falseLoop.composeSelectedEnumerated.WellFormed := by
  apply Graph.WellFormed.composeSelectedEnumerated
  simp [Graph.WellFormed, falseLoop]

example : ¬ (falseLoop.composeSelectedEnumerated.toGraph id).Satisfiable := by
  rw [Graph.satisfiable_composeSelectedEnumerated_iff]
  rintro ⟨σ, hσ⟩
  exact Bool.false_ne_true (hσ ⟨0, by decide⟩)

example : (falseLoop.toGraph id).unsatVal / 840 ≤
    (falseLoop.composeSelectedEnumerated.toGraph id).unsatVal :=
  Graph.le_unsatVal_composeSelectedEnumerated _

-- The compact-CNF alphabet has an ordinary Pi Fintype as well as a constructive enumeration.
local instance : FinEnum Bool := FinEnum.ofList [false, true] (by decide)

example : ComputableInPolyTime
    (fun g : Graph ((Fin 3 → Bool) → (Fin 3 → Bool) → Bool) => g.composeSelectedEnumerated)
    (Graph.encoding (encPi (encPi encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

section Arbitrary

variable {α Input : Type} [FinEnum α] {input : Input ↪ List Bool}
  {constraints : (α → α → Bool) ↪ List Bool} (graph : Input → Graph (α → α → Bool))
  (hg : ComputableInPolyTime graph input (Graph.encoding constraints))

example : ComputableInPolyTime (fun x => (graph x).composeSelectedEnumerated)
    input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hg; fun_prop)
  fun_prop

example : ComputableInPolyTime
    (fun x => let g := graph x; g.composeSelectedEnumerated)
    input (Graph.encoding (encPi (encPi encBool))) := by polytime

end Arbitrary

end CslibFrontierTests.PCPEncodedSelectedComposition
