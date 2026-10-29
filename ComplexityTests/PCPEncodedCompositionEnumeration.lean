/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import Complexity.Computability.PCP.Encoded.Composition.Enumeration
import Complexity.Tactic.PolyTime

/-! Complete constructive enumeration, exact graph semantics, and encoding inference clients. -/

namespace ComplexityTests.PCPEncodedCompositionEnumeration

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.HadamardTester Turing.MultiTapeTM

-- The complete empty-alphabet gadget has only 8 coins and 17 queries.
-- We evaluate its endpoints, not the enormous encoded answer tables.
private def emptyGraph : Graph (Fin 0 → Fin 0 → Bool) :=
  ⟨2, [⟨0, 1, fun _ _ => false⟩]⟩

example : emptyGraph.composeEnumerated.vertices = 33 := by decide
example : emptyGraph.composeEnumerated.edges.length = 136 := by
  rw [Graph.length_edges_composeEnumerated]
  decide
example : emptyGraph.composeEnumerated.WellFormed := by
  apply Graph.WellFormed.composeEnumerated
  simp [Graph.WellFormed, emptyGraph]

/-- info: (136, 33, true) -/
#guard_msgs in
#eval (emptyGraph.composeEnumerated.edges.length, emptyGraph.composeEnumerated.vertices,
  emptyGraph.composeEnumerated.isWellFormed)

/-- info: false -/
#guard_msgs in
#eval (Graph.mk 0 emptyGraph.edges).composeEnumerated.isWellFormed

-- The exact interpretation also applies to the empty alphabet.
example : (emptyGraph.composeEnumerated.toGraph id).unsatVal =
    (emptyGraph.toGraph id).compose.unsatVal := Graph.unsatVal_composeEnumerated_eq _

private def falseLoop : Graph (Unit → Unit → Bool) :=
  ⟨1, [⟨0, 0, fun _ _ => false⟩]⟩

example : falseLoop.composeEnumerated.WellFormed := by
  apply Graph.WellFormed.composeEnumerated
  simp [Graph.WellFormed, falseLoop]

example : ¬ (falseLoop.composeEnumerated.toGraph id).Satisfiable := by
  rw [Graph.satisfiable_composeEnumerated_iff]
  rintro ⟨σ, hσ⟩
  exact Bool.false_ne_true (hσ ⟨0, by decide⟩)

example : (falseLoop.toGraph id).unsatVal / 476 ≤
    (falseLoop.composeEnumerated.toGraph id).unsatVal :=
  Graph.le_unsatVal_composeEnumerated _

-- The compact-CNF alphabet has an ordinary Pi Fintype as well as a constructive enumeration.
local instance : FinEnum Bool := FinEnum.ofList [false, true] (by decide)

example : ComputableInPolyTime
    (fun g : Graph ((Fin 3 → Bool) → (Fin 3 → Bool) → Bool) => g.composeEnumerated)
    (Graph.encoding (encPi (encPi encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

section Arbitrary

variable {α Input : Type} [FinEnum α] {input : Input ↪ List Bool}
  {constraints : (α → α → Bool) ↪ List Bool} (graph : Input → Graph (α → α → Bool))
  (hg : ComputableInPolyTime graph input (Graph.encoding constraints))

example : ComputableInPolyTime (fun x => (graph x).composeEnumerated)
    input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hg; fun_prop)
  fun_prop

example : ComputableInPolyTime
    (fun x => let g := graph x; g.composeEnumerated)
    input (Graph.encoding (encPi (encPi encBool))) := by polytime

end Arbitrary

end ComplexityTests.PCPEncodedCompositionEnumeration
