/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Amplification.Arithmetic
import Complexity.Tactic.PolyTime

/-! Concrete complete amplification certificates and nonvacuous semantic clients.
The fixed complete tables are impractical to materialize. The zero-round evaluations below
exercise the program's boundary cases; the semantic tests use its checked whole-program contract.
-/

namespace ComplexityTests.PCPEncodedArithmeticAmplification

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.HadamardTester Turing.MultiTapeTM
open Cslib.PCP.ConstraintGraph.Amplification.Arithmetic

local notation "Alphabet" => (Bool × (Fin 6 → Bool))
local notation "Constraint" => (Alphabet → Alphabet → Bool)

variable {Input : Type} {input : Input ↪ List Bool} {graph : Input → Graph Constraint}
  (hgraph : ComputableInPolyTime graph input (Graph.encoding (encPi (encPi encBool))))
  (hwellFormed : ∀ x, (graph x).WellFormed)

example : ComputableInPolyTime (fun x => (graph x).arithmeticAmplify)
    input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hgraph; fun_prop)
  fail_if_success (clear hwellFormed; fun_prop)
  fun_prop

example : ComputableInPolyTime (fun x =>
    let initial := graph x
    initial.arithmeticAmplify) input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hgraph; polytime)
  fail_if_success (clear hwellFormed; polytime)
  polytime

private def emptyGraph : Graph Constraint := ⟨0, []⟩

private def rejectingEdge : Graph Constraint := ⟨1, [⟨0, 0, fun _ _ => false⟩]⟩

example : emptyGraph.arithmeticAmplify = emptyGraph := by
  unfold Graph.arithmeticAmplify Graph.amplifyIter
  rfl

example : rejectingEdge.arithmeticAmplify = rejectingEdge := by
  unfold Graph.arithmeticAmplify Graph.amplifyIter
  rfl

private theorem rejectingEdge_unsat : ¬ (rejectingEdge.toGraph id).Satisfiable := by
  rintro ⟨σ, hσ⟩
  exact Bool.false_ne_true (hσ ⟨0, by decide⟩)

example : gap ≤ (rejectingEdge.arithmeticAmplify.toGraph id).unsatVal :=
  Graph.gap_le_unsatVal_arithmeticAmplify rejectingEdge_unsat

example : (rejectingEdge.arithmeticAmplify.toGraph id).unsatVal = 1 := by
  have h : rejectingEdge.arithmeticAmplify = rejectingEdge := by
    unfold Graph.arithmeticAmplify Graph.amplifyIter
    rfl
  rw [h]
  apply le_antisymm (ConstraintGraph.unsatVal_le_one _)
  simpa [rejectingEdge] using
    (rejectingEdge.toGraph id).one_le_card_mul_unsatVal rejectingEdge_unsat

example : (emptyGraph.arithmeticAmplify.toGraph id).Satisfiable := by
  rw [Graph.satisfiable_arithmeticAmplify_iff]
  exact ⟨fun _ => (false, fun _ => false), fun i => Fin.elim0 i⟩

example : (rejectingEdge.arithmeticAmplify).WellFormed :=
  Graph.wellFormed_arithmeticAmplify (by
    intro edge hedge
    simp only [rejectingEdge, List.mem_singleton] at hedge
    subst edge
    exact ⟨by decide, by decide⟩)

example : 0 < gap ∧ gap = 1 / (2 : ℝ) ^ 61 := ⟨gap_pos, rfl⟩

-- Two parallel rejecting constraints force a complete round, beyond the zero-round clients.
-- We instantiate its semantic contract without attempting to materialize its enormous tables.
private def rejectingPair : Graph Constraint :=
  ⟨1, [⟨0, 0, fun _ _ => false⟩, ⟨0, 0, fun _ _ => false⟩]⟩

private theorem rejectingPair_unsat : ¬ (rejectingPair.toGraph id).Satisfiable := by
  rintro ⟨σ, hσ⟩
  exact Bool.false_ne_true (hσ ⟨0, by decide⟩)

example : Nat.clog 2 rejectingPair.edges.length = 1 := by decide

example : 1 / (2 : ℝ) ^ 61 ≤ (rejectingPair.arithmeticAmplify.toGraph id).unsatVal :=
  Graph.gap_le_unsatVal_arithmeticAmplify rejectingPair_unsat

example : ¬ (rejectingPair.arithmeticAmplify.toGraph id).Satisfiable :=
  mt (Graph.satisfiable_arithmeticAmplify_iff rejectingPair).mp rejectingPair_unsat

end ComplexityTests.PCPEncodedArithmeticAmplification
