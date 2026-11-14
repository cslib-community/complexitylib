/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ListedVariables
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateColors

/-!
# Corner colors on listed incidence rotations

Closed color paths on the actual positional variable words, together with the constraint
successor equations, give clockwise-compatible colors on the constructed incidence rotation.
Empty words impose no equation. No connectedness, degree or genus premise is used.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Literal closed paths on the variable words determine the variable-side corner equations.
The constraint-side equations use the original ordered argument successor. -/
theorem colors_rotate_rotationOfVariableCycles (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) (hn : cycles.flatten.Nodup) (P : Dart (incidenceGraph F) → Bool)
    (hconstraint : ∀ o : F.Occurrence,
      P (incidenceDart (argumentSuccessor o) true) = P (incidenceDart o false))
    (hwords : ∀ word ∈ cycles, ∃ color : Bool,
      List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
        ((color, color) :: word.map
          (fun j => (Dart.colorAtIndex P (2 * j), Dart.colorAtIndex P (2 * j + 1))) ++
          [(color, color)])) :
    ∀ d, P ((rotationOfVariableCycles F cycles hcover hfibers).rotate d) = P d.reverse := by
  intro d
  obtain ⟨o, ho⟩ := exists_incidenceDart d
  rw [← ho]
  cases d.2 with
  | true =>
    rw [rotate_rotationOfVariableCycles_true]
    exact hconstraint o
  | false =>
    obtain ⟨word, hw, how⟩ := List.mem_flatten.mp
      ((hcover _).mpr (incidenceEdgeIndex_lt o))
    obtain ⟨color, hc⟩ := hwords word hw
    have he := List.formPerm_colorPairs_of_isChain word
      ((List.nodup_flatten.mp hn).1 word hw)
      (fun j => Dart.colorAtIndex P (2 * j))
      (fun j => Dart.colorAtIndex P (2 * j + 1)) color hc (incidenceEdgeIndex o) how
    rw [rotate_rotationOfVariableCycles_false]
    let next := List.finiteCyclePermutation cycles hcover
      ⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩
    have hnext : P (next, false) = Dart.colorAtIndex P (2 * next.val) :=
      (Dart.colorAtIndex_index P (next, false)).symm
    change P (next, false) = P (incidenceDart o true)
    rw [hnext]
    change Dart.colorAtIndex P
      (2 * (List.finiteCyclePermutation cycles hcover
        ⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩).val) = _
    rw [List.val_finiteCyclePermutation,
      List.cyclePermutation_apply_of_mem cycles hn word hw _ how, he]
    exact Dart.colorAtIndex_index P (incidenceDart o true)

end Cslib.Complexity.CSP
