/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Incidence
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cyclic argument order in CSP incidence rotations

Each argument occurrence determines two distinct indexed ends of its incidence edge. The
constraint-side rotation must follow the scope's cyclic argument order. Variable-side rotations
are unrestricted beyond the graph rotation-system contract. Repeated variables and identical
constraints keep their different argument/constraint positions. Nullary constraints have no
argument darts, so the order condition is vacuous for them.

This is the argument-order part of the incidence model in Fulla–Živný, *On Planar Valued CSPs*,
arXiv:1602.06323v3, Section 2.1. It is not a genus-zero condition, planarity recognizer, supplied
embedding reduction or full planar CSP definition.

## Main definitions

* `Cslib.Complexity.CSP.incidenceDart`: indexed end of an argument's incidence edge.
* `Cslib.Complexity.CSP.argumentSuccessor`: next argument in the same ordered scope.
* `Cslib.Complexity.CSP.RespectsArgumentOrder`: constraint-side cyclic-order compatibility.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- A chosen end of an argument's incidence edge; `true` is its constraint end. -/
@[expose] def incidenceDart (o : F.Occurrence) (side : Bool) : Graph.Dart (incidenceGraph F) :=
  (⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩, side)

/-- Occurrence identity is retained at each choice of edge end. -/
theorem incidenceDart_injective (side : Bool) :
    Function.Injective (fun o : F.Occurrence => incidenceDart o side) := by
  intro o p h
  exact incidenceEdgeIndex_injective (congrArg (fun d => d.1.val) h)

/-- Constraint-side and variable-side indexed ends remain distinct, even at repeated names. -/
theorem incidenceDart_true_ne_false (o p : F.Occurrence) :
    incidenceDart o true ≠ incidenceDart p false := by
  intro h
  exact Bool.false_ne_true (congrArg Prod.snd h).symm

/-- The endpoint agrees with the original incidence construction. -/
@[simp] theorem vertex_incidenceDart (o : F.Occurrence) (side : Bool) :
    Graph.Dart.vertex (incidenceDart o side) =
      if side then F.numVars + o.1 else F.distinctVars.idxOf o.var :=
  edgeEndpoint_incidenceEdgeIndex o side

/-- Every indexed edge end comes from exactly one argument and its endpoint choice. -/
theorem exists_incidenceDart (d : Graph.Dart (incidenceGraph F)) :
    ∃ o : F.Occurrence, incidenceDart o d.2 = d := by
  obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex d.1 d.1.isLt
  refine ⟨o, ?_⟩
  exact Prod.ext (Fin.ext ho) rfl

/-- Next position in the same scope, with last-to-first wraparound. -/
@[expose] def argumentSuccessor (o : F.Occurrence) : F.Occurrence :=
  ⟨o.1, finRotate _ o.2⟩

omit [DecidableEq V] in
/-- The next argument belongs to the same constraint position. -/
@[simp] theorem argumentSuccessor_constraint (o : F.Occurrence) :
    (argumentSuccessor o).1 = o.1 := rfl

omit [DecidableEq V] in
/-- The scope's cyclic permutation makes argument succession injective. -/
theorem argumentSuccessor_injective : Function.Injective (argumentSuccessor (F := F)) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have hi : i = k := congrArg Sigma.fst h
  subst k
  have hj : finRotate _ j = finRotate _ l := by
    exact eq_of_heq (Sigma.mk.inj h).2
  exact congrArg (Sigma.mk i) ((finRotate _).injective hj)

/-- The cyclic rotation at every constraint follows its ordered argument positions.
Rotations at variable vertices are governed only by the graph rotation-system contract. -/
@[expose] def RespectsArgumentOrder (r : Graph.RotationSystem (incidenceGraph F)) : Prop :=
  ∀ o : F.Occurrence, r.rotate (incidenceDart o true) =
    incidenceDart (argumentSuccessor o) true

end Cslib.Complexity.CSP
