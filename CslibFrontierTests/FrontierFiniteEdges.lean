/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic

/-! Natural degree and width bounds require finitely many edges, including parallel edges. -/

open Cslib.Circuits.Frontier Set

namespace ComplexityTests.FrontierFiniteEdges

/-- Every edge joins the same two vertices. -/
def parallelEdges (E : Type*) : Multigraph Bool E where
  src _ := false
  tgt _ := true

example : (parallelEdges ℕ).incidenceSet false = univ := by
  ext e
  simp [Multigraph.incidenceSet, parallelEdges]

example : ((parallelEdges ℕ).edgeCut {false}).Infinite := by
  have h : (parallelEdges ℕ).edgeCut {false} = univ := by
    ext e
    simp [Multigraph.edgeCut, parallelEdges]
  rw [h]
  exact infinite_univ

-- The underlying natural set-cardinality operation alone would report zero.
example : ((parallelEdges ℕ).edgeCut {false}).ncard = 0 :=
  Set.Infinite.ncard (by
    have h : (parallelEdges ℕ).edgeCut {false} = univ := by
      ext e
      simp [Multigraph.edgeCut, parallelEdges]
    rw [h]
    exact infinite_univ)

-- Neither public natural-valued API may silently accept that infinite edge type.
example (_π : Layout Bool) : True := by
  fail_if_success have : Prop := (parallelEdges ℕ).MaxDegreeLE 0
  fail_if_success have : ℕ := (parallelEdges ℕ).width _π
  trivial

example : (parallelEdges (Fin 3)).MaxDegreeLE 3 := by
  intro v
  cases v <;> simp [Multigraph.incidenceSet, parallelEdges]

example (π : Layout Bool) : (parallelEdges (Fin 3)).width π ≤ 3 := by
  simpa using (parallelEdges (Fin 3)).width_le_card π

-- The Mathlib `Graph` bridge for a multigraph given by its endpoint map agrees with `edgeCut`.
example (S : Finset Bool) :
    ((_root_.Cslib.Multigraph.edgeCut (parallelEdges (Fin 3)).ends S : Finset (Fin 3)) :
        Set (Fin 3)) =
      (_root_.Cslib.Multigraph.toGraph (parallelEdges (Fin 3)).ends).edgeCut S :=
  _root_.Cslib.Multigraph.coe_edgeCut_eq_toGraph_edgeCut (parallelEdges (Fin 3)).ends S

/--
info: 'Cslib.Multigraph.toGraph_isLink' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Multigraph.toGraph_isLink

/--
info: 'Cslib.Multigraph.incidenceSet_toGraph' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Multigraph.incidenceSet_toGraph

end ComplexityTests.FrontierFiniteEdges
