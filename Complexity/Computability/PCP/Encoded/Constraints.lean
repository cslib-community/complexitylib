/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Tactic.PolyTime

/-!
# Changing and tabulating constraint descriptors

`g.mapConstraints f` changes the descriptor on every edge while retaining all endpoints and
edge indices. At a fixed finite alphabet, `g.mapConstraints eval` materializes each executable
constraint as its complete Boolean table, encoded with `encPi (encPi encBool)`. This returns
successive graph transformations to the same descriptor type `α → α → Bool`.

Tabulation requires an efficient evaluator jointly in the descriptor and both alphabet symbols.
The table certificate charges every entry; the alphabet is fixed independently of the input.
No decidability or efficiency is inferred for arbitrary proposition-valued constraints.

## Main definitions

* `Cslib.PCP.Encoded.Graph.mapConstraints`: transform every edge's constraint descriptor.

## Main results

* `Cslib.PCP.Encoded.Graph.toGraph_mapConstraints`: exact interpretation after descriptor change.
* `Cslib.PCP.Encoded.Graph.isPolyTime_tabulateConstraints`: materializing all finite tables is
  polynomial-time, including the unchanged endpoints and graph storage.
* `Cslib.PCP.Encoded.Graph.length_encoding_tabulateConstraints_le`: tabulation adds at most a
  constant number of bits per edge.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C C' C'' α Input : Type} {input : Input ↪ List Bool}
  {enc : C ↪ List Bool} {enc' : C' ↪ List Bool}

/-- Change each constraint descriptor, preserving the vertex count, edge order, and endpoints. -/
def mapConstraints (f : C → C') (g : Graph C) : Graph C' :=
  ⟨g.vertices, g.edges.map fun e => ⟨e.src, e.dst, f e.constraint⟩⟩

/-- Applying the identity descriptor map leaves the graph unchanged. -/
@[simp]
theorem mapConstraints_id (g : Graph C) : g.mapConstraints id = g := by
  cases g
  simp [mapConstraints]

/-- Successive descriptor changes compose without changing graph indices. -/
theorem mapConstraints_comp (g : Graph C) (f : C → C') (h : C' → C'') :
    (g.mapConstraints f).mapConstraints h = g.mapConstraints (h ∘ f) := by
  simp [mapConstraints, List.map_map, Function.comp_def]

/-- The vertex count is unchanged. -/
@[simp]
theorem vertices_mapConstraints (g : Graph C) (f : C → C') :
    (g.mapConstraints f).vertices = g.vertices := rfl

/-- Every original edge produces exactly one new edge. -/
@[simp]
theorem length_edges_mapConstraints (g : Graph C) (f : C → C') :
    (g.mapConstraints f).edges.length = g.edges.length :=
  List.length_map ..

/-- Changing descriptors preserves exactly the same endpoint bounds. -/
@[simp]
theorem wellFormed_mapConstraints_iff (g : Graph C) (f : C → C') :
    (g.mapConstraints f).WellFormed ↔ g.WellFormed := by
  simp [WellFormed, mapConstraints]

/-- The new graph interprets each original constraint through the descriptor map.
The finite edge-index cast retains its numerical index. -/
theorem toGraph_mapConstraints (g : Graph C) (f : C → C') (eval : C' → α → α → Bool) :
    (g.mapConstraints f).toGraph eval =
      (g.toGraph (fun c => eval (f c))).comap (finCongr (length_edges_mapConstraints g f)) := by
  ext i <;> simp only [mapConstraints, toGraph, ConstraintGraph.comap, List.get_eq_getElem,
    List.getElem_map, Function.comp_def] <;> rfl

/-- Changing descriptor representation preserves the exact constraint-violation value. -/
theorem unsatVal_mapConstraints (g : Graph C) (f : C → C') (eval : C' → α → α → Bool) :
    ((g.mapConstraints f).toGraph eval).unsatVal =
      (g.toGraph (fun c => eval (f c))).unsatVal := by
  rw [toGraph_mapConstraints, ConstraintGraph.unsatVal_comap_equiv]

/-- Changing descriptor representation preserves satisfiability. -/
theorem satisfiable_mapConstraints_iff (g : Graph C) (f : C → C')
    (eval : C' → α → α → Bool) :
    ((g.mapConstraints f).toGraph eval).Satisfiable ↔
      (g.toGraph (fun c => eval (f c))).Satisfiable := by
  rw [toGraph_mapConstraints, ConstraintGraph.satisfiable_comap_iff _ (Equiv.surjective _)]

/-- Changing every descriptor charges the transformation, copying endpoints, and the output list. -/
@[fun_prop]
theorem isPolyTime_mapConstraints {graph : Input → Graph C} {f : C → C'}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hf : ComputableInPolyTime f enc enc') :
    ComputableInPolyTime (fun x => (graph x).mapConstraints f)
      input (encoding enc') := by
  unfold mapConstraints
  polytime

/-- Materialize every value of an efficiently evaluable constraint at a fixed finite alphabet. -/
@[fun_prop]
theorem isPolyTime_constraintTable [Fintype α] {alphabet : α ↪ List Bool}
    {eval : C → α → α → Bool}
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime eval enc (encPi (encPi encBool)) := by
  apply ComputableInPolyTime.pi
  intro a
  apply ComputableInPolyTime.pi
  intro b
  exact heval.comp (.prod (.id' (encIn := enc)) (.prod (.const a) (.const b)))

/-- A fixed finite alphabet lets an efficient evaluator be materialized as its entire table.
The source descriptor may have unbounded encoded size. -/
@[fun_prop]
theorem isPolyTime_tabulateConstraints [Fintype α] {alphabet : α ↪ List Bool}
    {eval : C → α → α → Bool}
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime (mapConstraints eval) (encoding enc)
      (encoding (encPi (encPi encBool))) :=
  isPolyTime_mapConstraints (.id' (encIn := encoding enc)) (isPolyTime_constraintTable heval)

/-- Evaluate a stored constraint table at both runtime alphabet symbols. -/
@[fun_prop]
theorem isPolyTime_constraintTableEval [Fintype α] (alphabet : α ↪ List Bool) :
    ComputableInPolyTime (fun p : (α → α → Bool) × α × α => p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair alphabet alphabet)) encBool := by
  polytime

/-- The full two-dimensional constraint table has bounded encoded size, including its framing. -/
theorem length_constraintTable_le [Fintype α] (table : α → α → Bool) :
    (encPi (encPi encBool) table).length ≤
      Fintype.card α * (6 * Fintype.card α + 1) := by
  have hrow (a : α) : (encPi encBool (table a)).length ≤ 3 * Fintype.card α := by
    simpa only [Nat.mul_comm, show 2 * 1 + 1 = 3 from rfl] using
      length_encPi_le encBool (table a) (bound := 1) (by intro b; simp)
  simpa only [← Nat.mul_assoc] using
    length_encPi_le (encPi encBool) table hrow

/-- Bounded growth per descriptor gives bounded total encoded growth. Both the inner edge
encoding and the outer list framing are charged. -/
theorem length_encoding_mapConstraints_le (g : Graph C) (f : C → C') (bound : ℕ)
    (hf : ∀ c, (enc' (f c)).length ≤ (enc c).length + bound) :
    (encoding enc' (g.mapConstraints f)).length ≤
      (encoding enc g).length + 2 * g.edges.length * bound := by
  have he (e : Edge C) : (Edge.encoding enc' ⟨e.src, e.dst, f e.constraint⟩).length ≤
      (Edge.encoding enc e).length + bound := by
    change (encPair encUnary (encPair encUnary enc') (e.src, e.dst, f e.constraint)).length ≤
      (encPair encUnary (encPair encUnary enc) (e.src, e.dst, e.constraint)).length + bound
    simp only [length_encPair]
    have h := hf e.constraint
    lia
  have hlist : (encList (Edge.encoding enc')
      (g.edges.map fun e => ⟨e.src, e.dst, f e.constraint⟩)).length ≤
      (encList (Edge.encoding enc) g.edges).length + 2 * g.edges.length * bound := by
    induction g.edges with
    | nil => simp
    | cons e edges ih =>
      simp only [List.map_cons, encList_cons, List.length_append, length_frame, List.length_cons]
      have h := he e
      nlinarith
  change (encPair encUnary (encList (Edge.encoding enc'))
      (g.vertices, g.edges.map fun e => ⟨e.src, e.dst, f e.constraint⟩)).length ≤
    (encPair encUnary (encList (Edge.encoding enc)) (g.vertices, g.edges)).length + _
  simp only [length_encPair]
  lia

/-- Normalization to fixed-alphabet tables adds at most a constant number of bits per edge. -/
theorem length_encoding_tabulateConstraints_le [Fintype α] (g : Graph C)
    (eval : C → α → α → Bool) :
    (encoding (encPi (encPi encBool)) (g.mapConstraints eval)).length ≤
      (encoding enc g).length + 2 * g.edges.length *
        (Fintype.card α * (6 * Fintype.card α + 1)) :=
  g.length_encoding_mapConstraints_le eval _ fun c =>
    (length_constraintTable_le (eval c)).trans (Nat.le_add_left _ _)

end Cslib.PCP.Encoded.Graph
