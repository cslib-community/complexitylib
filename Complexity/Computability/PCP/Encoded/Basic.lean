/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.ConstraintGraph
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Foundations.Data.List.Equiv
import Mathlib.Data.List.GetD

/-!
# Executable constraint graphs

An edge list gives concrete indices to vertices and edges while keeping constraints as data.
The interpretation uses an explicit Boolean evaluator; in particular, it does not decide an
arbitrary proposition-valued relation. A separate `WellFormed` predicate says that endpoints
are below the declared vertex count. None of the algorithms requires or computes that proof.

The natural-number interpretation is convenient for proving transformations correct. On
well-formed inputs its vertices are the images of `Fin vertices`, with all other vertices
isolated, and `toFiniteGraph` recovers the corresponding finite constraint graph.

## Main definitions

* `Cslib.PCP.Encoded.Edge`, `Cslib.PCP.Encoded.Graph`: executable edge records and edge lists.
* `Cslib.PCP.Encoded.Graph.toGraph`, `Cslib.PCP.Encoded.Graph.toFiniteGraph`: interpretations.
* `Cslib.PCP.Encoded.Graph.isWellFormed`: an executable endpoint-bounds check.
* `Cslib.PCP.Encoded.Graph.checkEdge`: check a constraint against a list of vertex labels.

## Main results

* `Cslib.PCP.Encoded.Graph.checkEdge_eq_true_iff`: exact agreement with graph satisfaction.
* `Cslib.PCP.Encoded.Graph.satisfiable_toFiniteGraph_iff`,
  `Cslib.PCP.Encoded.Graph.unsatVal_toFiniteGraph`: finite interpretations preserve the value.
* `Cslib.PCP.Encoded.Graph.isPolyTime_checkEdge`: a uniform machine-backed certificate,
  including edge lookup, label lookup and constraint evaluation.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Turing.MultiTapeTM

/-- An edge with numbered endpoints and an executable constraint descriptor. -/
@[ext]
structure Edge (Constraint : Type) where
  /-- The first endpoint. -/
  src : ℕ
  /-- The second endpoint. -/
  dst : ℕ
  /-- The data interpreted by the constraint evaluator. -/
  constraint : Constraint
  deriving DecidableEq, Repr

namespace Edge

variable {C Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}

/-- An edge is encoded by its unary endpoints and its constraint descriptor. -/
def encoding (enc : C ↪ List Bool) : Edge C ↪ List Bool :=
  ⟨fun e => encPair encUnary (encPair encUnary enc) (e.src, e.dst, e.constraint),
    fun e f h => by
      have h := (encPair encUnary (encPair encUnary enc)).injective h
      exact Edge.ext (congrArg Prod.fst h) (congrArg (fun p => p.2.1) h)
        (congrArg (fun p => p.2.2) h)⟩

private theorem isPolyTime_toPair (enc : C ↪ List Bool) :
    ComputableInPolyTime (fun e : Edge C => (e.src, e.dst, e.constraint))
      (encoding enc) (encPair encUnary (encPair encUnary enc)) :=
  .of_eq fun _ => rfl

/-- Reading an edge's first endpoint is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_src {edge : Input → Edge C}
    (hedge : ComputableInPolyTime edge input (encoding enc)) :
    ComputableInPolyTime (fun x => (edge x).src) input encUnary :=
  (isPolyTime_toPair enc).fst'.comp hedge

/-- Reading an edge's second endpoint is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_dst {edge : Input → Edge C}
    (hedge : ComputableInPolyTime edge input (encoding enc)) :
    ComputableInPolyTime (fun x => (edge x).dst) input encUnary :=
  (isPolyTime_toPair enc).snd'.fst'.comp hedge

/-- Reading an edge's constraint descriptor is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_constraint {edge : Input → Edge C}
    (hedge : ComputableInPolyTime edge input (encoding enc)) :
    ComputableInPolyTime (fun x => (edge x).constraint) input enc :=
  (isPolyTime_toPair enc).snd'.snd'.comp hedge

/-- Assemble computed endpoints and a computed constraint into an edge. -/
@[fun_prop]
theorem isPolyTime_mk {Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}
    {src dst : Input → ℕ} {constraint : Input → C}
    (hsrc : ComputableInPolyTime src input encUnary)
    (hdst : ComputableInPolyTime dst input encUnary)
    (hconstraint : ComputableInPolyTime constraint input enc) :
    ComputableInPolyTime (fun x => Edge.mk (src x) (dst x) (constraint x))
      input (encoding enc) :=
  (hsrc.prod (hdst.prod hconstraint)).of_enc_eq fun _ => rfl

end Edge

/-- A finite graph represented by its vertex count and ordered list of edges.
The ordering distinguishes parallel edges. -/
@[ext]
structure Graph (Constraint : Type) where
  /-- The number of vertices. -/
  vertices : ℕ
  /-- The ordered edges, including parallel edges and loops. -/
  edges : List (Edge Constraint)
  deriving DecidableEq, Repr

namespace Graph

variable {C α Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}

/-- The vertex count is unary and the edges use the standard framed list encoding. -/
def encoding (enc : C ↪ List Bool) : Graph C ↪ List Bool :=
  ⟨fun g => encPair encUnary (encList (Edge.encoding enc)) (g.vertices, g.edges),
    fun g h heq => by
      have heq := (encPair encUnary (encList (Edge.encoding enc))).injective heq
      exact Graph.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)⟩

private theorem isPolyTime_toPair (enc : C ↪ List Bool) :
    ComputableInPolyTime (fun g : Graph C => (g.vertices, g.edges))
      (encoding enc) (encPair encUnary (encList (Edge.encoding enc))) :=
  .of_eq fun _ => rfl

/-- Reading the declared vertex count is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_vertices {graph : Input → Graph C}
    (hgraph : ComputableInPolyTime graph input (encoding enc)) :
    ComputableInPolyTime (fun x => (graph x).vertices) input encUnary :=
  (isPolyTime_toPair enc).fst'.comp hgraph

/-- Reading the edge list is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_edges {graph : Input → Graph C}
    (hgraph : ComputableInPolyTime graph input (encoding enc)) :
    ComputableInPolyTime (fun x => (graph x).edges) input (encList (Edge.encoding enc)) :=
  (isPolyTime_toPair enc).snd'.comp hgraph

/-- Assemble a computed vertex count and edge list into a graph. -/
@[fun_prop]
theorem isPolyTime_mk {Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}
    {vertices : Input → ℕ} {edges : Input → List (Edge C)}
    (hvertices : ComputableInPolyTime vertices input encUnary)
    (hedges : ComputableInPolyTime edges input (encList (Edge.encoding enc))) :
    ComputableInPolyTime (fun x => Graph.mk (vertices x) (edges x)) input (encoding enc) :=
  (hvertices.prod hedges).of_enc_eq fun _ => rfl

/-- All listed endpoints are among the declared vertices. -/
def WellFormed (g : Graph C) : Prop :=
  ∀ e ∈ g.edges, e.src < g.vertices ∧ e.dst < g.vertices

/-- Check the endpoint bounds by a scan through the edge records. -/
def isWellFormed (g : Graph C) : Bool :=
  g.edges.all fun e => decide (e.src < g.vertices ∧ e.dst < g.vertices)

/-- The executable endpoint check is exact. -/
@[simp]
theorem isWellFormed_eq_true (g : Graph C) : g.isWellFormed = true ↔ g.WellFormed := by
  simp [isWellFormed, WellFormed]

/-- Checking all endpoint bounds is uniformly polynomial-time. -/
@[fun_prop]
theorem isPolyTime_isWellFormed (enc : C ↪ List Bool) :
    ComputableInPolyTime (isWellFormed (C := C)) (encoding enc) encBool := by
  unfold isWellFormed
  fun_prop

/-- Read an edge by its natural-number index, returning a specified fallback if it is absent. -/
def edgeAt (fallback : C) (g : Graph C) (i : ℕ) : Edge C :=
  g.edges.getD i ⟨0, 0, fallback⟩

/-- A computed graph determines the edge encoding before the index is checked. -/
@[fun_prop]
theorem isPolyTime_edgeAt {graph : Input → Graph C} {index : Input → ℕ}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hindex : ComputableInPolyTime index input encUnary) (fallback : C) :
    ComputableInPolyTime (fun x => (graph x).edgeAt fallback (index x))
      input (Edge.encoding enc) :=
  (ComputableInPolyTime.listGetD (encA := Edge.encoding enc)
    (Edge.mk 0 0 fallback)).comp ((isPolyTime_edges hgraph).prod hindex)

/-- Check a numbered edge against a list of labels. Both lookups are total, with explicit
fallbacks; the correctness theorem applies to valid edge indices. -/
def checkEdge (eval : C → α → α → Bool) (fallback : C) (label : α)
    (g : Graph C) (labels : List α) (i : ℕ) : Bool :=
  let e := g.edgeAt fallback i
  eval e.constraint (labels.getD e.src label) (labels.getD e.dst label)

/-- Edge and label lookup, and the constraint evaluation, are all charged to the certificate. -/
@[fun_prop]
theorem isPolyTime_checkEdge {alphabet : α ↪ List Bool}
    {graph : Input → Graph C} {labels : Input → List α} {index : Input → ℕ}
    {eval : C → α → α → Bool} (fallback : C) (label : α)
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (hlabels : ComputableInPolyTime labels input (encList alphabet))
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime
      (fun x => checkEdge eval fallback label (graph x) (labels x) (index x)) input encBool := by
  have hedge := isPolyTime_edgeAt hgraph hindex fallback
  have hsrc := Edge.isPolyTime_src hedge
  have hdst := Edge.isPolyTime_dst hedge
  have hconstraint := Edge.isPolyTime_constraint hedge
  exact heval.comp (hconstraint.prod
    (((ComputableInPolyTime.listGetD (encA := alphabet) label).comp (hlabels.prod hsrc)).prod
      ((ComputableInPolyTime.listGetD (encA := alphabet) label).comp (hlabels.prod hdst))))

/-- Interpret the explicit edge list on natural-number vertices. Unlisted vertices are isolated. -/
def toGraph (g : Graph C) (eval : C → α → α → Bool) :
    ConstraintGraph ℕ (Fin g.edges.length) α where
  src i := (g.edges.get i).src
  dst i := (g.edges.get i).dst
  rel i a b := eval (g.edges.get i).constraint a b = true

/-- An occurrence enumeration and pointwise edge semantics identify the entire graph.
No injectivity of the stored edge values is required, so loops and parallel edges are retained. -/
theorem toGraph_eq_comap {V ι : Type*} (g : Graph C) (eval : C → α → α → Bool)
    {edge : ι → Edge C} (enumeration : List.Enumeration g.edges edge)
    (G : ConstraintGraph V ι α) (number : V → ℕ)
    (hsrc : ∀ i, (edge i).src = number (G.src i))
    (hdst : ∀ i, (edge i).dst = number (G.dst i))
    (hrel : ∀ i a b, eval (edge i).constraint a b = true ↔ G.rel i a b) :
    g.toGraph eval = (G.map number).comap enumeration.equiv := by
  ext i a b
  · exact (congrArg Edge.src (enumeration.get_eq i)).trans (hsrc _)
  · exact (congrArg Edge.dst (enumeration.get_eq i)).trans (hdst _)
  · exact (congrArg (fun e => eval e.constraint a b = true)
      (enumeration.get_eq i)).to_iff.trans (hrel _ a b)

/-- On an existing edge, the executable check is exactly satisfaction by the list's labelling. -/
theorem checkEdge_eq_true_iff (g : Graph C) (eval : C → α → α → Bool)
    (fallback : C) (label : α) (labels : List α) (i : Fin g.edges.length) :
    g.checkEdge eval fallback label labels i = true ↔
      (g.toGraph eval).Satisfies (fun v => labels.getD v label) i := by
  simp [checkEdge, edgeAt, toGraph, ConstraintGraph.Satisfies]

/-- Interpret a well-formed edge list using exactly its declared finite vertex set. -/
def toFiniteGraph (g : Graph C) (eval : C → α → α → Bool) (hg : g.WellFormed) :
    ConstraintGraph (Fin g.vertices) (Fin g.edges.length) α where
  src i := ⟨(g.edges.get i).src, (hg _ (List.get_mem ..)).1⟩
  dst i := ⟨(g.edges.get i).dst, (hg _ (List.get_mem ..)).2⟩
  rel i a b := eval (g.edges.get i).constraint a b = true

/-- The natural-number interpretation only adds isolated vertices. -/
theorem toFiniteGraph_map (g : Graph C) (eval : C → α → α → Bool) (hg : g.WellFormed) :
    (g.toFiniteGraph eval hg).map Fin.val = g.toGraph eval :=
  rfl

/-- The finite and natural-number interpretations have the same satisfiability. -/
theorem satisfiable_toFiniteGraph_iff [Nonempty α] (g : Graph C)
    (eval : C → α → α → Bool) (hg : g.WellFormed) :
    (g.toFiniteGraph eval hg).Satisfiable ↔ (g.toGraph eval).Satisfiable := by
  rw [← toFiniteGraph_map g eval hg]
  exact ((g.toFiniteGraph eval hg).satisfiable_map Fin.val_injective).symm

/-- The finite and natural-number interpretations have the same unsatisfiability value. -/
theorem unsatVal_toFiniteGraph [Nonempty α] (g : Graph C)
    (eval : C → α → α → Bool) (hg : g.WellFormed) :
    (g.toFiniteGraph eval hg).unsatVal = (g.toGraph eval).unsatVal := by
  rw [← toFiniteGraph_map g eval hg]
  exact ((g.toFiniteGraph eval hg).unsatVal_map Fin.val_injective).symm

end Graph

end Cslib.PCP.Encoded
