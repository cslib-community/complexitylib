/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.CloudRotation
import Complexity.Tactic.PolyTime
import Mathlib.Data.List.GetD
import Mathlib.Data.List.ProdSigma

/-!
# Executable degree reduction

The executable construction uses every half-edge as a vertex. Each has one original edge-link
and one cloud-link for every label of a fixed enumerated graph family. Original constraints
retain their orientation; cloud-links use equality. The program is polynomial-time given one
uniform certificate for the numerical cloud rotation.

## Main definitions

* `Cslib.PCP.Encoded.Graph.halfEdgeNumber`: number the half-edges by consecutive naturals.
* `Cslib.PCP.Encoded.Graph.degreeReduce`: the executable edge-list transformation.
* `Cslib.PCP.Encoded.Graph.degreeReduceEval`: interpret original and equality constraints.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_degreeReduce`: the entire transformation is polynomial-time.
* `Cslib.PCP.Encoded.Graph.toGraph_degreeReduce`: exact agreement with degree reduction.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_degreeReduce`: the retained constraint-violation gap.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C α D Input : Type} {input : Input ↪ List Bool}
  {enc : C ↪ List Bool} {labelEncoding : D ↪ List Bool}

/-- Consecutive vertex identifiers for the two ends of each numbered edge. -/
def halfEdgeNumber (p : ℕ × Bool) : ℕ :=
  2 * p.1 + if p.2 then 1 else 0

/-- Numbering half-edges uses only unary arithmetic. -/
@[fun_prop]
theorem isPolyTime_halfEdgeNumber :
    ComputableInPolyTime halfEdgeNumber (encPair encUnary encBool) encUnary := by
  unfold halfEdgeNumber
  polytime

/-- Numbering does not identify the two ends of a loop or distinct parallel edges. -/
theorem halfEdgeNumber_injective : Function.Injective halfEdgeNumber := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  cases a <;> cases b <;> simp_all [halfEdgeNumber, Prod.ext_iff] <;> lia

/-- Existing half-edges receive identifiers below twice the number of edges. -/
theorem halfEdgeNumber_lt {p : ℕ × Bool} {edges : ℕ} (hp : p.1 < edges) :
    halfEdgeNumber p < 2 * edges := by
  rcases p with ⟨i, b⟩
  cases b <;> dsimp only [halfEdgeNumber] <;> lia

/-- Edge-link labels are `none`; cloud-link labels are `some d`. -/
def degreeReduceDarts (g : Graph C) (labels : List D) : List ((ℕ × Bool) × Option D) :=
  g.halfEdges.product (none :: labels.map some)

/-- The constraint descriptor is `none` for equality or `some (reverse, original)` for an
original edge constraint, with its argument order retained. -/
def degreeReduceEdge (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (g : Graph C) (dart : (ℕ × Bool) × Option D) : Edge (Option (Bool × C)) :=
  dart.2.elim
    ⟨halfEdgeNumber dart.1, halfEdgeNumber (dart.1.1, !dart.1.2),
      some (dart.1.2, (g.edgeAt fallback dart.1.1).constraint)⟩
    fun d => ⟨halfEdgeNumber dart.1,
      halfEdgeNumber (g.cloudRotation fallback rotate (dart.1, d)).1, none⟩

/-- Construct the entire degree-reduced graph as ordinary enumeration followed by mapping. -/
def degreeReduce (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D) (g : Graph C) : Graph (Option (Bool × C)) :=
  ⟨2 * g.edges.length,
    (g.degreeReduceDarts labels).map (g.degreeReduceEdge fallback rotate)⟩

/-- Evaluate an original oriented constraint or a cloud equality constraint. -/
def degreeReduceEval [DecidableEq α] (eval : C → α → α → Bool)
    (constraint : Option (Bool × C)) (a b : α) : Bool :=
  constraint.elim (decide (a = b)) fun p => if p.1 then eval p.2 b a else eval p.2 a b

/-- Enumerating all darts of degree reduction charges the full output list. -/
@[fun_prop]
theorem isPolyTime_degreeReduceDarts {graph : Input → Graph C}
    (hgraph : ComputableInPolyTime graph input (encoding enc)) (labels : List D) :
    ComputableInPolyTime (fun x => (graph x).degreeReduceDarts labels)
      input (encList (encPair (encPair encUnary encBool) (encOption labelEncoding))) := by
  unfold degreeReduceDarts List.product
  polytime

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Every output edge is computed uniformly in the input graph and dart. -/
@[fun_prop]
theorem isPolyTime_degreeReduceEdge {graph : Input → Graph C}
    {dart : Input → (ℕ × Bool) × Option D} {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hdart : ComputableInPolyTime dart input
      (encPair (encPair encUnary encBool) (encOption labelEncoding)))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (fallback : C) :
    ComputableInPolyTime
      (fun x => (graph x).degreeReduceEdge fallback rotate (dart x))
      input (Edge.encoding (encOption (encPair encBool enc))) := by
  have hgraph := hgraph.tidy
  have hdart := hdart.tidy
  have hrotate := hrotate.tidy
  refine .of_tidy ?_
  unfold degreeReduceEdge
  polytime

/-- The whole edge-list construction is uniformly polynomial-time, including all cloud
scans, searches, rotation calls, copying, and storage of the resulting graph. -/
@[fun_prop]
theorem isPolyTime_degreeReduce (fallback : C) (labels : List D)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding)) :
    ComputableInPolyTime (degreeReduce fallback rotate labels)
      (encoding enc) (encoding (encOption (encPair encBool enc))) := by
  have hdarts := isPolyTime_degreeReduceDarts (enc := enc)
    (labelEncoding := labelEncoding) (ComputableInPolyTime.id' (encIn := encoding enc)) labels
  unfold degreeReduce
  fun_prop

/-- Constraint evaluation remains polynomial-time, with equality implemented by comparison
of encoded labels. -/
@[fun_prop]
theorem isPolyTime_degreeReduceEval [DecidableEq α] {alphabet : α ↪ List Bool}
    {eval : C → α → α → Bool}
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime
      (fun p : Option (Bool × C) × α × α => degreeReduceEval eval p.1 p.2.1 p.2.2)
      (encPair (encOption (encPair encBool enc)) (encPair alphabet alphabet)) encBool := by
  unfold degreeReduceEval
  polytime

/-- A degree-reduced edge list has the expected number of darts. -/
theorem length_edges_degreeReduce (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D) (g : Graph C) :
    (g.degreeReduce fallback rotate labels).edges.length =
      2 * g.edges.length * (1 + labels.length) := by
  simp only [degreeReduce, List.length_map, degreeReduceDarts]
  change (g.halfEdges ×ˢ (none :: labels.map some)).length = _
  simp [List.length_product, Nat.add_comm]

/-- Every enumerated dart comes from an existing original edge and a listed label. -/
@[simp]
theorem mem_degreeReduceDarts_iff (g : Graph C) (labels : List D)
    (p : (ℕ × Bool) × Option D) :
    p ∈ g.degreeReduceDarts labels ↔
      p.1.1 < g.edges.length ∧ (p.2 = none ∨ ∃ d ∈ labels, p.2 = some d) := by
  rcases p with ⟨p, d⟩
  cases d <;> simp [degreeReduceDarts]

/-- Enumerating distinct labels gives one occurrence of every dart. -/
theorem nodup_degreeReduceDarts (g : Graph C) (labels : List D) (hlabels : labels.Nodup) :
    (g.degreeReduceDarts labels).Nodup := by
  apply g.nodup_halfEdges.product
  exact List.nodup_cons.mpr ⟨by simp, hlabels.map (Option.some_injective _)⟩

/-- Forget the finite index proofs in a mathematical degree-reduction dart. -/
def numberDart {edges : ℕ} (p : (Fin edges × Bool) × (Unit ⊕ D)) :
    (ℕ × Bool) × Option D :=
  ((p.1.1.val, p.1.2), p.2.elim (fun _ => none) some)

/-- The ordered output occurrences are indexed by the mathematical degree-reduction darts.
The original edge precedes the cloud edges at each half-edge. -/
def degreeReduceEnumeration [DecidableEq D] (g : Graph C) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    List.Enumeration (g.degreeReduce fallback rotate labels).edges
      (fun p : (Fin g.edges.length × Bool) × (Unit ⊕ D) =>
        g.degreeReduceEdge fallback rotate (numberDart p)) :=
  (g.halfEdgesEnumeration.prod ((List.Enumeration.singleton none).append
    ((List.Enumeration.ofNodup labels hlabels hmem).map some))).map
      (g.degreeReduceEdge fallback rotate)

/-- The computed source is the numbered source half-edge. -/
@[simp]
theorem src_degreeReduceEdge (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (g : Graph C) (p : (ℕ × Bool) × Option D) :
    (g.degreeReduceEdge fallback rotate p).src = halfEdgeNumber p.1 := by
  cases hp : p.2 <;> simp [degreeReduceEdge, hp]

section Correctness

variable (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))

include hrotate in
/-- Every computed destination agrees with the existing mathematical degree reduction. -/
private theorem dst_degreeReduceEdge (p : (Fin g.edges.length × Bool) × (Unit ⊕ D)) :
    (g.degreeReduceEdge fallback rotate (numberDart p)).dst =
      let next := ((g.toGraph eval).degreeReduce
        (g.cloudFamily eval fallback family)).graph.neighbor
        p.1 p.2
      halfEdgeNumber (next.1.val, next.2) := by
  rcases p with ⟨⟨i, b⟩, u | d⟩
  · rfl
  · exact congrArg (fun p => halfEdgeNumber p.1)
      (g.cloudRotation_eq eval fallback family rotate hrotate
        ((g.toGraph eval).endpoint (i, b)) ⟨(i, b), rfl⟩ d)

/-- Original constraints retain their orientation, while cloud-links are equality constraints. -/
private theorem rel_degreeReduceEdge [DecidableEq α]
    (p : (Fin g.edges.length × Bool) × (Unit ⊕ D)) (a b : α) :
    degreeReduceEval eval
      (g.degreeReduceEdge fallback rotate (numberDart p)).constraint a b = true ↔
      ((g.toGraph eval).degreeReduce (g.cloudFamily eval fallback family)).rel p a b := by
  rcases p with ⟨⟨i, side⟩, u | d⟩
  · cases side <;> simp [degreeReduceEdge, degreeReduceEval, numberDart,
      ConstraintGraph.degreeReduce, edgeAt, toGraph, Function.flip_def]
  · simp [degreeReduceEdge, degreeReduceEval, numberDart, ConstraintGraph.degreeReduce]

include hrotate in
/-- The complete edge-list program is the existing degree reduction, with explicitly numbered
vertices and the proved enumeration of its darts. -/
theorem toGraph_degreeReduce [DecidableEq α] [DecidableEq D] (labels : List D)
    (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)) =
      ((((g.toGraph eval).degreeReduce (g.cloudFamily eval fallback family)).toConstraintGraph).map
        (fun p => halfEdgeNumber (p.1.val, p.2))).comap
          (g.degreeReduceEnumeration fallback rotate labels hlabels hmem).equiv := by
  apply toGraph_eq_comap _ _ (g.degreeReduceEnumeration fallback rotate labels hlabels hmem)
  · intro p
    simp only [src_degreeReduceEdge, numberDart]
    rfl
  · exact dst_degreeReduceEdge g eval fallback family rotate hrotate
  · exact rel_degreeReduceEdge g eval fallback family rotate

include hrotate in
/-- Every generated endpoint is in the output vertex range. The original graph's declared
vertex bound is irrelevant, because its edges themselves index the new vertices. -/
theorem wellFormed_degreeReduce (labels : List D) :
    (g.degreeReduce fallback rotate labels).WellFormed := by
  intro e he
  obtain ⟨⟨⟨i, b⟩, tag⟩, hp, rfl⟩ := List.mem_map.mp he
  have hi := ((g.mem_degreeReduceDarts_iff labels _).mp hp).1
  constructor
  · rw [src_degreeReduceEdge]
    exact halfEdgeNumber_lt hi
  · cases tag with
    | none => exact halfEdgeNumber_lt hi
    | some d =>
      change (g.degreeReduceEdge fallback rotate
        (numberDart ((⟨i, hi⟩, b), Sum.inr d))).dst < _
      rw [dst_degreeReduceEdge g (fun _ (_ _ : Unit) => true) fallback family rotate hrotate]
      apply halfEdgeNumber_lt
      exact Fin.isLt _

/-- Restricting half-edge numbering to existing edges is still injective. -/
theorem halfEdgeNumber_fin_injective (edges : ℕ) :
    Function.Injective (fun p : Fin edges × Bool => halfEdgeNumber (p.1.val, p.2)) := by
  intro p q h
  have h := halfEdgeNumber_injective h
  exact Prod.ext (Fin.ext (congrArg (fun r : ℕ × Bool => r.1) h))
    (congrArg (fun r : ℕ × Bool => r.2) h)

include hrotate in
/-- The executable output has exactly the value of the mathematical degree reduction. -/
theorem unsatVal_degreeReduce [DecidableEq α] [Nonempty α] [Fintype D]
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)).unsatVal =
      ((g.toGraph eval).degreeReduce
        (g.cloudFamily eval fallback family)).toConstraintGraph.unsatVal := by
  classical
  rw [toGraph_degreeReduce g eval fallback family rotate hrotate labels hlabels hmem,
    ConstraintGraph.unsatVal_comap_map_of_injective _ (halfEdgeNumber_fin_injective _)]

include hrotate in
/-- The executable output has exactly the satisfiability of the mathematical degree reduction. -/
theorem satisfiable_degreeReduce_iff [DecidableEq α] [Nonempty α]
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)).Satisfiable ↔
      ((g.toGraph eval).degreeReduce
        (g.cloudFamily eval fallback family)).toConstraintGraph.Satisfiable := by
  classical
  rw [toGraph_degreeReduce g eval fallback family rotate hrotate labels hlabels hmem,
    ConstraintGraph.satisfiable_comap_map_iff _ (halfEdgeNumber_fin_injective _)
      (Equiv.surjective _)]

include hrotate in
/-- The uniform spectral bound transfers through the computed cloud enumeration, so the existing
Dinur degree-reduction gap estimate applies to the executable graph. -/
theorem le_unsatVal_degreeReduce [DecidableEq α] [Nonempty α] [Fintype D]
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    (μ : ℝ) (hgap : ∀ n, (family n).spectralExpansion ≤ μ) :
    min 1 ((1 - μ) * Fintype.card D) / (2 * (1 + Fintype.card D)) *
      (g.toGraph eval).unsatVal ≤
        ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)).unsatVal := by
  classical
  rw [unsatVal_degreeReduce g eval fallback family rotate hrotate labels hlabels hmem]
  apply (g.toGraph eval).le_unsatVal_degreeReduce
  intro vertex
  simpa only [cloudFamily, RotationMap.spectralExpansion_reindex] using
    hgap (g.cloud fallback vertex).length

include hrotate in
/-- Degree reduction does not increase the number of violations after normalizing by its degree. -/
theorem one_add_card_mul_unsatVal_degreeReduce_le
    [DecidableEq α] [Nonempty α] [Fintype D]
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    (1 + Fintype.card D : ℝ) *
        ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)).unsatVal ≤
      (g.toGraph eval).unsatVal := by
  classical
  rw [unsatVal_degreeReduce g eval fallback family rotate hrotate labels hlabels hmem]
  exact (g.toGraph eval).one_add_card_mul_unsatVal_degreeReduce_le _

end Correctness

end Cslib.PCP.Encoded.Graph
