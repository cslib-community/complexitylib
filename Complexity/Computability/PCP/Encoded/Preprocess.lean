/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.DegreeReduction
public import Complexity.Computability.PCP.Encoded.AddTrivial
public import Complexity.Computability.PCP.Preprocess

/-!
# Executable preprocessing of constraint graphs

The program degree-reduces an explicit edge list, adds the edges of the numerical graph family
on its numbered half-edges, and adds one self-loop per half-edge. Original constraints remain
oriented; cloud constraints check equality; the added family edges and loops always accept.

The efficiency certificate is uniform in the input graph. Its numerical rotation hypothesis
covers the runtime graph size, vertex, and edge label jointly. The value and satisfiability
proofs reuse the existing degree-reduction argument and exact laws for appending trivial edges.

## Main definitions

* `Cslib.PCP.Encoded.Graph.rotationEdges`: enumerate the numerical family's directed edges.
* `Cslib.PCP.Encoded.Graph.preprocess`: the complete executable preprocessing program.
* `Cslib.PCP.Encoded.Graph.preprocessExpanders`: the exact-numbering spectral contract.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_preprocess`: machine-backed efficiency of the full program.
* `Cslib.PCP.Encoded.Graph.toGraph_preprocess`: exact agreement with regular preprocessing.
* `Cslib.PCP.Encoded.Graph.wellFormed_preprocess`: all output endpoints are in range.
* `Cslib.PCP.Encoded.Graph.unsatVal_preprocess`: adding family edges and loops halves the
  degree-reduced graph's value.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_preprocess`: the existing Dinur gap bound for the program.
* `Cslib.PCP.Encoded.Graph.spectralExpansion_regularPreprocess_le`: the spectral bound of
  preprocessing, for the program's own vertex numbering.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C α D : Type} {enc : C ↪ List Bool} {labelEncoding : D ↪ List Bool}

/-- Enumerate every outgoing edge of a numerical rotation, retaining its starting vertex.
The rotation's return label is not needed when enumerating constraint-graph edges. -/
def rotationEdges (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (vertices : ℕ) : List (ℕ × ℕ) :=
  (List.range vertices).flatMap fun v => labels.map fun d => (v, (rotate (vertices, v, d)).1)

/-- Degree reduction, addition of the numerical family's edges, and one self-loop per vertex. -/
def preprocess (fallback truth : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D) (g : Graph C) : Graph (Option (Bool × C)) :=
  let reduced := g.degreeReduce fallback rotate labels
  (reduced.addTrivial (some (false, truth))
    (rotationEdges rotate labels reduced.vertices)).addLoops (some (false, truth))

/-- Enumerating all edges charges the runtime vertex count and every rotation call. -/
@[fun_prop]
theorem isPolyTime_rotationEdges (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding)) :
    ComputableInPolyTime (rotationEdges rotate labels) encUnary
      (encList (encPair encUnary encUnary)) := by
  have houter := ComputableInPolyTime.fst (encPair encUnary encUnary) labelEncoding
  have hlabel := ComputableInPolyTime.snd (encPair encUnary encUnary) labelEncoding
  have harg := houter.fst'.prod (houter.snd'.prod hlabel)
  have hbody := ComputableInPolyTime.mapWithInput
    (f := fun p : ℕ × ℕ => fun d : D => (p.2, (rotate (p.1, p.2, d)).1))
    (ComputableInPolyTime.const (encOut := encList labelEncoding) labels)
    (houter.snd'.prod (hrotate.comp harg).fst')
  have h := ComputableInPolyTime.flatMapWithInput
    (f := fun n v => labels.map fun d => (v, (rotate (n, v, d)).1))
    ComputableInPolyTime.range hbody
  change ComputableInPolyTime (fun n => (List.range n).flatMap
    (fun v => labels.map fun d => (v, (rotate (n, v, d)).1))) encUnary
      (encList (encPair encUnary encUnary))
  exact h

/-- The full preprocessing program is polynomial-time, including enumeration, copying,
all edge checks used by cloud search, and materializing every intermediate graph. -/
@[fun_prop]
theorem isPolyTime_preprocess (fallback truth : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D)
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding)) :
    ComputableInPolyTime (preprocess fallback truth rotate labels)
      (encoding enc) (encoding (encOption (encPair encBool enc))) := by
  have hdegree := isPolyTime_degreeReduce (enc := enc) fallback labels rotate hrotate
  unfold preprocess
  fun_prop

/-- There is one enumerated edge per vertex and supplied edge label. -/
@[simp]
theorem length_rotationEdges (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (vertices : ℕ) : (rotationEdges rotate labels vertices).length = vertices * labels.length := by
  simp [rotationEdges, List.length_flatMap, List.sum_replicate]

/-- The output has two vertices per input edge. -/
@[simp]
theorem vertices_preprocess (fallback truth : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D) (g : Graph C) :
    (g.preprocess fallback truth rotate labels).vertices = 2 * g.edges.length :=
  rfl

/-- There are `2 + 2 |labels|` outgoing darts per half-edge in the construction. -/
theorem length_edges_preprocess (fallback truth : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D) (g : Graph C) :
    (g.preprocess fallback truth rotate labels).edges.length =
      2 * g.edges.length * (2 + 2 * labels.length) := by
  simp only [preprocess, length_edges_addLoops, length_edges_addTrivial, length_rotationEdges,
    length_edges_degreeReduce]
  change 2 * g.edges.length * (1 + labels.length) +
    2 * g.edges.length * labels.length + 2 * g.edges.length = _
  ring

/-- Consecutive half-edge numbers identify the actual vertex set with `Fin (2 |E|)`. -/
def halfEdgeEquiv (edges : ℕ) : Fin edges × Bool ≃ Fin (2 * edges) :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm edges 2))

/-- The vertex equivalence uses the executable half-edge numbering. -/
@[simp]
theorem halfEdgeEquiv_val (edges : ℕ) (p : Fin edges × Bool) :
    (halfEdgeEquiv edges p).val = halfEdgeNumber (p.1.val, p.2) := by
  rcases p with ⟨i, b⟩
  cases b <;> simp [halfEdgeEquiv, finProdFinEquiv, finTwoEquiv, halfEdgeNumber, Nat.add_comm]

/-- Interpret the numerical family on the half-edges using their explicit numbering. -/
def halfEdgeFamily (g : Graph C) (family : (n : ℕ) → RotationMap (Fin n) D) :
    RotationMap (Fin g.edges.length × Bool) D :=
  (family (2 * g.edges.length)).reindex (halfEdgeEquiv g.edges.length).symm

/-- The mathematical preprocessing pipeline with exactly the computed cloud and global numberings.
It uses the existing degree reduction, expanderization, and loop operations. -/
def regularPreprocess (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (family : (n : ℕ) → RotationMap (Fin n) D) :
    RegularConstraintGraph (Fin g.edges.length × Bool) (((Unit ⊕ D) ⊕ D) ⊕ Unit) α :=
  (((g.toGraph eval).degreeReduce (g.cloudFamily eval fallback family)).addTrivial
    (g.halfEdgeFamily family)).addLoops Unit

/-- A uniform spectral bound supplies the mathematical preprocessing contract with exactly the
cloud and half-edge numberings computed by the program. -/
def preprocessExpanders [Fintype D] (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (family : (n : ℕ) → RotationMap (Fin n) D) (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) :
    (g.toGraph eval).PreprocessExpanders D μ where
  cloud := g.cloudFamily eval fallback family
  whole := g.halfEdgeFamily family
  spectralExpansion_cloud_le v := by
    simpa only [cloudFamily, RotationMap.spectralExpansion_reindex] using
      hgap (g.cloud fallback v).length
  spectralExpansion_whole_le := by
    simpa only [halfEdgeFamily, RotationMap.spectralExpansion_reindex] using
      hgap (2 * g.edges.length)

/-- The interpreted program inherits the preprocessing spectral bound with its actual numbering. -/
theorem spectralExpansion_regularPreprocess_le [Fintype D] (g : Graph C)
    (eval : C → α → α → Bool) (fallback : C) (family : (n : ℕ) → RotationMap (Fin n) D)
    (μ : ℝ) (hgap : ∀ n, (family n).spectralExpansion ≤ μ) :
    (g.regularPreprocess eval fallback family).graph.spectralExpansion ≤
      1 - (1 - μ) * Fintype.card D / (2 * Fintype.card D + 2) :=
  (g.toGraph eval).spectralExpansion_preprocessWith_le
    (g.preprocessExpanders eval fallback family μ hgap)

private theorem toGraph_append_inverse (vertices : ℕ) (left right : List (Edge C))
    (eval : C → α → α → Bool) :
    ((Graph.mk vertices (left ++ right)).toGraph eval) =
      (((Graph.mk vertices left).toGraph eval).union
        ((Graph.mk vertices right).toGraph eval)).comap (appendEdgeEquiv left right).symm := by
  simpa only [ConstraintGraph.comap_comap, Equiv.self_comp_symm, ConstraintGraph.comap_id] using
    congrArg (fun graph : ConstraintGraph ℕ _ α => graph.comap (appendEdgeEquiv left right).symm)
      (toGraph_append vertices left right eval)

/-- Appending a fully enumerated family of trivial edges realizes
`RegularConstraintGraph.addTrivial`.
This is used for both the expander edges and the self-loops. -/
private theorem addTrivial_represents {V L L' : Type} (g : Graph C) (eval : C → α → α → Bool)
    (truth : C) (extra : List (ℕ × ℕ)) (R : RegularConstraintGraph V L α)
    (H : RotationMap V L') (number : V → ℕ)
    (hg : ∃ e : Fin g.edges.length ≃ V × L,
      g.toGraph eval = (R.toConstraintGraph.map number).comap e)
    (hextra : ∃ e : Fin (extra.map fun p => Edge.mk p.1 p.2 truth).length ≃ V × L',
      ((Graph.mk g.vertices (extra.map fun p => Edge.mk p.1 p.2 truth)).toGraph eval) =
        ((RegularConstraintGraph.unconstrained H).toConstraintGraph.map number).comap e) :
    ∃ e : Fin (g.addTrivial truth extra).edges.length ≃ V × (L ⊕ L'),
      (g.addTrivial truth extra).toGraph eval =
        ((R.addTrivial H).toConstraintGraph.map number).comap e := by
  obtain ⟨eg, hg⟩ := hg
  obtain ⟨eh, hh⟩ := hextra
  let e := ((appendEdgeEquiv g.edges (extra.map fun p => Edge.mk p.1 p.2 truth)).symm.trans
    (Equiv.sumCongr eg eh)).trans (Equiv.prodSumDistrib V L L').symm
  refine ⟨e, ?_⟩
  change (Graph.mk g.vertices
    (g.edges ++ extra.map fun p => Edge.mk p.1 p.2 truth)).toGraph eval = _
  rw [toGraph_append_inverse, hg, hh]
  have hunion : ((R.toConstraintGraph.map number).comap eg).union
      (((RegularConstraintGraph.unconstrained H).toConstraintGraph.map number).comap eh) =
      ((R.addTrivial H).toConstraintGraph.map number).comap
        ((Equiv.sumCongr eg eh).trans (Equiv.prodSumDistrib V L L').symm) := by
    ext (i | j) <;> rfl
  rw [hunion]
  rfl

private theorem rotationEdges_product (rotate : ℕ × (ℕ × D) → ℕ × D)
    (labels : List D) (vertices : ℕ) :
    rotationEdges rotate labels vertices =
      ((List.range vertices).product labels).map fun p => (p.1, (rotate (vertices, p)).1) := by
  simp [rotationEdges, List.product, List.map_flatMap, List.map_map, Function.comp_def]

private theorem rotationEdges_represents {V : Type} (vertices : ℕ)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    (eval : C → α → α → Bool) (truth : C) (htruth : ∀ a b, eval truth a b = true)
    (H : RotationMap (Fin vertices) D)
    (hrotate : ∀ (v : Fin vertices) d,
      rotate (vertices, v.val, d) = ((H.rot (v, d)).1.val, (H.rot (v, d)).2))
    (eV : Fin vertices ≃ V) (number : V → ℕ) (hnumber : ∀ v, number (eV v) = v.val) :
    ∃ e : Fin ((rotationEdges rotate labels vertices).map
        fun p => Edge.mk p.1 p.2 truth).length ≃ V × D,
      ((Graph.mk vertices ((rotationEdges rotate labels vertices).map
        fun p => Edge.mk p.1 p.2 truth)).toGraph eval) =
      ((RegularConstraintGraph.unconstrained (H.reindex eV)).toConstraintGraph.map
        number).comap e := by
  classical
  rw [rotationEdges_product, List.map_map]
  let edge := fun p : ℕ × D => Edge.mk p.1 (rotate (vertices, p)).1 truth
  let enumeration := (((List.Enumeration.range vertices).prod
    (List.Enumeration.ofNodup labels hlabels hmem)).map edge).reindex
      (Equiv.prodCongr eV (Equiv.refl D))
  refine ⟨enumeration.equiv, ?_⟩
  apply toGraph_eq_comap ⟨vertices, ((List.range vertices).product labels).map edge⟩ eval
    enumeration
  · intro p
    simpa [edge, RegularConstraintGraph.toConstraintGraph] using
      (hnumber (eV.symm p.1)).symm
  · intro p
    change (rotate (vertices, (eV.symm p.1).val, p.2)).1 = _
    rw [hrotate]
    simp [RegularConstraintGraph.toConstraintGraph, RegularConstraintGraph.unconstrained,
      RotationMap.neighbor_def, hnumber]
  · intro p a b
    simp [edge, htruth, RegularConstraintGraph.toConstraintGraph,
      RegularConstraintGraph.unconstrained]

section Correctness

variable (g : Graph C) (eval : C → α → α → Bool) (fallback truth : C)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))

include hrotate in
/-- A numerical realization of rotations only emits endpoints among the declared vertices. -/
private theorem endpoints_rotationEdges (labels : List D) (vertices : ℕ)
    (p : ℕ × ℕ) (hp : p ∈ rotationEdges rotate labels vertices) :
    p.1 < vertices ∧ p.2 < vertices := by
  obtain ⟨v, hv, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp
  have hv := List.mem_range.mp hv
  rw [hrotate vertices ⟨v, hv⟩ d]
  exact ⟨hv, Fin.isLt _⟩

include hrotate in
/-- All endpoints in the materialized preprocessing result are in range. -/
theorem wellFormed_preprocess (labels : List D) :
    (g.preprocess fallback truth rotate labels).WellFormed := by
  unfold preprocess
  apply WellFormed.addLoops
  apply (g.wellFormed_degreeReduce fallback family rotate hrotate labels).addTrivial
  intro p hp
  exact endpoints_rotationEdges family rotate hrotate labels _ p hp

include hrotate in
/-- The executable preprocessing program is the existing mathematical construction, using the
same cloud and half-edge numberings. The edge equivalence enumerates each mathematical dart once. -/
theorem toGraph_preprocess [DecidableEq α] (htruth : ∀ a b, eval truth a b = true)
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    ∃ e : Fin (g.preprocess fallback truth rotate labels).edges.length ≃
        (Fin g.edges.length × Bool) × (((Unit ⊕ D) ⊕ D) ⊕ Unit),
      (g.preprocess fallback truth rotate labels).toGraph (degreeReduceEval eval) =
        ((g.regularPreprocess eval fallback family).toConstraintGraph.map
          (fun p => halfEdgeNumber (p.1.val, p.2))).comap e := by
  classical
  let n := 2 * g.edges.length
  let eV := (halfEdgeEquiv g.edges.length).symm
  let number := fun p : Fin g.edges.length × Bool => halfEdgeNumber (p.1.val, p.2)
  let reduced := g.degreeReduce fallback rotate labels
  let R := (g.toGraph eval).degreeReduce (g.cloudFamily eval fallback family)
  let extra := rotationEdges rotate labels n
  let accept := some (false, truth)
  have htrue (a b : α) : degreeReduceEval eval accept a b = true := htruth a b
  have hnumber (v : Fin n) : number (eV v) = v.val := by
    change halfEdgeNumber ((halfEdgeEquiv g.edges.length).symm v |>.1.val,
      (halfEdgeEquiv g.edges.length).symm v |>.2) = v.val
    rw [← halfEdgeEquiv_val, Equiv.apply_symm_apply]
  have hg : ∃ e : Fin reduced.edges.length ≃ (Fin g.edges.length × Bool) × (Unit ⊕ D),
      reduced.toGraph (degreeReduceEval eval) = (R.toConstraintGraph.map number).comap e :=
    ⟨(g.degreeReduceEnumeration fallback rotate labels hlabels hmem).equiv,
      g.toGraph_degreeReduce eval fallback family rotate hrotate labels hlabels hmem⟩
  have hextra := rotationEdges_represents n rotate labels hlabels hmem
    (degreeReduceEval eval) accept htrue (family n) (hrotate n) eV number hnumber
  have hadded := addTrivial_represents reduced (degreeReduceEval eval) accept extra
    R (g.halfEdgeFamily family) number hg hextra
  have hloops := rotationEdges_represents n (fun p : ℕ × ℕ × Unit => p.2) [()]
    (by simp) (fun d => by cases d; simp) (degreeReduceEval eval) accept htrue
    (RotationMap.loops (Fin n) Unit) (fun _ _ => rfl) eV number hnumber
  have hreindex : (RotationMap.loops (Fin n) Unit).reindex eV =
      RotationMap.loops (Fin g.edges.length × Bool) Unit := by
    ext p <;> simp
  have hloopedges : rotationEdges (fun p : ℕ × ℕ × Unit => p.2) [()] n =
      (List.range n).map (fun v => (v, v)) := by
    simp only [rotationEdges, List.map_cons, List.map_nil]
    exact List.flatMap_pure_eq_map ..
  rw [hreindex, hloopedges] at hloops
  exact addTrivial_represents (reduced.addTrivial accept extra) (degreeReduceEval eval)
    accept ((List.range n).map fun v => (v, v)) (R.addTrivial (g.halfEdgeFamily family))
    (RotationMap.loops _ Unit) number hadded hloops

variable [DecidableEq α] [Nonempty α] (htruth : ∀ a b, eval truth a b = true)

include htruth in
/-- The final two steps halve the degree-reduced value, including for the empty graph. -/
theorem unsatVal_preprocess (labels : List D) :
    ((g.preprocess fallback truth rotate labels).toGraph (degreeReduceEval eval)).unsatVal =
      ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)).unsatVal / 2 := by
  have htrue (a b : α) : degreeReduceEval eval (some (false, truth)) a b = true := htruth a b
  rw [preprocess, unsatVal_addLoops _ _ _ htrue, unsatVal_addTrivial _ _ _ htrue]
  simp only [length_edges_addTrivial, length_rotationEdges, length_edges_degreeReduce]
  change
    ((2 * g.edges.length * (1 + labels.length) + 2 * g.edges.length * labels.length : ℕ) : ℝ) /
        ((2 * g.edges.length * (1 + labels.length) + 2 * g.edges.length * labels.length : ℕ) +
          (2 * g.edges.length : ℕ)) *
      (((2 * g.edges.length * (1 + labels.length) : ℕ) : ℝ) /
        ((2 * g.edges.length * (1 + labels.length) : ℕ) +
          (2 * g.edges.length * labels.length : ℕ)) *
        ((g.degreeReduce fallback rotate labels).toGraph (degreeReduceEval eval)).unsatVal) = _
  rcases g.edges.length.eq_zero_or_pos with hzero | hpos
  · have hvalue : ((g.degreeReduce fallback rotate labels).toGraph
        (degreeReduceEval eval)).unsatVal = 0 := by
      simp [ConstraintGraph.unsatVal, ConstraintGraph.unsatFrac, length_edges_degreeReduce, hzero]
    simp [hzero, hvalue]
  · have hpos' : (0 : ℝ) < g.edges.length := by exact_mod_cast hpos
    push_cast
    field_simp
    ring

include hrotate htruth in
/-- The computed graph has exactly the value of the regular preprocessing construction. -/
theorem unsatVal_preprocess_eq [Fintype D] (labels : List D)
    (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels) :
    ((g.preprocess fallback truth rotate labels).toGraph (degreeReduceEval eval)).unsatVal =
      (g.regularPreprocess eval fallback family).toConstraintGraph.unsatVal := by
  obtain ⟨e, he⟩ := g.toGraph_preprocess eval fallback truth family rotate hrotate
    htruth labels hlabels hmem
  rw [he, ConstraintGraph.unsatVal_comap_map_of_injective _ (halfEdgeNumber_fin_injective _)]

include hrotate htruth in
/-- The existing Dinur gap estimate applies to the exact executable preprocessing output. -/
theorem le_unsatVal_preprocess [Fintype D] (labels : List D)
    (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    (μ : ℝ) (hgap : ∀ n, (family n).spectralExpansion ≤ μ) :
    min 1 ((1 - μ) * Fintype.card D) / (4 * (1 + Fintype.card D)) *
      (g.toGraph eval).unsatVal ≤
        ((g.preprocess fallback truth rotate labels).toGraph (degreeReduceEval eval)).unsatVal := by
  rw [unsatVal_preprocess_eq g eval fallback truth family rotate hrotate htruth labels hlabels hmem]
  exact (g.toGraph eval).le_unsatVal_preprocessWith
    (g.preprocessExpanders eval fallback family μ hgap)

include hrotate htruth in
/-- Efficient preprocessing preserves satisfiability whenever the supplied clouds expand. -/
theorem satisfiable_preprocess_iff [Fintype D] [Nonempty D] (labels : List D)
    (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    (μ : ℝ) (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) :
    ((g.preprocess fallback truth rotate labels).toGraph (degreeReduceEval eval)).Satisfiable ↔
      (g.toGraph eval).Satisfiable := by
  obtain ⟨e, he⟩ := g.toGraph_preprocess eval fallback truth family rotate hrotate
    htruth labels hlabels hmem
  rw [he, ConstraintGraph.satisfiable_comap_map_iff _ (halfEdgeNumber_fin_injective _)
    e.surjective]
  exact (g.toGraph eval).satisfiable_preprocessWith_iff
    (g.preprocessExpanders eval fallback family μ hgap) hμ

end Correctness

end Cslib.PCP.Encoded.Graph
