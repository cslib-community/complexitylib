/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.ComponentCounts
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Differences
public import Complexity.Foundations.Data.BitString.ZModTwo
import Complexity.Foundations.LinearAlgebra.Matrix.EndpointIncidence
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lifting face-even edge labels to vertex spins

The finite-field proof uses the actual indexed source and dual incidence matrices.
Connectedness gives their ranks; componentwise Euler makes the included cut and face-kernel
spaces have equal dimension. This finite-field argument is an original reconstruction.

[DvorakKupec2015], Section 3, Lemma 5 and Corollary 4 (printed p. 439), use differences on
connected plane instances; the proof of Theorem 2 (printed p. 440) applies that correspondence
to satisfiability. Here the statement is the graph-theoretic lifting prerequisite for arbitrary
listed graphs and arbitrary edge bits. Its hypotheses are declared endpoints and the existing
componentwise numerical Euler predicate. It asserts neither the cited CSP equivalence nor a
geometric realization or native complexity bound. Spanning-cotree certificates, runtime
oracles, and a finite natural-number universe are not assumed.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.component_euler_le`: the matrix Euler bound for an
  incident component, without a numerical genus hypothesis.
* `Cslib.Complexity.Graph.RotationSystem.exists_vertexSpins_of_faceEven`: disconnected lifting.
* `Cslib.Complexity.Graph.RotationSystem.faceEven_iff_exists_vertexSpins`: the exact parity test.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

private abbrev Vertex (G : Graph) (root : ℕ) := ↥(G.componentVertexSet root)
private abbrev Edge (G : Graph) (root : ℕ) := ↥(G.componentEdgeSet root)

private noncomputable def endpoint (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (i : Edge G root) (b : Bool) : Vertex G root :=
  ⟨Dart.vertex (G := G) (i.val, b),
    (mem_componentEdgeSet_iff root hG i.val b).mp i.property⟩

private noncomputable def extend (G : Graph) (root : ℕ) (s : Vertex G root → ZMod 2)
    (v : ℕ) : ZMod 2 :=
  if h : v ∈ G.componentVertexSet root then s ⟨v, h⟩ else 0

private theorem extend_endpoint (G : Graph) (root : ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (s : Vertex G root → ZMod 2)
    (i : Edge G root) (b : Bool) :
    extend G root s (Dart.vertex (G := G) (i.val, b)) = s (endpoint G root hG i b) := by
  simp only [extend, dite_eq_left ((mem_componentEdgeSet_iff root hG i.val b).mp i.property),
    endpoint]

private noncomputable def rootVertex (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) : Vertex G d.vertex :=
  ⟨d.vertex, (mem_componentVertexSet_dart _ hG d).mpr (.refl (vertex_mem hG d))⟩

private theorem component_constant (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G)
    (s : Vertex G d.vertex → ZMod 2)
    (hs : ∀ i : Edge G d.vertex,
      s (endpoint G d.vertex hG i false) = s (endpoint G d.vertex hG i true)) :
    ∀ a b, s a = s b := by
  classical
  have hedge (i : Fin G.2.length) :
      extend G d.vertex s (Dart.vertex (G := G) (i, false)) =
        extend G d.vertex s (Dart.vertex (G := G) (i, true)) := by
    by_cases hi : i ∈ G.componentEdgeSet d.vertex
    · rw [extend_endpoint G d.vertex hG s ⟨i, hi⟩ false,
        extend_endpoint G d.vertex hG s ⟨i, hi⟩ true]
      exact hs ⟨i, hi⟩
    · have hl := mt (mem_componentEdgeSet_iff d.vertex hG i false).mpr hi
      have hr := mt (mem_componentEdgeSet_iff d.vertex hG i true).mpr hi
      simp only [extend, dite_eq_right hl, dite_eq_right hr]
  intro a b
  have hda := (Finset.mem_filter.mp a.property).2
  have hdb := (Finset.mem_filter.mp b.property).2
  obtain ⟨p, hp⟩ := Dart.exists_of_sameComponent d a.val hda
  obtain ⟨q, hq⟩ := Dart.exists_of_sameComponent d b.val hdb
  have heq := Dart.eq_of_sameComponent
    (fun p : Dart G => extend G d.vertex s p.vertex)
    (fun p q h => congrArg (extend G d.vertex s) h)
    (fun p => by
      rcases p with ⟨i, side⟩
      cases side
      · exact hedge i
      · exact (hedge i).symm)
    (d := p) (e := q) (by simpa only [hp, hq] using hda.symm.trans hdb)
  simpa only [hp, hq, extend, dite_eq_left a.property, dite_eq_left b.property] using heq

private noncomputable def primalMatrix (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    Matrix (Vertex G d.vertex) (Edge G d.vertex) (ZMod 2) :=
  Matrix.endpointIncidence (fun i => endpoint G d.vertex hG i false)
    (fun i => endpoint G d.vertex hG i true)

private theorem rank_primalMatrix (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    (primalMatrix G hG d).rank + 1 = Fintype.card (Vertex G d.vertex) :=
  Matrix.rank_endpointIncidence_add_one _ _ (rootVertex G hG d)
    (component_constant G hG d)

private noncomputable def dualEndpoint {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G)
    (i : Edge G d.vertex) (b : Bool) :
    Vertex r.dualGraph (r.dualDartEquiv d).vertex :=
  endpoint r.dualGraph (r.dualDartEquiv d).vertex r.dualGraph_endpoints_declared
    (r.componentEdgeDualEquiv hG d i) b

private theorem dualEndpoint_val {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G)
    (i : Edge G d.vertex) (b : Bool) :
    (dualEndpoint r hG d i b).val = r.faceId (i.val, b) := by
  change (r.dualDartEquiv (i.val, b)).vertex = _
  exact r.vertex_dualDartEquiv _

private noncomputable def dualMatrix {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    Matrix (Vertex r.dualGraph (r.dualDartEquiv d).vertex) (Edge G d.vertex) (ZMod 2) :=
  Matrix.endpointIncidence (fun i => dualEndpoint r hG d i false)
    (fun i => dualEndpoint r hG d i true)

private theorem rank_dualMatrix {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    (dualMatrix r hG d).rank + 1 =
      Fintype.card (Vertex r.dualGraph (r.dualDartEquiv d).vertex) := by
  apply Matrix.rank_endpointIncidence_add_one _ _
    (rootVertex r.dualGraph r.dualGraph_endpoints_declared (r.dualDartEquiv d))
  intro s hs
  apply component_constant r.dualGraph r.dualGraph_endpoints_declared (r.dualDartEquiv d) s
  intro i
  obtain ⟨i, rfl⟩ := (r.componentEdgeDualEquiv hG d).surjective i
  exact hs i

private theorem dualMatrix_mulVec_sum {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G)
    (x : Fin G.2.length → ZMod 2)
    (v : Vertex r.dualGraph (r.dualDartEquiv d).vertex) :
    (dualMatrix r hG d).mulVec (fun i => x i.val) v =
      ∑ a : Dart G, if r.faceId a = v.val then x a.1 else 0 := by
  have hmem (i : Fin G.2.length) (b : Bool) (h : r.faceId (i, b) = v.val) :
      i ∈ G.componentEdgeSet d.vertex := by
    apply (mem_componentEdgeSet_iff d.vertex hG i b).mpr
    apply (mem_componentVertexSet_dart _ hG _).mpr
    apply (r.sameComponent_dual_iff hG d (i, b)).mp
    apply (mem_componentVertexSet_dart _ r.dualGraph_endpoints_declared _).mp
    rw [r.vertex_dualDartEquiv (i, b), h]
    exact v.property
  have hsum (b : Bool) :
      (∑ i ∈ G.componentEdgeSet d.vertex,
        if r.faceId (i, b) = v.val then x i else 0) =
        ∑ i : Fin G.2.length, if r.faceId (i, b) = v.val then x i else 0 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn : r.faceId (i, b) ≠ v.val := fun h => hi (hmem i b h)
    simp only [hn, ite_false]
  have heq (i : Edge G d.vertex) (b : Bool) :
      v = dualEndpoint r hG d i b ↔ r.faceId (i.val, b) = v.val := by
    rw [Subtype.ext_iff, dualEndpoint_val, eq_comm]
  calc
    (dualMatrix r hG d).mulVec (fun i => x i.val) v =
        (∑ i : Edge G d.vertex, if r.faceId (i.val, false) = v.val then x i.val else 0) +
        ∑ i : Edge G d.vertex, if r.faceId (i.val, true) = v.val then x i.val else 0 := by
      simp only [dualMatrix, Matrix.endpointIncidence, Matrix.mulVec, dotProduct,
        add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, heq]
    _ = (∑ i ∈ G.componentEdgeSet d.vertex,
          if r.faceId (i, false) = v.val then x i else 0) +
        ∑ i ∈ G.componentEdgeSet d.vertex,
          if r.faceId (i, true) = v.val then x i else 0 := by
      exact congrArg₂ (· + ·)
        (Finset.sum_coe_sort (G.componentEdgeSet d.vertex)
          (fun i => if r.faceId (i, false) = v.val then x i else 0))
        (Finset.sum_coe_sort (G.componentEdgeSet d.vertex)
          (fun i => if r.faceId (i, true) = v.val then x i else 0))
    _ = (∑ i : Fin G.2.length, if r.faceId (i, false) = v.val then x i else 0) +
        ∑ i : Fin G.2.length, if r.faceId (i, true) = v.val then x i else 0 := by
      rw [hsum false, hsum true]
    _ = ∑ a : Dart G, if r.faceId a = v.val then x a.1 else 0 := by
      simp only [Dart, Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
      exact add_comm _ _

private theorem dualMatrix_mulVec_bit {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G)
    (x : Fin G.2.length → Bool)
    (v : Vertex r.dualGraph (r.dualDartEquiv d).vertex) (a : Dart G)
    (ha : r.faceId a = v.val) :
    (dualMatrix r hG d).mulVec (fun i => BitString.bitEquiv.symm (x i.val)) v =
      BitString.bitEquiv.symm (r.faceParity x (Quotient.mk _ a)) := by
  rw [dualMatrix_mulVec_sum r hG d (fun i => BitString.bitEquiv.symm (x i)) v,
    r.faceParity_eq_sum_faceId, map_sum]
  simp only [apply_ite, map_zero, ha]

private theorem primalMatrix_gradient (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G)
    (s : Vertex G d.vertex → ZMod 2) (i : Edge G d.vertex) :
    (primalMatrix G hG d).transpose.mulVec s i =
      BitString.bitEquiv.symm
        (G.edgeGradient (fun v => BitString.bitEquiv (extend G d.vertex s v)) i.val) := by
  rw [primalMatrix, Matrix.endpointIncidence_transpose_mulVec]
  apply BitString.bitEquiv.injective
  simp only [map_add, RingEquiv.apply_symm_apply, edgeGradient, ← Bool.add_eq_xor]
  rw [extend_endpoint G d.vertex hG s i false, extend_endpoint G d.vertex hG s i true]

private theorem matrix_product_zero {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    dualMatrix r hG d * (primalMatrix G hG d).transpose = 0 := by
  classical
  apply Matrix.mulVec_injective
  funext s v
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, Pi.zero_apply]
  have hv := List.mem_toFinset.mp (Finset.mem_filter.mp v.property).1
  obtain ⟨a, ha⟩ := r.dualGraph_no_isolates v.val hv
  obtain ⟨a, rfl⟩ := r.dualDartEquiv.surjective a
  have hvec := funext (primalMatrix_gradient G hG d s)
  rw [hvec, dualMatrix_mulVec_bit r hG d _ v a
    (by simpa only [vertex_dualDartEquiv] using ha)]
  rw [r.faceEven_edgeGradient]
  rfl

/-- The actual vertices and face cycles of an incident component satisfy the Euler bound.
This elementary consequence of the primal and dual incidence ranks needs neither numerical
genus zero nor global connectedness. The supplied dart selects an incident component; this
statement does not apply to isolated points or assert a geometric realization. -/
theorem component_euler_le {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    (G.componentVertexSet d.vertex).card + (r.componentFaceIndices d.vertex).card ≤
      (G.componentEdgeSet d.vertex).card + 2 := by
  classical
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero (matrix_product_zero r hG d)
  rw [Matrix.rank_transpose] at h
  have hp := rank_primalMatrix G hG d
  have hd := rank_dualMatrix r hG d
  rw [r.card_component_faces_eq_dual_vertices hG]
  simp only [Vertex, Edge, Fintype.card_coe] at h hp hd
  omega

/-- Every face-even assignment lifts on each edge component, with all rank and dimension
ingredients discharged internally from existing reachability and componentwise Euler. -/
theorem exists_vertexSpins_on_component {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    (x : Fin G.2.length → Bool) (hx : r.FaceEven x) (d : Dart G) :
    ∃ spin : ℕ → Bool, ∀ i ∈ G.componentEdgeSet d.vertex, G.edgeGradient spin i = x i := by
  classical
  have heuler := (r.numericalGenusZero_iff_component_cards hG).mp hgenus d
  rw [r.card_component_faces_eq_dual_vertices hG] at heuler
  have heq := Matrix.range_transpose_eq_ker_of_euler (primalMatrix G hG d)
    (dualMatrix r hG d) (matrix_product_zero r hG d)
    (rank_primalMatrix G hG d) (rank_dualMatrix r hG d)
    (by simpa only [Vertex, Edge, Fintype.card_coe] using heuler)
  have hk : (fun i : Edge G d.vertex => BitString.bitEquiv.symm (x i.val)) ∈
      (dualMatrix r hG d).mulVecLin.ker := by
    rw [LinearMap.mem_ker]
    funext v
    have hv := List.mem_toFinset.mp (Finset.mem_filter.mp v.property).1
    obtain ⟨a, ha⟩ := r.dualGraph_no_isolates v.val hv
    obtain ⟨a, rfl⟩ := r.dualDartEquiv.surjective a
    rw [Matrix.mulVecLin_apply, dualMatrix_mulVec_bit r hG d x v a
      (by simpa only [vertex_dualDartEquiv] using ha), hx]
    rfl
  rw [← heq] at hk
  obtain ⟨s, hs⟩ := hk
  refine ⟨fun v => BitString.bitEquiv (extend G d.vertex s v), ?_⟩
  intro i hi
  apply BitString.bitEquiv.symm.injective
  exact (primalMatrix_gradient G hG d s ⟨i, hi⟩).symm.trans (congrFun hs ⟨i, hi⟩)

private noncomputable def chosenVertex (G : Graph) (c : G.induced.ConnectedComponent) :
    {v // v ∈ G.1} :=
  (Quot.exists_rep c).choose

private theorem chosenVertex_spec (G : Graph) (c : G.induced.ConnectedComponent) :
    G.induced.connectedComponentMk (chosenVertex G c) = c :=
  (Quot.exists_rep c).choose_spec

private noncomputable def componentSpin {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    (x : Fin G.2.length → Bool) (hx : r.FaceEven x) (c : G.induced.ConnectedComponent) :
    ℕ → Bool :=
  if h : ∃ d : Dart G, d.vertex = (chosenVertex G c).val then
    (r.exists_vertexSpins_on_component hG hgenus x hx h.choose).choose
  else fun _ => false

private theorem componentSpin_correct {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    (x : Fin G.2.length → Bool) (hx : r.FaceEven x) (c : G.induced.ConnectedComponent)
    (h : ∃ d : Dart G, d.vertex = (chosenVertex G c).val)
    (i : Fin G.2.length) (hi : i ∈ G.componentEdgeSet (chosenVertex G c).val) :
    G.edgeGradient (componentSpin r hG hgenus x hx c) i = x i := by
  rw [componentSpin, dite_eq_left h]
  apply (r.exists_vertexSpins_on_component hG hgenus x hx h.choose).choose_spec
  rwa [h.choose_spec]

/-- Every face-even assignment on a componentwise numerically genus-zero indexed rotation
lifts to spins on the original natural-number names. Components are solved independently;
isolated declared points and names outside the graph may be assigned `false`. -/
theorem exists_vertexSpins_of_faceEven {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    (x : Fin G.2.length → Bool) (hx : r.FaceEven x) :
    ∃ spin : ℕ → Bool, G.edgeGradient spin = x := by
  let spin (v : ℕ) : Bool :=
    if hv : v ∈ G.1 then
      componentSpin r hG hgenus x hx (G.induced.connectedComponentMk ⟨v, hv⟩) v
    else false
  refine ⟨spin, funext fun i => ?_⟩
  let u := Dart.vertex (G := G) (i, false)
  let v := Dart.vertex (G := G) (i, true)
  have hu : u ∈ G.1 := vertex_mem hG (i, false)
  have hv : v ∈ G.1 := vertex_mem hG (i, true)
  let c := G.induced.connectedComponentMk ⟨u, hu⟩
  have hcomp : RotationCertificate.SameComponent G u v := sameComponent_reverse hG (i, false)
  have hcc : c = G.induced.connectedComponentMk ⟨v, hv⟩ :=
    SimpleGraph.ConnectedComponent.sound hcomp.2.2
  have hroot : RotationCertificate.SameComponent G u (chosenVertex G c).val :=
    ⟨hu, (chosenVertex G c).property,
      SimpleGraph.ConnectedComponent.exact (chosenVertex_spec G c).symm⟩
  have hinc := Dart.exists_of_sameComponent ((i, false) : Dart G)
    (chosenVertex G c).val hroot
  have hi : i ∈ G.componentEdgeSet (chosenVertex G c).val := by
    apply (mem_componentEdgeSet_iff _ hG i false).mpr
    exact (mem_componentVertexSet_dart _ hG _).mpr hroot.symm
  have he := componentSpin_correct r hG hgenus x hx c hinc i hi
  have hsU : spin u = componentSpin r hG hgenus x hx c u := by
    simp only [spin, dite_eq_left hu, c]
  have hsV : spin v = componentSpin r hG hgenus x hx c v := by
    simp only [spin, dite_eq_left hv, ← hcc]
  change (spin u ^^ spin v) = x i
  rw [hsU, hsV]
  exact he

/-- Face parity characterizes vertex gradients for arbitrary finite listed graphs under the
existing componentwise numerical genus-zero predicate. The endpoint-declaration hypothesis
is explicit. Loops, parallel occurrences, disconnected components, points, duplicate vertex
declarations, and sparse natural-number names are all retained. The converse needs no genus
assumption; see `faceEven_edgeGradient`. -/
theorem faceEven_iff_exists_vertexSpins {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    (x : Fin G.2.length → Bool) :
    r.FaceEven x ↔ ∃ spin : ℕ → Bool, G.edgeGradient spin = x := by
  constructor
  · exact r.exists_vertexSpins_of_faceEven hG hgenus x
  · rintro ⟨spin, rfl⟩
    exact r.faceEven_edgeGradient spin

end Cslib.Complexity.Graph.RotationSystem
