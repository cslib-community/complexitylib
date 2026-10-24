/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Preprocess.Programs
public import Complexity.Computability.PCP.Power.Complexity
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.PCP.Encoded.Constraints
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Executable powering after preprocessing

Every half-edge and supplied killed walk gives one edge. Its endpoint is computed by the same
rotation program as its constraint; the complete Boolean truth table is charged by the output
encoding. The input graph and its original constraints may be arbitrarily large. Walk length,
killing rate, degree and alphabet are fixed parameters of this transformation.

## Main definitions

* `Cslib.PCP.Encoded.Graph.powerPreprocess`: construct the complete powered graph.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_powerPreprocess`: uniform machine-backed construction.
* `Cslib.PCP.Encoded.Graph.length_edges_powerPreprocess`: exact edge count.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {C α D : Type}

/-- Killed-walk labels on the preprocessed regular graph. -/
abbrev PowerLabel (D : Type) (T q : ℕ) :=
  (Fin T → PreprocessLabel D) × (Fin T → Fin q)

/-- Each powered vertex holds an opinion about every walk of length at most `T`. -/
abbrev PowerAlphabet (D α : Type) (T : ℕ) := WalkLabels (PreprocessLabel D) T → α

/-- Construct one powered edge and its complete Boolean relation. -/
def powerPreprocessEdge [DecidableEq α] (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (g : Graph C) (dart : (ℕ × Bool) × PowerLabel D T q) :
    Edge (PowerAlphabet D α T → PowerAlphabet D α T → Bool) :=
  let rot := fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
    p.1.preprocessRotation fallback rotate p.2
  let rel := fun p : Graph C × (((ℕ × Bool) × PreprocessLabel D) × (α × α)) =>
    p.1.preprocessRelation eval fallback p.2.1 p.2.2.1 p.2.2.2
  ⟨halfEdgeNumber dart.1,
    halfEdgeNumber (RotationMap.killedPowRotWithInput rot T q (g, dart)).1,
    fun a b => RegularConstraintGraph.powerRelationWithInput rot rel T q (g, dart, a, b)⟩

/-- Enumerate every half-edge and supplied killed walk, computing endpoints and constraints. -/
def powerPreprocess [DecidableEq α] (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (walks : List (PowerLabel D T q)) (g : Graph C) :
    Graph (PowerAlphabet D α T → PowerAlphabet D α T → Bool) :=
  ⟨2 * g.edges.length,
    (g.halfEdges.product walks).map (g.powerPreprocessEdge eval fallback rotate T q)⟩

/-- Powering retains the preprocessed half-edge vertices. -/
@[simp]
theorem vertices_powerPreprocess [DecidableEq α] (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (walks : List (PowerLabel D T q)) (g : Graph C) :
    (g.powerPreprocess eval fallback rotate T q walks).vertices = 2 * g.edges.length := rfl

/-- Every original half-edge contributes one edge per supplied killed walk. -/
@[simp]
theorem length_edges_powerPreprocess [DecidableEq α] (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (walks : List (PowerLabel D T q)) (g : Graph C) :
    (g.powerPreprocess eval fallback rotate T q walks).edges.length =
      2 * g.edges.length * walks.length := by
  simp only [powerPreprocess, List.length_map]
  change (g.halfEdges ×ˢ walks).length = _
  rw [List.length_product, length_halfEdges]

/-- The ordered output occurrences are indexed by the mathematical killed-walk darts.
Mapping darts to stored edges preserves multiplicities, including equal constraints. -/
def powerPreprocessEnumeration [DecidableEq α] [DecidableEq D] (g : Graph C)
    (eval : C → α → α → Bool) (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
    (hwalks : walks.Nodup) (hmem : ∀ d, d ∈ walks) :
    List.Enumeration (g.powerPreprocess eval fallback rotate T q walks).edges
      (fun dart : (Fin g.edges.length × Bool) × PowerLabel D T q =>
        g.powerPreprocessEdge eval fallback rotate T q ((dart.1.1.val, dart.1.2), dart.2)) :=
  (g.halfEdgesEnumeration.prod (List.Enumeration.ofNodup walks hwalks hmem)).map
    (g.powerPreprocessEdge eval fallback rotate T q)

section Correctness

variable [DecidableEq α] (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
  (T q : ℕ) [NeZero q]

include hrotate in
/-- The executable destination is the numbered endpoint of the mathematical killed walk. -/
private theorem dst_powerPreprocessEdge
    (dart : (Fin g.edges.length × Bool) × PowerLabel D T q) :
    (g.powerPreprocessEdge eval fallback rotate T q
      ((dart.1.1.val, dart.1.2), dart.2)).dst =
      let next := ((g.regularPreprocess eval fallback family).power T q).graph.neighbor
        dart.1 dart.2
      halfEdgeNumber (next.1.val, next.2) := by
  exact congrArg (fun out => halfEdgeNumber out.1)
    (RotationMap.killedPowRotWithInput_eq
      (fun p => p.1.preprocessRotation fallback rotate p.2)
      g (g.regularPreprocess eval fallback family).graph (fun v => (v.1.val, v.2))
      (g.preprocessRotation_eq eval fallback family rotate hrotate) T q dart.1 dart.2.1 dart.2.2)

include hrotate in
/-- Each computed Boolean table is exactly the mathematical powered relation. -/
private theorem rel_powerPreprocessEdge
    (dart : (Fin g.edges.length × Bool) × PowerLabel D T q) (a b : PowerAlphabet D α T) :
    (g.powerPreprocessEdge eval fallback rotate T q
      ((dart.1.1.val, dart.1.2), dart.2)).constraint a b = true ↔
      ((g.regularPreprocess eval fallback family).power T q).rel dart a b := by
  exact RegularConstraintGraph.powerRelationWithInput_eq_true
    (fun p => p.1.preprocessRotation fallback rotate p.2)
    (fun p => p.1.preprocessRelation eval fallback p.2.1 p.2.2.1 p.2.2.2)
    g (g.regularPreprocess eval fallback family) (fun v => (v.1.val, v.2))
    (g.preprocessRotation_eq eval fallback family rotate hrotate)
    (g.preprocessRelation_eq_true eval fallback family) T q dart.1 dart.2.1 dart.2.2 a b

include hrotate in
/-- The full executable graph is the mathematical power, with exact vertex and edge numbering. -/
theorem toGraph_powerPreprocess [DecidableEq D] (walks : List (PowerLabel D T q))
    (hwalks : walks.Nodup) (hmem : ∀ d, d ∈ walks) :
    (g.powerPreprocess eval fallback rotate T q walks).toGraph id =
      (((g.regularPreprocess eval fallback family).power T q).toConstraintGraph.map
        (fun v => halfEdgeNumber (v.1.val, v.2))).comap
          (g.powerPreprocessEnumeration eval fallback rotate T q walks hwalks hmem).equiv := by
  apply toGraph_eq_comap _ _ (g.powerPreprocessEnumeration eval fallback rotate T q
    walks hwalks hmem)
  · intro dart; rfl
  · exact dst_powerPreprocessEdge g eval fallback family rotate hrotate T q
  · exact rel_powerPreprocessEdge g eval fallback family rotate hrotate T q

include hrotate in
/-- Every destination is a numbered half-edge; malformed original vertex bounds are irrelevant. -/
theorem wellFormed_powerPreprocess (walks : List (PowerLabel D T q)) :
    (g.powerPreprocess eval fallback rotate T q walks).WellFormed := by
  intro e he
  obtain ⟨⟨⟨i, side⟩, walk⟩, hp, rfl⟩ := List.mem_map.mp he
  have hi := (g.mem_halfEdges_iff _).mp (List.mem_product.mp hp).1
  constructor
  · exact halfEdgeNumber_lt hi
  · change (g.powerPreprocessEdge eval fallback rotate T q
      (((⟨i, hi⟩ : Fin g.edges.length).val, side), walk)).dst < _
    rw [dst_powerPreprocessEdge g eval fallback family rotate hrotate T q
      ((⟨i, hi⟩, side), walk)]
    exact halfEdgeNumber_lt (Fin.isLt _)

include hrotate in
/-- Exact numbering preserves the unsatisfied fraction of the complete powered graph. -/
theorem unsatVal_powerPreprocess [Nonempty α] [Fintype D]
    (walks : List (PowerLabel D T q)) (hwalks : walks.Nodup) (hmem : ∀ d, d ∈ walks) :
    ((g.powerPreprocess eval fallback rotate T q walks).toGraph id).unsatVal =
      ((g.regularPreprocess eval fallback family).power T q).toConstraintGraph.unsatVal := by
  classical
  rw [toGraph_powerPreprocess g eval fallback family rotate hrotate T q walks hwalks hmem,
    ConstraintGraph.unsatVal_comap_map_of_injective _ (halfEdgeNumber_fin_injective _)]

include hrotate in
/-- Exact numbering preserves satisfiability of the complete powered graph. -/
theorem satisfiable_powerPreprocess_iff [Nonempty α]
    (walks : List (PowerLabel D T q)) (hwalks : walks.Nodup) (hmem : ∀ d, d ∈ walks) :
    ((g.powerPreprocess eval fallback rotate T q walks).toGraph id).Satisfiable ↔
      ((g.regularPreprocess eval fallback family).power T q).toConstraintGraph.Satisfiable := by
  classical
  rw [toGraph_powerPreprocess g eval fallback family rotate hrotate T q walks hwalks hmem,
    ConstraintGraph.satisfiable_comap_map_iff _ (halfEdgeNumber_fin_injective _)
      (Equiv.surjective _)]

end Correctness

section Complexity

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool}

attribute [local fun_prop] ComputableInPolyTime.tidy in
private theorem polytime_powerPreprocessEdge (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ComputableTidilyInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (heval : ComputableTidilyInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (T q : ℕ) [NeZero q] :
    ComputableTidilyInPolyTime
      (fun p : Graph C × ((ℕ × Bool) × PowerLabel D T q) =>
        p.1.powerPreprocessEdge eval fallback rotate T q p.2)
      (encPair (encoding enc) (encPair (encPair encUnary encBool)
        (encPair (encPi (encFinite (PreprocessLabel D))) (encPi (encFinEnum (Fin q))))))
      (Edge.encoding (encPi (encPi encBool))) := by
  have hr : ComputableTidilyInPolyTime
      (fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
        p.1.preprocessRotation fallback rotate p.2)
      (encPair (encoding enc) (encPair (encPair encUnary encBool)
        (encFinite (PreprocessLabel D))))
      (encPair (encPair encUnary encBool) (encFinite (PreprocessLabel D))) :=
    ComputableInPolyTime.tidy (isPolyTime_preprocessRotation (.of_tidy (.fst _ _))
      (.of_tidy (.snd _ _)) (.of_tidy hrotate) fallback)
  have he : ComputableTidilyInPolyTime
      (fun p : Graph C × (((ℕ × Bool) × PreprocessLabel D) × (α × α)) =>
        p.1.preprocessRelation eval fallback p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encoding enc) (encPair
        (encPair (encPair encUnary encBool) (encFinite (PreprocessLabel D)))
        (encPair alphabet alphabet))) encBool :=
    ComputableInPolyTime.tidy (isPolyTime_preprocessRelation (.of_tidy (.fst _ _))
      (.of_tidy ((ComputableTidilyInPolyTime.snd _ _).fst')) (.of_tidy heval)
      (.of_tidy ((ComputableTidilyInPolyTime.snd _ _).snd'.fst'))
      (.of_tidy ((ComputableTidilyInPolyTime.snd _ _).snd'.snd')) fallback)
  have hwalk := rotationMap_killedPowRotWithInput hr T q (encFinEnum (Fin q))
  have hrel := (RegularConstraintGraph.isPolyTime_powerRelationWithInput
    (.of_tidy hr) (.of_tidy he) T q (encFinEnum (Fin q))).tidy
  unfold powerPreprocessEdge
  refine ComputableInPolyTime.tidy (Edge.isPolyTime_mk (.of_tidy ?_) (.of_tidy ?_) (.of_tidy ?_))
  · have := isPolyTime_halfEdgeNumber.tidy
    fun_prop
  · exact isPolyTime_halfEdgeNumber.tidy.comp hwalk.fst'
  · apply pi
    intro a
    apply pi
    intro b
    simpa only [RegularConstraintGraph.powerInputEncoding, Function.comp_def] using
      hrel.comp ((fst _ _).prod ((snd _ _).prod (const (a, b))))

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Construct the entire output truth tables, charging every rotation, constraint lookup,
opinion table, copied graph, edge record and list delimiter. All finite parameters are fixed. -/
private theorem polytime_powerPreprocess (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ComputableTidilyInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (heval : ComputableTidilyInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q)) :
    ComputableTidilyInPolyTime (powerPreprocess eval fallback rotate T q walks)
      (encoding enc) (encoding (encPi (encPi encBool))) := by
  have hedge := polytime_powerPreprocessEdge eval fallback rotate hrotate heval T q
  have hdarts : ComputableTidilyInPolyTime
      (fun g : Graph C => g.halfEdges.product walks) (encoding enc)
      (encList (encPair (encPair encUnary encBool)
        (encPair (encPi (encFinite (PreprocessLabel D))) (encPi (encFinEnum (Fin q)))))) := by
    have := (isPolyTime_halfEdges (enc := enc) (.of_tidy .id')).tidy
    unfold List.product
    fun_prop
  unfold powerPreprocess
  refine ComputableInPolyTime.tidy (isPolyTime_mk (.of_tidy ?_) (.of_tidy ?_))
  · have := (isPolyTime_edges (enc := enc) (.of_tidy .id')).tidy
    fun_prop
  exact mapWithInput hdarts hedge

omit [Fintype D] [Fintype α] [DecidableEq D] in
/-- The output descriptor encoding is arbitrary and fixed. Finite-table conversion hides the
internal enumeration, so matching an ordinary graph expression never unfolds that enumeration. -/
@[fun_prop]
theorem isPolyTime_powerPreprocess [Finite D] [Finite α] {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph C} {eval : C → α → α → Bool} {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (heval : ComputableInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (fallback : C) (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
    {output : (PowerAlphabet D α T → PowerAlphabet D α T → Bool) ↪ List Bool} :
    ComputableInPolyTime
      (fun x => (graph x).powerPreprocess eval fallback rotate T q walks)
      input (encoding output) := by
  have hgraph := hgraph.tidy
  have hrotate := hrotate.tidy
  have heval := heval.tidy
  refine .of_tidy ?_
  classical
  let _ := Fintype.ofFinite D
  let _ := Fintype.ofFinite α
  have hp := (polytime_powerPreprocess eval fallback rotate hrotate heval T q walks).comp hgraph
  have hconvert : ComputableTidilyInPolyTime
      (id : (PowerAlphabet D α T → PowerAlphabet D α T → Bool) → _)
      (encPi (encPi encBool)) output := .of_finite _
  simpa only [mapConstraints_id, Function.comp_def] using
    (isPolyTime_mapConstraints (.of_tidy hp) (.of_tidy hconvert)).tidy

end Complexity

end Cslib.PCP.Encoded.Graph
