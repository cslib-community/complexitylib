/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Parity
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native frozen parity-query computation

Every certificate covers all raw inputs. Unary ranges are funded only by actual vertex/edge
list lengths. All supplied endpoint/dart labels use binary comparisons and saturating binary
lookup, including malformed huge indices. The concrete query composes the sparse compiler with
`XORSAT.computableInPolyTime_solve`; there is no solver, recognizer, growth or encoding provider
hypothesis.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.query_polyTime`: native all-raw algebraic query.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

private theorem read_polyTime {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    (fallback : β) {table : α → List β} {index : α → ℕ}
    (ht : ComputableInPolyTime table input (encList enc))
    (hi : ComputableInPolyTime index input encNat) :
    ComputableInPolyTime (fun x => (table x).getD (index x) fallback) input enc :=
  ComputableInPolyTime.listGetD_binary fallback ht hi

attribute [local fun_prop] read_polyTime

private theorem graph_polyTime :
    ComputableInPolyTime FixedRotationInput.graph encFixedRotationInput encGraph :=
  encFixedRotationInput_graph_deg.computableInPolyTime

private theorem orders_polyTime :
    ComputableInPolyTime FixedRotationInput.orders encFixedRotationInput
      (encList (encOption (encList encNat))) :=
  encFixedRotationInput_orders_deg.computableInPolyTime

attribute [local fun_prop] graph_polyTime orders_polyTime

private theorem vertices_polyTime : ComputableInPolyTime
    (fun I : FixedRotationInput => I.graph.vertices) encFixedRotationInput (encList encNat) :=
  encGraph_vertices_deg.computableInPolyTime.comp graph_polyTime

private theorem edges_polyTime : ComputableInPolyTime
    (fun I : FixedRotationInput => I.graph.edges) encFixedRotationInput
      (encList (encPair encNat encNat)) :=
  encGraph_edges_deg.computableInPolyTime.comp graph_polyTime

attribute [local fun_prop] vertices_polyTime edges_polyTime

private theorem vertexCount_polyTime : ComputableInPolyTime
    (fun I : FixedRotationInput => I.graph.vertices.length) encFixedRotationInput encUnary :=
  (ComputableInPolyTime.length_list encNat).comp vertices_polyTime

private theorem binaryVertexCount_polyTime : ComputableInPolyTime
    (fun I : FixedRotationInput => I.graph.vertices.length) encFixedRotationInput encNat :=
  ComputableInPolyTime.unary_to_binary.comp vertexCount_polyTime

attribute [local fun_prop] vertexCount_polyTime binaryVertexCount_polyTime

private theorem word_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × ℕ => (p.1.orders.getD p.2 none).getD [])
    (encPair encFixedRotationInput encNat) (encList encNat) := by
  apply ComputableInPolyTime.optionGetDWithInput
  · exact read_polyTime none (orders_polyTime.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  · exact ComputableInPolyTime.const []

attribute [local fun_prop] word_polyTime

private theorem frameCount_polyTime :
    ComputableInPolyTime Frame.vertexCount encFrame encUnary :=
  encFrame_vertexCount_deg.computableInPolyTime

private theorem frameSegments_polyTime :
    ComputableInPolyTime Frame.segments encFrame (encList encSegment) :=
  encFrame_segments_deg.computableInPolyTime

private theorem frameOrder_polyTime :
    ComputableInPolyTime Frame.order encFrame (encList encNat) :=
  encFrame_order_deg.computableInPolyTime

attribute [local fun_prop] frameCount_polyTime frameSegments_polyTime frameOrder_polyTime

/-- Binary-indexed endpoint fibers are computed from the actual edge count on all graphs. -/
theorem fiber_polyTime :
    ComputableInPolyTime (fun p : Graph × ℕ => fiber p.1 p.2)
      (encPair encGraph encNat) (encList encNat) := by
  have hinc := RotationCertificate.incidenceVertices_polyTime
  have hr : ComputableInPolyTime (fun p : Graph × ℕ => List.range (2 * p.1.edges.length))
      (encPair encGraph encNat) (encList encNat) :=
    RotationCertificate.range_binary.comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
          (encGraph_edges_polyTime (ComputableInPolyTime.fst encGraph encNat))))
  unfold fiber
  fun_prop

attribute [local fun_prop] fiber_polyTime

/-- The dense/full-order validator has no raw well-formedness premise. -/
theorem validate_polyTime : ComputableInPolyTime validate encFixedRotationInput encBool := by
  have hr : ComputableInPolyTime
      (fun I : FixedRotationInput => List.range I.graph.vertices.length)
      encFixedRotationInput (encList encNat) :=
    RotationCertificate.range_binary.comp vertexCount_polyTime
  unfold validate
  apply ComputableInPolyTime.bool_and'
  · apply ComputableInPolyTime.bool_and'
    · apply ComputableInPolyTime.bool_and'
      · fun_prop
      · apply ComputableInPolyTime.allWithInput
          (RotationCertificate.incidenceVertices_polyTime.comp graph_polyTime)
        exact ComputableInPolyTime.binary_lt' (ComputableInPolyTime.snd _ _)
          (binaryVertexCount_polyTime.comp (ComputableInPolyTime.fst _ _))
    · fun_prop
  · apply ComputableInPolyTime.allWithInput
      ((ComputableInPolyTime.zipIdx (encOption (encList encNat))).comp orders_polyTime)
    apply ComputableInPolyTime.optionElimWithInput (by fun_prop)
      (ComputableInPolyTime.const true)
    have hg : ComputableInPolyTime
        (fun p : (FixedRotationInput × (Option (List ℕ) × ℕ)) × List ℕ => p.1.1.graph)
        (encPair (encPair encFixedRotationInput (encPair (encOption (encList encNat)) encUnary))
          (encList encNat)) encGraph := by fun_prop
    have hi : ComputableInPolyTime
        (fun p : (FixedRotationInput × (Option (List ℕ) × ℕ)) × List ℕ => p.1.2.2)
        (encPair (encPair encFixedRotationInput (encPair (encOption (encList encNat)) encUnary))
          (encList encNat)) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    exact computableInPolyTime_enumeratesBool.comp
      ((fiber_polyTime.comp (hg.prod hi)).prod (ComputableInPolyTime.snd _ _))

/-- Twice subdivision preserves list occurrence identity and is native on every raw input. -/
theorem subdivide_polyTime :
    ComputableInPolyTime subdivide encFixedRotationInput (encList encSegment) := by
  unfold subdivide encSegment
  apply ComputableInPolyTime.flatMapWithInput
    (encA := encPair (encPair encNat encNat) encUnary)
    ((ComputableInPolyTime.zipIdx (encPair encNat encNat)).comp edges_polyTime)
  have ha : ComputableInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.graph.vertices.length + 2 * p.2.2)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary)) encNat :=
    (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_add'
        (vertexCount_polyTime.comp
          (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
          ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))))
  have hb : ComputableInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.graph.vertices.length + 2 * p.2.2 + 1)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary)) encNat :=
    ComputableInPolyTime.binary_add' ha (ComputableInPolyTime.const 1)
  have he : ComputableInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.2.1)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary))
      (encPair encNat encNat) := by fun_prop
  have ht : ComputableInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.orders)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary))
      (encList (encOption (encList encNat))) :=
    orders_polyTime.comp (ComputableInPolyTime.fst _ _)
  exact ComputableInPolyTime.cons'
    ((he.fst'.prod ha).prod (read_polyTime none ht he.fst').optionIsSome)
    (ComputableInPolyTime.cons'
      ((ha.prod hb).prod (ComputableInPolyTime.const false))
      (ComputableInPolyTime.cons'
        ((hb.prod he.snd').prod (read_polyTime none ht he.snd').optionIsSome)
        (ComputableInPolyTime.const [])))

/-- The full reference order is built from bounded list scans, including malformed words. -/
theorem referenceOrder_polyTime :
    ComputableInPolyTime referenceOrder encFixedRotationInput (encList encNat) := by
  have hblocks : ComputableInPolyTime centerBlocks encFixedRotationInput
      (encList encNat) := by
    have hr : ComputableInPolyTime
        (fun I : FixedRotationInput => List.range I.graph.vertices.length)
        encFixedRotationInput (encList encNat) :=
      RotationCertificate.range_binary.comp vertexCount_polyTime
    unfold centerBlocks
    apply ComputableInPolyTime.flatMapWithInput hr
    apply ComputableInPolyTime.cons'
      (ComputableInPolyTime.snd _ _)
    apply ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.listReverseWithInput word_polyTime)
    exact ComputableInPolyTime.binary_add'
      (binaryVertexCount_polyTime.comp
        ((ComputableInPolyTime.fst encFixedRotationInput encNat).comp
          (ComputableInPolyTime.fst (encPair encFixedRotationInput encNat) encNat)))
      (ComputableInPolyTime.snd (encPair encFixedRotationInput encNat) encNat)
  have hr : ComputableInPolyTime
      (fun I : FixedRotationInput => List.range (2 * I.graph.edges.length))
      encFixedRotationInput (encList encNat) :=
    RotationCertificate.range_binary.comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
          edges_polyTime))
  unfold referenceOrder
  apply ComputableInPolyTime.listAppend' hblocks
  apply ComputableInPolyTime.filterWithInput
    (ComputableInPolyTime.mapWithInput hr
      (ComputableInPolyTime.binary_add'
        (binaryVertexCount_polyTime.comp
          (ComputableInPolyTime.fst encFixedRotationInput encNat))
        (ComputableInPolyTime.snd encFixedRotationInput encNat)))
  apply ComputableInPolyTime.bool_not.comp
  apply ComputableInPolyTime.anyWithInput
    (hblocks.comp (ComputableInPolyTime.fst encFixedRotationInput encNat))
  exact ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.snd (encPair encFixedRotationInput encNat) encNat)
    ((ComputableInPolyTime.snd encFixedRotationInput encNat).comp
      (ComputableInPolyTime.fst (encPair encFixedRotationInput encNat) encNat))

/-- Frame construction is native, with its unary stride funded by actual list lengths. -/
theorem frame_polyTime : ComputableInPolyTime frame encFixedRotationInput encFrame := by
  have hs := subdivide_polyTime
  have ho := referenceOrder_polyTime
  have hn : ComputableInPolyTime subdivisionSize encFixedRotationInput encUnary := by
    unfold subdivisionSize
    exact (ComputableInPolyTime.unary_add' vertexCount_polyTime
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
          edges_polyTime)))
  exact (encFrame_mk_deg.computableInPolyTime.comp (hn.prod (hs.prod ho)))

private theorem independent_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (ℕ × ℕ) => independent p.1 p.2)
    (encPair (encPair encNat encNat) (encPair encNat encNat)) encBool := by
  unfold independent
  fun_prop

attribute [local fun_prop] independent_polyTime

private theorem moveLabels_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (Segment × (ℕ × ℕ)) => moveLabels p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encUnary encUnary) (encPair encSegment (encPair encNat encNat)))
    (encList encNat) := by
  unfold moveLabels moveLabel encSegment
  apply ComputableInPolyTime.ite' (by fun_prop)
    (ComputableInPolyTime.const [])
  apply ComputableInPolyTime.cons'
  · exact ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop)) (by fun_prop)
  · apply ComputableInPolyTime.cons'
    · exact ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.unary_to_binary.comp (by fun_prop)) (by fun_prop)
    · exact ComputableInPolyTime.const []

private theorem crossing_polyTime : ComputableInPolyTime
    (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => crossing p.1.1 p.1.2 p.2)
    (encPair (encPair (encList encNat) (encPair encNat encNat)) (encPair encNat encNat))
    encBool := by
  unfold crossing between
  fun_prop

attribute [local fun_prop] moveLabels_polyTime crossing_polyTime

private theorem row_polyTime :
    ComputableInPolyTime (fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
      row p.1.1 p.1.2 p.2)
      (encPair (encPair encFrame (encPair encSegment encUnary)) (encPair encSegment encUnary))
      (encAffineEquation encNat) := by
  unfold row
  refine ComputableInPolyTime.of_enc_eq (encMid := encPair (encList encNat) encBool)
    (f := fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
      ((row p.1.1 p.1.2 p.2).vars, (row p.1.1 p.1.2 p.2).rhs)) ?_ fun _ => rfl
  apply ComputableInPolyTime.prod
  · apply ComputableInPolyTime.listAppend'
    · exact moveLabels_polyTime.comp
        (g := fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
          ((p.1.1.vertexCount, p.1.2.2), (p.1.2.1, p.2.1.1)))
        (by unfold encSegment; fun_prop)
    · exact moveLabels_polyTime.comp
        (g := fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
          ((p.1.1.vertexCount, p.2.2), (p.2.1, p.1.2.1.1)))
        (by unfold encSegment; fun_prop)
  · exact crossing_polyTime.comp
      (g := fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
        ((p.1.1.order, p.1.2.1.1), p.2.1.1))
      (by unfold encSegment; fun_prop)

attribute [local fun_prop] row_polyTime

/-- Sparse row emission scans only segment occurrences, with width at most four. -/
theorem compileFrame_polyTime :
    ComputableInPolyTime compileFrame encFrame XORSAT.encoding := by
  unfold compileFrame XORSAT.encoding
  apply ComputableInPolyTime.flatMapWithInput
    ((ComputableInPolyTime.zipIdx encSegment).comp frameSegments_polyTime)
  apply ComputableInPolyTime.mapWithInput
  · apply ComputableInPolyTime.filterWithInput
      (((ComputableInPolyTime.zipIdx encSegment).comp frameSegments_polyTime).comp
        (ComputableInPolyTime.fst _ _))
    unfold encSegment
    fun_prop
  · exact row_polyTime

/-- The full graph/order-to-XOR compiler is an ordinary native polynomial-time function. -/
theorem compile_polyTime : ComputableInPolyTime compile encFixedRotationInput XORSAT.encoding :=
  compileFrame_polyTime.comp frame_polyTime

/-- Concrete all-raw native query. Invalid models reject, and every valid query actually calls
existing certified sparse Gaussian elimination. No topological criterion is used. -/
theorem query_polyTime : ComputableInPolyTime query encFixedRotationInput encBool :=
  validate_polyTime.bool_and' (XORSAT.computableInPolyTime_solve.comp compile_polyTime)

end Cslib.Complexity.Graph.RotationRecognition
