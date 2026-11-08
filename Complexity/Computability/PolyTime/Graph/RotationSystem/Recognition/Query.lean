/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Parity
public import Complexity.Computability.PolyTime.Graph.RotationSystem
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native frozen parity-query computation

Every certificate covers all raw inputs. Unary ranges are funded only by actual vertex/edge
list lengths. All supplied endpoint/dart labels use binary comparisons and saturating binary
lookup, including malformed huge indices. The concrete query composes the sparse compiler with
`XORSAT.solve_polyTime`; there is no solver, recognizer, growth or encoding provider hypothesis.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.query_polyTime`: native all-raw algebraic query.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

private theorem read_polyTime {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    (fallback : β) {table : α → List β} {index : α → ℕ}
    (ht : ComputableTidilyInPolyTime table input (encList enc))
    (hi : ComputableTidilyInPolyTime index input encNat) :
    ComputableTidilyInPolyTime (fun x => (table x).getD (index x) fallback) input enc :=
  ComputableTidilyInPolyTime.listGetD_binary fallback ht hi

attribute [local fun_prop] read_polyTime

private theorem range_binary :
    ComputableTidilyInPolyTime List.range encUnary (encList encNat) := by
  simpa using (ComputableTidilyInPolyTime.map
    ComputableTidilyInPolyTime.unary_to_binary).comp ComputableTidilyInPolyTime.range

private theorem graph_polyTime :
    ComputableTidilyInPolyTime FixedRotationInput.graph encFixedRotationInput encGraph :=
  encFixedRotationInput_graph_deg.computableInPolyTime.tidy

private theorem orders_polyTime :
    ComputableTidilyInPolyTime FixedRotationInput.orders encFixedRotationInput
      (encList (encOption (encList encNat))) :=
  encFixedRotationInput_orders_deg.computableInPolyTime.tidy

attribute [local fun_prop] graph_polyTime orders_polyTime

private theorem vertices_polyTime : ComputableTidilyInPolyTime
    (fun I : FixedRotationInput => I.graph.1) encFixedRotationInput (encList encNat) :=
  (ComputableTidilyInPolyTime.fst _ _).comp graph_polyTime

private theorem edges_polyTime : ComputableTidilyInPolyTime
    (fun I : FixedRotationInput => I.graph.2) encFixedRotationInput
      (encList (encPair encNat encNat)) :=
  (ComputableTidilyInPolyTime.snd _ _).comp graph_polyTime

attribute [local fun_prop] vertices_polyTime edges_polyTime

private theorem vertexCount_polyTime : ComputableTidilyInPolyTime
    (fun I : FixedRotationInput => I.graph.1.length) encFixedRotationInput encUnary :=
  (ComputableTidilyInPolyTime.length_list encNat).comp vertices_polyTime

private theorem binaryVertexCount_polyTime : ComputableTidilyInPolyTime
    (fun I : FixedRotationInput => I.graph.1.length) encFixedRotationInput encNat :=
  ComputableTidilyInPolyTime.unary_to_binary.comp vertexCount_polyTime

attribute [local fun_prop] vertexCount_polyTime binaryVertexCount_polyTime

private theorem word_polyTime : ComputableTidilyInPolyTime
    (fun p : FixedRotationInput × ℕ => (p.1.orders.getD p.2 none).getD [])
    (encPair encFixedRotationInput encNat) (encList encNat) := by
  apply ComputableTidilyInPolyTime.optionGetDWithInput
  · exact read_polyTime none (orders_polyTime.comp (ComputableTidilyInPolyTime.fst _ _))
      (ComputableTidilyInPolyTime.snd _ _)
  · exact ComputableTidilyInPolyTime.const []

attribute [local fun_prop] word_polyTime

private theorem frameCount_polyTime :
    ComputableTidilyInPolyTime Frame.vertexCount encFrame encUnary :=
  encFrame_vertexCount_deg.computableInPolyTime.tidy

private theorem frameSegments_polyTime :
    ComputableTidilyInPolyTime Frame.segments encFrame (encList encSegment) :=
  encFrame_segments_deg.computableInPolyTime.tidy

private theorem frameOrder_polyTime :
    ComputableTidilyInPolyTime Frame.order encFrame (encList encNat) :=
  encFrame_order_deg.computableInPolyTime.tidy

attribute [local fun_prop] frameCount_polyTime frameSegments_polyTime frameOrder_polyTime

private theorem incidenceVertices_polyTime :
    ComputableTidilyInPolyTime incidenceVertices encGraph (encList encNat) := by
  unfold incidenceVertices encGraph
  fun_prop

attribute [local fun_prop] incidenceVertices_polyTime

/-- Binary-indexed endpoint fibers are computed from the actual edge count on all graphs. -/
theorem fiber_polyTime :
    ComputableInPolyTime (fun p : Graph × ℕ => fiber p.1 p.2)
      (encPair encGraph encNat) (encList encNat) := by
  apply ComputableInPolyTime.of_tidy
  have hr : ComputableTidilyInPolyTime (fun p : Graph × ℕ => List.range (2 * p.1.2.length))
      (encPair encGraph encNat) (encList encNat) :=
    range_binary.comp (by unfold encGraph; fun_prop)
  unfold fiber
  fun_prop

attribute [local fun_prop] fiber_polyTime

/-- The dense/full-order validator has no raw well-formedness premise. -/
theorem validate_polyTime : ComputableInPolyTime validate encFixedRotationInput encBool := by
  apply ComputableInPolyTime.of_tidy
  have hr : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => List.range I.graph.1.length)
      encFixedRotationInput (encList encNat) :=
    range_binary.comp (by fun_prop)
  unfold validate
  apply ComputableTidilyInPolyTime.bool_and'
  · apply ComputableTidilyInPolyTime.bool_and'
    · apply ComputableTidilyInPolyTime.bool_and'
      · fun_prop
      · apply ComputableTidilyInPolyTime.allWithInput
          (incidenceVertices_polyTime.comp graph_polyTime)
        exact ComputableTidilyInPolyTime.binary_lt' (ComputableTidilyInPolyTime.snd _ _)
          (binaryVertexCount_polyTime.comp (ComputableTidilyInPolyTime.fst _ _))
    · fun_prop
  · apply ComputableTidilyInPolyTime.allWithInput
      ((ComputableTidilyInPolyTime.zipIdx (encOption (encList encNat))).comp orders_polyTime)
    apply ComputableTidilyInPolyTime.optionElimWithInput (by fun_prop)
      (ComputableTidilyInPolyTime.const true)
    have hg : ComputableTidilyInPolyTime
        (fun p : (FixedRotationInput × (Option (List ℕ) × ℕ)) × List ℕ => p.1.1.graph)
        (encPair (encPair encFixedRotationInput (encPair (encOption (encList encNat)) encUnary))
          (encList encNat)) encGraph := by fun_prop
    have hi : ComputableTidilyInPolyTime
        (fun p : (FixedRotationInput × (Option (List ℕ) × ℕ)) × List ℕ => p.1.2.2)
        (encPair (encPair encFixedRotationInput (encPair (encOption (encList encNat)) encUnary))
          (encList encNat)) encNat :=
      ComputableTidilyInPolyTime.unary_to_binary.comp (by fun_prop)
    exact computableInPolyTime_enumeratesBool.tidy.comp
      ((fiber_polyTime.tidy.comp (hg.prod hi)).prod (ComputableTidilyInPolyTime.snd _ _))

/-- Twice subdivision preserves list occurrence identity and is native on every raw input. -/
theorem subdivide_polyTime :
    ComputableInPolyTime subdivide encFixedRotationInput (encList encSegment) := by
  apply ComputableInPolyTime.of_tidy
  unfold subdivide encSegment
  apply ComputableTidilyInPolyTime.flatMapWithInput
    (encA := encPair (encPair encNat encNat) encUnary)
    ((ComputableTidilyInPolyTime.zipIdx (encPair encNat encNat)).comp edges_polyTime)
  have ha : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.graph.1.length + 2 * p.2.2)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary)) encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp (by fun_prop)
  have hb : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.graph.1.length + 2 * p.2.2 + 1)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary)) encNat :=
    ComputableTidilyInPolyTime.binary_add' ha (ComputableTidilyInPolyTime.const 1)
  have he : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.2.1)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary))
      (encPair encNat encNat) := by fun_prop
  have ht : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.orders)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary))
      (encList (encOption (encList encNat))) :=
    orders_polyTime.comp (ComputableTidilyInPolyTime.fst _ _)
  exact ComputableTidilyInPolyTime.cons'
    ((he.fst'.prod ha).prod (read_polyTime none ht he.fst').optionIsSome)
    (ComputableTidilyInPolyTime.cons'
      ((ha.prod hb).prod (ComputableTidilyInPolyTime.const false))
      (ComputableTidilyInPolyTime.cons'
        ((hb.prod he.snd').prod (read_polyTime none ht he.snd').optionIsSome)
        (ComputableTidilyInPolyTime.const [])))

/-- The full reference order is built from bounded list scans, including malformed words. -/
theorem referenceOrder_polyTime :
    ComputableInPolyTime referenceOrder encFixedRotationInput (encList encNat) := by
  apply ComputableInPolyTime.of_tidy
  have hblocks : ComputableTidilyInPolyTime centerBlocks encFixedRotationInput
      (encList encNat) := by
    have hr : ComputableTidilyInPolyTime
        (fun I : FixedRotationInput => List.range I.graph.1.length)
        encFixedRotationInput (encList encNat) :=
      range_binary.comp (by fun_prop)
    unfold centerBlocks
    apply ComputableTidilyInPolyTime.flatMapWithInput hr
    apply ComputableTidilyInPolyTime.cons'
      (ComputableTidilyInPolyTime.snd _ _)
    apply ComputableTidilyInPolyTime.mapWithInput
      ((ComputableTidilyInPolyTime.listReverse encNat).comp word_polyTime)
    exact ComputableTidilyInPolyTime.binary_add'
      (binaryVertexCount_polyTime.comp (by fun_prop)) (ComputableTidilyInPolyTime.snd _ _)
  have hr : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => List.range (2 * I.graph.2.length))
      encFixedRotationInput (encList encNat) :=
    range_binary.comp (by fun_prop)
  unfold referenceOrder
  fun_prop

/-- Frame construction is native, with its unary stride funded by actual list lengths. -/
theorem frame_polyTime : ComputableInPolyTime frame encFixedRotationInput encFrame := by
  have hs := subdivide_polyTime.tidy
  have ho := referenceOrder_polyTime.tidy
  have hn : ComputableTidilyInPolyTime subdivisionSize encFixedRotationInput encUnary := by
    unfold subdivisionSize
    fun_prop
  exact .of_tidy (encFrame_mk_deg.computableInPolyTime.tidy.comp (hn.prod (hs.prod ho)))

private theorem independent_polyTime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × (ℕ × ℕ) => independent p.1 p.2)
    (encPair (encPair encNat encNat) (encPair encNat encNat)) encBool := by
  unfold independent
  fun_prop

attribute [local fun_prop] independent_polyTime

private theorem moveLabels_polyTime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × (Segment × (ℕ × ℕ)) => moveLabels p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encUnary encUnary) (encPair encSegment (encPair encNat encNat)))
    (encList encNat) := by
  unfold moveLabels moveLabel encSegment
  apply ComputableTidilyInPolyTime.ite' (by fun_prop)
    (ComputableTidilyInPolyTime.const [])
  apply ComputableTidilyInPolyTime.cons'
  · exact ComputableTidilyInPolyTime.binary_add'
      (ComputableTidilyInPolyTime.unary_to_binary.comp (by fun_prop)) (by fun_prop)
  · apply ComputableTidilyInPolyTime.cons'
    · exact ComputableTidilyInPolyTime.binary_add'
        (ComputableTidilyInPolyTime.unary_to_binary.comp (by fun_prop)) (by fun_prop)
    · exact ComputableTidilyInPolyTime.const []

private theorem crossing_polyTime : ComputableTidilyInPolyTime
    (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => crossing p.1.1 p.1.2 p.2)
    (encPair (encPair (encList encNat) (encPair encNat encNat)) (encPair encNat encNat))
    encBool := by
  unfold crossing between
  fun_prop

attribute [local fun_prop] moveLabels_polyTime crossing_polyTime

private theorem row_polyTime :
    ComputableTidilyInPolyTime (fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
      row p.1.1 p.1.2 p.2)
      (encPair (encPair encFrame (encPair encSegment encUnary)) (encPair encSegment encUnary))
      XORSAT.equationEncoding := by
  unfold row XORSAT.equationEncoding
  apply ComputableTidilyInPolyTime.prod
  · apply ComputableTidilyInPolyTime.listAppend'
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
  apply ComputableInPolyTime.of_tidy
  unfold compileFrame XORSAT.encoding
  apply ComputableTidilyInPolyTime.flatMapWithInput
    ((ComputableTidilyInPolyTime.zipIdx encSegment).comp frameSegments_polyTime)
  apply ComputableTidilyInPolyTime.mapWithInput
  · apply ComputableTidilyInPolyTime.filterWithInput
      (((ComputableTidilyInPolyTime.zipIdx encSegment).comp frameSegments_polyTime).comp
        (ComputableTidilyInPolyTime.fst _ _))
    unfold encSegment
    fun_prop
  · exact row_polyTime

/-- The full graph/order-to-XOR compiler is an ordinary native polynomial-time function. -/
theorem compile_polyTime : ComputableInPolyTime compile encFixedRotationInput XORSAT.encoding :=
  compileFrame_polyTime.comp frame_polyTime

/-- Concrete all-raw native query. Invalid models reject, and every valid query actually calls
existing certified sparse Gaussian elimination. No topological criterion is used. -/
theorem query_polyTime : ComputableInPolyTime query encFixedRotationInput encBool :=
  validate_polyTime.bool_and' (XORSAT.solve_polyTime.comp compile_polyTime)

end Cslib.Complexity.Graph.RotationRecognition
