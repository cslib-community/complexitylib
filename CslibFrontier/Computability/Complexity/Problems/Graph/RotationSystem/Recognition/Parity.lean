/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Input
public import CslibFrontier.Computability.Complexity.Problems.XORSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Finite frozen-edge parity queries

Each listed edge is replaced by three indexed segments through two fresh subdivision vertices.
A completely prescribed original vertex freezes every incident first/last segment; the middle
segments remain movable. The reference order lists each center followed by its selected leaves
in reverse clockwise order, then the remaining subdivision points. Crossing bits use strict
endpoint interleaving in that order. Independent unordered segment pairs contribute sparse XOR
rows, with all frozen-edge move variables omitted.

This is a finite specialization of the equations in [MarcusSchaefer2013Planarity], Sections
5.3–5.4, printed pp. 399–401. `row_holds_iff` and `query_eq_true_iff` prove their literal Boolean
meaning using the existing native XOR solver. They assert no geometric or numerical feasibility
criterion. The proposed full-rotation application of [FulekKynclPalvolgyi2017], Theorem 1, p. 2,
and the necessary drawing/parity bridges remain separate mathematical obligations.

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.subdivide`: twice subdivision with frozen flags.
* `Cslib.Complexity.Graph.RotationRecognition.compile`: sparse independent-edge equations.
* `Cslib.Complexity.Graph.RotationRecognition.query`: validate, compile and call `XORSAT.solve`.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM Cslib.Logic.PL

/-- A segment retains its two endpoints and whether edge/vertex moves of this edge are frozen. -/
abbrev Segment := (ℕ × ℕ) × Bool

/-- The ordered endpoint pair of a subdivision segment. -/
abbrev Segment.endpoints (segment : Segment) : ℕ × ℕ := segment.1

/-- The source vertex of a subdivision segment. -/
abbrev Segment.source (segment : Segment) : ℕ := segment.endpoints.1

/-- The target vertex of a subdivision segment. -/
abbrev Segment.target (segment : Segment) : ℕ := segment.endpoints.2

/-- Whether edge/vertex moves of this subdivision segment are frozen. -/
abbrev Segment.frozen (segment : Segment) : Bool := segment.2

/-- Two binary endpoints, framed together, then the frozen bit. -/
abbrev encSegment := encPair (encPair encNat encNat) encBool

/-- The total subdivided vertex count; only actual list lengths fund this unary count. -/
@[expose] def subdivisionSize (I : FixedRotationInput) : ℕ :=
  I.graph.1.length + 2 * I.graph.2.length

/-- Replace edge `e=(u,v)` by `u--a_e--b_e--v`, retaining all occurrence indices. A fixed endpoint
freezes its entire first/last segment. Even loops and parallel edges get distinct fresh points. -/
@[expose] def subdivide (I : FixedRotationInput) : List Segment :=
  I.graph.2.zipIdx.flatMap fun ((source, target), index) =>
    let a := I.graph.1.length + 2 * index
    let b := a + 1
    [((source, a), (I.orders.getD source none).isSome),
      ((a, b), false), ((b, target), (I.orders.getD target none).isSome)]

/-- Existing listed graph underlying the twice subdivision. -/
@[expose] def subdivisionGraph (I : FixedRotationInput) : Graph :=
  (List.range (subdivisionSize I), (subdivide I).map fun e => e.1)

/-- Center blocks with leaves in reverse prescribed clockwise order. A binary dart index `d`
names precisely subdivision point `n+d`, including the two separate ends of an original loop. -/
@[expose] def centerBlocks (I : FixedRotationInput) : List ℕ :=
  (List.range I.graph.1.length).flatMap fun v =>
    v :: (((I.orders.getD v none).getD []).reverse.map fun d => I.graph.1.length + d)

/-- Append subdivision points not already selected into a center block. -/
@[expose] def referenceOrder (I : FixedRotationInput) : List ℕ :=
  centerBlocks I ++ ((List.range (2 * I.graph.2.length)).map
    (fun d => I.graph.1.length + d)).filter fun v =>
      !(centerBlocks I).any fun w => decide (w = v)

/-- Finite algebraic frame. The count is unary; endpoint labels and reference ranks are binary. -/
structure Frame where
  /-- Declared number of vertices, used as the move-label stride. -/
  vertexCount : ℕ
  /-- Segment records, including the frozen flags. -/
  segments : List Segment
  /-- Reference vertex order. -/
  order : List ℕ
  deriving DecidableEq, Repr

/-- Unary stride, then framed binary segments and framed binary reference order. -/
enc_structure encFrame : Frame where
  vertexCount : encUnary, segments : (encList encSegment), order : (encList encNat)

/-- Concrete frame compiled from the raw existing graph and fixed orders. -/
@[expose] def frame (I : FixedRotationInput) : Frame :=
  ⟨subdivisionSize I, subdivide I, referenceOrder I⟩

/-- Independent endpoints; no equation is emitted for a pair sharing a vertex. -/
@[expose] def independent (e f : ℕ × ℕ) : Bool :=
  decide (e.1 ≠ f.1) && decide (e.1 ≠ f.2) &&
    decide (e.2 ≠ f.1) && decide (e.2 ≠ f.2)

/-- Strict interval membership of the reference rank of a vertex. -/
@[expose] def between (order : List ℕ) (e : ℕ × ℕ) (v : ℕ) : Bool :=
  decide (min (order.idxOf e.1) (order.idxOf e.2) < order.idxOf v) &&
    decide (order.idxOf v < max (order.idxOf e.1) (order.idxOf e.2))

/-- Reference crossing parity, computed without coordinates. -/
@[expose] def crossing (order : List ℕ) (e f : ℕ × ℕ) : Bool :=
  between order e f.1 ^^ between order e f.2

/-- Binary label of the move of indexed segment `e` past vertex `v`. -/
@[expose] def moveLabel (n e v : ℕ) : ℕ := e * n + v

/-- The two endpoint move labels of an unfrozen segment, or no labels for a frozen segment. -/
@[expose] def moveLabels (n i : ℕ) (e : Segment) (f : ℕ × ℕ) : List ℕ :=
  if e.2 then [] else [moveLabel n i f.1, moveLabel n i f.2]

/-- Literal sparse row for two indexed segment records. No label deduplication is performed. -/
@[expose] def row (F : Frame) (e f : Segment × ℕ) : AffineEquation ℕ :=
  (moveLabels F.vertexCount e.2 e.1 f.1.endpoints ++
    moveLabels F.vertexCount f.2 f.1 e.1.endpoints, crossing F.order e.1.endpoints f.1.endpoints)

/-- Every unordered independent pair appears once, in increasing first segment index and then
increasing second index. All scans traverse actual segment lists, never move-label intervals. -/
@[expose] def compileFrame (F : Frame) : XORSAT.System :=
  F.segments.zipIdx.flatMap fun e =>
    (F.segments.zipIdx.filter fun f =>
      decide (f.2 < e.2) && independent e.1.endpoints f.1.endpoints).map fun f => row F e f

/-- The concrete sparse system on the twice-subdivided existing graph. -/
@[expose] def compile (I : FixedRotationInput) : XORSAT.System := compileFrame (frame I)

/-- Ordinary native XOR solving, after raw input validation. This is an algebraic query;
no result identifying it with `Feasible` is assumed or asserted. -/
@[expose] def query (I : FixedRotationInput) : Bool :=
  validate I && XORSAT.solve (compile I)

/-- A frozen segment contributes zero regardless of the assignment; an unfrozen segment reads
its actual binary move label. -/
@[expose] def moveValue (F : Frame) (assignment : ℕ → Bool)
    (e : Segment × ℕ) (v : ℕ) : Bool :=
  if e.1.frozen then false else assignment (moveLabel F.vertexCount e.2 v)

/-- A sparse row states exactly the four endpoint moves with the frozen zeros retained. -/
theorem row_holds_iff (F : Frame) (assignment : ℕ → Bool) (e f : Segment × ℕ) :
    (row F e f).Holds assignment ↔
      moveValue F assignment e f.1.source + moveValue F assignment e f.1.target +
        (moveValue F assignment f e.1.source + moveValue F assignment f e.1.target) =
          crossing F.order e.1.endpoints f.1.endpoints := by
  simp only [AffineEquation.Holds, row, List.map_append, List.sum_append,
    moveLabels, moveValue]
  split_ifs <;> simp [← Bool.zero_eq_false]

/-- Exact row enumeration, including the strict unordered-pair scan and independence guard. -/
theorem holds_compileFrame_iff (F : Frame) (assignment : ℕ → Bool) :
    (compileFrame F).Holds assignment ↔
      ∀ e ∈ F.segments.zipIdx, ∀ f ∈ F.segments.zipIdx,
        f.2 < e.2 → independent e.1.endpoints f.1.endpoints = true →
          (row F e f).Holds assignment := by
  simp only [AffineSystem.Holds, compileFrame, List.mem_flatMap, List.mem_map,
    List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h e he f hf hlt hind
    exact h _ ⟨e, he, f, ⟨hf, hlt, hind⟩, rfl⟩
  · rintro h _ ⟨e, he, f, ⟨hf, hlt, hind⟩, rfl⟩
    exact h e he f hf hlt hind

/-- The actual native query accepts exactly valid inputs whose concrete frozen parity rows
have a Boolean assignment. This uses the implemented XOR solver without a hypothesis. -/
theorem query_eq_true_iff (I : FixedRotationInput) :
    query I = true ↔ Valid I ∧ ∃ assignment : ℕ → Bool, (compile I).Holds assignment := by
  rw [query, Bool.and_eq_true, validate_eq_true_iff, XORSAT.solve_eq_true_iff]
  rfl

/-- There are exactly three listed segments per original edge occurrence. -/
@[simp] theorem length_subdivide (I : FixedRotationInput) :
    (subdivide I).length = 3 * I.graph.2.length := by
  simp [subdivide, List.length_flatMap, Nat.mul_comm]

/-- Twice subdivision has the advertised dense vertex count, including isolates. -/
@[simp] theorem length_subdivisionGraph_vertices (I : FixedRotationInput) :
    (subdivisionGraph I).1.length = I.graph.1.length + 2 * I.graph.2.length := by
  simp [subdivisionGraph, subdivisionSize]

/-- Each independent-edge row contains at most four binary move labels. -/
theorem length_row_le (F : Frame) (e f : Segment × ℕ) : (row F e f).1.length ≤ 4 := by
  simp only [row, List.length_append, moveLabels]
  split_ifs <;> simp

/-- The number of rows is at most the square of the actual segment-list length. -/
theorem length_compileFrame_le (F : Frame) :
    (compileFrame F).length ≤ F.segments.length ^ 2 := by
  unfold compileFrame
  rw [List.length_flatMap]
  have h : ∀ e ∈ F.segments.zipIdx,
      ((F.segments.zipIdx.filter fun f => decide (f.2 < e.2) &&
        independent e.1.endpoints f.1.endpoints).map fun f => row F e f).length ≤
      F.segments.length := by
    intro e _
    simpa only [List.length_map, List.length_zipIdx] using List.length_filter_le
      (fun f : Segment × ℕ =>
        decide (f.2 < e.2) && independent e.1.endpoints f.1.endpoints) F.segments.zipIdx
  calc
    _ ≤ (F.segments.zipIdx.map fun _ => F.segments.length).sum := List.sum_le_sum h
    _ = F.segments.length ^ 2 := by simp [pow_two]

/-- A bounded endpoint produces a move label below the full rectangular move budget. -/
theorem moveLabel_lt {n m e v : ℕ} (he : e < m) (hv : v < n) :
    moveLabel n e v < m * n := by
  unfold moveLabel
  calc e * n + v < (e + 1) * n := by nlinarith
       _ ≤ m * n := Nat.mul_le_mul_right n (by omega)

end Cslib.Complexity.Graph.RotationRecognition
