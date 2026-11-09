/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Bounds
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.GetD

/-!
# Finite move assignments for frozen sparse equations

Assignments have one bit per segment/vertex pair in the finite frame. Frozen segments contribute
zero, including when the unused assignment bit is true. The sparse solver's arbitrary binary
label assignment and this finite move semantics are equivalent; neither direction assumes any
recognizer or topological theorem.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Logic.PL

/-- The finite rectangle of potential segment/vertex moves. -/
abbrev Moves (F : Frame) := Fin F.segments.length → Fin F.vertexCount → Bool

/-- Total lookup of a finite move table, returning zero outside the rectangle. -/
@[expose] def readMove (F : Frame) (moves : Moves F) (e v : ℕ) : Bool :=
  if he : e < F.segments.length then
    if hv : v < F.vertexCount then moves ⟨e, he⟩ ⟨v, hv⟩ else false
  else false

/-- Frozen edges contribute zero; all other entries are read from the finite move rectangle. -/
@[expose] def finiteMoveValue (F : Frame) (moves : Moves F) (e : Segment × ℕ) (v : ℕ) : Bool :=
  if e.1.2 then false else readMove F moves e.2 v

/-- The literal independent-pair switch equations, with all frozen contributions zero. -/
@[expose] def MoveEquations (F : Frame) (moves : Moves F) : Prop :=
  ∀ e ∈ F.segments.zipIdx, ∀ f ∈ F.segments.zipIdx,
    f.2 < e.2 → independent e.1.1 f.1.1 = true →
      finiteMoveValue F moves e f.1.1.1 + finiteMoveValue F moves e f.1.1.2 +
        (finiteMoveValue F moves f e.1.1.1 + finiteMoveValue F moves f e.1.1.2) =
          crossing F.order e.1.1 f.1.1

/-- Decode a binary move label by quotient and remainder, with a total zero fallback. -/
@[expose] def assignmentOfMoves (F : Frame) (moves : Moves F) (label : ℕ) : Bool :=
  readMove F moves (label / F.vertexCount) (label % F.vertexCount)

private theorem entry_bounds {F : Frame} (hF : BoundedEndpoints F)
    {e : Segment × ℕ} (he : e ∈ F.segments.zipIdx) :
    e.2 < F.segments.length ∧ e.1.1.1 < F.vertexCount ∧ e.1.1.2 < F.vertexCount := by
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
  exact ⟨hi, hF e.1 (hv ▸ List.getElem_mem hi)⟩

/-- Binary label decoding is exact throughout the finite move rectangle. -/
theorem assignmentOfMoves_label (F : Frame) (moves : Moves F) {e v : ℕ}
    (hv : v < F.vertexCount) :
    assignmentOfMoves F moves (moveLabel F.vertexCount e v) = readMove F moves e v := by
  have hn : 0 < F.vertexCount := by omega
  simp only [assignmentOfMoves, moveLabel, Nat.mul_comm e F.vertexCount,
    Nat.mul_add_div hn, Nat.div_eq_of_lt hv,
    Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

/-- Every finite move table evaluates the sparse rows exactly as the frozen switch equations. -/
theorem holds_assignmentOfMoves_iff {F : Frame} (hF : BoundedEndpoints F) (moves : Moves F) :
    (compileFrame F).Holds (assignmentOfMoves F moves) ↔ MoveEquations F moves := by
  rw [holds_compileFrame_iff]
  have value (e : Segment × ℕ) (v : ℕ) (hv : v < F.vertexCount) :
      moveValue F (assignmentOfMoves F moves) e v = finiteMoveValue F moves e v := by
    simp only [moveValue, finiteMoveValue, assignmentOfMoves_label F moves hv]
  constructor
  · intro h e he f hf hlt hind
    have eb := entry_bounds hF he
    have fb := entry_bounds hF hf
    simpa only [value e _ fb.2.1, value e _ fb.2.2, value f _ eb.2.1, value f _ eb.2.2] using
      (row_holds_iff F _ e f).mp (h e he f hf hlt hind)
  · intro h e he f hf hlt hind
    have eb := entry_bounds hF he
    have fb := entry_bounds hF hf
    apply (row_holds_iff F _ e f).mpr
    simpa only [value e _ fb.2.1, value e _ fb.2.2, value f _ eb.2.1, value f _ eb.2.2] using
      h e he f hf hlt hind

/-- Sparse satisfiability is precisely existence of finitely many move bits with frozen zeros.
Unused and out-of-range labels in the solver's assignment have no effect. -/
theorem satisfiable_iff_exists_moves {F : Frame} (hF : BoundedEndpoints F) :
    XORSAT.Satisfiable (compileFrame F) ↔ ∃ moves : Moves F, MoveEquations F moves := by
  constructor
  · rintro ⟨assignment, ha⟩
    let moves : Moves F := fun e v => assignment (moveLabel F.vertexCount e.val v.val)
    refine ⟨moves, ?_⟩
    intro e he f hf hlt hind
    have eb := entry_bounds hF he
    have fb := entry_bounds hF hf
    have value (x : Segment × ℕ) (v : ℕ) (hx : x.2 < F.segments.length)
        (hv : v < F.vertexCount) :
        finiteMoveValue F moves x v = moveValue F assignment x v := by
      simp only [finiteMoveValue, readMove, hx, hv, dite_true, moves, moveValue]
    simpa only [value e _ eb.1 fb.2.1, value e _ eb.1 fb.2.2,
      value f _ fb.1 eb.2.1, value f _ fb.1 eb.2.2] using
      (row_holds_iff F assignment e f).mp ((holds_compileFrame_iff F assignment).mp ha
        e he f hf hlt hind)
  · rintro ⟨moves, hm⟩
    exact ⟨assignmentOfMoves F moves, (holds_assignmentOfMoves_iff hF moves).mpr hm⟩

/-- Every stored bit at a frozen segment is literally zero. -/
@[expose] def FrozenMoves (F : Frame) (moves : Moves F) : Prop :=
  ∀ e v, (F.segments.getD e.val ((0, 0), false)).2 = true → moves e v = false

/-- Explicitly set every frozen-edge entry of the finite rectangle to zero. -/
@[expose] def freezeMoves (F : Frame) (moves : Moves F) : Moves F := fun e v =>
  if (F.segments.getD e.val ((0, 0), false)).2 then false else moves e v

/-- Frozen coordinates can actually be zero in the finite witness, not merely omitted from
its sparse variable list. No value of an unused solver label is treated as a permitted move. -/
theorem satisfiable_iff_exists_frozen_moves {F : Frame} (hF : BoundedEndpoints F) :
    XORSAT.Satisfiable (compileFrame F) ↔
      ∃ moves : Moves F, FrozenMoves F moves ∧ MoveEquations F moves := by
  constructor
  · intro h
    obtain ⟨moves, hm⟩ := (satisfiable_iff_exists_moves hF).mp h
    refine ⟨freezeMoves F moves, ?_, ?_⟩
    · intro e v he
      simp only [freezeMoves, he, ↓reduceIte]
    · have value (e : Segment × ℕ) (he : e ∈ F.segments.zipIdx) (v : ℕ)
          (hv : v < F.vertexCount) :
          finiteMoveValue F (freezeMoves F moves) e v = finiteMoveValue F moves e v := by
        obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
        have hread : F.segments.getD e.2 ((0, 0), false) = e.1 := by
          rw [List.getD_eq_getElem _ _ hi, hval]
        simp only [finiteMoveValue, readMove, hi, hv, dite_true, freezeMoves, hread]
        split <;> rfl
      intro e he f hf hlt hind
      have eb := entry_bounds hF he
      have fb := entry_bounds hF hf
      simpa only [value e he _ fb.2.1, value e he _ fb.2.2,
        value f hf _ eb.2.1, value f hf _ eb.2.2] using hm e he f hf hlt hind
  · rintro ⟨moves, _, hm⟩
    exact (satisfiable_iff_exists_moves hF).mpr ⟨moves, hm⟩

/-- The actual validated native query decides exactly existence of finite frozen move bits. -/
theorem query_eq_true_iff_exists_moves (I : FixedRotationInput) :
    query I = true ↔ Valid I ∧ ∃ moves : Moves (frame I), MoveEquations (frame I) moves := by
  rw [query_eq_true_iff]
  constructor
  · rintro ⟨hI, ha⟩
    exact ⟨hI, (satisfiable_iff_exists_moves (boundedEndpoints_frame hI)).mp ha⟩
  · rintro ⟨hI, hm⟩
    exact ⟨hI, (satisfiable_iff_exists_moves (boundedEndpoints_frame hI)).mpr hm⟩

/-- Finite query semantics with literal zeros on every coordinate of every fixed segment. -/
theorem query_eq_true_iff_exists_frozen_moves (I : FixedRotationInput) :
    query I = true ↔ Valid I ∧ ∃ moves : Moves (frame I),
      FrozenMoves (frame I) moves ∧ MoveEquations (frame I) moves := by
  rw [query_eq_true_iff]
  constructor
  · rintro ⟨hI, ha⟩
    exact ⟨hI, (satisfiable_iff_exists_frozen_moves (boundedEndpoints_frame hI)).mp ha⟩
  · rintro ⟨hI, hm⟩
    exact ⟨hI, (satisfiable_iff_exists_frozen_moves (boundedEndpoints_frame hI)).mpr hm⟩

end Cslib.Complexity.Graph.RotationRecognition
