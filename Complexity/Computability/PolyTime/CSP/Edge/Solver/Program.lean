/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Semantics
public import Complexity.Computability.PolyTime.CSP.Edge.Forest.Spec
public import Complexity.Computability.PolyTime.CSP.Edge.Augmenting
public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Ancestry
public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Lifting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-!
# Finite stack for one edge-CSP improvement

Frames retain the prepared original body, its finite occurrence buffer and its actual cycle.
Descent performs a fresh native forest search and pushes exactly one frame per contraction.
The first improvement unwinds those frames once, lifting an arbitrary improving child buffer.
An exhausted child propagates optimality immediately. There is no recursive optimization of
children. Clocks use actual occurrence-list lengths, independently of binary label magnitudes.

This program uses the original `CSP Table ℕ`, existing occurrence buffers, native forest
codes and augmenting-walk codes. Preparation, contraction and lifting execute actual finite
buffer operations, with no implementation or lifting provider as input. `Agreement` proves
exact mathematical agreement; `PolyTime` supplies ordinary native certificates with full
encoded storage bounds.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (WalkCode encWalkCode)

/-- Prepared parent problem and the cycle used for its actual whole-instance contraction. -/
structure Frame where
  /-- Original body and exact-width prepared buffer. -/
  parent : EdgeForest.Input
  /-- Binary original base name and binary global occurrence positions. -/
  cycle : WalkCode

/-- The framed parent input precedes the cycle's framed base and ordered position pairs. -/
enc_structure encFrame : Frame where
  parent : EdgeForest.encInput, cycle : encWalkCode

/-- Encode the actual positional labeling by scanning actual incidences. -/
abbrev buffer {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) : List Bool :=
  (incidenceList F).map f

/-- Read the actual blossom event, perform its preparatory flip and construct the child.
All old constraint positions and all nullaries are retained by `Blossom.contract`. -/
@[expose] def push (input : EdgeForest.Input) (event : EdgeForest.MeetingCode) :
    Option (Frame × EdgeForest.Input) :=
  (NativeForest.blossom input.body event).map fun b =>
    let prepared := NativeWalk.flip input.labels (NativeWalk.edges b.prepare)
    let vs := NativeWalk.internal input.body b.cycle
    let parent : EdgeForest.Input := ⟨input.body, prepared⟩
    let child : EdgeForest.Input :=
      ⟨Contraction.contract parent vs, (Contraction.referenceRows parent vs).flatten⟩
    (⟨parent, b.cycle⟩, child)

/-- Flip the actual decoded native augmentation and return its exact-width buffer. -/
@[expose] def augment (input : EdgeForest.Input) (event : EdgeForest.MeetingCode) :
    Option (List Bool) := do
  return NativeWalk.flip input.labels (NativeWalk.edges (NativeForest.meetingWalk input.body event))

/-- Lift one actual child improvement into its prepared parent. Every outside change in the
comparison is retained; the full `liftComparison` construction selects and lifts its walk. -/
@[expose] def lift (frame : Frame) (comparison : List Bool) : Option (List Bool) :=
  NativeLifting.liftComparison frame.parent frame.cycle comparison

/-- Finite stack state. Status is running, proved optimal, or an improving finite buffer. -/
structure State where
  /-- Current contracted problem; restored to the parent after every pop. -/
  current : EdgeForest.Input
  /-- Prepared parents, newest first. -/
  frames : List Frame
  /-- Remaining contraction depth, in unary and funded by the original occurrence list. -/
  budget : ℕ
  /-- `none` descends; `some none` stops; `some (some bits)` unwinds. -/
  status : Option (Option (List Bool))

/-- Current input and stack are framed fields, followed by the two status tags and framed bits. -/
enc_structure encState : State where
  current : EdgeForest.encInput, frames : (encList encFrame),
  budget : encUnary,
  status : (encOption (encOption (encList encBool)))

/-- One descent or one lift. A stopped optimum needs no parent labeling reconstruction:
count-preserving preparation and reference optimality transfer certify the original optimum. -/
@[expose] def step (state : State) : State :=
  match state.status with
  | some none => ⟨state.current, [], state.budget, some none⟩
  | some (some bits) =>
    match state.frames with
    | [] => state
    | frame :: frames => ⟨frame.parent, frames, state.budget, some (lift frame bits)⟩
  | none =>
    match state.budget with
    | 0 => ⟨state.current, [], 0, some none⟩
    | budget + 1 =>
      match EdgeForest.run state.current with
      | none => ⟨state.current, [], budget, some none⟩
      | some (.inl _) => ⟨state.current, [], budget, some none⟩
      | some (.inr (.inl event)) =>
        ⟨state.current, state.frames, budget, some (augment state.current event)⟩
      | some (.inr (.inr event)) =>
        match push state.current event with
        | none => ⟨state.current, [], budget, some none⟩
        | some (frame, child) => ⟨child, frame :: state.frames, budget, none⟩

/-- One-improvement stack program. Each contraction uses one descent and at most one lift.
The additional steps fund the terminal search and final status. Clock value is unary and
funded by the input occurrence list; no binary name or arity is expanded. -/
@[expose] def improve (input : EdgeForest.Input) : Option (List Bool) :=
  let final := step^[2 * (CSP.occurrences input.body).length + 3]
    ⟨input, [], (CSP.occurrences input.body).length + 1, none⟩
  if final.frames.isEmpty then final.status.join else none

/-- Outer optimization state: current original buffer and a flag preserving first exhaustion. -/
abbrev OptimizeState := List Bool × Bool

/-- Improve the original problem once, stopping permanently after optimality is established. -/
@[expose] def optimizeStep (F : CSP Table ℕ) (state : OptimizeState) : OptimizeState :=
  if state.2 then state else
    match improve ⟨F, state.1⟩ with
    | none => (state.1, true)
    | some bits => (bits, false)

/-- Guarded finite optimization program. The occurrence list pays for all outer iterations.
Malformed models reject before any forest search or contraction. -/
@[expose] def optimize (F : CSP Table ℕ) : Option (List Bool) :=
  if checkModel F then
    let start := buffer (initial F)
    some (((optimizeStep F)^[F.vars.eraseDups.length + 1] (start, false)).1)
  else none

/-- Complete guarded finite decision program. -/
@[expose] def decideSAT (F : CSP Table ℕ) : Bool :=
  (optimize F).any fun bits => !(F.vars.any (EdgeAugmenting.inconsistent F bits))

end Cslib.Complexity.CSP.EdgeSolver.Program
