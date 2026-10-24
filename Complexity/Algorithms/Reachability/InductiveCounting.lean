/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Basic

/-!
# A binary-choice inductive-counting controller

The controller scans vertex identifiers in increasing order. It guesses whether to include each
identifier, certifies each included identifier by a padded walk, and checks the selected count
against the previous round's count. Only a fixed number of natural-number registers and Boolean
flags are stored. An edge or bad-vertex oracle is consulted only in an explicit query phase.

## Main definitions

* `Cslib.InductiveCounting.Phase`, `Cslib.InductiveCounting.Query`,
  `Cslib.InductiveCounting.State`: the finite control phase, oracle requests, and register state.
* `Cslib.InductiveCounting.reject`, `Cslib.InductiveCounting.accept`,
  `Cslib.InductiveCounting.halted`, `Cslib.InductiveCounting.initial`: canonical terminal and
  initial states and the halting predicate.
* `Cslib.InductiveCounting.query`, `Cslib.InductiveCounting.answer`: the request made in a query
  phase and its oracle evaluation.
* `Cslib.InductiveCounting.registerBound`, `Cslib.InductiveCounting.Bounded`,
  `Cslib.InductiveCounting.candidateCost`, `Cslib.InductiveCounting.targetCost`,
  `Cslib.InductiveCounting.roundCost`, `Cslib.InductiveCounting.rank`: uniform register bounds and
  progress measure.
* `Cslib.InductiveCounting.instruction`, `Cslib.InductiveCounting.advance`,
  `Cslib.InductiveCounting.step`: unchecked, checked, and graph-backed controller transitions.
* `Cslib.InductiveCounting.replay`, `Cslib.InductiveCounting.Accepts`: replay of a finite sequence
  of choices and acceptance from the initial state.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Cslib.InductiveCounting

variable {N width source : ℕ} {edge : ℕ → ℕ → Bool} {bad : ℕ → Bool}

/-- The finite control. Neither a walk nor a set of selected vertices is stored. -/
inductive Phase
  | round | target | candidate | walk | guess | edge | observe | done | accept | reject
  deriving DecidableEq, Repr

/-- Explicit `Fintype` enumeration of all ten control phases. -/
instance : Fintype Phase where
  elems := {.round, .target, .candidate, .walk, .guess, .edge, .observe, .done, .accept, .reject}
  complete p := by cases p <;> simp

/-- A request for one bit of the graph or of the bad-vertex predicate. -/
inductive Query
  | edge (src dst : ℕ)
  | bad (vertex : ℕ)
  deriving DecidableEq, Repr

/-- Ten registers and two flags suffice, independently of the number of vertices. `remaining`
is the number of padded walk steps still to check; `bits` counts unguessed bits of `guess`. -/
structure State where
  /-- Current instruction. -/
  phase : Phase := .round
  /-- Current round. -/
  round : ℕ := 0
  /-- Certified size of the current round. -/
  count : ℕ := 1
  /-- Target currently being tested. -/
  target : ℕ := 0
  /-- Accumulated size of the next round. -/
  nextCount : ℕ := 0
  /-- Candidate currently being scanned. -/
  candidate : ℕ := 0
  /-- Number of selected candidates. -/
  selected : ℕ := 0
  /-- Number of walk steps left. -/
  remaining : ℕ := 0
  /-- Current walk vertex. -/
  current : ℕ := 0
  /-- Partially guessed next vertex. -/
  guess : ℕ := 0
  /-- Number of vertex bits left. -/
  bits : ℕ := 0
  /-- Has a selected candidate satisfied the scan's predicate? -/
  hit : Bool := false
  /-- Is this the last scan, which tests the bad-vertex predicate? -/
  finalScan : Bool := false
  deriving DecidableEq, Repr

variable {s : State}

/-- Canonical rejecting state. -/
def reject : State := { phase := .reject }

/-- Canonical accepting state. -/
def accept : State := { phase := .accept }

/-- A state has halted when it is accepting or rejecting. -/
def halted (s : State) : Bool := s.phase == .accept || s.phase == .reject

/-- Oracle calls occur only at these two instructions. -/
def query (s : State) : Option Query :=
  match s.phase with
  | .edge => some (.edge s.current s.guess)
  | .observe => some (if s.finalScan then .bad s.candidate
      else .edge s.candidate s.target)
  | _ => none

/-- The underlying instruction, before the uniform storage and termination checks. `answer`
is consulted only at `edge` and `observe`; `choice` only at `candidate` and `guess`.
Vertex identifiers are guessed from most significant to least significant bit. -/
def instruction (N width source : ℕ) (s : State) (answer choice : Bool) : State :=
  match s.phase with
  | .round =>
    if s.round + 1 < N then
      { s with phase := .target, target := 0, nextCount := 0, finalScan := false }
    else
      { s with
        phase := .candidate, candidate := 0, selected := 0, hit := false, finalScan := true }
  | .target =>
    if s.target < N then
      { s with phase := .candidate, candidate := 0, selected := 0, hit := false }
    else
      { s with phase := .round, round := s.round + 1, count := s.nextCount }
  | .candidate =>
    if s.candidate < N then
      if choice then
        { s with phase := .walk, remaining := s.round, current := source }
      else { s with candidate := s.candidate + 1 }
    else { s with phase := .done }
  | .walk =>
    if s.remaining = 0 then
      if s.current = s.candidate then { s with phase := .observe } else reject
    else { s with phase := .guess, guess := 0, bits := width }
  | .guess =>
    if s.bits = 0 then
      if s.guess < N then { s with phase := .edge } else reject
    else { s with guess := 2 * s.guess + choice.toNat, bits := s.bits - 1 }
  | .edge =>
    if s.current == s.guess || answer then
      { s with phase := .walk, current := s.guess, remaining := s.remaining - 1 }
    else reject
  | .observe =>
    { s with
      phase := .candidate, candidate := s.candidate + 1,
      selected := s.selected + 1,
      hit := s.hit || answer || (!s.finalScan && s.candidate == s.target) }
  | .done =>
    if s.selected = s.count then
      if s.finalScan then (if s.hit then reject else accept)
      else { s with
        phase := .target, target := s.target + 1, nextCount := s.nextCount + s.hit.toNat }
    else reject
  | .accept => s
  | .reject => s

/-- A uniform bound on each register. It includes the whole range of a width-bit guess,
vertex counts (which can equal `N`), and the width counter. -/
def registerBound (N width : ℕ) : ℕ := N + 2 ^ width + width + 2

/-- The bounds checked at each transition, including transitions on dishonest guesses. -/
def Bounded (N width : ℕ) (s : State) : Prop :=
  s.round < registerBound N width ∧ s.count < registerBound N width ∧
  s.target < registerBound N width ∧ s.nextCount < registerBound N width ∧
  s.candidate < registerBound N width ∧ s.selected < registerBound N width ∧
  s.remaining < registerBound N width ∧ s.current < registerBound N width ∧
  s.guess < registerBound N width ∧ s.bits < registerBound N width

/-- Register boundedness is decidable. -/
instance : Decidable (Bounded N width s) := by unfold Bounded; infer_instance

/-- Worst-case cost of checking one candidate, with slack for the loop instructions. -/
def candidateCost (N width : ℕ) : ℕ := N * (width + 3) + 4

/-- Worst-case cost of one target scan, with slack for the loop instructions. -/
def targetCost (N width : ℕ) : ℕ := (N + 1) * candidateCost N width + 6

/-- Worst-case cost of one whole round, with slack for the loop instructions. -/
def roundCost (N width : ℕ) : ℕ := (N + 1) * targetCost N width + 2

/-- A natural-number progress measure. In a legitimate state, each instruction decreases it.
The runtime check also rejects malformed states rather than allowing them to cycle. -/
def rank (N width : ℕ) (s : State) : ℕ :=
  let base := if s.finalScan then 0 else
    (N - s.round - 1) * roundCost N width +
    (N - s.target - 1) * targetCost N width
  match s.phase with
  | .round => (N - s.round) * roundCost N width + 1
  | .target => (N - s.round - 1) * roundCost N width +
      (N - s.target) * targetCost N width + 2
  | .candidate => base + (N - s.candidate) * candidateCost N width + 4
  | .walk => base + (N - s.candidate - 1) * candidateCost N width +
      s.remaining * (width + 3) + 6
  | .guess => base + (N - s.candidate - 1) * candidateCost N width +
      (s.remaining - 1) * (width + 3) + s.bits + 8
  | .edge => base + (N - s.candidate - 1) * candidateCost N width +
      (s.remaining - 1) * (width + 3) + 7
  | .observe => base + (N - s.candidate - 1) * candidateCost N width + 5
  | .done => base + 3
  | .accept | .reject => 0

/-- One instruction, checked for bounded storage and progress. These checks are executable and
do not consult the edge relation or the bad-vertex predicate. -/
def advance (N width source : ℕ) (s : State) (answer choice : Bool) : State :=
  if halted s then s else
    let t := instruction N width source s answer choice
    if Bounded N width t ∧ rank N width t < rank N width s then t else reject

/-- Supply the answer to the unique pending oracle request. -/
def answer (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool) (s : State) : Bool :=
  match query s with
  | some (.edge u v) => edge u v
  | some (.bad u) => bad u
  | none => false

/-- A graph-backed step of the controller. -/
def step (N width source : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool)
    (s : State) (choice : Bool) : State :=
  advance N width source s (answer edge bad s) choice

/-- Initial state; an out-of-range source is rejected. -/
def initial (N source : ℕ) : State := if source < N then {} else reject

/-- Replay finite binary choices. Bits at deterministic instructions are ignored. -/
def replay (N width source : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool)
    (s : State) : List Bool → State
  | [] => s
  | b :: bs => replay N width source edge bad (step N width source edge bad s b) bs

/-- A finite run from the canonical initial state. -/
def Accepts (N width source : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool) : Prop :=
  ∃ bs, (replay N width source edge bad (initial N source) bs).phase = .accept

/-- The canonical rejecting state satisfies `Bounded`. -/
@[simp] theorem bounded_reject : Bounded N width reject := by
  simp [Bounded, reject, registerBound]

/-- The canonical accepting state satisfies `Bounded`. -/
@[simp] theorem bounded_accept : Bounded N width accept := by
  simp [Bounded, accept, registerBound]

/-- All branches preserve the uniform register bound. -/
theorem bounded_advance (ans choice : Bool) (h : Bounded N width s) :
    Bounded N width (advance N width source s ans choice) := by
  unfold advance
  split
  · exact h
  · dsimp only
    split
    · exact And.left ‹_ ∧ _›
    · exact bounded_reject

/-- Each unhalted transition decreases the progress measure. -/
theorem rank_advance_lt (ans choice : Bool) (h : halted s = false) :
    rank N width (advance N width source s ans choice) < rank N width s := by
  have hs : 0 < rank N width s := by
    cases hp : s.phase <;> simp_all [halted, rank]
  simp only [advance, h, Bool.false_eq_true, ↓reduceIte]
  split_ifs with ht
  · exact ht.2
  · exact hs

/-- Advancing a halted state leaves it unchanged. -/
@[simp] theorem advance_halted (ans choice : Bool) (h : halted s = true) :
    advance N width source s ans choice = s := by simp [advance, h]

/-- Register bounds hold at every point of every replay. -/
theorem bounded_replay (h : Bounded N width s) (bs : List Bool) :
    Bounded N width (replay N width source edge bad s bs) := by
  induction bs generalizing s with
  | nil => exact h
  | cons b bs ih => exact ih (bounded_advance _ _ h)

/-- Appending choice sequences composes their executions. -/
theorem replay_append (xs ys : List Bool) :
    replay N width source edge bad s (xs ++ ys) =
      replay N width source edge bad (replay N width source edge bad s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih => exact ih

/-- Further choices do not change a halted state. -/
theorem replay_halted (h : halted s = true) (bs : List Bool) :
    replay N width source edge bad s bs = s := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [replay, show step N width source edge bad s b = s from advance_halted _ _ h, ih]

/-- Every branch halts within the initial progress measure, including adversarial guesses. -/
theorem halted_replay_of_rank_le (bs : List Bool) (h : rank N width s ≤ bs.length) :
    halted (replay N width source edge bad s bs) = true := by
  induction bs generalizing s with
  | nil =>
    cases hp : s.phase <;> simp_all [rank, halted, replay]
  | cons b bs ih =>
    by_cases hh : halted s = true
    · rw [replay_halted hh]
      exact hh
    · have hh' : halted s = false := Bool.eq_false_iff.mpr hh
      have hr := rank_advance_lt (N := N) (width := width) (source := source)
        (answer edge bad s) b hh'
      apply ih
      change rank N width (advance N width source s (answer edge bad s) b) ≤ bs.length
      simp only [List.length_cons] at h
      omega

end Cslib.InductiveCounting
