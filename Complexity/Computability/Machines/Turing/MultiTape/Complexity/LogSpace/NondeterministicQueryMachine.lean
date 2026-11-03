/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Termination
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Nondeterministic query machines

A query machine with one binary nondeterministic choice per step. An abstract state can be
infinite; it is data to be encoded on work tapes, rather than native finite control. The input
is read by position, with `none` returned beyond its end. Halted states self-loop.

Finite lists of choices describe paths at the proof level. They are not additional inputs or
work tapes of the machine. Acceptance requires both halting and an accepting state.

## Main definitions

* `Turing.NondeterministicQueryMachine`: the binary-choice query model.
* `Turing.NondeterministicQueryMachine.replay`: replay choices from an arbitrary state.
* `Turing.NondeterministicQueryMachine.RunPath`: finite paths of the step relation.
* `Turing.NondeterministicQueryMachine.Accepts`: existential acceptance by a halted branch.

## Main results

* `Turing.NondeterministicQueryMachine.exists_runPath_iff`: paths are exactly finite replays.
* `Turing.NondeterministicQueryMachine.accepts_iff_length`: an all-branches halting bound lets
  acceptance be checked at one common abstract time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

namespace Turing

/-- A decision-only query machine with one binary nondeterministic choice per step. -/
structure NondeterministicQueryMachine (σ : Type*) where
  /-- The initial state. -/
  init : σ
  /-- The queried input position. -/
  query : σ → ℕ
  /-- The next state, given the current state, input answer and nondeterministic choice. -/
  next : σ × Option Bool × Bool → σ
  /-- Whether the state has halted. -/
  halted : σ → Bool
  /-- Whether a halted state accepts. This field is ignored before halting. -/
  accept : σ → Bool

namespace NondeterministicQueryMachine

variable {σ : Type*} (M : NondeterministicQueryMachine σ) (input : List Bool)

/-- The input answer, `none` past the end of the input. -/
def read (s : σ) : Option Bool := input[M.query s]?

/-- A step selected by one choice; halted states are fixed. -/
def step (s : σ) (choice : Bool) : σ :=
  if M.halted s then s else M.next (s, M.read input s, choice)

/-- The existential one-step relation, including halted self-loops. -/
abbrev Step (s s' : σ) : Prop := ∃ choice, M.step input s choice = s'

/-- Replay a finite sequence of choices from a supplied state. -/
def replay (choices : List Bool) (s : σ) : σ := choices.foldl (M.step input) s

/-- Run from the initial state with a finite sequence of choices. -/
def run (choices : List Bool) : σ := M.replay input choices M.init

/-- Finite paths of the abstract step relation. -/
abbrev RunPath := RelSeries ({(s, s') | M.Step input s s'} : SetRel σ σ)

/-- A state reached by some finite branch. -/
def Reachable (s : σ) : Prop := ∃ choices, M.run input choices = s

/-- Some finite branch halts and accepts. -/
def Accepts : Prop :=
  ∃ choices, M.halted (M.run input choices) = true ∧ M.accept (M.run input choices) = true

/-- Every branch of exactly `t` abstract steps has halted. -/
def HaltsWithin (t : ℕ) : Prop :=
  ∀ choices : List Bool, choices.length = t → M.halted (M.run input choices) = true

@[simp]
theorem replay_nil (s : σ) : M.replay input [] s = s := rfl

theorem replay_cons (choice : Bool) (choices : List Bool) (s : σ) :
    M.replay input (choice :: choices) s =
      M.replay input choices (M.step input s choice) := rfl

theorem replay_append (choices more : List Bool) (s : σ) :
    M.replay input (choices ++ more) s = M.replay input more (M.replay input choices s) :=
  List.foldl_append

@[simp]
theorem run_nil : M.run input [] = M.init := rfl

theorem run_append (choices more : List Bool) :
    M.run input (choices ++ more) = M.replay input more (M.run input choices) :=
  M.replay_append input choices more M.init

theorem step_of_halted {s : σ} (h : M.halted s = true) (choice : Bool) :
    M.step input s choice = s := by
  simp [step, h]

/-- After halting, every further choice is ignored. -/
theorem replay_of_halted {s : σ} (h : M.halted s = true) (choices : List Bool) :
    M.replay input choices s = s := by
  induction choices with
  | nil => rfl
  | cons choice choices ih => rw [replay_cons, M.step_of_halted input h, ih]

theorem run_append_of_halted {choices : List Bool}
    (h : M.halted (M.run input choices) = true) (more : List Bool) :
    M.run input (choices ++ more) = M.run input choices := by
  rw [run_append, M.replay_of_halted input h]

/-- Every finite relational path is a choice replay of the same length, and conversely. -/
theorem exists_runPath_iff {s s' : σ} {n : ℕ} :
    (∃ p : M.RunPath input, p.head = s ∧ p.length = n ∧ p.last = s') ↔
      ∃ choices : List Bool, choices.length = n ∧ M.replay input choices s = s' := by
  constructor
  · rintro ⟨p, rfl, rfl, rfl⟩
    induction p using RelSeries.inductionOn' with
    | singleton s => exact ⟨[], rfl, rfl⟩
    | snoc p s hs ih =>
      obtain ⟨choices, hlen, hchoices⟩ := ih
      obtain ⟨choice, hchoice⟩ := (show M.Step input p.last s from hs)
      refine ⟨choices ++ [choice], ?_, ?_⟩
      · change (choices ++ [choice]).length = p.length + 1
        simp [hlen]
      · rw [RelSeries.head_snoc, RelSeries.last_snoc]
        rw [replay_append, hchoices]
        exact hchoice
  · rintro ⟨choices, rfl, rfl⟩
    induction choices generalizing s with
    | nil => exact ⟨RelSeries.singleton _ s, rfl, rfl, rfl⟩
    | cons choice choices ih =>
      obtain ⟨p, hhead, hlen, hlast⟩ := ih (s := M.step input s choice)
      have hstep : M.Step input s p.head := ⟨choice, hhead.symm⟩
      exact ⟨p.cons s hstep, rfl, by simp [hlen], by simp [hlast, replay_cons]⟩

theorem reachable_init : M.Reachable input M.init := ⟨[], rfl⟩

theorem Reachable.step {s : σ} (h : M.Reachable input s) (choice : Bool) :
    M.Reachable input (M.step input s choice) := by
  obtain ⟨choices, rfl⟩ := h
  exact ⟨choices ++ [choice], by simp [run_append, replay]⟩

/-- A common all-branches clock also bounds every longer branch. -/
theorem HaltsWithin.mono {t t' : ℕ} (h : M.HaltsWithin input t) (ht : t ≤ t') :
    M.HaltsWithin input t' := by
  intro choices hlen
  have hp : M.halted (M.run input (choices.take t)) = true :=
    h _ (by simp [List.length_take, hlen, Nat.min_eq_left ht])
  rw [← List.take_append_drop t choices, M.run_append_of_halted input hp]
  exact hp

/-- Acceptance can be tested at the common clock: short branches are padded by halted self-loops,
and longer branches already halted at the clock. The padding is proof-level data only. -/
theorem accepts_iff_length {t : ℕ} (h : M.HaltsWithin input t) :
    M.Accepts input ↔ ∃ choices : List Bool, choices.length = t ∧
      M.accept (M.run input choices) = true := by
  constructor
  · rintro ⟨choices, hhalt, haccept⟩
    by_cases hlen : choices.length ≤ t
    · refine ⟨choices ++ List.replicate (t - choices.length) false,
        by simp only [List.length_append, List.length_replicate]; omega, ?_⟩
      rw [M.run_append_of_halted input hhalt]
      exact haccept
    · have htake : (choices.take t).length = t := by simp only [List.length_take]; omega
      have hp := h _ htake
      refine ⟨choices.take t, htake, ?_⟩
      have heq : M.run input choices = M.run input (choices.take t) := by
        conv_lhs => rw [← List.take_append_drop t choices]
        exact M.run_append_of_halted input hp _
      rw [← heq]
      exact haccept
  · rintro ⟨choices, hlen, haccept⟩
    exact ⟨choices, h _ hlen, haccept⟩

/-- A branch longer than the common clock has the same state as its clock-length prefix. -/
theorem run_take_of_haltsWithin {t : ℕ} (h : M.HaltsWithin input t)
    (choices : List Bool) : M.run input (choices.take t) = M.run input choices := by
  by_cases ht : t ≤ choices.length
  · have hp := h (choices.take t) (by simp [List.length_take, Nat.min_eq_left ht])
    conv_rhs => rw [← List.take_append_drop t choices]
    exact (M.run_append_of_halted input hp _).symm
  · rw [List.take_of_length_le (by omega)]

/-- Any total local runtime has a common finite bound on all reachable states of an abstract
machine with an all-branches clock. This maximum is proof-level data: it need not be computed
by the simulator, encoded in a state, or stored on a tape. -/
theorem exists_bound_on_reachable {t : ℕ} (h : M.HaltsWithin input t) (cost : σ → ℕ) :
    ∃ bound, ∀ s, M.Reachable input s → cost s ≤ bound := by
  classical
  let choices : Finset (Σ n : Fin (t + 1), Fin n.val → Bool) := Finset.univ
  let value (p : Σ n : Fin (t + 1), Fin n.val → Bool) : ℕ :=
    cost (M.run input (List.ofFn p.2))
  refine ⟨choices.sup value, ?_⟩
  rintro s ⟨coins, rfl⟩
  let coins₀ := coins.take t
  have hlen : coins₀.length < t + 1 := by simp [coins₀, List.length_take]
  let p : Σ n : Fin (t + 1), Fin n.val → Bool := ⟨⟨coins₀.length, hlen⟩, coins₀.get⟩
  have hp := Finset.le_sup (f := value) (show p ∈ choices from Finset.mem_univ p)
  have hcost : value p = cost (M.run input coins) := by
    dsimp only [value, p]
    rw [List.ofFn_get]
    exact congrArg cost (M.run_take_of_haltsWithin input h coins)
  rw [hcost] at hp
  exact hp

/-- Every branch of `t` steps from the supplied abstract state has halted. -/
def HaltsFrom (s : σ) (t : ℕ) : Prop :=
  ∀ choices : List Bool, choices.length = t → M.halted (M.replay input choices s) = true

/-- A clock for the initial state is also a clock from every reachable state. The extra history
only makes the complete branch longer than the original clock. -/
theorem haltsFrom_of_reachable {t : ℕ} (h : M.HaltsWithin input t) {s : σ}
    (hs : M.Reachable input s) : M.HaltsFrom input s t := by
  obtain ⟨history, rfl⟩ := hs
  intro choices hlen
  have hp := HaltsWithin.mono M input h (show t ≤ history.length + t by omega)
    (history ++ choices) (by simp [hlen])
  rw [run_append] at hp
  exact hp

/-- The least all-branches halting clock from a state, or zero when no such clock exists. This
is a ghost ranking function, not a counter stored by the native simulator. -/
noncomputable def remainingSteps (s : σ) : ℕ :=
  open scoped Classical in
  if h : ∃ t, M.HaltsFrom input s t then Nat.find h else 0

theorem remainingSteps_spec {s : σ} (h : ∃ t, M.HaltsFrom input s t) :
    M.HaltsFrom input s (M.remainingSteps input s) := by
  classical
  simpa only [remainingSteps, dite_eq_left h] using Nat.find_spec h

theorem remainingSteps_le {s : σ} {t : ℕ} (h : M.HaltsFrom input s t) :
    M.remainingSteps input s ≤ t := by
  have hex : ∃ t, M.HaltsFrom input s t := ⟨t, h⟩
  classical
  rw [remainingSteps, dite_eq_left hex]
  exact Nat.find_min' hex h

theorem remainingSteps_pos {s : σ} (h : ∃ t, M.HaltsFrom input s t)
    (hs : M.halted s = false) : 0 < M.remainingSteps input s := by
  by_contra hzero
  have hz : M.remainingSteps input s = 0 := by omega
  have hp := M.remainingSteps_spec input h [] (by simp [hz])
  simp [hs] at hp

/-- The ghost clock strictly decreases on every branch from a running state. The native machine
can therefore be proved terminating without computing or storing any runtime maximum. -/
theorem remainingSteps_step_lt {s : σ} (h : ∃ t, M.HaltsFrom input s t)
    (hs : M.halted s = false) (choice : Bool) :
    M.remainingSteps input (M.step input s choice) < M.remainingSteps input s := by
  have hpos := M.remainingSteps_pos input h hs
  have hnext : M.HaltsFrom input (M.step input s choice) (M.remainingSteps input s - 1) := by
    intro choices hlen
    have hp := M.remainingSteps_spec input h (choice :: choices)
      (by simp only [List.length_cons, hlen]; omega)
    rw [replay_cons] at hp
    exact hp
  exact (M.remainingSteps_le input hnext).trans_lt (by omega)

/-! ### Reusing the deterministic input pass -/

/-- Fixing the choice gives a deterministic query machine. This does not enumerate choices or
store a witness: it supplies either of the two local transition routines. -/
def withChoice (choice : Bool) : QueryMachine σ where
  init := M.init
  query := M.query
  next p := M.next (p.1, p.2, choice)
  emit _ := []
  halted := M.halted
  finish s := [M.accept s]

theorem step_withChoice (choice : Bool) (s : σ) :
    (M.withChoice choice).step input s = M.step input s choice := rfl

/-- The deterministic input scan fetches exactly the abstract query answer. -/
theorem streamState_passNext (choice : Bool) (s : σ) :
    MultiTapeTM.streamState ((s, 0, none) : QueryMachine.Simulation.PassState σ)
      (QueryMachine.Simulation.passNext (M.withChoice choice)) input input.length =
      (s, input.length, M.read input s) :=
  QueryMachine.Simulation.streamState_passNext_length _ _ _

/-- The end of a deterministic pass performs the selected nondeterministic abstract step and
resets the position counter and fetched answer. -/
theorem passEnd_streamState (choice : Bool) (s : σ) :
    QueryMachine.Simulation.passEnd (M.withChoice choice)
      (MultiTapeTM.streamState ((s, 0, none) : QueryMachine.Simulation.PassState σ)
        (QueryMachine.Simulation.passNext (M.withChoice choice)) input input.length) =
      (M.step input s choice, 0, none) := by
  rw [M.streamState_passNext input choice s]
  rfl

/-! ### Local computation and space bounds -/

open MultiTapeTM

/-- Fixing the native choice preserves linear-space computability of the transition routine. -/
theorem next_withChoice_inSpace {σ : Type} {encS : σ ↪ List Bool}
    {M : NondeterministicQueryMachine σ}
    (hnext : ComputableInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (choice : Bool) :
    ComputableInSpace (M.withChoice choice).next
      (encPair encS (encOption encBool)) encS
      fun p => (encPair encS (encOption encBool) p).length := by
  apply ComputableInSpace.budget_comp_linear hnext
  exact ComputableInSpace.budget_prod (.fst _ _)
    (ComputableInSpace.budget_prod (.snd _ _)
      (ComputableInSpace.budget_const choice (.refl _)))

/-- The input-scan callback is the deterministic one and does not depend on the choice. -/
theorem passNext_inSpace {σ : Type} {encS : σ ↪ List Bool}
    {M : NondeterministicQueryMachine σ}
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (choice : Bool) :
    ComputableInSpace (QueryMachine.Simulation.passNext (M.withChoice choice))
      (encPair (QueryMachine.Simulation.encPass encS) encBool)
      (QueryMachine.Simulation.encPass encS)
      fun p => (encPair (QueryMachine.Simulation.encPass encS) encBool p).length :=
  QueryMachine.Simulation.passNext_inSpace hquery

/-- Either end-of-pass routine is computable in space linear in the encoded pass state. -/
theorem passEnd_inSpace {σ : Type} {encS : σ ↪ List Bool}
    {M : NondeterministicQueryMachine σ}
    (hnext : ComputableInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (choice : Bool) :
    ComputableInSpace (QueryMachine.Simulation.passEnd (M.withChoice choice))
      (QueryMachine.Simulation.encPass encS) (QueryMachine.Simulation.encPass encS)
      fun p => (QueryMachine.Simulation.encPass encS p).length :=
  QueryMachine.Simulation.passEnd_inSpace (next_withChoice_inSpace hnext choice) hhalted

/-- The pass continuation test is computable in linear space. -/
theorem passCont_inSpace {σ : Type} {encS : σ ↪ List Bool}
    {M : NondeterministicQueryMachine σ}
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (choice : Bool) :
    ComputableInSpace (QueryMachine.Simulation.passCont (M.withChoice choice))
      (QueryMachine.Simulation.encPass encS) encBool
      fun p => (QueryMachine.Simulation.encPass encS p).length :=
  QueryMachine.Simulation.passCont_inSpace hhalted

/-- The finalizer emits exactly the acceptance bit, with linear-space computation. -/
theorem passFinish_inSpace {σ : Type} {encS : σ ↪ List Bool}
    {M : NondeterministicQueryMachine σ}
    (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length)
    (choice : Bool) :
    ComputableInSpace (QueryMachine.Simulation.passFinish (M.withChoice choice))
      (QueryMachine.Simulation.encPass encS) encBits
      fun p => (QueryMachine.Simulation.encPass encS p).length :=
  QueryMachine.Simulation.passFinish_inSpace (haccept.of_enc_eq fun _ => rfl)

/-- The encoded scan state fits in the abstract-state budget plus the binary input counter.
This estimate is independent of the number of passes and of all earlier choices. -/
theorem length_passState_le {σ : Type} {encS : σ ↪ List Bool}
    {s : σ} {j S c : ℕ} (hstate : (encS s).length ≤ c * S)
    (hlog : Nat.log2 input.length + 1 ≤ S) (hj : j ≤ input.length) (answer : Option Bool) :
    (QueryMachine.Simulation.encPass encS (s, j, answer)).length ≤ (2 * c + 6) * S := by
  have hcounter := (length_encNat_le_log2 hj).trans hlog
  have hpositive : 1 ≤ S := (Nat.le_add_left _ _).trans hlog
  refine (QueryMachine.Simulation.length_encPass_le encS _).trans ?_
  nlinarith

/-- Every abstract prefix state has the same space bound when the bound holds on reachable
states. No choice history is included in the encoded state. -/
theorem length_scanState_le {σ : Type} {encS : σ ↪ List Bool}
    {M : NondeterministicQueryMachine σ} {S c : ℕ}
    (hstate : ∀ s, M.Reachable input s → (encS s).length ≤ c * S)
    (hlog : Nat.log2 input.length + 1 ≤ S) (choices : List Bool) {j : ℕ}
    (hj : j ≤ input.length) (answer : Option Bool) :
    (QueryMachine.Simulation.encPass encS (M.run input choices, j, answer)).length ≤
      (2 * c + 6) * S :=
  length_passState_le input (hstate _ ⟨choices, rfl⟩) hlog hj answer

end NondeterministicQueryMachine

end Turing
