/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
public import Complexity.Computability.Machines.Turing.MultiTape.FiniteConfiguration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Logic.Relation

/-!
# Finite views of space-bounded nondeterministic machines

A nondeterministic machine whose computation paths visit at most `s` work-tape cells reaches only
configurations of bounded size, however long it runs. This file gives these configurations a
finite description that preserves acceptance.

Along a run path from blank tapes with every head at `0`, the heads move by at most one cell per
step and only visited cells are written, so every head position and every non-blank cell lies
within the space used by its tape (`Turing.MultiTapeNTM.RunPath.natAbs_lt_spaceUsedByTape`).

A configuration is viewed as finite data (`Turing.FiniteCfg`), with every work tape stored
relative to its head and the append-only output summarized by
`Turing.MultiTapeNTM.outputClass`: empty, exactly `[true]`, or `[false]` for every other
word. The summary is a congruence for appending, so the
views step exactly as the machine does (`Turing.MultiTapeNTM.ViewStep`); a halted view steps only
to itself. A computation path accepts exactly when a halted view with output `[true]` is reachable
from the initial view (`Turing.MultiTapeNTM.accepts_iff_reflTransGen_viewStep`). Under a space
bound every reachable view has a bounded encoding (`Turing.MultiTapeNTM.length_encFiniteCfg_le`),
whatever the length of the path reaching it.

## Main definitions

* `Turing.MultiTapeNTM.outputClass`: the summary of an output word.
* `Turing.MultiTapeNTM.ViewStep`: the steps of the views of a machine.

## Main results

* `Turing.MultiTapeNTM.RunPath.natAbs_lt_spaceUsedByTape`: heads and non-blank cells lie within
  the space used.
* `Turing.MultiTapeNTM.accepts_iff_reflTransGen_viewStep`: acceptance is reachability of views.
* `Turing.MultiTapeNTM.length_encFiniteCfg_le`: reachable views are small under a space bound.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.1][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol} {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- A single configuration visits its head position only. -/
theorem visitedByTapeHead_singleton (c : Cfg k Symbol State input) (i : Fin k) :
    visitedByTapeHead (RelSeries.singleton (ntm.stepRel input) c) i = {c.workTapePos i} := by
  ext z
  simp only [mem_visitedByTapeHead, Finset.mem_singleton, RelSeries.mem_def,
    Set.mem_range]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    rfl
  · rintro rfl
    exact ⟨c, ⟨0, rfl⟩, rfl⟩

/-- The invariant of a run path from blank tapes with the heads at `0`: the visited positions
form an interval around `0` containing every non-blank cell. -/
structure VisitedInterval (p : ntm.RunPath input) (i : Fin k) : Prop where
  /-- The starting position is visited. -/
  zero_mem : 0 ∈ p.visitedByTapeHead i
  /-- The visited positions form an interval. -/
  convex : ∀ a ∈ p.visitedByTapeHead i, ∀ b ∈ p.visitedByTapeHead i, ∀ z, a ≤ z → z ≤ b →
    z ∈ p.visitedByTapeHead i
  /-- Every non-blank cell of the last configuration has been visited. -/
  written : ∀ z, p.last.workTapes i z ≠ none → z ∈ p.visitedByTapeHead i

/-- The invariant holds along every run path from blank tapes with the heads at `0`. -/
theorem visitedInterval (p : ntm.RunPath input) (hblank : ∀ i z, p.head.workTapes i z = none)
    (hpos : ∀ i, p.head.workTapePos i = 0) (i : Fin k) : p.VisitedInterval i := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    have hvis := visitedByTapeHead_singleton (ntm := ntm) c i
    refine ⟨?_, ?_, ?_⟩
    · rw [hvis, Finset.mem_singleton, ← hpos i]
      rfl
    · intro a ha b hb z h₁ h₂
      rw [hvis, Finset.mem_singleton] at ha hb ⊢
      omega
    · intro z hz
      exact absurd (hblank i z) hz
  | snoc p c hc ih =>
    obtain ⟨h₀, hconv, hwritten⟩ := ih (by simpa using hblank) (by simpa using hpos)
    have hsnoc := visitedByTapeHead_snoc p c hc i
    have hlast : p.last.workTapePos i ∈ visitedByTapeHead p i :=
      (mem_visitedByTapeHead _).mpr ⟨p.last, p.last_mem, rfl⟩
    -- the new head is next to the old one, and only the old head's cell is written
    have hmove : |c.workTapePos i - p.last.workTapePos i| ≤ 1 ∧
        ∀ z, c.workTapes i z ≠ none → p.last.workTapes i z ≠ none ∨
          z = p.last.workTapePos i := by
      change ntm.Step p.last c at hc
      rcases hs : p.last.state with _ | q
      · rw [(step_of_halt hs).mp hc]
        exact ⟨by simp, fun z hz => .inl hz⟩
      · simp only [Step, hs] at hc
        obtain ⟨action, -, rfl⟩ := hc
        refine ⟨workTapePos_apply_le action p.last i, fun z hz => ?_⟩
        rcases hw : (action.workTapes i).1 with _ | symbol
        · simp only [Action.apply, hw] at hz
          exact .inl hz
        · simp only [Action.apply, hw] at hz
          by_cases hz' : z = p.last.workTapePos i
          · exact .inr hz'
          · exact .inl (by rwa [Function.update_of_ne hz'] at hz)
    obtain ⟨hdist, hwrite⟩ := hmove
    have habs := abs_le.mp hdist
    refine ⟨?_, fun a ha b hb z h₁ h₂ => ?_, fun z hz => ?_⟩
    · rw [hsnoc]
      exact Finset.mem_insert_of_mem h₀
    · rw [hsnoc, Finset.mem_insert] at ha hb ⊢
      by_cases hz : z = c.workTapePos i
      · exact .inl hz
      refine .inr ?_
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · omega
      · exact hconv _ hlast _ hb _ (by omega) h₂
      · exact hconv _ ha _ hlast _ h₁ (by omega)
      · exact hconv _ ha _ hb _ h₁ h₂
    · rw [hsnoc]
      rw [RelSeries.last_snoc] at hz
      rcases hwrite z hz with h | h
      · exact Finset.mem_insert_of_mem (hwritten z h)
      · exact Finset.mem_insert_of_mem (h ▸ hlast)

/-- Positions of an interval around `0` are smaller than its size. -/
theorem VisitedInterval.natAbs_lt {p : ntm.RunPath input} {i : Fin k} (h : p.VisitedInterval i)
    {z : ℤ} (hz : z ∈ p.visitedByTapeHead i) : z.natAbs < p.spaceUsedByTape i := by
  have hsub : Finset.Icc (min 0 z) (max 0 z) ⊆ p.visitedByTapeHead i := fun y hy => by
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hy
    rcases le_total 0 z with h₀ | h₀
    · exact h.convex 0 h.zero_mem z hz y (by simpa [h₀] using h₁) (by simpa [h₀] using h₂)
    · exact h.convex z hz 0 h.zero_mem y (by simpa [h₀] using h₁) (by simpa [h₀] using h₂)
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  unfold spaceUsedByTape
  omega

/-- **Heads and written cells lie within the space used.** On a run path from blank tapes with
the heads at `0`, the last head position and every non-blank cell of a tape are smaller in absolute
value than the number of cells the tape's head has visited. -/
theorem natAbs_lt_spaceUsedByTape (p : ntm.RunPath input)
    (hblank : ∀ i z, p.head.workTapes i z = none) (hpos : ∀ i, p.head.workTapePos i = 0)
    (i : Fin k) :
    (p.last.workTapePos i).natAbs < p.spaceUsedByTape i ∧
      ∀ z, p.last.workTapes i z ≠ none → z.natAbs < p.spaceUsedByTape i := by
  have h := p.visitedInterval hblank hpos i
  exact ⟨h.natAbs_lt ((mem_visitedByTapeHead _).mpr ⟨p.last, p.last_mem, rfl⟩),
    fun z hz => h.natAbs_lt (h.written z hz)⟩

end RunPath

end Turing.MultiTapeNTM

/-! ### The size of tapes with bounded contents -/

namespace Cslib.Turing

variable {Symbol : Type*}

/-- A stack that reads blank from position `m` on stores at most `m` cells, since its last stored
cell is not blank. -/
theorem StackTape.length_le_of_read_eq_none (tape : StackTape Symbol) {m : ℕ}
    (h : ∀ j, m ≤ j → tape.read j = none) : tape.length ≤ m := by
  by_contra! hlt
  obtain ⟨values, hvalues⟩ := tape
  simp only [StackTape.length] at hlt
  obtain ⟨last, hlast⟩ : ∃ last, values.getLast? = some last :=
    Option.ne_none_iff_exists'.mp (by simpa using List.ne_nil_of_length_pos (by omega))
  have hne : last ≠ none := fun hnone => hvalues (hnone ▸ hlast)
  have hget : values[values.length - 1]? = some last := by
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have := h (values.length - 1) (by omega)
  rw [StackTape.read_eq_getElem?] at this
  simp only [hget, Option.join_some] at this
  exact hne this

/-- A tape whose cells are blank from displacement `m` on, on both sides, uses at most
`2 * m + 1` cells. -/
theorem BiTape.spaceUsed_le_of_read_eq_none (tape : BiTape Symbol) {m : ℕ}
    (hleft : ∀ j, m ≤ j → tape.read (Int.negSucc j) = none)
    (hright : ∀ j, m ≤ j → tape.read ((j : ℤ) + 1) = none) : tape.spaceUsed ≤ 2 * m + 1 := by
  have h₁ := tape.left.length_le_of_read_eq_none hleft
  have h₂ := tape.right.length_le_of_read_eq_none hright
  unfold BiTape.spaceUsed
  omega

end Cslib.Turing

/-! ### Views -/

namespace Turing.MultiTapeNTM

/-- The summary of an output word for acceptance: empty, exactly `[true]`, or `[false]` for every
other word. -/
def outputClass (word : List Bool) : List Bool :=
  if word = [] then [] else if word = [true] then [true] else [false]

/-- The empty word is its own summary. -/
@[simp] theorem outputClass_nil : outputClass [] = [] := rfl

/-- The summary is `[true]` exactly for the word `[true]`. -/
theorem outputClass_eq_true_iff {word : List Bool} : outputClass word = [true] ↔ word = [true] := by
  unfold outputClass
  split_ifs <;> simp_all

/-- Words of at least two symbols are summarized as `[false]`. -/
theorem outputClass_of_two_le {word : List Bool} (h : 2 ≤ word.length) :
    outputClass word = [false] := by
  have h₁ : word ≠ [] := by rintro rfl; simp at h
  have h₂ : word ≠ [true] := by rintro rfl; simp at h
  simp only [outputClass, h₁, h₂, ↓reduceIte]

/-- Nonempty words have a summary of one symbol. -/
theorem length_outputClass_cons (a : Bool) (word : List Bool) :
    (outputClass (a :: word)).length = 1 := by
  unfold outputClass
  split_ifs <;> simp_all

/-- **The summary is a congruence for appending a symbol.** -/
theorem outputClass_append (word : List Bool) (symbol : Option Bool) :
    outputClass (outputClass word ++ symbol.toList) = outputClass (word ++ symbol.toList) := by
  rcases symbol with _ | b
  · simp only [Option.toList_none, List.append_nil]
    unfold outputClass
    split_ifs <;> simp_all
  · rcases word with _ | ⟨a, word⟩
    · rfl
    · rw [outputClass_of_two_le (by simp [length_outputClass_cons]),
        outputClass_of_two_le (by simp)]

/-- The summary has at most one symbol. -/
theorem length_outputClass_le (word : List Bool) : (outputClass word).length ≤ 1 := by
  unfold outputClass
  split_ifs <;> simp

section Views

/-- The finite configuration with its output replaced by the summary. -/
def _root_.Turing.FiniteCfg.summarizeOutput {k : ℕ} {State : Type*}
    (finite : FiniteCfg k Bool State) : FiniteCfg k Bool State :=
  { finite with output := outputClass finite.output }

variable {k : ℕ} {State : Type*} (ntm : MultiTapeNTM k Bool State)

/-- **The steps of the views.** A running view takes the summarized result of a permitted action;
a halted view steps only to itself. -/
def ViewStep (finite next : FiniteCfg k Bool State) : Prop :=
  match finite.state with
  | none => next = finite
  | some state => ∃ action, ntm.Tr state finite.inputSymbol finite.workTapeSymbols action ∧
      next = (finite.step action).summarizeOutput

/-- The initial view on an input. -/
def initView (input : List Bool) : FiniteCfg k Bool State := FiniteCfg.init ntm.q₀ input

variable {ntm} {input : List Bool}

/-- A view represents a native configuration on `input`: the same input, control and input head,
work tapes centered at the native heads, and the summary of the native output. With the native
output in place of the summary, it is `Turing.FiniteCfg.Represents` (`ViewRep.represents`). -/
structure ViewRep (finite : FiniteCfg k Bool State) (cfg : Cfg k Bool State input) : Prop where
  /-- The inputs agree. -/
  input : finite.input = input
  /-- The controls agree. -/
  state : finite.state = cfg.state
  /-- The input heads agree. -/
  inputPos : finite.inputPos.val = cfg.inputPos.val
  /-- Each work tape represents the native tape at its native head. -/
  workTapes : ∀ tape, (finite.workTapes tape).Represents (cfg.workTapes tape) (cfg.workTapePos tape)
  /-- The output is the summary of the native output. -/
  output : finite.output = outputClass cfg.output

/-- The initial view represents the initial configuration. -/
theorem viewRep_init (input : List Bool) :
    ViewRep (ntm.initView input) (ntm.initCfg input) :=
  ⟨rfl, rfl, rfl, fun _ => BiTape.represents_nil _, rfl⟩

/-- With the native output in place of the summary, a view on the native input is a
`Turing.FiniteCfg.Represents` of the native configuration. -/
theorem ViewRep.represents {finite : FiniteCfg k Bool State} {cfg : Cfg k Bool State finite.input}
    (h : ViewRep finite cfg) :
    ({ finite with output := cfg.output } : FiniteCfg k Bool State).Represents cfg :=
  ⟨h.state, Fin.ext h.inputPos, h.workTapes, rfl⟩

/-- Represented configurations read the same symbols. -/
theorem ViewRep.symbols {finite : FiniteCfg k Bool State} {cfg : Cfg k Bool State input}
    (h : ViewRep finite cfg) :
    finite.inputSymbol = cfg.inputSymbol ∧ finite.workTapeSymbols = cfg.workTapeSymbols := by
  have hinput := h.input
  subst hinput
  exact ⟨h.represents.inputSymbol, h.represents.workTapeSymbols⟩

/-- **Views step with the machine.** The same action preserves the representation. -/
theorem ViewRep.step {finite : FiniteCfg k Bool State} {cfg : Cfg k Bool State input}
    (h : ViewRep finite cfg) (action : Action k Bool State) :
    ViewRep (finite.step action).summarizeOutput (action.apply cfg) := by
  have hinput := h.input
  subst hinput
  have hstep := h.represents.step action
  refine ⟨rfl, hstep.state, congrArg Fin.val hstep.inputPos, hstep.workTapes, ?_⟩
  simp only [FiniteCfg.summarizeOutput, FiniteCfg.step, Action.apply, h.output,
    outputClass_append]

/-- **Every computation path has a reachable view.** -/
theorem exists_viewStep_of_runPath (p : ntm.RunPath input) (hp : p.head = ntm.initCfg input) :
    ∃ finite, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite ∧
      ViewRep finite p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp only [RelSeries.head_singleton] at hp
    subst hp
    exact ⟨_, .refl, viewRep_init input⟩
  | snoc p c hc ih =>
    obtain ⟨finite, hreach, hrep⟩ := ih (by simpa using hp)
    simp only [RelSeries.last_snoc]
    change ntm.Step p.last c at hc
    rcases hs : p.last.state with _ | state
    · rw [(step_of_halt hs).mp hc]
      exact ⟨finite, hreach, hrep⟩
    · simp only [Step, hs] at hc
      obtain ⟨action, htr, rfl⟩ := hc
      obtain ⟨hin, hwork⟩ := hrep.symbols
      refine ⟨_, hreach.tail ?_, hrep.step action⟩
      have hfs : finite.state = some state := hrep.state.trans hs
      simp only [ViewStep, hfs]
      exact ⟨action, by rwa [hin, hwork], rfl⟩

/-- **Every reachable view is the view of a computation path.** -/
theorem exists_computationPath_of_viewStep {finite : FiniteCfg k Bool State}
    (h : Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) :
    ∃ p : ntm.ComputationPath input, ViewRep finite p.last := by
  induction h with
  | refl => exact ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, viewRep_init input⟩
  | @tail view next _ hstep ih =>
    obtain ⟨p, hrep⟩ := ih
    rcases hs : view.state with _ | state
    · simp only [ViewStep, hs] at hstep
      exact ⟨p, hstep ▸ hrep⟩
    · simp only [ViewStep, hs] at hstep
      obtain ⟨action, htr, rfl⟩ := hstep
      obtain ⟨hin, hwork⟩ := hrep.symbols
      have hnative : ntm.Step p.last (action.apply p.last) := by
        simp only [Step, ← hrep.state, hs]
        exact ⟨action, by rwa [← hin, ← hwork], rfl⟩
      exact ⟨⟨p.toRunPath.snoc _ hnative, by simpa using p.head_eq⟩,
        by simpa using hrep.step action⟩

/-- **Acceptance is reachability of views.** A machine accepts exactly when a halted view with
output `[true]` is reachable from the initial view. -/
theorem accepts_iff_reflTransGen_viewStep :
    ntm.Accepts input ↔ ∃ finite, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite ∧
      finite.state = none ∧ finite.output = [true] := by
  constructor
  · rintro ⟨p, hhalt, hout⟩
    obtain ⟨finite, hreach, hrep⟩ := exists_viewStep_of_runPath p.toRunPath p.head_eq
    exact ⟨finite, hreach, hrep.state.trans hhalt, hrep.output.trans (by rw [hout]; rfl)⟩
  · rintro ⟨finite, hreach, hstate, hout⟩
    obtain ⟨p, hrep⟩ := exists_computationPath_of_viewStep hreach
    exact ⟨p, hrep.state.symm.trans hstate,
      outputClass_eq_true_iff.mp (hrep.output.symm.trans hout)⟩

end Views

/-! ### The size of reachable views -/

section Size

/-- A tape representing contents whose head and non-blank cells lie within distance `s` of `0`
is stored in at most `4 * s + 1` cells relative to its head. -/
theorem _root_.Cslib.Turing.BiTape.Represents.spaceUsed_le {tape : BiTape Bool}
    {contents : ℤ → Option Bool} {head : ℤ} (h : tape.Represents contents head) {s : ℕ}
    (hhead : head.natAbs < s) (hcells : ∀ z, contents z ≠ none → z.natAbs < s) :
    tape.spaceUsed ≤ 4 * s + 1 := by
  have hblank (z : ℤ) (hz : s ≤ z.natAbs) : contents z = none := by
    by_contra hne
    exact absurd (hcells z hne) (by omega)
  refine (BiTape.spaceUsed_le_of_read_eq_none tape (m := 2 * s) (fun j hj => ?_)
    fun j hj => ?_).trans (by omega)
  · rw [h]
    exact hblank _ (by omega)
  · rw [h]
    exact hblank _ (by omega)

/-- The bound of `Turing.MultiTapeNTM.length_encFiniteCfg_le` on the encodings of the reachable
views of a machine with `k` work tapes and controls `State`, on inputs of length `n` under the
space bound `s`: linear in `n` and `s`, with a constant depending only on `k` and `State`. -/
noncomputable def viewLengthBound (k : ℕ) (State : Type*) (n s : ℕ) : ℕ :=
  (10 + 2 * Nat.card (Option State) + 200 * k) * (n + s + 1)

/-- The bound grows with the space bound. -/
theorem viewLengthBound_mono (k : ℕ) (State : Type*) (n : ℕ) {s s' : ℕ} (h : s ≤ s') :
    viewLengthBound k State n s ≤ viewLengthBound k State n s' :=
  Nat.mul_le_mul_left _ (by omega)

variable {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}
  {input : List Bool}

/-- **Reachable views are small.** Under a space bound `s`, every view reachable from the initial
view has an encoding of length at most `Turing.MultiTapeNTM.viewLengthBound`, linear in the input
and in `s`, whatever the length of the path reaching it. -/
theorem length_encFiniteCfg_le {s : ℕ} (hs : ntm.RunsInSpace input s)
    {finite : FiniteCfg k Bool State}
    (h : Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite) :
    (MultiTapeTM.encFiniteCfg finite).length ≤ viewLengthBound k State input.length s := by
  rw [viewLengthBound]
  obtain ⟨p, hrep⟩ := exists_computationPath_of_viewStep h
  have hspace : RunPath.space p.toRunPath ≤ s := hs p
  -- every work tape is stored in few cells
  have htape (tape : Fin k) : (finite.workTapes tape).spaceUsed ≤ 4 * s + 1 := by
    have hle : RunPath.spaceUsedByTape p.toRunPath tape ≤ s :=
      (Finset.single_le_sum (f := fun i => RunPath.spaceUsedByTape p.toRunPath i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ tape)).trans hspace
    obtain ⟨hhead, hcells⟩ := RunPath.natAbs_lt_spaceUsedByTape p.toRunPath
      (fun i z => by rw [p.head_eq]; rfl) (fun i => by rw [p.head_eq]; rfl) tape
    exact (hrep.workTapes tape).spaceUsed_le (hhead.trans_le hle)
      fun z hz => (hcells z hz).trans_le hle
  have hwork : (MultiTapeTM.encPi (MultiTapeTM.encBiTape MultiTapeTM.encBool)
      finite.workTapes).length ≤ k * (2 * (12 * (4 * s + 1)) + 1) := by
    simpa using MultiTapeTM.length_encPi_le (MultiTapeTM.encBiTape MultiTapeTM.encBool)
      finite.workTapes fun tape => (MultiTapeTM.length_encBiTape_le MultiTapeTM.encBool _
        (bound := 1) (by simp)).trans (by have := htape tape; nlinarith)
  have hcontrol := MultiTapeTM.length_encFinite_lt finite.state
  have hin : finite.input.length = input.length := by rw [hrep.input]
  have hpos : finite.inputPos.val ≤ input.length + 1 := by
    have := finite.inputPos.isLt
    omega
  have hout : finite.output.length ≤ 1 := hrep.output ▸ length_outputClass_le _
  have hw : 2 * (MultiTapeTM.encPi (MultiTapeTM.encBiTape MultiTapeTM.encBool)
      finite.workTapes).length ≤ 200 * k * (input.length + s + 1) := by nlinarith
  have hc : 2 * (MultiTapeTM.encFinite (Option State) finite.state).length + 2 ≤
      2 * Nat.card (Option State) * (input.length + s + 1) := by nlinarith
  simp only [MultiTapeTM.encFiniteCfg_apply, MultiTapeTM.length_encPair, MultiTapeTM.encBits,
    Function.Embedding.refl_apply, MultiTapeTM.encUnary_apply, List.length_replicate]
  nlinarith

end Size

end Turing.MultiTapeNTM
