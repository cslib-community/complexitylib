/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic

/-!
# Replaying nondeterministic choices with fair coins

A nondeterministic machine with finitely many states and a binary alphabet has finitely many
actions. Its choice table `Turing.MultiTapeNTM.choiceTable` is one fixed finite fair-coin table
that replays a computation path from a list of coins. At a running configuration it scans the
permitted actions in a fixed order (`Turing.MultiTapeNTM.actions`), one coin per candidate: the
coin `true` takes the current candidate, the coin `false` moves on, and the last candidate is
taken under either coin. A step of the nondeterministic machine choosing the candidate of
(zero-based) index `j` therefore costs the coins `false^j true`, at most `Nat.card` of the action
type. Every coin list thus selects permitted actions, except at a stuck configuration, which has
none; there the table rejects: it halts without output.

The table emits nothing while it simulates. It records in its finite control whether the
simulated output is empty, exactly `[true]` or something else
(`Turing.MultiTapeNTM.ChoiceTable.OutputTrack`), and when the simulated machine halts it emits
`true` exactly when the simulated output is `[true]`.
So a running prefix of output `[true]` is never mistaken for acceptance. A halted table ignores
the remaining coins, which allows padding.

## Main definitions

* `Turing.MultiTapeNTM.actions`: the permitted actions, in a fixed order.
* `Turing.MultiTapeNTM.choiceTable`: the fair-coin table replaying choices. Its states
  `Turing.MultiTapeNTM.ChoiceTable.ScanState` record the simulated state, the candidate index
  and the track `Turing.MultiTapeNTM.ChoiceTable.OutputTrack` of the simulated output.

## Main results

* `Turing.MultiTapeNTM.accepts_of_runClosedCoins_choiceTable`: a coin list on which the table
  emits `[true]` encodes an accepting computation path.
* `Turing.MultiTapeNTM.exists_runClosedCoins_choiceTable`: a computation path of `t` steps ending
  halted with output `[true]` is encoded by at most `Nat.card (Action k Bool State) * t` coins,
  followed by arbitrary padding.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State : Type} [Finite State] {input : List Bool}

/-- The actions permitted by `ntm` at a state and read symbols, in a fixed order. -/
noncomputable def actions (ntm : MultiTapeNTM k Bool State) (state : State) (symbol : Option Bool)
    (work : Fin k → Option Bool) : List (Turing.Action k Bool State) :=
  (Set.toFinite {action | ntm.Tr state symbol work action}).toFinset.toList

variable (ntm : MultiTapeNTM k Bool State)

theorem mem_actions {state : State} {symbol : Option Bool} {work : Fin k → Option Bool}
    {action : Turing.Action k Bool State} :
    action ∈ ntm.actions state symbol work ↔ ntm.Tr state symbol work action := by
  simp [actions]

/-- There are at most as many permitted actions as actions. -/
theorem length_actions_le (state : State) (symbol : Option Bool) (work : Fin k → Option Bool) :
    (ntm.actions state symbol work).length ≤ Nat.card (Turing.Action k Bool State) := by
  classical
  have := Fintype.ofFinite (Turing.Action k Bool State)
  rw [actions, Finset.length_toList, Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _

namespace ChoiceTable

/-- Whether an emitted word is empty, exactly `[true]`, or something else. -/
inductive OutputTrack
  /-- Nothing has been emitted. -/
  | empty
  /-- Exactly `[true]` has been emitted. -/
  | accept
  /-- Something else has been emitted. -/
  | other
  deriving DecidableEq

namespace OutputTrack

instance : Fintype OutputTrack :=
  ⟨{empty, accept, other}, fun t => by cases t <;> simp⟩

/-- The track of a word. -/
def ofWord (word : List Bool) : OutputTrack :=
  if word = [] then empty else if word = [true] then accept else other

/-- The track after emitting one more symbol, if any. -/
def emit : OutputTrack → Option Bool → OutputTrack
  | track, none => track
  | empty, some true => accept
  | _, some _ => other

@[simp] theorem ofWord_nil : ofWord [] = empty := rfl

/-- Emitting a symbol updates the track of the word. -/
theorem ofWord_append (word : List Bool) (symbol : Option Bool) :
    ofWord (word ++ symbol.toList) = (ofWord word).emit symbol := by
  rcases symbol with _ | b
  · simp [emit]
  · rcases word with _ | ⟨x, word⟩
    · cases b <;> simp [ofWord, emit]
    · by_cases h : x :: word = [true]
      · simp [ofWord, emit, h]
      · simp [ofWord, emit, h]

/-- A word is `[true]` exactly when its track is `accept`. -/
theorem ofWord_eq_accept_iff (word : List Bool) : ofWord word = accept ↔ word = [true] := by
  unfold ofWord
  split_ifs with h₁ h₂ <;> simp_all

/-- Emitting the same word after words with the same track gives words with the same track. -/
theorem ofWord_append_eq_of_eq {word word' : List Bool} (h : ofWord word = ofWord word')
    (more : List Bool) : ofWord (word ++ more) = ofWord (word' ++ more) := by
  induction more using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton more symbol ih =>
    have hsym : [symbol] = (some symbol).toList := rfl
    rw [← List.append_assoc, ← List.append_assoc, hsym, ofWord_append, ofWord_append, ih]

/-- A word with a given track: `[]`, `[true]` or `[false]`. -/
def toWord : OutputTrack → List Bool
  | empty => []
  | accept => [true]
  | other => [false]

@[simp] theorem ofWord_toWord (track : OutputTrack) : ofWord track.toWord = track := by
  cases track <;> rfl

end OutputTrack

/-- The states of the choice table: the simulated state, the index of the candidate action, and
the track of the simulated output. -/
abbrev ScanState (k : ℕ) (State : Type) :=
  State × Fin (Nat.card (Turing.Action k Bool State) + 1) × OutputTrack

/-- Take a simulated action. Its output is recorded in the track instead of being emitted; when
it halts, `true` is emitted exactly when the simulated output is `[true]`. -/
noncomputable def perform (track : OutputTrack) (action : Turing.Action k Bool State) :
    Turing.Action k Bool (ScanState k State) :=
  match action.state with
  | some next =>
    ⟨action.inputTape, action.workTapes, none, some (next, 0, track.emit action.output)⟩
  | none =>
    ⟨action.inputTape, action.workTapes,
      if track.emit action.output = .accept then some true else none, none⟩

/-- Leave the tapes unchanged and continue in `next`, or halt without output. -/
def idle {S : Type} (next : Option S) : Turing.Action k Bool S :=
  ⟨0, fun _ => (none, 0), none, next⟩

/-- One instruction of the choice table: take or skip the candidate `j`, or reject if there is
no such candidate. -/
noncomputable def scan (s : ScanState k State) (symbol : Option Bool) (work : Fin k → Option Bool)
    (bit : Bool) : Turing.Action k Bool (ScanState k State) :=
  let candidates := ntm.actions s.1 symbol work
  match candidates[s.2.1.val]? with
  | none => idle none
  | some action =>
    if bit || s.2.1.val + 1 = candidates.length then perform s.2.2 action
    else idle (some (s.1, ⟨min (s.2.1.val + 1) (Nat.card (Turing.Action k Bool State)),
      Nat.lt_succ_of_le (min_le_right _ _)⟩, s.2.2))

end ChoiceTable

/-- **The choice table.** A fixed finite fair-coin table replaying the choices of `ntm`, one coin
per candidate action. -/
noncomputable def choiceTable : MultiTapePTM k Bool (ChoiceTable.ScanState k State) where
  initial := (ntm.q₀, 0, .empty)
  tr s symbol work _ bit := .step (ChoiceTable.scan ntm s symbol work bit) Empty.elim Empty.elim

namespace ChoiceTable

/-- A running instruction of the choice table applies `scan`. -/
theorem step_choiceTable {cfg : Cfg k Bool (ScanState k State) input} {s : ScanState k State}
    (h : cfg.state = some s) (bit : Bool) :
    (ntm.choiceTable.withCoin bit).toTM.step cfg =
      (scan ntm s cfg.inputSymbol cfg.workTapeSymbols bit).apply cfg := by
  rw [MultiTapeTM.step_of_state h, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  rfl

/-- The table simulating the running configuration `c` in state `state`, before candidate `j`. -/
def scanCfg (c : Cfg k Bool State input) (state : State)
    (j : Fin (Nat.card (Turing.Action k Bool State) + 1)) : Cfg k Bool (ScanState k State) input :=
  ⟨some (state, j, OutputTrack.ofWord c.output), c.inputPos, c.workTapes, c.workTapePos, []⟩

/-- The halted table after simulating the halted configuration `c`. -/
def haltCfg (c : Cfg k Bool State input) : Cfg k Bool (ScanState k State) input :=
  ⟨none, c.inputPos, c.workTapes, c.workTapePos, if c.output = [true] then [true] else []⟩

/-- The table simulating a configuration, before its first candidate. -/
noncomputable def simCfg (c : Cfg k Bool State input) : Cfg k Bool (ScanState k State) input :=
  match c.state with
  | some state => scanCfg c state 0
  | none => haltCfg c

/-- The table starts by simulating the initial configuration. -/
theorem initCfg_choiceTable (input : List Bool) :
    ntm.choiceTable.toNTM.initCfg input = simCfg (ntm.initCfg input) := rfl

omit [Finite State] in
/-- Taking a candidate simulates its step. -/
theorem apply_perform (c : Cfg k Bool State input) (state : State)
    (j : Fin (Nat.card (Turing.Action k Bool State) + 1)) (action : Turing.Action k Bool State) :
    (perform (OutputTrack.ofWord c.output) action).apply (scanCfg c state j) =
      simCfg (action.apply c) := by
  rcases hs : action.state with _ | next
  · have hacc : (OutputTrack.ofWord c.output).emit action.output = .accept ↔
        c.output ++ action.output.toList = [true] := by
      rw [← OutputTrack.ofWord_append, OutputTrack.ofWord_eq_accept_iff]
    simp only [perform, hs, simCfg, haltCfg, Action.apply, scanCfg, Cfg.mk.injEq, true_and,
      List.nil_append, hacc]
    split_ifs <;> rfl
  · simp only [perform, hs, simCfg, scanCfg, Action.apply, Cfg.mk.injEq, Option.toList_none,
      List.append_nil, and_true]
    rw [OutputTrack.ofWord_append]

/-- An idle instruction changes only the control state. -/
theorem apply_idle {S : Type} (next : Option S) (cfg : Cfg k Bool S input) :
    (idle next).apply cfg = ⟨next, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩ := by
  simp [idle, Action.apply]

variable {ntm}

section scan

variable {state : State} {symbol : Option Bool} {work : Fin k → Option Bool}
  {j : Fin (Nat.card (Turing.Action k Bool State) + 1)} {track : OutputTrack}
  {action : Turing.Action k Bool State}

theorem scan_of_getElem?_eq_none (hj : (ntm.actions state symbol work)[j.val]? = none)
    (bit : Bool) : scan ntm (state, j, track) symbol work bit = idle none := by
  simp [scan, hj]

theorem scan_of_take (hj : (ntm.actions state symbol work)[j.val]? = some action) {bit : Bool}
    (hbit : bit = true ∨ j.val + 1 = (ntm.actions state symbol work).length) :
    scan ntm (state, j, track) symbol work bit = perform track action := by
  have hcond : (bit || decide (j.val + 1 = (ntm.actions state symbol work).length)) = true := by
    rcases hbit with rfl | h <;> simp [*]
  simp only [scan, hj, hcond, ↓reduceIte]

theorem scan_of_skip (hj : (ntm.actions state symbol work)[j.val]? = some action)
    (hlast : j.val + 1 ≠ (ntm.actions state symbol work).length) :
    scan ntm (state, j, track) symbol work false = idle (some (state, ⟨j.val + 1,
      Nat.lt_succ_of_le (by
        have := ntm.length_actions_le state symbol work
        have := (List.getElem?_eq_some_iff.mp hj).1
        omega)⟩, track)) := by
  have hle : j.val + 1 ≤ Nat.card (Turing.Action k Bool State) := by
    have := ntm.length_actions_le state symbol work
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  simp only [scan, hj, Bool.false_or, decide_eq_true_eq, hlast, ↓reduceIte, min_eq_left hle]

end scan

variable {c : Cfg k Bool State input} {state : State}
  {j : Fin (Nat.card (Turing.Action k Bool State) + 1)} {action : Turing.Action k Bool State}

/-- Skipping a candidate that is not the last moves to the next candidate. -/
theorem step_scanCfg_skip
    (hj : (ntm.actions state c.inputSymbol c.workTapeSymbols)[j.val]? = some action)
    (hlast : j.val + 1 ≠ (ntm.actions state c.inputSymbol c.workTapeSymbols).length) :
    (ntm.choiceTable.withCoin false).toTM.step (scanCfg c state j) =
      scanCfg c state ⟨j.val + 1, Nat.lt_succ_of_le (by
        have := ntm.length_actions_le state c.inputSymbol c.workTapeSymbols
        have := (List.getElem?_eq_some_iff.mp hj).1
        omega)⟩ := by
  rw [step_choiceTable ntm rfl]
  change (scan ntm (state, j, _) c.inputSymbol c.workTapeSymbols false).apply _ = _
  rw [scan_of_skip hj hlast, apply_idle]
  rfl

/-- Taking a candidate, under the coin `true` or as the last candidate, simulates its step. -/
theorem step_scanCfg_take
    (hj : (ntm.actions state c.inputSymbol c.workTapeSymbols)[j.val]? = some action) {bit : Bool}
    (hbit : bit = true ∨ j.val + 1 = (ntm.actions state c.inputSymbol c.workTapeSymbols).length) :
    (ntm.choiceTable.withCoin bit).toTM.step (scanCfg c state j) = simCfg (action.apply c) := by
  rw [step_choiceTable ntm rfl]
  change (scan ntm (state, j, _) c.inputSymbol c.workTapeSymbols bit).apply _ = _
  rw [scan_of_take hj hbit]
  exact apply_perform c state j action

/-- Without a candidate `j`, the table rejects: it halts without output. -/
theorem step_scanCfg_reject
    (hj : (ntm.actions state c.inputSymbol c.workTapeSymbols)[j.val]? = none) (bit : Bool) :
    (ntm.choiceTable.withCoin bit).toTM.step (scanCfg c state j) =
      ⟨none, c.inputPos, c.workTapes, c.workTapePos, []⟩ := by
  rw [step_choiceTable ntm rfl]
  change (scan ntm (state, j, _) c.inputSymbol c.workTapeSymbols bit).apply _ = _
  rw [scan_of_getElem?_eq_none hj, apply_idle]
  rfl

/-! ### Soundness -/

/-- The configurations reachable by replaying coins: simulating a reachable running
configuration, rejected, or accepted after an accepting computation path. -/
def Replayable (ntm : MultiTapeNTM k Bool State) (input : List Bool)
    (b : Cfg k Bool (ScanState k State) input) : Prop :=
  (∃ (p : ntm.ComputationPath input) (state : State) (j : _), p.last.state = some state ∧
    b = scanCfg p.last state j) ∨
  (b.state = none ∧ b.output = []) ∨
  (b.state = none ∧ b.output = [true] ∧ ntm.Accepts input)

/-- Every coin preserves replayability. -/
theorem Replayable.step {b : Cfg k Bool (ScanState k State) input}
    (h : Replayable ntm input b) (bit : Bool) :
    Replayable ntm input ((ntm.choiceTable.withCoin bit).toTM.step b) := by
  rcases h with ⟨p, state, j, hstate, rfl⟩ | ⟨hhalt, hout⟩ | ⟨hhalt, hout, hacc⟩
  · rcases hj : (ntm.actions state p.last.inputSymbol p.last.workTapeSymbols)[j.val]? with
      _ | action
    · rw [step_scanCfg_reject hj]
      exact .inr (.inl ⟨rfl, rfl⟩)
    have hmem := List.mem_of_getElem? hj
    have hstep : ntm.Step p.last (action.apply p.last) := by
      simp only [Step, hstate]
      exact ⟨action, (ntm.mem_actions).mp hmem, rfl⟩
    obtain ⟨q, -, hq⟩ := ComputationPath.exists_snoc p hstep
    have htake : ∀ bit : Bool,
        bit = true ∨ j.val + 1 = (ntm.actions state p.last.inputSymbol
          p.last.workTapeSymbols).length →
        Replayable ntm input
          ((ntm.choiceTable.withCoin bit).toTM.step (scanCfg p.last state j)) := by
      intro bit hbit
      rw [step_scanCfg_take hj hbit, ← hq]
      rcases hs : q.last.state with _ | next
      · simp only [simCfg, hs, haltCfg]
        by_cases hout : q.last.output = [true]
        · exact .inr (.inr ⟨rfl, by simp [hout], q, hs, hout⟩)
        · exact .inr (.inl ⟨rfl, by simp [hout]⟩)
      · simp only [simCfg, hs]
        exact .inl ⟨q, next, 0, hs, rfl⟩
    by_cases hlast : j.val + 1 = (ntm.actions state p.last.inputSymbol
        p.last.workTapeSymbols).length
    · exact htake bit (.inr hlast)
    · cases bit
      · rw [step_scanCfg_skip hj hlast]
        exact .inl ⟨p, state, _, hstate, rfl⟩
      · exact htake true (.inl rfl)
  · rw [MultiTapeTM.step_of_halt hhalt]
    exact .inr (.inl ⟨hhalt, hout⟩)
  · rw [MultiTapeTM.step_of_halt hhalt]
    exact .inr (.inr ⟨hhalt, hout, hacc⟩)

/-! ### Completeness -/

/-- One step of a running configuration is replayed by at most `Nat.card` coins. -/
theorem exists_coins_step {c c' : Cfg k Bool State input} {state : State}
    (hstate : c.state = some state) (h : ntm.Step c c') :
    ∃ coins : List Bool, coins.length ≤ Nat.card (Turing.Action k Bool State) ∧
      ntm.choiceTable.stepCoins coins (simCfg c) = simCfg c' := by
  simp only [Step, hstate] at h
  obtain ⟨action, htr, rfl⟩ := h
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem ((ntm.mem_actions).mpr htr)
  have hlen := ntm.length_actions_le state c.inputSymbol c.workTapeSymbols
  -- skip the first `i` candidates
  have hskip : ∀ i (hi : i ≤ j), ntm.choiceTable.stepCoins (List.replicate i false)
      (scanCfg c state 0) = scanCfg c state ⟨i, by omega⟩ := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [List.replicate_succ', MultiTapePTM.stepCoins_append, ih (by omega),
        MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_nil]
      obtain ⟨a, ha⟩ : ∃ a, (ntm.actions state c.inputSymbol c.workTapeSymbols)[i]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact step_scanCfg_skip (j := ⟨i, by omega⟩) ha (by change i + 1 ≠ _; omega)
  refine ⟨List.replicate j false ++ [true], by
    simp only [List.length_append, List.length_replicate, List.length_singleton]; omega, ?_⟩
  rw [MultiTapePTM.stepCoins_append]
  simp only [simCfg, hstate]
  rw [hskip j le_rfl, MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_nil]
  exact step_scanCfg_take (j := ⟨j, by omega⟩) (by simp [← hget]) (.inl rfl)

/-- A run path is replayed from the simulation of its head by at most `Nat.card` coins per step.
Halted steps need no coins. -/
theorem exists_coins_runPath (p : ntm.RunPath input) :
    ∃ coins : List Bool, coins.length ≤ Nat.card (Turing.Action k Bool State) * p.length ∧
      ntm.choiceTable.stepCoins coins (simCfg p.head) = simCfg p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton c => exact ⟨[], by simp, rfl⟩
  | snoc p c hc ih =>
    obtain ⟨coins, hlen, hcoins⟩ := ih
    simp only [RelSeries.head_snoc, RelSeries.last_snoc, RelSeries.snoc_length]
    rcases hs : p.last.state with _ | state
    · have hc' : c = p.last := (step_of_halt hs).mp hc
      exact ⟨coins, hlen.trans (Nat.mul_le_mul_left _ (Nat.le_succ _)), hc' ▸ hcoins⟩
    · obtain ⟨more, hmore, hstep⟩ := exists_coins_step hs hc
      refine ⟨coins ++ more, ?_, ?_⟩
      · rw [List.length_append, Nat.mul_succ]
        omega
      · rw [MultiTapePTM.stepCoins_append, hcoins, hstep]

/-- A halted table ignores further coins. -/
theorem stepCoins_haltCfg (c : Cfg k Bool State input) (coins : List Bool) :
    ntm.choiceTable.stepCoins coins (haltCfg c) = haltCfg c := by
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    rw [MultiTapePTM.stepCoins_cons, MultiTapeTM.step_of_halt rfl]
    exact ih

end ChoiceTable

open ChoiceTable

variable {ntm}

/-- **Soundness.** A coin list on which the choice table emits `[true]` encodes an accepting
computation path. -/
theorem accepts_of_runClosedCoins_choiceTable {coins : List Bool}
    (h : ntm.choiceTable.runClosedCoins coins input = [true]) : ntm.Accepts input := by
  have hinit : Replayable ntm input (ntm.choiceTable.toNTM.initCfg input) :=
    .inl ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, ntm.q₀, 0, rfl, rfl⟩
  have hreplay : ∀ (coins : List Bool) (b : Cfg k Bool (ScanState k State) input),
      Replayable ntm input b → Replayable ntm input (ntm.choiceTable.stepCoins coins b) := by
    intro coins
    induction coins with
    | nil => exact fun _ hb => hb
    | cons bit coins ih => exact fun b hb => ih _ (hb.step bit)
  have hout : (ntm.choiceTable.stepCoins coins (ntm.choiceTable.toNTM.initCfg input)).output =
      [true] := by
    rw [MultiTapePTM.initCfg_toNTM, ← MultiTapePTM.tapes_runClosedConfigFromCoins]
    exact h
  rcases hreplay coins _ hinit with ⟨p, state, j, -, hb⟩ | ⟨-, hnil⟩ | ⟨-, -, hacc⟩
  · rw [hb] at hout
    simp [scanCfg] at hout
  · rw [hnil] at hout
    simp at hout
  · exact hacc

/-- **Completeness.** A computation path of `t` steps ending halted with output `[true]` is
encoded by at most `Nat.card (Action k Bool State) * t` coins, after which any padding is
ignored. -/
theorem exists_runClosedCoins_choiceTable (p : ntm.ComputationPath input) (hhalt : p.last.Halted)
    (hout : p.last.output = [true]) :
    ∃ coins : List Bool, coins.length ≤ Nat.card (Turing.Action k Bool State) * p.time ∧
      ∀ padding, ntm.choiceTable.runClosedCoins (coins ++ padding) input = [true] := by
  obtain ⟨coins, hlen, hcoins⟩ := exists_coins_runPath p.toRunPath
  refine ⟨coins, hlen, fun padding => ?_⟩
  have hsim : simCfg p.last = haltCfg p.last := by
    simp only [simCfg, show p.last.state = none from hhalt]
  rw [MultiTapePTM.runClosedCoins, MultiTapePTM.tapes_runClosedConfigFromCoins,
    ← MultiTapePTM.initCfg_toNTM, initCfg_choiceTable, ← p.head_eq,
    MultiTapePTM.stepCoins_append, hcoins, hsim, stepCoins_haltCfg]
  simp [haltCfg, hout]

end Turing.MultiTapeNTM
