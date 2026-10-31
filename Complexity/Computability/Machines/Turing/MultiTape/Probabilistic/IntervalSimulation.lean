/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalTensor
public import Complexity.Computability.Machines.Turing.MultiTape.Run
public import Complexity.Foundations.Data.BiTape.OfCells

/-!
# Interval steps by finite simulation

An interval step (`Turing.MultiTapePTM.IntervalStep`) replays coins from a configuration whose
work tapes are functions on `ℤ`. This module decides it by a simulation on finite storage, the
first step towards computing the block-counting networks of #1833 in polynomial time.

**Finite storage** (`Turing.MultiTapePTM.LocalCfg`) keeps the control, the input position as a
natural number, every work tape as a `Cslib.Turing.BiTape` around its head together with the
head's absolute position, and only the track of the output
(`Turing.MultiTapeNTM.ChoiceTable.OutputTrack`), which is all a control record keeps. One coin
step (`Turing.MultiTapePTM.localCoinStep`) applies the table's action; on halted storage it changes
nothing. Finite storage *represents* a configuration (`Turing.MultiTapePTM.LocalCfg.Represents`)
when it has its control, input position, head positions, output track and the contents of every
work tape around its head; steps preserve this
(`Turing.MultiTapePTM.LocalCfg.Represents.localRun`).

**The window.** The configuration embedded at block indices `J` with control record `cIn` and
window contents `wIn` (`Turing.embedCfg`) is represented by `Turing.MultiTapePTM.localStart`,
which loads the `3 b` cells of each window into a tape (`Cslib.Turing.BiTape.ofCells`). Its control
record, block indices and window contents are read back from finite storage
(`Turing.MultiTapePTM.LocalCfg.blockControl`, `Turing.MultiTapePTM.LocalCfg.blockIndex`,
`Turing.MultiTapePTM.LocalCfg.windowContents`).

## Main definitions

* `Turing.MultiTapePTM.LocalCfg`: finite storage for replaying an interval.
* `Turing.MultiTapePTM.coinAction`, `Turing.MultiTapePTM.localCoinStep`,
  `Turing.MultiTapePTM.localRun`: one coin step and a replay on finite storage.
* `Turing.MultiTapePTM.windowCells`, `Turing.MultiTapePTM.localStart`: the finite storage of an
  embedded window.
* `Turing.MultiTapePTM.LocalIntervalStep`: the interval condition on finite storage.

## Main results

* `Turing.MultiTapePTM.LocalCfg.Represents.localRun`: replays preserve the representation.
* `Turing.MultiTapePTM.represents_localStart`: the finite storage of an embedded window.
* `Turing.MultiTapePTM.intervalStep_iff_localIntervalStep`: interval steps are decided by finite
  simulation.
* `Turing.MultiTapePTM.intervalCount_eq_card_localIntervalStep`: so are the interval tensors.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeNTM.ChoiceTable Cslib.Turing

variable {k : ℕ} {State : Type}

/-! ### Finite storage and its steps -/

/-- **Finite storage** for replaying an interval: the control, the input position (`0` and
`|input| + 1` are the end cells), every work tape around its head with the head's absolute
position, and the track of the output. -/
structure LocalCfg (k : ℕ) (State : Type) where
  /-- The control, or `none` when halted. -/
  state : Option State
  /-- The input position, as in `Turing.Cfg.inputPos`. -/
  inputPos : ℕ
  /-- Every work tape, around its head. -/
  workTapes : Fin k → BiTape Bool
  /-- The absolute position of every work head. -/
  workTapePos : Fin k → ℤ
  /-- The track of the output. -/
  track : OutputTrack

variable (machine : MultiTapePTM k Bool State)

/-- The action from a control under a coin: the table's action when running, and the action that
changes nothing when halted. -/
@[expose] def coinAction (state : Option State) (symbol : Option Bool)
    (work : Fin k → Option Bool) (bit : Bool) : Action k Bool State :=
  match state with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some q => MultiTapeMachine.Action.emptyOracleEquiv (machine.tr q symbol work Empty.elim bit)

/-- One coin step on finite storage. -/
@[expose] def localCoinStep (input : List Bool) (l : LocalCfg k State) (bit : Bool) :
    LocalCfg k State :=
  let a := machine.coinAction l.state (inputAt input l.inputPos) (fun h => (l.workTapes h).head) bit
  { state := a.state
    inputPos := moveInputPosNat input.length l.inputPos a.inputTape
    workTapes := fun h => (l.workTapes h).step (a.workTapes h)
    workTapePos := fun h => l.workTapePos h + (a.workTapes h).2
    track := l.track.emit a.output }

/-- Replaying coins on finite storage. -/
@[expose] def localRun (input : List Bool) (coins : List Bool) (l : LocalCfg k State) :
    LocalCfg k State :=
  coins.foldl (machine.localCoinStep input) l

/-- Finite storage **represents** a configuration when it has its control, input position, head
positions and output track, and every work tape holds the configuration's tape around its
head. -/
structure LocalCfg.Represents {input : List Bool} (l : LocalCfg k State)
    (c : Cfg k Bool State input) : Prop where
  /-- The controls agree. -/
  state : l.state = c.state
  /-- The input positions agree. -/
  inputPos : l.inputPos = c.inputPos.val
  /-- Every finite work tape holds the configuration's tape around its head. -/
  workTapes : ∀ h, (l.workTapes h).Represents (c.workTapes h) (c.workTapePos h)
  /-- The work head positions agree. -/
  workTapePos : l.workTapePos = c.workTapePos
  /-- The output track is the track of the configuration's output. -/
  track : l.track = OutputTrack.ofWord c.output

/-- A coin step of a fair-coin table applies `coinAction`. -/
theorem withCoin_step_eq (bit : Bool) {input : List Bool} (c : Cfg k Bool State input) :
    (machine.withCoin bit).toTM.step c =
      (machine.coinAction c.state c.inputSymbol c.workTapeSymbols bit).apply c := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    simp only [coinAction]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [Action.apply, hs]
    · simp [Action.apply]
    · funext h
      simp [Action.apply]
    · funext h
      simp [Action.apply]
    · simp [Action.apply]
  | some q =>
    rw [MultiTapeTM.step_of_state hs]
    simp only [coinAction, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    rfl

/-- **A coin step preserves the representation.** -/
theorem LocalCfg.Represents.localCoinStep {input : List Bool} {l : LocalCfg k State}
    {c : Cfg k Bool State input} (h : l.Represents c) (bit : Bool) :
    (machine.localCoinStep input l bit).Represents ((machine.withCoin bit).toTM.step c) := by
  have hsym : inputAt input l.inputPos = c.inputSymbol := by
    rw [Cfg.inputSymbol_eq_inputAt, h.inputPos]
  have hwork : (fun i => (l.workTapes i).head) = c.workTapeSymbols :=
    funext fun i => (h.workTapes i).head
  rw [withCoin_step_eq]
  unfold MultiTapePTM.localCoinStep
  rw [hsym, hwork, h.state]
  set a := machine.coinAction c.state c.inputSymbol c.workTapeSymbols bit
  refine ⟨rfl, ?_, fun i => ?_, ?_, ?_⟩
  · rw [h.inputPos]
    exact (val_moveInputPos_eq_moveInputPosNat _ _).symm
  · have hstep := (h.workTapes i).step (a.workTapes i)
    rcases hw : (a.workTapes i) with ⟨w, m⟩
    rw [hw] at hstep
    cases w <;> simpa [Action.apply, hw] using hstep
  · funext i
    simp [Action.apply, h.workTapePos]
  · simp [Action.apply, h.track, OutputTrack.ofWord_append]

/-- **A replay preserves the representation.** -/
theorem LocalCfg.Represents.localRun {input : List Bool} {l : LocalCfg k State}
    {c : Cfg k Bool State input} (h : l.Represents c) (coins : List Bool) :
    (machine.localRun input coins l).Represents (machine.stepCoins coins c) := by
  induction coins generalizing l c with
  | nil => exact h
  | cons bit coins ih => exact ih (h.localCoinStep machine bit)

/-! ### Reading a configuration's view off finite storage -/

section View

variable (b : ℕ) [NeZero b]

/-- The control record of finite storage: its control, the offset of every head in its block,
and its output track. -/
@[expose] def LocalCfg.blockControl (l : LocalCfg k State) : BlockControl k State b :=
  (l.state, fun head => match head with
    | none => (((l.inputPos : ℤ) - 1 : ℤ) : ZMod b)
    | some h => ((l.workTapePos h : ℤ) : ZMod b), l.track)

/-- The block index of every head of finite storage. -/
@[expose] def LocalCfg.blockIndex (l : LocalCfg k State) : Option (Fin k) → ℤ
  | none => ((l.inputPos : ℤ) - 1) / b
  | some h => l.workTapePos h / b

/-- The contents of the windows around block indices `J`, read off finite storage. -/
@[expose] def LocalCfg.windowContents (J : Option (Fin k) → ℤ) (l : LocalCfg k State) :
    Fin k → Fin 3 → ZMod b → Option Bool := fun h d r =>
  (l.workTapes h).read (b * (J (some h) + d - 1) + r.val - l.workTapePos h)

variable {b} {input : List Bool} {l : LocalCfg k State} {c : Cfg k Bool State input}

omit [NeZero b] in
theorem LocalCfg.Represents.blockControl (h : l.Represents c) :
    l.blockControl b = c.blockControl b := by
  simp only [LocalCfg.blockControl, Cfg.blockControl, h.state, h.track, h.inputPos,
    h.workTapePos]
  congr 2
  funext head
  cases head <;> simp

omit [NeZero b] in
theorem LocalCfg.Represents.blockIndex (h : l.Represents c) :
    l.blockIndex b = c.blockIndex b := by
  funext head
  cases head <;> simp [LocalCfg.blockIndex, Cfg.blockIndex, h.inputPos, h.workTapePos]

omit [NeZero b] in
theorem LocalCfg.Represents.windowContents (h : l.Represents c) (J : Option (Fin k) → ℤ) :
    l.windowContents b J = c.windowContents b J := by
  funext i d r
  simp only [LocalCfg.windowContents, Cfg.windowContents, Cfg.blockContents,
    h.workTapes i _, h.workTapePos]
  congr 1
  ring

end View

/-! ### The finite storage of an embedded window -/

section Window

variable (b : ℕ) [NeZero b]

/-- The `3 b` cells of the three blocks of a window, left to right. -/
@[expose] def windowCells (w : Fin 3 → ZMod b → Option Bool) : List (Option Bool) :=
  (List.range (3 * b)).map fun c => if hc : c / b < 3 then w ⟨c / b, hc⟩ (c : ZMod b) else none

/-- The finite storage of the configuration embedded at block indices `J` with control record
`cIn` and window contents `wIn` (`Turing.embedCfg`): each work tape holds the cells of its window
with its head on cell `b + offset`, in the middle block. -/
@[expose] def localStart (input : List Bool) (J : Option (Fin k) → ℤ)
    (cIn : BlockControl k State b) (wIn : Fin k → Fin 3 → ZMod b → Option Bool) :
    LocalCfg k State where
  state := cIn.1
  inputPos := (inputPosOfCoord input (b * J none + (cIn.2.1 none).val)).val
  workTapes h := BiTape.ofCells (windowCells b (wIn h)) (b + (cIn.2.1 (some h)).val)
  workTapePos h := b * J (some h) + (cIn.2.1 (some h)).val
  track := cIn.2.2

/-- The window cells hold the window: the cell at offset `c` from the start of the window is
entry `c / b` of the window at `c mod b`. -/
private theorem windowCell_eq (J : Option (Fin k) → ℤ) (w : Fin k → Fin 3 → ZMod b → Option Bool)
    (h : Fin k) (c : ℤ) :
    windowCell b J w h (b * (J (some h) - 1) + c) =
      if 0 ≤ c then (windowCells b (w h)).getD c.toNat none else none := by
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  have hdiv : (b * (J (some h) - 1) + c) / b = J (some h) - 1 + c / b := by
    rw [add_comm, Int.add_mul_ediv_left _ _ hb.ne', add_comm]
  unfold windowCell
  by_cases hc : 0 ≤ c
  · rw [ite_eq_left hc]
    have hcn : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc
    obtain ⟨d, hd⟩ : ∃ d, d = c.toNat / b := ⟨_, rfl⟩
    have hcd : c / b = (d : ℤ) := by
      rw [hd, Int.natCast_div, hcn]
    by_cases hlt : c.toNat < 3 * b
    · have hcb : d < 3 := by
        rw [hd, Nat.div_lt_iff_lt_mul (Nat.pos_of_neZero b)]
        linarith
      have hcond : 0 ≤ (b * (J (some h) - 1) + c) / b - J (some h) + 1 ∧
          (b * (J (some h) - 1) + c) / b - J (some h) + 1 < 3 := by
        rw [hdiv, hcd]
        omega
      have hidx : ((b * (J (some h) - 1) + c) / b - J (some h) + 1).toNat = d := by
        rw [hdiv, hcd]
        omega
      have hcast : (((b * (J (some h) - 1) + c : ℤ)) : ZMod b) = ((c.toNat : ℕ) : ZMod b) := by
        rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
          ← Int.cast_natCast, hcn]
      rw [dite_eq_left hcond, windowCells, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hlt, Option.map_some, Option.getD_some, ← hd, dite_eq_left hcb,
        hcast]
      simp only [hidx]
    · have hlen : (windowCells b (w h)).length ≤ c.toNat := by
        simp only [windowCells, List.length_map, List.length_range]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      have : 3 ≤ c / b := by
        rw [hcd]
        have : 3 ≤ d := hd ▸ (Nat.le_div_iff_mul_le (Nat.pos_of_neZero b)).mpr (by omega)
        omega
      rw [dite_eq_right (by rw [hdiv]; omega)]
      rfl
  · rw [ite_eq_right hc]
    have : c / b < 0 := Int.ediv_neg_of_neg_of_pos (by omega) hb
    exact dite_eq_right (by rw [hdiv]; omega)

/-- **The finite storage of an embedded window represents it.** -/
theorem represents_localStart (input : List Bool) (J : Option (Fin k) → ℤ)
    (cIn : BlockControl k State b) (wIn : Fin k → Fin 3 → ZMod b → Option Bool) :
    (localStart b input J cIn wIn).Represents (embedCfg (input := input) b J cIn wIn) := by
  refine ⟨rfl, rfl, fun h z => ?_, rfl, (OutputTrack.ofWord_toWord _).symm⟩
  rw [localStart, BiTape.read_ofCells]
  change _ = windowCell b J wIn h (b * J (some h) + (cIn.2.1 (some h)).val + z)
  rw [show (b : ℤ) * J (some h) + (cIn.2.1 (some h)).val + z =
      b * (J (some h) - 1) + (((b + (cIn.2.1 (some h)).val : ℕ) : ℤ) + z) by push_cast; ring,
    windowCell_eq]

end Window

/-! ### Interval steps by finite simulation -/

section Interval

variable (b : ℕ) [NeZero b]

/-- **The interval condition on finite storage**: replaying `coins` on the finite storage of the
embedded window leaves the control record `cOut` and the window contents `wOut`, and moves the
block of every head `h` by `δ h`. -/
@[expose] def LocalIntervalStep (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool) (coins : List Bool)
    (cOut : BlockControl k State b) (wOut : Fin k → Fin 3 → ZMod b → Option Bool) : Prop :=
  (machine.localRun input coins (localStart b input J cIn wIn)).blockControl b = cOut ∧
    (machine.localRun input coins (localStart b input J cIn wIn)).windowContents b J = wOut ∧
    ∀ head, (machine.localRun input coins (localStart b input J cIn wIn)).blockIndex b head =
      J head + δ head

instance [DecidableEq State] (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool) (coins : List Bool)
    (cOut : BlockControl k State b) (wOut : Fin k → Fin 3 → ZMod b → Option Bool) :
    Decidable (machine.LocalIntervalStep b input J δ cIn wIn coins cOut wOut) := by
  unfold LocalIntervalStep
  infer_instance

/-- **Interval steps are decided by finite simulation.** -/
theorem intervalStep_iff_localIntervalStep (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool) (coins : List Bool)
    (cOut : BlockControl k State b) (wOut : Fin k → Fin 3 → ZMod b → Option Bool) :
    machine.IntervalStep b input J δ cIn wIn coins cOut wOut ↔
      machine.LocalIntervalStep b input J δ cIn wIn coins cOut wOut := by
  have h := (represents_localStart b input J cIn wIn).localRun machine coins
  simp only [IntervalStep, LocalIntervalStep, h.blockControl, h.windowContents,
    h.blockIndex]

open scoped Classical in
/-- **Interval tensors by finite simulation**: the interval tensor counts the bit strings that
satisfy the interval condition on finite storage. -/
theorem intervalCount_eq_card_localIntervalStep (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool)
    (cOut : BlockControl k State b) (wOut : Fin k → Fin 3 → ZMod b → Option Bool) :
    machine.intervalCount b input J δ cIn wIn cOut wOut =
      (Finset.univ.filter fun u : Fin b → Bool =>
        machine.LocalIntervalStep b input J δ cIn wIn (List.ofFn u) cOut wOut).card := by
  unfold intervalCount
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    intervalStep_iff_localIntervalStep]

end Interval

end Turing.MultiTapePTM
