/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation
public import Complexity.Computability.Machines.Turing.MultiTape.BlockTrace
public import
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call
public import
  Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic
import Complexity.Foundations.Data.List.Lookup

/-!
# Query-machine replay inside a local tape window

The query machine stores three blocks per work tape, binary head positions and a remaining-step
counter. The original input is read only through the query-machine input channel. Both native
input boundaries read blank and input movement uses the existing clamping arithmetic.

A halted simulated machine keeps its data fixed while the replay counter continues to zero.
Only the three-valued output track is retained; no accumulated output word is stored or emitted.
Initialization receives the input length explicitly; computing that length and decoding a caller's
block labels are charged by the caller.

## Main results

* `Turing.MultiTapePTM.BlockComputation.QueryReplay.runFrom_loadView_represents`: every clocked
  prefix represents the native replay from the existing configuration embedding.
* `Turing.MultiTapePTM.BlockComputation.QueryReplay.result_runFrom_loadView`: the returned view
  agrees with the native block replay.
* `Turing.MultiTapePTM.BlockComputation.QueryReplay.halted_runFrom_loadView`,
  `live_runFrom_loadView`: the subroutine takes exactly its requested duration.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay

open MultiTapeNTM.ChoiceTable
open MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {Q : Type}

/-- Decode the existing ternary cell code; malformed codes read blank. -/
@[expose] def cellOfCode (n : ℕ) : Option Bool :=
  if n = 1 then some false else if n = 2 then some true else none

@[simp] theorem cellOfCode_symbolCode (b : Option Bool) : cellOfCode (symbolCode b) = b := by
  rcases b with _ | _ | _ <;> rfl

/-- Finite local storage. Tape families are fixed-size tuples, not finite lookup tables over
whole windows. Every runtime work cell and every head position is explicitly encoded. -/
@[ext] structure Config (k : ℕ) (Q : Type) where
  /-- Length of the original read-only input. -/
  inputLength : ℕ
  /-- Runtime block width. -/
  width : ℕ
  /-- Ticks still to replay. -/
  remaining : ℕ
  /-- Native padded input position, including both blank boundaries. -/
  inputPos : ℕ
  /-- Current simulated control, or halted. -/
  control : Option Q
  /-- Local work-head positions. -/
  heads : Fin k → ℕ
  /-- Explicit local windows using ternary symbol codes. -/
  cells : Fin k → List ℕ
  /-- Finite summary of emitted output. -/
  track : OutputTrack

/-- Signed movement on the natural coordinates of a finite window. Valid replay heads do not
attempt a left move at zero before their remaining-step counter reaches zero. -/
@[expose] def move (p : ℕ) : SignType → ℕ
  | .neg => p - 1
  | .zero => p
  | .pos => p + 1

/-- The symbol currently under each local work head. -/
@[expose] def symbols (s : Config k Q) (h : Fin k) : Option Bool :=
  cellOfCode ((s.cells h).getD (s.heads h) 0)

/-- Apply a native action to the fixed local windows. Writes outside a malformed short list do
not allocate a long gap. -/
@[expose] def applyAction (s : Config k Q) (a : Action k Bool Q) : Config k Q :=
  { s with
    inputPos := inputMove s.inputLength s.inputPos a.inputTape
    control := a.state
    heads := fun h => move (s.heads h) (a.workTapes h).2
    cells := fun h => match (a.workTapes h).1 with
      | none => s.cells h
      | some b => (s.cells h).set (s.heads h) (symbolCode b)
    track := s.track.emit a.output }

/-- One replay tick. Even after the simulated machine halts, the duration counter decreases. -/
@[expose] noncomputable def tick (M : MultiTapeTM k Bool Q) (s : Config k Q)
    (symbol : Option Bool) : Config k Q :=
  let after := s.control.elim s fun q =>
    applyAction s (M.tr q (inputSymbol s.inputLength s.inputPos symbol) (symbols s))
  { after with remaining := s.remaining - 1 }

/-- A silent state-returning query subroutine. Callers supply an initialized state via `runFrom`. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) : QueryMachine (Config k Q) where
  init := ⟨0, 0, 0, 0, none, fun _ => 0, fun _ => [], .empty⟩
  query s := s.inputPos - 1
  next p := tick M p.1 p.2
  emit _ := []
  halted s := decide (s.remaining = 0)
  finish _ := []

@[simp] theorem tick_remaining (M : MultiTapeTM k Bool Q) (s : Config k Q) (symbol) :
    (tick M s symbol).remaining = s.remaining - 1 := rfl

@[simp] theorem tick_width (M : MultiTapeTM k Bool Q) (s : Config k Q) (symbol) :
    (tick M s symbol).width = s.width := by
  cases hs : s.control <;> simp [QueryReplay.tick, hs, QueryReplay.applyAction]

@[simp] theorem tick_inputLength (M : MultiTapeTM k Bool Q) (s : Config k Q) (symbol) :
    (tick M s symbol).inputLength = s.inputLength := by
  cases hs : s.control <;> simp [QueryReplay.tick, hs, QueryReplay.applyAction]

/-- Each local tape keeps exactly its original number of cells. -/
theorem length_cells_tick (M : MultiTapeTM k Bool Q) (s : Config k Q) (symbol) (h : Fin k) :
    ((tick M s symbol).cells h).length = (s.cells h).length := by
  cases hs : s.control with
  | none => simp [QueryReplay.tick, hs]
  | some q =>
    simp only [QueryReplay.tick, hs, Option.elim_some, QueryReplay.applyAction]
    split <;> simp

variable {w : List Bool}

/-- A local window agrees with the native configuration on every stored cell. Absolute tape
origins belong to this proof relation, not to the runtime tape data. -/
structure Represents (s : Config k Q) (c : Cfg k Bool Q w) (base : Fin k → ℤ) : Prop where
  inputLength : s.inputLength = w.length
  inputPos : s.inputPos = c.inputPos.val
  control : s.control = c.state
  track : s.track = OutputTrack.ofWord c.output
  heads : ∀ h, c.workTapePos h = base h + (s.heads h : ℤ)
  cells : ∀ h i, i < (s.cells h).length →
    cellOfCode ((s.cells h).getD i 0) = c.workTapes h (base h + i)

private theorem inputSymbol_read (s : Config k Q) (c : Cfg k Bool Q w)
    (hN : s.inputLength = w.length) (hp : s.inputPos = c.inputPos.val) :
    inputSymbol s.inputLength s.inputPos w[s.inputPos - 1]? = c.inputSymbol := by
  rw [hN, hp]
  by_cases hz : c.inputPos.val = 0
  · rw [inputSymbol_eq_none_of_boundary (Or.inl hz)]
    simp [inputSymbol, hz]
  · by_cases hr : c.inputPos.val = w.length + 1
    · rw [inputSymbol_eq_none_of_boundary (Or.inr hr)]
      simp [inputSymbol, hr]
    · have hlt : c.inputPos.val - 1 < w.length := by have := c.inputPos.isLt; omega
      rw [inputSymbolInner (c.inputPos.val - 1) (by omega) hlt]
      simp [inputSymbol, hz, hr, List.getElem?_eq_getElem hlt]

private theorem inputMove_native (c : Cfg k Bool Q w) (d : SignType) :
    inputMove w.length c.inputPos.val d = (moveInputPos c.inputPos d).val := by
  have h := val_moveInputPos_eq c.inputPos d
  have hb := c.inputPos.isLt
  cases d <;> simp only [inputMove, SignType.cast] at * <;> omega

private theorem move_cast (p : ℕ) (d : SignType) (hp : 0 < p) :
    (move p d : ℤ) = (p : ℤ) + d := by
  cases d <;> simp only [move, SignType.cast] <;> omega

/-- Applying the same action preserves every stored cell and the output track. -/
theorem Represents.applyAction {s : Config k Q} {c : Cfg k Bool Q w} {base : Fin k → ℤ}
    (hs : Represents s c base) (a : Action k Bool Q)
    (hin : ∀ h, s.heads h < (s.cells h).length) (hpos : ∀ h, 0 < s.heads h) :
    Represents (applyAction s a) (a.apply c) base := by
  refine ⟨hs.inputLength, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [QueryReplay.applyAction, Action.apply_inputPos, hs.inputLength, hs.inputPos]
    exact inputMove_native c a.inputTape
  · simp only [QueryReplay.applyAction, Action.apply_output, hs.track,
      OutputTrack.ofWord_append]
  · intro h
    simp only [QueryReplay.applyAction, Action.apply_workTapePos, hs.heads h,
      move_cast _ _ (hpos h)]
    ring
  · intro h i hi
    simp only [QueryReplay.applyAction] at hi ⊢
    have hlen : i < (s.cells h).length := by
      cases hw : (a.workTapes h).1 <;> simpa only [hw, List.length_set] using hi
    cases hw : (a.workTapes h).1 with
    | none => simpa only [Action.apply_workTapes, hw] using hs.cells h i hlen
    | some b =>
      simp only [Action.apply_workTapes, hw]
      by_cases he : i = s.heads h
      · subst i
        rw [List.getD_set_self (hin h), cellOfCode_symbolCode, hs.heads h,
          Function.update_self]
      · rw [List.getD_set_ne (Ne.symm he), hs.cells h i hlen]
        have hne : base h + (i : ℤ) ≠ c.workTapePos h := by
          rw [hs.heads h]
          intro heq
          exact he (by exact_mod_cast (add_left_cancel heq))
        rw [Function.update_of_ne hne]

/-- The duration counter does not change the represented native data. -/
theorem Represents.withRemaining {s : Config k Q} {c : Cfg k Bool Q w} {base : Fin k → ℤ}
    (hs : Represents s c base) (remaining : ℕ) :
    Represents { s with remaining := remaining } c base :=
  ⟨hs.inputLength, hs.inputPos, hs.control, hs.track, hs.heads, hs.cells⟩

/-- A tick simulates one native step whenever all current work heads are in the stored window. -/
theorem Represents.tick {s : Config k Q} {c : Cfg k Bool Q w} {base : Fin k → ℤ}
    (M : MultiTapeTM k Bool Q) (hs : Represents s c base)
    (hin : ∀ h, s.heads h < (s.cells h).length) (hpos : ∀ h, 0 < s.heads h) :
    Represents (tick M s w[s.inputPos - 1]?) (M.step c) base := by
  cases hcontrol : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hcontrol]
    simpa only [QueryReplay.tick, hs.control, hcontrol, Option.elim_none] using
      hs.withRemaining (s.remaining - 1)
  | some q =>
    have hsymbols : symbols s = c.workTapeSymbols := by
      funext h
      exact (hs.cells h (s.heads h) (hin h)).trans (by rw [← hs.heads h]; rfl)
    rw [MultiTapeTM.step_of_state hcontrol]
    have ha := hs.applyAction (M.tr q c.inputSymbol c.workTapeSymbols) hin hpos
    simpa only [QueryReplay.tick, hs.control, hcontrol, Option.elim_some,
      inputSymbol_read s c hs.inputLength hs.inputPos, hsymbols] using
      ha.withRemaining (s.remaining - 1)

/-- A live duration counter takes one local replay tick. -/
theorem step_eq_tick (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q)
    (hrem : 0 < s.remaining) :
    (machine M).step w s = tick M s w[s.inputPos - 1]? := by
  simp [QueryMachine.step, QueryMachine.read, machine, ne_of_gt hrem]

private theorem remaining_step (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q) :
    ((machine M).step w s).remaining = s.remaining - 1 := by
  by_cases hz : s.remaining = 0
  · simp [QueryMachine.step, machine, hz]
  · rw [step_eq_tick M w s (Nat.pos_of_ne_zero hz), tick_remaining]

private theorem width_step (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q) :
    ((machine M).step w s).width = s.width := by
  by_cases hz : s.remaining = 0
  · simp [QueryMachine.step, machine, hz]
  · rw [step_eq_tick M w s (Nat.pos_of_ne_zero hz), tick_width]

private theorem length_cells_step (M : MultiTapeTM k Bool Q) (w : List Bool)
    (s : Config k Q) (h : Fin k) :
    (((machine M).step w s).cells h).length = (s.cells h).length := by
  by_cases hz : s.remaining = 0
  · simp [QueryMachine.step, machine, hz]
  · rw [step_eq_tick M w s (Nat.pos_of_ne_zero hz), length_cells_tick]

/-- The counter uses exactly the requested duration, including halted simulated prefixes. -/
theorem remaining_runFrom (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q) (t : ℕ) :
    ((machine M).runFrom w s t).remaining = s.remaining - t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.runFrom_succ, remaining_step, ih]
    omega

/-- Replay never changes the block width. -/
theorem width_runFrom (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q) (t : ℕ) :
    ((machine M).runFrom w s t).width = s.width := by
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, width_step, ih]

/-- Replay never allocates cells beyond its supplied fixed windows. -/
theorem length_cells_runFrom (M : MultiTapeTM k Bool Q) (w : List Bool)
    (s : Config k Q) (t : ℕ) (h : Fin k) :
    (((machine M).runFrom w s t).cells h).length = (s.cells h).length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, length_cells_step, ih]

/-- Replaying a block preserves the native state, heads, stored windows and output track at
all clocked prefixes. The initial heads are in the middle block, leaving room for `width` moves. -/
theorem runFrom_represents (M : MultiTapeTM k Bool Q) {s : Config k Q}
    {c : Cfg k Bool Q w} {base : Fin k → ℤ} (hs : Represents s c base)
    (hrem : s.remaining = s.width)
    (hlen : ∀ h, (s.cells h).length = 3 * s.width)
    (hheads : ∀ h, s.width ≤ s.heads h ∧ s.heads h < 2 * s.width)
    {t : ℕ} (ht : t ≤ s.width) :
    Represents ((machine M).runFrom w s t) (M.runFrom c t) base := by
  induction t with
  | zero => exact hs
  | succ t ih =>
    have hprev := ih (by omega)
    have hcounter : 0 < ((machine M).runFrom w s t).remaining := by
      rw [remaining_runFrom, hrem]
      omega
    have hinterior (h : Fin k) :
        0 < ((machine M).runFrom w s t).heads h ∧
          ((machine M).runFrom w s t).heads h <
            (((machine M).runFrom w s t).cells h).length := by
      have hdist := abs_le.mp (M.workTapePos_runFrom_abs_sub_le c t h)
      rw [hprev.heads h, hs.heads h] at hdist
      have hstart := hheads h
      rw [length_cells_runFrom, hlen h]
      constructor <;> omega
    rw [QueryMachine.runFrom_succ, step_eq_tick M w _ hcounter, MultiTapeTM.runFrom_succ]
    exact hprev.tick M (fun h => (hinterior h).2) (fun h => (hinterior h).1)

/-- Initialize the local replay from decoded block data. The input length is an explicit
argument, and every work cell is stored using the existing ternary symbol code. Native loading
and its semantic correspondence are provided by `QueryReplayLoad` and `QueryReplayLoadCorrect`. -/
@[expose] def loadView (inputLength width : ℕ)
    (J : Option (Fin k) → ℤ) (v : View k Q width) : Config k Q :=
  { inputLength := inputLength
    width := width
    remaining := width
    inputPos :=
      let p : ℤ := width * J none + (v.1.2.1 none).val + 1
      if 0 ≤ p ∧ p < inputLength + 2 then p.toNat else 0
    control := v.1.1
    heads := fun h => width + (v.1.2.1 (some h)).val
    cells := fun h => List.ofFn fun r : Fin (3 * width) =>
      symbolCode (windowCell width J v.2 h (width * (J (some h) - 1) + r))
    track := v.1.2.2 }

/-- Decoded local data represents precisely the existing embedded native configuration. -/
theorem loadView_represents (width : ℕ) (J : Option (Fin k) → ℤ)
    (v : View k Q width) :
    Represents (loadView w.length width J v) (embedCfg (input := w) width J v.1 v.2)
      (fun h => width * (J (some h) - 1)) := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [loadView, embedCfg, inputPosOfCoord]
    split_ifs <;> rfl
  · simp only [loadView, embedCfg, OutputTrack.ofWord_toWord]
  · intro h
    simp only [loadView, embedCfg]
    push_cast
    ring
  · intro h i hi
    have hi' : i < 3 * width := by simpa only [loadView, List.length_ofFn] using hi
    simp only [loadView]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi')]
    simp only [List.getElem_ofFn, cellOfCode_symbolCode, embedCfg]

/-- The actual query subroutine realizes the native block replay on the original input, without
storing that word in its state. -/
theorem runFrom_loadView_represents (M : MultiTapeTM k Bool Q) (width : ℕ) [NeZero width]
    (J : Option (Fin k) → ℤ) (v : View k Q width) {t : ℕ} (ht : t ≤ width) :
    Represents ((machine M).runFrom w (loadView w.length width J v) t)
      (M.runFrom (embedCfg (input := w) width J v.1 v.2) t)
      (fun h => width * (J (some h) - 1)) := by
  apply runFrom_represents M (loadView_represents width J v) rfl
  · intro h
    simp only [loadView, List.length_ofFn]
  · intro h
    have ho := ZMod.val_lt (v.1.2.1 (some h))
    simp only [loadView]
    omega
  · exact ht

/-- A requested replay is halted at exactly its width, even if the native machine halts sooner. -/
theorem halted_runFrom_loadView (M : MultiTapeTM k Bool Q) (width : ℕ)
    (J : Option (Fin k) → ℤ) (v : View k Q width) :
    (machine M).halted ((machine M).runFrom w (loadView w.length width J v) width) = true := by
  change decide (((machine M).runFrom w (loadView w.length width J v) width).remaining = 0) = true
  rw [remaining_runFrom]
  change decide (width - width = 0) = true
  simp only [Nat.sub_self, decide_true]

/-- Every proper prefix remains live, even if the simulated machine has already halted. -/
theorem live_runFrom_loadView (M : MultiTapeTM k Bool Q) (width : ℕ)
    (J : Option (Fin k) → ℤ) (v : View k Q width) {t : ℕ} (ht : t < width) :
    (machine M).halted ((machine M).runFrom w (loadView w.length width J v) t) = false := by
  change decide (((machine M).runFrom w (loadView w.length width J v) t).remaining = 0) = false
  rw [remaining_runFrom]
  change decide (width - t = 0) = false
  exact decide_eq_false_iff_not.mpr (by omega)

/-- Decode the final local data back to a leaving view. Absolute work origins are multiples of
`width`, so they do not affect the head residues. -/
@[expose] def result (width : ℕ) (s : Config k Q) : View k Q width :=
  ((s.control, fun head => match head with
    | none => (((s.inputPos : ℤ) - 1 : ℤ) : ZMod width)
    | some h => (s.heads h : ZMod width), s.track),
    fun h d r => cellOfCode ((s.cells h).getD (d * width + r.val) 0))

/-- A represented replay returns the native control and the contents of the original windows. -/
theorem Represents.result_eq {s : Config k Q} {c : Cfg k Bool Q w}
    (width : ℕ) [NeZero width] (J : Option (Fin k) → ℤ)
    (hs : Represents s c (fun h => width * (J (some h) - 1)))
    (hlen : ∀ h, (s.cells h).length = 3 * width) :
    result width s = (c.blockControl width, c.windowContents width J) := by
  refine Prod.ext (Prod.ext hs.control (Prod.ext ?_ hs.track)) ?_
  · funext head
    cases head with
    | none => simp only [result, Cfg.blockControl, Cfg.headPos_none, hs.inputPos]
    | some h =>
      change (s.heads h : ZMod width) = (c.workTapePos h : ZMod width)
      rw [hs.heads h]
      push_cast
      simp
  · funext h d r
    have hr := ZMod.val_lt r
    have hd := d.isLt
    change cellOfCode ((s.cells h).getD (d * width + r.val) 0) =
      c.workTapes h (width * (J (some h) + d - 1) + r.val)
    rw [hs.cells h (d * width + r.val) (by rw [hlen h]; nlinarith)]
    congr 1
    push_cast
    ring

/-- The state-returning query subroutine computes exactly the native leaving view of the block. -/
theorem result_runFrom_loadView (M : MultiTapeTM k Bool Q) (width : ℕ) [NeZero width]
    (J : Option (Fin k) → ℤ) (v : View k Q width) :
    result width ((machine M).runFrom w (loadView w.length width J v) width) =
      ((M.runFrom (embedCfg (input := w) width J v.1 v.2) width).blockControl width,
        (M.runFrom (embedCfg (input := w) width J v.1 v.2) width).windowContents width J) := by
  apply Represents.result_eq width J (runFrom_loadView_represents M width J v le_rfl)
  intro h
  rw [length_cells_runFrom]
  simp only [loadView, List.length_ofFn]

/-- Every new work-cell code remains one of the three canonical symbols. -/
theorem cells_lt_three_tick (M : MultiTapeTM k Bool Q) (s : Config k Q) (symbol : Option Bool)
    (hcells : ∀ h a, a ∈ s.cells h → a < 3) :
    ∀ h a, a ∈ (tick M s symbol).cells h → a < 3 := by
  intro h
  cases hc : s.control with
  | none => simpa only [QueryReplay.tick, hc, Option.elim_none] using hcells h
  | some q =>
    simp only [QueryReplay.tick, hc, Option.elim_some, QueryReplay.applyAction]
    split
    · exact hcells h
    · exact List.forall_mem_set_of_forall_mem (hcells h) (symbolCode_lt _)

private theorem cells_lt_three_step (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q)
    (hcells : ∀ h a, a ∈ s.cells h → a < 3) :
    ∀ h a, a ∈ ((machine M).step w s).cells h → a < 3 := by
  by_cases hz : s.remaining = 0
  · simpa [QueryMachine.step, machine, hz] using hcells
  · rw [step_eq_tick M w s (Nat.pos_of_ne_zero hz)]
    exact cells_lt_three_tick M s _ hcells

/-- Replay preserves canonical ternary cell codes at every clocked prefix. -/
theorem cells_lt_three_runFrom (M : MultiTapeTM k Bool Q) (w : List Bool) (s : Config k Q)
    (hcells : ∀ h a, a ∈ s.cells h → a < 3) (t : ℕ) :
    ∀ h a, a ∈ ((machine M).runFrom w s t).cells h → a < 3 := by
  induction t with
  | zero => exact hcells
  | succ t ih =>
    rw [QueryMachine.runFrom_succ]
    exact cells_lt_three_step M w _ ih

/-- The view loader writes only the existing blank/false/true codes. -/
theorem cells_lt_three_loadView (width : ℕ) (J : Option (Fin k) → ℤ)
    (v : View k Q width) (h : Fin k) :
    ∀ a ∈ (loadView w.length width J v).cells h, a < 3 := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact symbolCode_lt _

end Turing.MultiTapePTM.BlockComputation.QueryReplay
