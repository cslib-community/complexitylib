/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.FiniteConfiguration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time runs of a fixed deterministic machine

For a fixed deterministic machine `tm` with finitely many states, the configuration reached after
`t` steps on an input `w` is computable in polynomial time in the length of `w` and the number `t`,
written in unary (`Turing.MultiTapeTM.computableInPolyTime_trackedRun`). The configuration is
stored as finite data (`Turing.FiniteCfg`), whose work tapes are kept relative to their heads,
together with the absolute positions of the work heads;
`Turing.MultiTapeTM.trackedAgrees_trackedRun` relates it to the native run
`tm.runFrom (tm.initCfg w) t`.

The machine is a fixed parameter: one step is a finite case analysis on the state and the symbols
read (`Turing.MultiTapeTM.ComputableInPolyTime.finite_cases`), followed by a fixed action, and the
run iterates it with storage growing by at most one cell per step on each tape.

## Main definitions

* `Turing.MultiTapeTM.trackedStep`: one step on finite storage with absolute head positions.
* `Turing.MultiTapeTM.trackedRun`: `t` steps from the initial configuration on `w`.
* `Turing.MultiTapeTM.encTrackedCfg`: the encoding of tracked storage.
* `Turing.MultiTapeTM.TrackedAgrees`: finite storage with head positions describes a native
  configuration.

## Main results

* `Turing.MultiTapeTM.trackedAgrees_trackedRun`: the tracked run describes the native run.
* `Turing.MultiTapeTM.computableInPolyTime_trackedStep`,
  `Turing.MultiTapeTM.computableInPolyTime_trackedRun`: the tracked step and run are
  polynomial-time.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Turing MultiTapeMachine

variable {k : ℕ} {State : Type}

/-- One step of `tm` on finite storage, tracking the absolute positions of the work heads. A
halted configuration is left unchanged. -/
noncomputable def trackedStep (tm : MultiTapeTM k Bool State)
    (c : FiniteCfg k Bool State × (Fin k → ℤ)) : FiniteCfg k Bool State × (Fin k → ℤ) :=
  match c.1.state with
  | none => c
  | some q =>
    (c.1.step (tm.tr q c.1.inputSymbol c.1.workTapeSymbols),
      fun i => c.2 i + ((tm.tr q c.1.inputSymbol c.1.workTapeSymbols).workTapes i).2)

/-- The tracked run: `x.2` steps of `tm` from the initial configuration on the input `x.1`, with
all work heads starting at position `0`. -/
noncomputable def trackedRun (tm : MultiTapeTM k Bool State) (x : List Bool × ℕ) :
    FiniteCfg k Bool State × (Fin k → ℤ) :=
  (trackedStep tm)^[x.2] (FiniteCfg.init tm.q₀ x.1, fun _ => 0)

/-- Finite storage `c.1` with work-head positions `c.2` describes the native configuration `cfg`
on the input `w`: the stored input is `w`, the control, input head and output agree, the positions
are the native ones, and each finite work tape reads the native tape relative to its head. -/
structure TrackedAgrees {w : List Bool} (c : FiniteCfg k Bool State × (Fin k → ℤ))
    (cfg : Cfg k Bool State w) : Prop where
  /-- The stored input is `w`. -/
  input : c.1.input = w
  /-- The controls agree. -/
  state : c.1.state = cfg.state
  /-- The input heads agree. -/
  inputPos : c.1.inputPos.val = cfg.inputPos.val
  /-- The tracked positions are the native work-head positions. -/
  workTapePos : c.2 = cfg.workTapePos
  /-- Each finite work tape reads the native one at every displacement from its head. -/
  workTapes : ∀ i, (c.1.workTapes i).Represents (cfg.workTapes i) (cfg.workTapePos i)
  /-- The outputs agree. -/
  output : c.1.output = cfg.output

namespace TrackedAgrees

variable {w : List Bool} {c : FiniteCfg k Bool State × (Fin k → ℤ)} {cfg : Cfg k Bool State w}

/-- Agreeing configurations read the same input symbol. -/
theorem inputSymbol (h : TrackedAgrees c cfg) : c.1.inputSymbol = cfg.inputSymbol := by
  obtain ⟨⟨input, state, pos, work, output⟩, positions⟩ := c
  obtain ⟨rfl, -, hpos, -, -, -⟩ := h
  rw [FiniteCfg.inputSymbol, Cfg.inputSymbol_eq_inputAt, Cfg.inputSymbol_eq_inputAt]
  exact congrArg _ hpos

/-- Agreeing configurations read the same work-tape symbols. -/
theorem workTapeSymbols (h : TrackedAgrees c cfg) :
    c.1.workTapeSymbols = cfg.workTapeSymbols :=
  funext fun i => by
    simpa [FiniteCfg.workTapeSymbols, Cfg.workTapeSymbols] using h.workTapes i 0

/-- A work tape of agreeing configurations, at an absolute position. -/
theorem read_sub (h : TrackedAgrees c cfg) (i : Fin k) (z : ℤ) :
    (c.1.workTapes i).read (z - c.2 i) = cfg.workTapes i z := by
  rw [h.workTapes i (z - c.2 i), h.workTapePos, add_sub_cancel]

end TrackedAgrees

/-- The initial finite storage, with every work head at position `0`, describes the initial native
configuration. -/
theorem trackedAgrees_init (tm : MultiTapeTM k Bool State) (w : List Bool) :
    TrackedAgrees (FiniteCfg.init tm.q₀ w, fun _ => 0) (tm.initCfg w) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => BiTape.represents_nil _, rfl⟩

/-- **One step preserves agreement.** -/
theorem TrackedAgrees.trackedStep {tm : MultiTapeTM k Bool State} {w : List Bool}
    {c : FiniteCfg k Bool State × (Fin k → ℤ)} {cfg : Cfg k Bool State w}
    (h : TrackedAgrees c cfg) : TrackedAgrees (trackedStep tm c) (tm.step cfg) := by
  cases hs : cfg.state with
  | none =>
    have hc : c.1.state = none := h.state.trans hs
    rw [MultiTapeTM.step_of_halt hs]
    unfold Turing.MultiTapeTM.trackedStep
    rw [hc]
    exact h
  | some q =>
    have hc : c.1.state = some q := h.state.trans hs
    rw [MultiTapeTM.step_of_state hs]
    unfold Turing.MultiTapeTM.trackedStep
    rw [hc]
    dsimp only
    rw [h.inputSymbol, h.workTapeSymbols]
    refine ⟨h.input, rfl, ?_, ?_, fun i => ?_, ?_⟩
    · simp only [FiniteCfg.step, Action.apply, val_moveInputPos_eq_moveInputPosNat, h.inputPos,
        h.input]
    · rw [h.workTapePos]
      rfl
    · have hstep := (h.workTapes i).step ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i)
      cases hw : ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i).1 <;>
        simpa [FiniteCfg.step, Action.apply, hw] using hstep
    · simp only [FiniteCfg.step, Action.apply, h.output]

/-- **The tracked run describes the native run.** -/
theorem trackedAgrees_trackedRun (tm : MultiTapeTM k Bool State) (w : List Bool) (t : ℕ) :
    TrackedAgrees (trackedRun tm (w, t)) (tm.runFrom (tm.initCfg w) t) := by
  induction t with
  | zero => exact trackedAgrees_init tm w
  | succ t ih =>
    rw [trackedRun, Function.iterate_succ_apply', runFrom, Function.iterate_succ_apply']
    exact ih.trackedStep

/-! ### Polynomial time -/

section PolyTime

variable [Finite State]

/-- The encoding of tracked storage: the finite configuration and the unary head positions. -/
noncomputable abbrev encTrackedCfg : FiniteCfg k Bool State × (Fin k → ℤ) ↪ List Bool :=
  encPair encFiniteCfg (encPi encIntUnary)

/-- One tracked step of a fixed machine is polynomial-time: a finite case analysis on the
control and the symbols read selects a fixed action. -/
theorem computableInPolyTime_trackedStep (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime (trackedStep tm) (encTrackedCfg)
      (encTrackedCfg) := by
  classical
  let key (c : FiniteCfg k Bool State × (Fin k → ℤ)) :
      Option State × Option Bool × (Fin k → Option Bool) :=
    (c.1.state, c.1.inputSymbol, c.1.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (c : FiniteCfg k Bool State × (Fin k → ℤ)) : FiniteCfg k Bool State × (Fin k → ℤ) :=
    match tag.1 with
    | none => c
    | some q => (c.1.step (tm.tr q tag.2.1 tag.2.2),
        fun i => c.2 i + ((tm.tr q tag.2.1 tag.2.2).workTapes i).2)
  have heq : trackedStep tm = fun c => branch (key c) c := by
    funext c
    rcases c with ⟨⟨_, _ | _, _, _, _⟩, _⟩ <;> rfl
  rw [heq]
  refine ComputableInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite _) (encPair (encFinEnum _) (encFinEnum _))) ?_ fun tag => ?_
  · exact (ComputableInPolyTime.finiteCfg_state.prod
      (ComputableInPolyTime.finiteCfg_inputSymbol.prod
        ComputableInPolyTime.finiteCfg_workTapeSymbols)).comp (.fst _ _)
  · rcases tag with ⟨_ | q, symbol, work⟩
    · exact ComputableInPolyTime.id'
    · refine ((ComputableInPolyTime.finiteCfg_step _).comp (.fst _ _)).prod
        (ComputableInPolyTime.pi fun i => ?_)
      have hi : ComputableInPolyTime (fun c : FiniteCfg k Bool State × (Fin k → ℤ) => c.2 i)
          (encTrackedCfg) encIntUnary :=
        (ComputableInPolyTime.pi_apply encIntUnary i).comp (.snd _ _)
      have hmove := (ComputableInPolyTime.int_sub_sign
        (-((tm.tr q symbol work).workTapes i).2)).comp hi
      simpa only [SignType.coe_neg, sub_neg_eq_add, Function.comp_def] using hmove

/-- Storage bounds along a tracked run of `steps` steps on an input of length at most
`inputSize`. -/
private structure TrackedBound (inputSize steps : ℕ) (c : FiniteCfg k Bool State × (Fin k → ℤ)) :
    Prop where
  input : c.1.input.length ≤ inputSize
  work : ∀ i, (c.1.workTapes i).spaceUsed ≤ steps + 1
  output : c.1.output.length ≤ steps
  positions : ∀ i, |c.2 i| ≤ steps

omit [Finite State] in
private theorem TrackedBound.trackedStep {tm : MultiTapeTM k Bool State} {inputSize steps : ℕ}
    {c : FiniteCfg k Bool State × (Fin k → ℤ)} (h : TrackedBound inputSize steps c) :
    TrackedBound inputSize (steps + 1) (trackedStep tm c) := by
  unfold Turing.MultiTapeTM.trackedStep
  split
  · exact ⟨h.input, fun i => (h.work i).trans (by lia), h.output.trans (by lia),
      fun i => (h.positions i).trans (by lia)⟩
  · rename_i q _
    refine ⟨h.input, fun i => ?_, ?_, fun i => ?_⟩
    · exact (BiTape.spaceUsed_step_le _ _).trans (Nat.add_le_add_right (h.work i) 1)
    · simpa only [FiniteCfg.step, List.length_append] using
        Nat.add_le_add h.output Option.length_toList_le
    · have hp := h.positions i
      have hs : |(((tm.tr q c.1.inputSymbol c.1.workTapeSymbols).workTapes i).2 : ℤ)| ≤ 1 := by
        rcases ((tm.tr q c.1.inputSymbol c.1.workTapeSymbols).workTapes i).2 with _ | _ | _ <;>
          simp [SignType.cast]
      calc |c.2 i + _| ≤ |c.2 i| + |_| := abs_add_le _ _
        _ ≤ steps + 1 := by lia

/-- The encoding of tracked storage is linear in the input size and the number of steps. -/
private theorem length_encTracked_le : ∃ C : ℕ, ∀ (inputSize steps : ℕ)
    (c : FiniteCfg k Bool State × (Fin k → ℤ)), TrackedBound inputSize steps c →
      (encTrackedCfg c).length ≤ C * (inputSize + steps + 1) := by
  obtain ⟨C, hC⟩ := length_encFiniteConfig_le (k := k) (State := State) (Oracle := Empty)
  refine ⟨2 * C + 2 + k * 5, fun inputSize steps c h => ?_⟩
  have hfin : (encFiniteCfg c.1).length ≤ C * (inputSize + steps + 0 + 1) := by
    have hbound : FiniteConfig.SpaceBound inputSize steps 0
        (⟨c.1, Empty.elim⟩ : FiniteConfig k Bool State Empty) :=
      ⟨h.input, h.work, h.output, fun e => e.elim, fun e => e.elim⟩
    refine le_trans ?_ (hC _ _ _ _ hbound)
    simp only [encFiniteConfig_apply, length_encPair]
    lia
  have hpos : (encPi encIntUnary c.2).length ≤ k * (2 * (steps + 1) + 1) := by
    simpa using length_encPi_le encIntUnary c.2 (bound := steps + 1) fun i => by
      have := abs_le.mp (h.positions i)
      rw [length_encIntUnary]
      split <;> omega
  simp only [length_encPair]
  nlinarith

/-- **The tracked run of a fixed machine is polynomial-time** in the input and the number of
steps, written in unary. -/
theorem computableInPolyTime_trackedRun (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime (trackedRun tm) (encPair encBits encUnary)
      (encTrackedCfg) := by
  obtain ⟨C, hC⟩ := length_encTracked_le (k := k) (State := State)
  refine (ComputableInPolyTime.iterate_spec (ComputableInPolyTime.snd encBits encUnary)
    ((ComputableInPolyTime.finiteCfg_init (.fst _ _) tm.q₀).prod (ComputableInPolyTime.const _))
    (computableInPolyTime_trackedStep tm)
    (fun x i c => TrackedBound x.1.length i c)
    (fun x => ⟨le_rfl, fun i => by simp [FiniteCfg.init, BiTape.spaceUsed, BiTape.nil,
      StackTape.length_nil], by simp [FiniteCfg.init], fun i => by simp⟩)
    (fun _ _ _ _ h => h.trackedStep)
    (size := fun x => C * ((encPair encBits encUnary x).length +
      (encPair encBits encUnary x).length + 1))
    ((PolyBounded.const _).mul ((PolyBounded.self.add PolyBounded.self).add
      (PolyBounded.const 1))) ?_).1
  intro x i c hi hc
  refine (hC _ _ _ hc).trans (Nat.mul_le_mul_left C ?_)
  have h1 := length_le_encPair_left encBits encUnary x
  have h2 := length_le_encPair_right encBits encUnary x
  simp only [encBits_apply, encUnary_apply, List.length_replicate] at h1 h2
  lia

end PolyTime

end Turing.MultiTapeTM
