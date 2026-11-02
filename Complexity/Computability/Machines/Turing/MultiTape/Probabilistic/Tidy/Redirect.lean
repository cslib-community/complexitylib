/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OnWords
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
public import Cslib.Foundations.Data.Fin.Tuple
import Complexity.Probability.PMF.Bind

/-!
# Tape extension and word-redirection combinators for probabilistic oracle machines

This module lifts the deterministic tape-reindexing and word-redirection combinators (`extendTapes`,
`outputToWord`, `inputFromWord`, and `onWords`) to `MultiTapePTM` specifications in `RunsWords` and
`ComputesTidily`. Every combinator preserves the exact joint distribution of tape words, emitted
output and external oracle state, and maintains clean query buffers at phase boundaries.

## Main definitions

* `Turing.MultiTapePTM.outputToWord`: redirect output to a new last work tape and rewind its head.
* `Turing.MultiTapePTM.inputFromWord`: read input from a work tape flagged by `markFlag`.
* `Turing.MultiTapePTM.onWords`: run a tidy probabilistic machine between two work tapes.

## Main results

* `Turing.MultiTapePTM.RunsWords.extendTapes`, `Turing.MultiTapePTM.ComputesTidily.extendTapes`:
  tape-reindexing laws.
* `Turing.MultiTapePTM.ComputesTidily.outputToWord`,
  `Turing.MultiTapePTM.RunsWords.inputFromWord`, `Turing.MultiTapePTM.ComputesTidily.onWords_of_le`:
  word-redirection laws.

## References

Adapts the deterministic word-redirection combinators of Christian Reitwiessner's
crei:crei/tidy-universal @7f7c0696 (`Plumbing/OnWords` and `Plumbing/Tidy`) to the probabilistic
oracle machines of the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {k k' : ℕ} {State Operation OracleState : Type}
  {x : List Bool} [DecidableEq Operation]

/-! ### Tape extension -/

/-- Reindexing work tapes via `extendTapes` transforms the selected tapes according to `machine`
and preserves all unselected tape words. -/
theorem RunsWords.extendTapes {machine : MultiTapePTM k Bool State Operation}
    {ws₀ : Fin k' → List Bool} {out₀ : List Bool} {time : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool} (e : Fin k ↪ Fin k')
    (h : machine.RunsWords x (fun j => ws₀ (e j)) out₀ time program ws₁ emit) :
    (machine.extendTapes e).RunsWords x ws₀ out₀ time program
      (fun a l => (MultiTapeTM.partialInv e l).elim (ws₀ l) (ws₁ a)) emit := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) (fun j => ws₀ (e j)) out₀
      channels := cfg.channels }
  have hembed : cfg = cfg₀.embed e (fun l => tapeOfList (ws₀ l)) (fun _ => 0) := by
    refine Config.ext ?_ rfl
    rw [htapes]
    exact (MultiTapeTM.embed_wordsCfg e (fun _ => rfl) (fun _ _ => rfl)).symm
  have hrun :
      (machine.extendTapes e).runOracleConfigFrom time cfg =
        (fun final => final.embed e (fun l => tapeOfList (ws₀ l)) (fun _ => 0)) <$>
          machine.runOracleConfigFrom time cfg₀ := by
    rw [hembed]
    exact MultiTapePTM.runConfigFrom_embed machine e _ _ cfg₀ _ _ time
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg₀ rfl hbuf
  dsimp only
  rw [hrun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  constructor
  · have hmap :
        PMF.map (fun (final, s') => (final.tapes, s'))
          (PMF.map (fun (a, s') => (a.embed e (fun l => tapeOfList (ws₀ l)) (fun _ => 0), s'))
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) =
        PMF.map (fun (tapes, s') =>
            (MultiTapeTM.embed e tapes (fun l => tapeOfList (ws₀ l)) (fun _ => 0), s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, Config.embed]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
    funext ⟨a, s'⟩
    refine Prod.ext ?_ rfl
    exact MultiTapeTM.embed_wordsCfg e (fun j => by simp)
      (fun l hl => by simp [MultiTapeTM.partialInv_eq_none e hl])
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

/-- Reindexing a tidy probabilistic machine preserves `ComputesTidily`. -/
theorem ComputesTidily.extendTapes {machine : MultiTapePTM k Bool State Operation}
    {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program) (e : Fin k ↪ Fin k') :
    (machine.extendTapes e).ComputesTidily x time program := by
  intro out₀
  have hext := (h out₀).extendTapes (ws₀ := fun _ => []) e
  have hblank : (fun (a : List Bool) (l : Fin k') =>
      (MultiTapeTM.partialInv e l).elim ([] : List Bool) (fun _ => [])) =
      fun _ _ => [] := by
    funext a l
    cases MultiTapeTM.partialInv e l <;> rfl
  simpa only [hblank] using hext

/-! ### Redirecting output to a work-tape word (`outputToWord`) -/

/-- `machine` with its output redirected to a new last work tape, whose head is then rewound to
cell `0`. -/
noncomputable def outputToWord (machine : MultiTapePTM k Bool State Operation) :
    MultiTapePTM (k + 1) Bool (State ⊕ RewindWorkState) Operation :=
  machine.outputToTape.seq (ofDeterministic ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k))))

/-- Redirecting the output of a blank `wordsCfg` configuration adds a blank last work tape. -/
private theorem outCfg_wordsCfg_nil (x : List Bool) (q : Option State) :
    outCfg (wordsCfg x q (fun _ : Fin k => []) []) = wordsCfg x q (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- Rewinding the last work tape of `outCfg (wordsCfg x _ (fun _ => []) w)` in `r + 2` steps for
any `w.length ≤ r` leaves `w` on the last work tape and halts. -/
private theorem runFrom_rewindLast {w : List Bool} {r : ℕ} (hr : w.length ≤ r) :
    ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k))).runFrom
      (outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ : Fin k => []) w)) (r + 2) =
      wordsCfg x none (Function.update (fun _ => []) (Fin.last k) w) [] := by
  let cfg := outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ : Fin k => []) w)
  have hone : oneTapeCfg (Fin.last k) cfg =
      ⟨some (rewindWork Bool).q₀, 1, fun _ => tapeOfList w, fun _ => (w.length : ℤ), []⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, cfg]
  have hrun₀ : (rewindWork Bool).runFrom (oneTapeCfg (Fin.last k) cfg) (w.length + 2) =
      ⟨none, 1, fun _ => tapeOfList w, fun _ => 0, []⟩ := by
    rw [hone]
    exact runFrom_rewindWork_none _ _ _ rfl le_rfl
  have hrun : (rewindWork Bool).runFrom (oneTapeCfg (Fin.last k) cfg) (r + 2) =
      ⟨none, 1, fun _ => tapeOfList w, fun _ => 0, []⟩ := by
    rw [runFrom_eq_of_halt _ _ (by omega : w.length + 2 ≤ r + 2) (by rw [hrun₀]), hrun₀]
  rw [runFrom_tapeEmb, hrun, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [wordsCfg]

/-- If `machine` computes `program` tidily in `time` steps and every supported output of `program`
has length at most `l`, then `machine.outputToWord` writes `program`'s output onto its new last
work tape in `time + l + 2` steps and emits nothing. -/
theorem ComputesTidily.outputToWord_of_le {machine : MultiTapePTM k Bool State Operation}
    {time l : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w : List Bool) (s' : OracleState),
      (w, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).support → w.length ≤ l) :
    ∀ out₀, machine.outputToWord.RunsWords x (fun _ => []) out₀ (time + (l + 2)) program
      (fun w => Function.update (fun _ => []) (Fin.last k) w) (fun _ => []) := by
  intro out₀
  apply RunsWords.of_nil_output
  intro OracleState oracle s cfg htapes hbuf
  let rew : MultiTapePTM (k + 1) Bool RewindWorkState Operation :=
    ofDeterministic ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k)))
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) (fun _ => []) [], channels := cfg.channels }
  have hleft : cfg = Sequential.left rew (OutputToTape.config cfg₀) := by
    refine Config.ext ?_ rfl
    rw [htapes]
    change wordsCfg x (some (Sum.inl machine.initial)) (fun _ => []) [] =
      (outCfg (wordsCfg x (some machine.initial) (fun _ => []) [])).mapState (Option.map Sum.inl)
    rw [outCfg_wordsCfg_nil]
    rfl
  have houtRun :
      machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀) =
        OutputToTape.config <$> machine.runOracleConfigFrom time cfg₀ :=
    MultiTapePTM.runConfigFrom_outputToTape machine _ _ time cfg₀
  have hhalt₁ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀))).run s).support,
      result.1.tapes.state = none := by
    intro result hres
    rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    exact (h []).halted oracle s cfg₀ rfl hbuf (mid, s₁) hmid
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀))).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (rew.runOracleConfigFrom (l + 2)
          (Sequential.start rew result.1))).run result.2).support,
        final.1.tapes.state = none := by
    intro result hres ⟨final₁, final₂⟩ hfinal
    rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    obtain ⟨⟨w, hw, hmidTapes⟩, _⟩ := (h []).mem_support oracle s cfg₀ rfl hbuf hmid
    have hstart : (Sequential.start rew (OutputToTape.config mid)).tapes =
        outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ => []) w) := by
      simp only [Sequential.start, OutputToTape.config, outCfg, hmidTapes, id_eq,
        List.nil_append, wordsCfg_state, wordsCfg_inputPos, wordsCfg_output, wordsCfg_workTapePos]
      rfl
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstart,
      runFrom_rewindLast (hl OracleState oracle s w s₁ hw),
      PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    rfl
  dsimp only [outputToWord]
  rw [hleft, run_interpret_runOracleConfigFrom_seq _ _ oracle (OutputToTape.config cfg₀)
    time (l + 2) s hhalt₁ hhalt₂]
  constructor
  · rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
      PMF.bind_map, PMF.map_bind]
    trans (((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg₀)).run s).bind
      (fun a =>
        PMF.pure
          (wordsCfg x none
            (Function.update (fun _ => []) (Fin.last k) a.1.tapes.output) [], a.2)))
    · apply PMF.bind_congr_on_support
      intro ⟨mid, s₁⟩ hmid
      dsimp only [Function.comp_def]
      obtain ⟨⟨w, hw, hmidTapes⟩, _⟩ := (h []).mem_support oracle s cfg₀ rfl hbuf hmid
      have hstart : (Sequential.start rew (OutputToTape.config mid)).tapes =
          outCfg (wordsCfg x (some (rewindWork Bool).q₀) (fun _ => []) w) := by
        simp only [Sequential.start, OutputToTape.config, outCfg, hmidTapes, id_eq,
          List.nil_append, wordsCfg_state, wordsCfg_inputPos, wordsCfg_output,
          wordsCfg_workTapePos]
        rfl
      have hout : mid.tapes.output = w := by rw [hmidTapes]; rfl
      rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstart,
        runFrom_rewindLast (hl OracleState oracle s w s₁ hw), hout]
      simp only [Sequential.right, Cfg.mapState, PMF.pure_map, wordsCfg_state, Option.map_none,
        wordsCfg_inputPos, wordsCfg_output]
      rfl
    · have hlaw := ((h []) OracleState oracle s cfg₀ rfl hbuf).1
      have hmapOut := congrArg
        (PMF.map (fun (p : Cfg k Bool State x × OracleState) =>
          (wordsCfg x (none : Option (State ⊕ RewindWorkState))
            (Function.update (fun _ => []) (Fin.last k) p.1.output) [], p.2))) hlaw
      change ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfg₀)).run s).bind
        (PMF.pure ∘ fun a =>
          (wordsCfg x none
            (Function.update (fun _ => []) (Fin.last k) a.1.tapes.output) [], a.2)) = _
      rw [PMF.bind_pure_comp]
      simpa only [PMF.map_comp, Function.comp_def, List.nil_append, id_eq, wordsCfg] using hmapOut
  · intro final hfinal op
    obtain ⟨result, hmid, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    rw [houtRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hmid
    obtain ⟨⟨mid₀, s₁⟩, hmid₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmid
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal₀
    rcases Prod.mk.inj hfinal₀ with ⟨rfl, rfl⟩
    exact ((h []).mem_support oracle s cfg₀ rfl hbuf hmid₀).2 op

/-- Unconditional `outputToWord` specification using `ComputesTidily.length_output_le`. -/
theorem ComputesTidily.outputToWord {machine : MultiTapePTM k Bool State Operation}
    {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (h : machine.ComputesTidily x time program) (out₀ : List Bool) :
    machine.outputToWord.RunsWords x (fun _ => []) out₀ (2 * time + 2) program
      (fun w => Function.update (fun _ => []) (Fin.last k) w) (fun _ => []) := by
  simpa only [Nat.two_mul, Nat.add_assoc] using
    h.outputToWord_of_le (fun _ oracle s _ _ hw => h.length_output_le oracle s hw) out₀

/-! ### Reading input from a work-tape word (`inputFromWord` and `onWords`) -/

/-- `machine` reading its input from the virtual input tape `Fin.natAdd k 0`, with `mark` written to
cell `-1` of the flag tape `Fin.natAdd k 1` before and erased after. -/
noncomputable def inputFromWord (machine : MultiTapePTM k Bool State Operation) (mark : Bool) :
    MultiTapePTM (k + 2) Bool (MarkWorkState ⊕ State ⊕ MarkWorkState) Operation :=
  (ofDeterministic (markFlag k (some mark))).seq
    (machine.inputFromTape.seq (ofDeterministic (markFlag k none)))

/-- Updating the flag tape of an appended family of tapes only changes the flag entry. -/
private theorem update_append_flag {α : Type*} (ws₀ : Fin k → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff]

/-- Setting or erasing the flag on `Fin.natAdd k 1` in `2` deterministic steps. -/
private theorem runFrom_markFlag (write : Option Bool)
    (WS : Fin k → ℤ → Option Bool) (vip flag : ℤ → Option Bool) (out : List Bool)
    (ip : Fin (x.length + 2)) :
    (markFlag k write).runFrom
      ⟨some (markFlag k write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ 2 =
      ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ := by
  let cfg : Cfg (k + 2) Bool MarkWorkState x :=
    ⟨some (markWork Bool write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩
  have hone : oneTapeCfg (Fin.natAdd k 1) cfg =
      ⟨some (markWork Bool write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, cfg, Fin.append_right]
  change (markFlag k write).runFrom cfg 2 = _
  rw [markFlag, runFrom_tapeEmb, hone, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa [cfg] using update_append_flag WS vip flag (Function.update flag (-1) write)
  · funext l
    simp [cfg, Function.update_apply]

/-- A `wordsCfg` configuration whose last two words are `w` and `[]`, written out. -/
private theorem wordsCfg_append_words {State' : Type} {outer : List Bool} (q : Option State')
    (ws : Fin k → List Bool) (w out : List Bool) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append tapeOfList ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

/-- If `machine` transforms `ws₀` to `ws₁ a` and emits `emit a` on input `w`, then
`machine.inputFromWord mark` transforms `Fin.append ws₀ ![w, []]` to `Fin.append (ws₁ a) ![w, []]`
and emits `emit a` on any outer input `x` in `time + 4` steps. -/
theorem RunsWords.inputFromWord {machine : MultiTapePTM k Bool State Operation}
    {w : List Bool} {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool} (mark : Bool)
    (h : machine.RunsWords w ws₀ out₀ time program ws₁ emit) :
    (machine.inputFromWord mark).RunsWords x (Fin.append ws₀ ![w, []]) out₀ (time + 4)
      program (fun a => Fin.append (ws₁ a) ![w, []]) emit := by
  intro OracleState oracle s cfg htapes hbuf
  let setF : MultiTapePTM (k + 2) Bool MarkWorkState Operation :=
    ofDeterministic (markFlag k (some mark))
  let eraseF : MultiTapePTM (k + 2) Bool MarkWorkState Operation :=
    ofDeterministic (markFlag k none)
  let midM := machine.inputFromTape.seq eraseF
  let cfg₀ : Config (k + 2) Bool MarkWorkState Operation x :=
    { tapes := wordsCfg x (some (markFlag k (some mark)).q₀) (Fin.append ws₀ ![w, []]) out₀
      channels := cfg.channels }
  have hleft₀ : cfg = Sequential.left midM cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    rfl
  let cfgIn : Config k Bool State Operation w :=
    { tapes := wordsCfg w (some machine.initial) ws₀ out₀, channels := cfg.channels }
  let ready : Config (k + 2) Bool MarkWorkState Operation x :=
    { tapes := inCfg mark (wordsCfg w (none : Option MarkWorkState) ws₀ out₀) x
      channels := cfg.channels }
  have hset : (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (setF.runOracleConfigFrom 2 cfg₀)).run s = PMF.pure (ready, s) := by
    rw [run_interpret_runOracleConfigFrom_ofDeterministic]
    congr 1
    refine Prod.ext (Config.ext ?_ rfl) rfl
    dsimp only [ready]
    change (markFlag k (some mark)).runFrom
      (wordsCfg x (some (markFlag k (some mark)).q₀) (Fin.append ws₀ ![w, []]) out₀) 2 = _
    rw [wordsCfg_append_words, inCfg_wordsCfg]
    exact runFrom_markFlag (some mark) _ _ _ _ _
  have hstartReady : Sequential.start midM ready =
      Sequential.left eraseF (InputFromTape.config mark cfgIn x 1) := by
    refine Config.ext ?_ rfl
    simp only [Sequential.start, Cfg.withState, inCfg_wordsCfg, Int.reduceNeg, Sequential.left,
      Cfg.mapState, InputFromTape.config, Option.elim_some, Cfg.mk.injEq, Option.some.injEq,
      and_self, and_true, cfgIn, ready]
    rfl
  have hinRun :
      machine.inputFromTape.runOracleConfigFrom time (InputFromTape.config mark cfgIn x 1) =
        (fun final => InputFromTape.config mark final x 1) <$>
          machine.runOracleConfigFrom time cfgIn :=
    MultiTapePTM.runConfigFrom_inputFromTape machine _ _ mark time cfgIn x 1
  have hhalt₁ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.inputFromTape.runOracleConfigFrom time
        (InputFromTape.config mark cfgIn x 1))).run s).support,
      result.1.tapes.state = none := by
    intro result hres
    rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    exact h.halted oracle s cfgIn rfl hbuf (mid, s₁) hmid
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.inputFromTape.runOracleConfigFrom time
        (InputFromTape.config mark cfgIn x 1))).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (eraseF.runOracleConfigFrom 2
          (Sequential.start eraseF result.1))).run result.2).support,
        final.1.tapes.state = none := by
    intro result hres ⟨final₁, final₂⟩ hfinal
    rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid, s₁⟩, hmid, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    obtain ⟨⟨a, _, hmidTapes⟩, _⟩ := h.mem_support oracle s cfgIn rfl hbuf hmid
    have hstartErase : (Sequential.start eraseF (InputFromTape.config mark mid x 1)).tapes =
        ⟨some (markFlag k (none : Option Bool)).q₀, 1,
          Fin.append (fun j => tapeOfList (ws₁ a j))
            ![tapeOfList w, Function.update (fun _ : ℤ => (none : Option Bool)) (-1) (some mark)],
          fun _ => 0, out₀ ++ emit a⟩ := by
      simp [Sequential.start, InputFromTape.config, hmidTapes, inCfg_wordsCfg, Cfg.withState,
        eraseF, ofDeterministic]
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstartErase,
      runFrom_markFlag none, PMF.mem_support_pure_iff] at hfinal
    rcases Prod.mk.inj hfinal with ⟨rfl, rfl⟩
    rfl
  have hmidSeq := run_interpret_runOracleConfigFrom_seq machine.inputFromTape eraseF oracle
    (InputFromTape.config mark cfgIn x 1) time 2 s hhalt₁ hhalt₂
  have hhaltMid : ∀ final ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (midM.runOracleConfigFrom (time + 2) (Sequential.start midM ready))).run s).support,
      final.1.tapes.state = none := by
    intro final hfinal
    rw [hstartReady, hmidSeq] at hfinal
    obtain ⟨result, hres, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    simpa [Sequential.right, Cfg.mapState] using hhalt₂ result hres (final₀, s₂) hfinal₀
  have hsplit : time + 4 = 2 + (time + 2) := by omega
  change
    PMF.map (fun (final, s') => (final.tapes, s'))
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((setF.seq midM).runOracleConfigFrom (time + 4) cfg)).run s) = _ ∧
    ∀ final ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((setF.seq midM).runOracleConfigFrom (time + 4) cfg)).run s).support, _
  rw [hleft₀, hsplit,
    run_interpret_runOracleConfigFrom_seq setF midM oracle cfg₀ 2 (time + 2) s
      (fun ⟨res₁, res₂⟩ hres => by
        rw [hset, PMF.mem_support_pure_iff] at hres
        rcases Prod.mk.inj hres with ⟨rfl, rfl⟩
        rfl)
      (fun ⟨res₁, res₂⟩ hres => by
        rw [hset, PMF.mem_support_pure_iff] at hres
        rcases Prod.mk.inj hres with ⟨rfl, rfl⟩
        exact hhaltMid),
    hset, PMF.pure_bind, hstartReady, hmidSeq]
  let F (c : Cfg k Bool State w) : Cfg (k + 2) Bool (MarkWorkState ⊕ State ⊕ MarkWorkState) x :=
    ⟨none, 1, Fin.append c.workTapes ![tapeOfList w, fun _ => none], fun _ => 0, c.output⟩
  have hF_wordsCfg (ws : Fin k → List Bool) (out : List Bool) :
      F (wordsCfg w none ws out) = wordsCfg x none (Fin.append ws ![w, []]) out := by
    rw [wordsCfg_append_words]
    rfl
  constructor
  · rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
      PMF.bind_map, PMF.map_bind, PMF.map_bind]
    trans (((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfgIn)).run s).bind
      (fun p => PMF.pure (F p.1.tapes, p.2)))
    · apply PMF.bind_congr_on_support
      intro ⟨mid, s₁⟩ hmid
      dsimp only [Function.comp_def]
      obtain ⟨⟨a, _, hmidTapes⟩, _⟩ := h.mem_support oracle s cfgIn rfl hbuf hmid
      have hstartErase : (Sequential.start eraseF (InputFromTape.config mark mid x 1)).tapes =
          ⟨some (markFlag k (none : Option Bool)).q₀, 1,
            Fin.append (fun j => tapeOfList (ws₁ a j))
              ![tapeOfList w, Function.update (fun _ : ℤ => (none : Option Bool)) (-1) (some mark)],
            fun _ => 0, out₀ ++ emit a⟩ := by
        simp [Sequential.start, InputFromTape.config, hmidTapes, inCfg_wordsCfg, Cfg.withState,
          eraseF, ofDeterministic]
      rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstartErase,
        runFrom_markFlag none, hmidTapes, Function.update_idem]
      simp [Sequential.right, Cfg.mapState, F, wordsCfg]
    · have hlaw := (h OracleState oracle s cfgIn rfl hbuf).1
      have hmapF := congrArg (PMF.map (fun (p : Cfg k Bool State w × OracleState) => (F p.1, p.2)))
        hlaw
      change ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfgIn)).run s).bind
        (PMF.pure ∘ fun p => (F p.1.tapes, p.2)) = _
      rw [PMF.bind_pure_comp]
      simpa only [PMF.map_comp, Function.comp_def, hF_wordsCfg] using hmapF
  · intro final hfinal op
    obtain ⟨p₁, hfinal₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    obtain ⟨result, hres, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal₁
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    rw [hinRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at hres
    obtain ⟨⟨mid₀, s₃⟩, hmid₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal₀
    rcases Prod.mk.inj hfinal₀ with ⟨rfl, rfl⟩
    exact (h.mem_support oracle s cfgIn rfl hbuf hmid₀).2 op

/-- `machine` with its output written to work tape `(Fin.last k).castAdd 2` and its input read from
work tape `Fin.natAdd (k + 1) 0`, using `mark` to flag the left boundary. -/
noncomputable def onWords (machine : MultiTapePTM k Bool State Operation) (mark : Bool) :
    MultiTapePTM (k + 1 + 2) Bool
      (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState) Operation :=
  machine.outputToWord.inputFromWord mark

/-- If `machine` computes `program` tidily on `w` in `time` steps and every supported output has
length at most `l`, then `machine.onWords mark` reads `w` from `Fin.natAdd (k + 1) 0` and writes
`program`'s output to `(Fin.last k).castAdd 2` in `time + l + 6` steps. -/
theorem ComputesTidily.onWords_of_le {machine : MultiTapePTM k Bool State Operation}
    {w : List Bool} {time l : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}
    (mark : Bool) (h : machine.ComputesTidily w time program)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (w' : List Bool) (s' : OracleState),
      (w', s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).support → w'.length ≤ l) :
    ∀ out₀, (machine.onWords mark).RunsWords x
      (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) w) out₀ (time + l + 6) program
      (fun w' =>
        Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) w)
          ((Fin.last k).castAdd 2) w')
      (fun _ => []) := by
  intro out₀
  have hpost (w' : List Bool) :
      Fin.append (Function.update (fun _ : Fin (k + 1) => ([] : List Bool)) (Fin.last k) w')
          ![w, []] =
        Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) w)
          ((Fin.last k).castAdd 2) w' := by
    rw [Fin.append_update_left, append_nil_eq_update]
  have hin := ((h.outputToWord_of_le hl out₀).inputFromWord (x := x) mark).mono
    (time' := time + l + 6) (by omega)
  dsimp only [MultiTapePTM.onWords]
  simpa only [append_nil_eq_update, hpost] using hin

end Turing.MultiTapePTM
