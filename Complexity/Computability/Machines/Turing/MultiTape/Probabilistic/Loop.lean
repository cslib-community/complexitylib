/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Repeating a probabilistic oracle machine until a tape goes blank

`repeatUntilBlank i body` runs `body` repeatedly. After each round it reads the cell under the
head of work tape `i`, without moving a head, and halts if that cell is blank. Every round of a
`Turing.MultiTapePTM.RunsWords` specification ends with all heads on the first cells of their
words, so the loop stops exactly when the word on tape `i` is empty. The body always runs at least
once. Rounds may halt at random times; the remaining rounds start from the halted configuration,
with its tapes, oracle channels and external oracle state.

## Main definitions

* `Turing.MultiTapePTM.repeatUntilBlank`: the looping machine.
* `Turing.MultiTapePTM.RepeatUntilBlank.fromCheck`: the same transition table started at its test.

## Main results

* `Turing.MultiTapePTM.RunsWords.repeatUntilBlank_round`: one round followed by the remaining loop.
* `Turing.MultiTapePTM.RunsWords.repeatUntilBlank`: `rounds` rounds governed by an invariant run
  `OracleComp.iterate rounds step` within `rounds * (t + 1)` steps, preserving the joint law of
  the tape words and the external oracle state.

## References

Adapts cslib's `Plumbing/RepeatUntilBlank`, by Christian Reitwiessner, to probabilistic oracle
machines and the joint stateful semantics of `Turing.MultiTapePTM.RunsWords`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM

variable {k : ℕ} {State Operation OracleState : Type} {x : List Bool} [DecidableEq Operation]

/-- Clocked runs compose by sequencing their programs. -/
theorem runOracleConfigFrom_add {S : Type}
    (machine : MultiTapePTM k Bool S Operation) (first second : ℕ)
    (cfg : Config k Bool S Operation x) :
    machine.runOracleConfigFrom (first + second) cfg =
      machine.runOracleConfigFrom first cfg >>= machine.runOracleConfigFrom second :=
  MultiTapeMachine.runConfigFrom_add machine _ _ first second cfg

namespace RepeatUntilBlank

/-- Embed an action of the repeated machine, sending its halt to the blank test. -/
def runAction : MultiTapeMachine.Action k Bool State Operation →
    MultiTapeMachine.Action k Bool (RepeatUntilBlankState State) Operation
  | .step action symbol move =>
    .step { action with state := some (action.state.elim .check .run) } symbol move
  | .query op next => .query op (.run next)

/-- The instruction that writes nothing, moves no head and enters `q`. -/
def idle {S : Type} (q : Option S) : Turing.Action k Bool S :=
  { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := q }

/-- The blank test: halt if the cell under the head of work tape `i` is blank, and otherwise
restart at `initial`, moving no head and writing nothing. -/
def checkAction (i : Fin k) (initial : State) (work : Fin k → Option Bool) :
    MultiTapeMachine.Action k Bool (RepeatUntilBlankState State) Operation :=
  .step (idle ((work i).map fun _ => .run initial)) (fun _ => none) (fun _ => 0)

end RepeatUntilBlank

open RepeatUntilBlank

/-- `body`, with its halting transitions sent to a test of the cell under the head of work tape
`i`: a blank cell halts the loop, and any other cell restarts `body`. -/
def repeatUntilBlank (i : Fin k) (body : MultiTapePTM k Bool State Operation) :
    MultiTapePTM k Bool (RepeatUntilBlankState State) Operation where
  initial := .run body.initial
  tr q symbol work answer bit := match q with
    | .run q => runAction (body.tr q symbol work answer bit)
    | .check => checkAction i body.initial work

namespace RepeatUntilBlank

/-- The loop's transition table, started at its blank test. -/
def fromCheck (i : Fin k) (body : MultiTapePTM k Bool State Operation) :
    MultiTapePTM k Bool (RepeatUntilBlankState State) Operation :=
  { repeatUntilBlank i body with initial := .check }

/-- A configuration of the repeated machine as one of the loop: a live state `q` becomes `run q`
and the halted state becomes the blank test. -/
def runConfig (cfg : Config k Bool State Operation x) :
    Config k Bool (RepeatUntilBlankState State) Operation x :=
  { cfg with tapes := cfg.tapes.mapState fun state => some (state.elim .check .run) }

variable (i : Fin k) (body : MultiTapePTM k Bool State Operation)

/-- Starting at the test changes only the initial state, not the clocked program. -/
theorem runOracleConfigFrom_fromCheck (fuel : ℕ)
    (cfg : Config k Bool (RepeatUntilBlankState State) Operation x) :
    (fromCheck i body).runOracleConfigFrom fuel cfg =
      (repeatUntilBlank i body).runOracleConfigFrom fuel cfg :=
  (MultiTapeMachine.runConfigFrom_map (repeatUntilBlank i body) (fromCheck i body) _ _ _ _
    id (fun _ => (id_map _).symm) fuel cfg).trans (id_map _)

/-- While the repeated machine is live, one loop instruction mirrors its complete program. -/
theorem runOracleConfigFrom_one_runConfig (cfg : Config k Bool State Operation x)
    (h : cfg.tapes.state ≠ none) :
    (repeatUntilBlank i body).runOracleConfigFrom 1 (runConfig cfg) =
      runConfig <$> body.runOracleConfigFrom 1 cfg := by
  obtain ⟨state, hs⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runConfig cfg).tapes.state = some (.run state) := by
    simp [runConfig, Cfg.mapState, hs]
  have hinp : (runConfig cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl
  have hwork : (runConfig cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl
  have hans : (runConfig cfg).answerSymbols = cfg.answerSymbols := rfl
  dsimp only [runOracleConfigFrom, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom]
  rw [hstate, hs, hinp, hwork, hans]
  simp only [bind_map_left, map_bind]
  congr 1
  funext bit
  rw [show (repeatUntilBlank i body).tr (.run state) cfg.tapes.inputSymbol
    cfg.tapes.workTapeSymbols cfg.answerSymbols bit = runAction (body.tr state
      cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit) from rfl]
  cases body.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit with
  | step action symbol move =>
    simp [runAction, runConfig, Config.step, Turing.Action.apply, Cfg.mapState]
  | query op next => simp [runAction, runConfig, Config.receive, Cfg.mapState]

variable (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))

/-- The loop runs a clocked phase of `body` and then continues from its configuration, even when
`body` halts at a random time: an early halt reaches the blank test early, and the extra time is
absorbed because the remaining loop halts within its own clock. -/
theorem run_interpret_runOracleConfigFrom_add (cfg : Config k Bool State Operation x)
    (fuel rest : ℕ) (s : OracleState)
    (hrest : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (body.runOracleConfigFrom fuel cfg)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((repeatUntilBlank i body).runOracleConfigFrom rest (runConfig result.1))).run
          result.2).support,
        final.1.tapes.state = none) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((repeatUntilBlank i body).runOracleConfigFrom (fuel + rest) (runConfig cfg))).run s =
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (body.runOracleConfigFrom fuel cfg)).run s).bind (fun result =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((repeatUntilBlank i body).runOracleConfigFrom rest (runConfig result.1))).run
          result.2) := by
  induction fuel generalizing cfg s with
  | zero =>
    simp only [Nat.zero_add, runOracleConfigFrom, MultiTapePTM.runConfigFrom,
      MultiTapeMachine.runConfigFrom_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
  | succ fuel ih =>
    by_cases hhalt : cfg.tapes.state = none
    · have hpure : body.runOracleConfigFrom (fuel + 1) cfg = pure cfg :=
        MultiTapeMachine.runConfigFrom_halted _ _ _ _ cfg hhalt
      have hrest' := hrest (cfg, s) (by
        simp only [hpure, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, PMF.support_pure, Set.mem_singleton_iff])
      rw [hpure, OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
        PMF.pure_bind, Nat.add_comm (fuel + 1) rest]
      exact run_interpret_runOracleConfigFrom_add_of_halted _ oracle _ rest (fuel + 1) s hrest'
    · rw [show fuel + 1 + rest = 1 + (fuel + rest) by lia, runOracleConfigFrom_add,
        runOracleConfigFrom_one_runConfig i body cfg hhalt, bind_map_left,
        OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
        show fuel + 1 = 1 + fuel by lia, runOracleConfigFrom_add, OracleComp.interpret_bind,
        StateT.run_bind, Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
      apply Probability.PMF.bind_congr_on_support
      rintro ⟨next, s'⟩ hnext
      apply ih
      intro result hresult
      apply hrest result
      rw [show fuel + 1 = 1 + fuel by lia, runOracleConfigFrom_add, OracleComp.interpret_bind,
        StateT.run_bind, Probability.PMF.monad_bind_eq_bind]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(next, s'), hnext, hresult⟩

/-- An instruction that writes nothing and moves no head changes only the control state of a word
configuration. -/
theorem apply_idle_wordsCfg {S : Type} (q q' : Option S) (ws : Fin k → List Bool)
    (out : List Bool) : (idle q).apply (wordsCfg x q' ws out) = wordsCfg x q ws out := by
  refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;> simp [idle, Turing.Action.apply, wordsCfg]

omit [DecidableEq Operation] in
/-- Such an instruction also leaves every oracle channel unchanged. -/
theorem step_idle_channels {S : Type} (cfg : Config k Bool S Operation x) (q : Option S) :
    (cfg.step (idle q) (fun _ => none) (fun _ => 0)).channels = cfg.channels := by
  funext op
  simp [Config.step]

end RepeatUntilBlank

open RepeatUntilBlank

/-- At the blank test on an empty word, the loop halts after one instruction. -/
theorem RunsWords.fromCheck_nil (i : Fin k) (body : MultiTapePTM k Bool State Operation)
    {ws : Fin k → List Bool} {out₀ : List Bool} (hi : ws i = []) :
    (fromCheck i body).RunsWords x ws out₀ 1 (pure ()) (fun _ => ws) (fun _ => []) := by
  intro OracleState oracle s cfg htapes hbuf
  have hstate : cfg.tapes.state = some .check := by rw [htapes]; rfl
  have hsym : cfg.tapes.workTapeSymbols i = none := by
    rw [htapes]
    simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi]
  have hrun := run_interpret_runOracleConfigFrom_succ_step (fromCheck i body) oracle 0 cfg s
    hstate (action := idle none) (symbol := fun _ => none) (move := fun _ => 0)
    (fun _ => by simp only [fromCheck, repeatUntilBlank, checkAction, hsym, Option.map_none])
  have hstep : cfg.step (idle none) (fun _ => none) (fun _ => 0) =
      { tapes := wordsCfg x none ws out₀, channels := cfg.channels } :=
    Config.ext (by rw [Config.step, htapes, apply_idle_wordsCfg]) (step_idle_channels cfg none)
  dsimp only
  rw [hrun, hstep]
  simp only [runOracleConfigFrom, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom_zero,
    OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure, PMF.pure_map,
    List.append_nil, PMF.support_pure, Set.mem_singleton_iff, forall_eq, true_and]
  exact hbuf

/-- At the blank test on a non-empty word, the loop restarts its body after one instruction. -/
theorem RunsWords.fromCheck_ne_nil (i : Fin k) {body : MultiTapePTM k Bool State Operation}
    {ws : Fin k → List Bool} {out₀ : List Bool} {t : ℕ} {α : Type}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws' : α → Fin k → List Bool} {emit : α → List Bool} (hi : ws i ≠ [])
    (h : (repeatUntilBlank i body).RunsWords x ws out₀ t program ws' emit) :
    (fromCheck i body).RunsWords x ws out₀ (t + 1) program ws' emit := by
  intro OracleState oracle s cfg htapes hbuf
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil hi
  have hstate : cfg.tapes.state = some .check := by rw [htapes]; rfl
  have hsym : cfg.tapes.workTapeSymbols i = some b := by
    rw [htapes]
    simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hb]
  have hrun := run_interpret_runOracleConfigFrom_succ_step (fromCheck i body) oracle t cfg s
    hstate (action := idle (some (.run body.initial))) (symbol := fun _ => none)
    (move := fun _ => 0)
    (fun _ => by simp only [fromCheck, repeatUntilBlank, checkAction, hsym, Option.map_some])
  have hstep := (step_idle_channels cfg (some (.run body.initial)))
  dsimp only
  rw [hrun, runOracleConfigFrom_fromCheck]
  refine h OracleState oracle s _ ?_ (fun op => by rw [hstep]; exact hbuf op)
  rw [Config.step, htapes, apply_idle_wordsCfg]
  rfl

/-- One round of `body`, followed by the loop started at its blank test. The round's final tape
words and emitted output must determine its program value. -/
theorem RunsWords.repeatUntilBlank_round (i : Fin k) {body : MultiTapePTM k Bool State Operation}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {t₁ t₂ : ℕ} {α β : Type}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {prog₂ : α → ProbOracleComp (fun _ : Operation × List Bool => List Bool) β}
    {ws₁ : α → Fin k → List Bool} {emit₁ : α → List Bool}
    {ws₂ : α → β → Fin k → List Bool} {emit₂ : α → β → List Bool}
    (hinj : Function.Injective (fun a => (ws₁ a, emit₁ a)))
    (h₁ : body.RunsWords x ws₀ out₀ t₁ prog₁ ws₁ emit₁)
    (h₂ : ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s s' : OracleState),
      (a, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      (fromCheck i body).RunsWords x (ws₁ a) (out₀ ++ emit₁ a) t₂ (prog₂ a) (ws₂ a) (emit₂ a)) :
    (repeatUntilBlank i body).RunsWords x ws₀ out₀ (t₁ + t₂)
      (prog₁ >>= fun a => (fun b => (a, b)) <$> prog₂ a)
      (fun p : α × β => ws₂ p.1 p.2) (fun p : α × β => emit₁ p.1 ++ emit₂ p.1 p.2) := by
  classical
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some body.initial) ws₀ out₀, channels := cfg.channels }
  have hcfg : cfg = runConfig cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    rfl
  let f (a : α) : Cfg k Bool State x := wordsCfg x none (ws₁ a) (out₀ ++ emit₁ a)
  have hf : Function.Injective f := by
    intro a₁ a₂ heq
    obtain ⟨hws, hem⟩ := wordsCfg_injective heq
    exact hinj (Prod.ext hws hem)
  have hcheck (mid : Config k Bool State Operation x) (a : α) (hmid : mid.tapes = f a) :
      (runConfig mid).tapes =
        wordsCfg x (some (fromCheck i body).initial) (ws₁ a) (out₀ ++ emit₁ a) := by
    simp only [runConfig, hmid, f, mapState_wordsCfg, Option.elim_none]
    rfl
  have hrest : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (body.runOracleConfigFrom t₁ cfg₀)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((repeatUntilBlank i body).runOracleConfigFrom t₂ (runConfig result.1))).run
          result.2).support,
        final.1.tapes.state = none := by
    rintro ⟨mid, s₁⟩ hmid
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    rw [← runOracleConfigFrom_fromCheck]
    exact (h₂ a OracleState oracle s s₁ ha).halted oracle s₁ (runConfig mid)
      (hcheck mid a hmidTapes) hmidBuf
  dsimp only
  rw [hcfg, run_interpret_runOracleConfigFrom_add i body oracle cfg₀ t₁ t₂ s hrest]
  constructor
  · rw [PMF.map_bind]
    let g (p : Cfg k Bool State x × OracleState) :
        PMF (Cfg k Bool (RepeatUntilBlankState State) x × OracleState) :=
      if h : ∃ a, p.1 = f a then
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (prog₂ (Classical.choose h))).run p.2).map
          (fun (b, s₂) =>
            (wordsCfg x none (ws₂ (Classical.choose h) b)
              (out₀ ++ (emit₁ (Classical.choose h) ++ emit₂ (Classical.choose h) b)), s₂))
      else PMF.pure (wordsCfg x none ws₀ out₀, p.2)
    have hg (a : α) (s₁ : OracleState) :
        g (f a, s₁) =
          ((OracleComp.interpret
            (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
            (prog₂ a)).run s₁).map
            (fun (b, s₂) =>
              (wordsCfg x none (ws₂ a b) (out₀ ++ (emit₁ a ++ emit₂ a b)), s₂)) := by
      have hex : ∃ a', f a = f a' := ⟨a, rfl⟩
      have hchoose : Classical.choose hex = a := hf (Classical.choose_spec hex).symm
      change (if h : ∃ a', f a = f a' then _ else _) = _
      simp only [hex, ↓reduceDIte, hchoose]
    have hcongr :
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (body.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result =>
            PMF.map (fun (final, s') => (final.tapes, s'))
              ((OracleComp.interpret
                (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                ((repeatUntilBlank i body).runOracleConfigFrom t₂
                  (runConfig result.1))).run result.2)) =
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (body.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result => g (result.1.tapes, result.2)) := by
      apply PMF.bind_congr_on_support
      rintro ⟨mid, s₁⟩ hmid
      obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
      have hlaw := ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
        (runConfig mid) (hcheck mid a hmidTapes) hmidBuf).1
      rw [runOracleConfigFrom_fromCheck] at hlaw
      dsimp only
      rw [hlaw, hmidTapes, hg a s₁]
      congr 1
      funext ⟨b, s₂⟩
      simp only [List.append_assoc]
    rw [hcongr]
    have hmapBind :
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (body.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result => g (result.1.tapes, result.2)) =
        (((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (body.runOracleConfigFrom t₁ cfg₀)).run s).map
          (fun (final, s') => (final.tapes, s'))).bind g := by
      rw [PMF.bind_map]
      rfl
    rw [hmapBind, (h₁ OracleState oracle s cfg₀ rfl hbuf).1, PMF.bind_map]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_map, StateT.run_bind,
      StateT.run_map, Probability.PMF.monad_bind_eq_bind, PMF.monad_map_eq_map,
      PMF.map_bind, PMF.map_comp, Function.comp_def]
    congr 1
    funext ⟨a, s₁⟩
    exact hg a s₁
  · intro final hfinal op
    obtain ⟨⟨mid, s₁⟩, hmid, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    rw [← runOracleConfigFrom_fromCheck] at hfinal
    exact ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
      (runConfig mid) (hcheck mid a hmidTapes) hmidBuf).2 final hfinal op

/-- A loop of `rounds + 1` rounds. Round `n < rounds` runs `step s` from the words `ws s` of a
state `s` satisfying `invariant n s`, and leaves a non-empty word on tape `i`; the last round runs
`last s` and leaves tape `i` empty. The loop then runs `OracleComp.iterate rounds step` followed by
`last` within `(rounds + 1) * (t + 1)` steps, preserving the joint law of the tape words and the
external oracle state, and emits nothing. -/
theorem RunsWords.repeatUntilBlank (i : Fin k) {body : MultiTapePTM k Bool State Operation}
    {σ : Type} {ws : σ → Fin k → List Bool} (hws : Function.Injective ws)
    {step last : σ → ProbOracleComp (fun _ : Operation × List Bool => List Bool) σ}
    {out₀ : List Bool} {t rounds : ℕ} {s₀ : σ}
    (invariant : ℕ → σ → Prop) (hbase : invariant 0 s₀)
    (hstep : ∀ n < rounds, ∀ s, invariant n s →
      body.RunsWords x (ws s) out₀ t (step s) ws (fun _ => []))
    (hlast : ∀ s, invariant rounds s → body.RunsWords x (ws s) out₀ t (last s) ws (fun _ => []))
    (hpreserve : ∀ n < rounds, ∀ s, invariant n s →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (step s)).run st).support → invariant (n + 1) s' ∧ ws s' i ≠ [])
    (hstop : ∀ s, invariant rounds s →
      ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (s' : σ),
        (s', st') ∈ ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (last s)).run st).support → ws s' i = []) :
    (repeatUntilBlank i body).RunsWords x (ws s₀) out₀ ((rounds + 1) * (t + 1))
      (OracleComp.iterate rounds step s₀ >>= last) ws (fun _ => []) := by
  have hinj : Function.Injective (fun s => (ws s, ([] : List Bool))) :=
    fun _ _ h => hws (congrArg Prod.fst h)
  suffices h : ∀ m n s, n + m = rounds → invariant n s →
      (MultiTapePTM.repeatUntilBlank i body).RunsWords x (ws s) out₀ ((m + 1) * (t + 1))
        (OracleComp.iterate m step s >>= last) ws (fun _ => []) from
    h rounds 0 s₀ (Nat.zero_add _) hbase
  intro m
  induction m with
  | zero =>
    intro n s hn hs
    subst hn
    have hround := (hlast s hs).repeatUntilBlank_round i hinj
      (prog₂ := fun _ => pure ()) (ws₂ := fun a _ => ws a) (emit₂ := fun _ _ => [])
      (fun a _ _ _ _ ha => by
        rw [List.append_nil]
        exact RunsWords.fromCheck_nil i body (hstop s hs _ _ _ _ a ha))
    have hmap := hround.of_map Prod.fst ws (fun _ => [])
    simpa only [map_pure, bind_pure_comp, Functor.map_map, OracleComp.iterate_zero, pure_bind,
      Nat.zero_add, Nat.one_mul, id_map'] using hmap
  | succ m ih =>
    intro n s hn hs
    have hround := (hstep n (by lia) s hs).repeatUntilBlank_round i hinj
      (prog₂ := fun a => OracleComp.iterate m step a >>= last) (ws₂ := fun _ b => ws b)
      (emit₂ := fun _ _ => [])
      (fun a _ _ _ _ ha => by
        obtain ⟨ha', hne⟩ := hpreserve n (by lia) s hs _ _ _ _ a ha
        rw [List.append_nil]
        exact RunsWords.fromCheck_ne_nil i hne (ih (n + 1) a (by lia) ha'))
    have hmap := hround.of_map Prod.snd ws (fun _ => [])
    rw [show (m + 1 + 1) * (t + 1) = t + ((m + 1) * (t + 1) + 1) by ring,
      OracleComp.iterate_succ_bind, bind_assoc]
    simpa only [map_bind, Functor.map_map, id_map'] using hmap

end Turing.MultiTapePTM
