/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.OutputPrefix
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Word-configuration phases and tidy probabilistic oracle specifications

`RunsWords` and `ComputesTidily` express that a probabilistic oracle machine starts from a word
configuration with empty query buffers, halts within a strict step bound with empty query buffers,
and realizes the exact joint distribution of resulting tape words, emitted output and external
oracle state.

## Main definitions

* `Turing.MultiTapePTM.runOracleConfigFrom`: clocked configuration run with fair coins and named
  word queries.
* `Turing.MultiTapePTM.RunsWords`: word-configuration phase specification preserving external
  oracle state and empty query buffers.
* `Turing.MultiTapePTM.ComputesTidily`: tidy computation from blank work tapes to blank work tapes.

## Main results

* `Turing.MultiTapePTM.RunsWords.of_transformsTapes`: lift deterministic `TransformsTapes` phases.
* `Turing.MultiTapePTM.RunsWords.seq_bind`: sequence two `RunsWords` phases.
* `Turing.MultiTapePTM.RunsWords.of_nil_output`: an initial output prefix is retained automatically.
* `Turing.MultiTapePTM.RunsWords.of_first_step_mapState`: lift a `RunsWords` specification across a
  deterministic first-step dispatch into a state-mapped submachine.
* `Turing.MultiTapePTM.ComputesTidily.length_output_le`: any supported output of a tidy run has
  length at most the step budget.

## References

`RunsWords` and `ComputesTidily` adapt the deterministic `TransformsTapes` and tidy-machine
notions of cslib's `Plumbing/TransformsTapes` and `Plumbing/Tidy`, by Christian Reitwiessner, in
the run form of crei:crei/tidy-universal @7f7c0696, to the probabilistic oracle machines of the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {k : ℕ} {Symbol State State₀ State₁ Operation OracleState : Type}
  {input : List Symbol} [DecidableEq Operation]

/-- `tapeOfList` is injective on words. -/
theorem tapeOfList_injective : Function.Injective (@tapeOfList Symbol) := by
  intro u v h
  exact List.ext_getElem? fun n => congrFun h n

/-- A `wordsCfg` uniquely determines its work-tape words and the suffix appended to `out₀`. -/
theorem wordsCfg_injective {q : Option State} {ws₁ ws₂ : Fin k → List Symbol}
    {out₀ e₁ e₂ : List Symbol}
    (h : wordsCfg input q ws₁ (out₀ ++ e₁) = wordsCfg input q ws₂ (out₀ ++ e₂)) :
    ws₁ = ws₂ ∧ e₁ = e₂ := by
  refine ⟨funext fun i => tapeOfList_injective (congrFun (congrArg Cfg.workTapes h) i), ?_⟩
  exact List.append_cancel_left (congrArg Cfg.output h)

/-- Retain the complete configuration of an open fair-coin run with external word queries. -/
noncomputable def runOracleConfigFrom (machine : MultiTapePTM k Symbol State Operation)
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) :
    ProbOracleComp (fun _ : Operation × List Symbol => List Symbol)
      (Config k Symbol State Operation input) :=
  machine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word)) fuel cfg

/-- `runOracle` is the output projection of `runOracleConfigFrom` from the initial configuration. -/
theorem runOracle_eq_map (machine : MultiTapePTM k Symbol State Operation) (fuel : ℕ)
    (input : List Symbol) :
    machine.runOracle fuel input =
      (fun final => final.tapes.output) <$>
        machine.runOracleConfigFrom fuel (machine.initialConfig input) := rfl

omit [DecidableEq Operation] in
/-- Drawing one fair bit in `ProbOracleComp` leaves the external oracle state unchanged. -/
theorem run_interpret_sample_uniform_bool
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol)) (s : OracleState) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (ProbOracleComp.sample (ProbComp.uniform Bool))).run s =
      (PMF.uniformOfFintype Bool).map (fun bit => (bit, s)) := by
  simp only [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform]

/-- Padding a halted oracle run preserves the joint configuration and external state
distribution. -/
theorem run_interpret_runOracleConfigFrom_add_of_halted
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (cfg : Config k Symbol State Operation input) (fuel padding : ℕ) (s : OracleState)
    (hhalt : ∀ final ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel cfg)).run s).support,
      final.1.tapes.state = none) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom (fuel + padding) cfg)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom fuel cfg)).run s :=
  MultiTapeMachine.run_interpret_runConfigFrom_add_of_halted machine _ _ _ cfg fuel padding s hhalt

/-- Any larger clock gives the same joint configuration and external state distribution after a
halting bound. -/
theorem run_interpret_runOracleConfigFrom_eq_of_halted
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (cfg : Config k Symbol State Operation input) {fuel larger : ℕ} (hle : fuel ≤ larger)
    (s : OracleState)
    (hhalt : ∀ final ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel cfg)).run s).support,
      final.1.tapes.state = none) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom larger cfg)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom fuel cfg)).run s := by
  simpa only [Nat.add_sub_of_le hle] using
    run_interpret_runOracleConfigFrom_add_of_halted machine oracle cfg fuel (larger - fuel) s hhalt

/-- A deterministic machine embedded in `MultiTapePTM` preserves channels and external state. -/
theorem run_interpret_runOracleConfigFrom_ofDeterministic
    (machine : MultiTapeTM k Symbol State)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) (s : OracleState) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((ofDeterministic machine).runOracleConfigFrom fuel cfg)).run s =
      PMF.pure ({ cfg with tapes := machine.runFrom cfg.tapes fuel }, s) :=
  run_interpret_runConfigFrom_ofDeterministic machine _ _ _ (PMF.uniformOfFintype Bool)
    (run_interpret_sample_uniform_bool oracle) fuel cfg s

/-- Sequencing law for `runOracleConfigFrom` when both phases halt on all supported paths. -/
theorem run_interpret_runOracleConfigFrom_seq
    (first : MultiTapePTM k Symbol State₀ Operation)
    (second : MultiTapePTM k Symbol State₁ Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (cfg : Config k Symbol State₀ Operation input) (t₁ t₂ : ℕ) (s : OracleState)
    (h₁ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg)).run s).support,
      result.1.tapes.state = none)
    (h₂ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (second.runOracleConfigFrom t₂ (Sequential.start second result.1))).run result.2).support,
        final.1.tapes.state = none) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((first.seq second).runOracleConfigFrom (t₁ + t₂) (Sequential.left second cfg))).run s =
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg)).run s).bind (fun result =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (second.runOracleConfigFrom t₂
          (Sequential.start second result.1))).run result.2).map
        (fun (final, s') => (Sequential.right final, s'))) :=
  run_interpret_runConfigFrom_seq first second _ _ _ cfg t₁ t₂ s h₁ h₂

/-- A live step whose transition does not depend on the coin bit advances the configuration
deterministically while preserving the external oracle state. -/
theorem run_interpret_runOracleConfigFrom_succ_step
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) (s : OracleState)
    {state : State} (hstate : cfg.tapes.state = some state)
    {action : Turing.Action k Symbol State}
    {symbol : Operation → Option Symbol} {move : Operation → SignType}
    (htr : ∀ bit,
      machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit =
        .step action symbol move) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom (fuel + 1) cfg)).run s =
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel (cfg.step action symbol move))).run s := by
  dsimp only [runOracleConfigFrom, runConfigFrom]
  rw [MultiTapeMachine.runConfigFrom]
  simp only [hstate, bind_map_left, htr, OracleComp.interpret_bind, StateT.run_bind,
    run_interpret_sample_uniform_bool, Probability.PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def, PMF.bind_const]

/-- A live query step whose transition does not depend on the coin bit submits the accumulated
query on `op` and continues from the updated configuration. -/
theorem run_interpret_runOracleConfigFrom_succ_query
    (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (cfg : Config k Symbol State Operation input) (s : OracleState)
    {state : State} (hstate : cfg.tapes.state = some state)
    {op : Operation} {next : State}
    (htr : ∀ bit,
      machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit =
        .query op next) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom (fuel + 1) cfg)).run s =
    (oracle (op, (cfg.channels op).queryBuffer) s).bind (fun (answer, s') =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom fuel (cfg.receive op next answer))).run s') := by
  dsimp only [runOracleConfigFrom, runConfigFrom]
  rw [MultiTapeMachine.runConfigFrom]
  simp only [hstate, bind_map_left, htr, OracleComp.interpret_bind, StateT.run_bind,
    ProbOracleComp.interpret_query, run_interpret_sample_uniform_bool,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
  rfl

/-- Starting from a `wordsCfg` with empty query buffers, `machine` halts within `time` steps with
empty query buffers, realizing `program` on the work tapes and emitted output while preserving the
joint distribution with any external oracle state. -/
def RunsWords (machine : MultiTapePTM k Bool State Operation) (x : List Bool)
    (ws₀ : Fin k → List Bool) (out₀ : List Bool) (time : ℕ)
    {α : Type} (program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α)
    (ws₁ : α → Fin k → List Bool) (emit : α → List Bool) : Prop :=
  ∀ (OracleState : Type) (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (cfg : Config k Bool State Operation x),
    cfg.tapes = wordsCfg x (some machine.initial) ws₀ out₀ →
    (∀ op, (cfg.channels op).queryBuffer = []) →
    let run := (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg)).run s
    run.map (fun (final, s') => (final.tapes, s')) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).map
        (fun (a, s') => (wordsCfg x none (ws₁ a) (out₀ ++ emit a), s')) ∧
    ∀ final ∈ run.support, ∀ op, (final.1.channels op).queryBuffer = []

/-- A tidy probabilistic oracle computation starts with blank work tapes and empty query buffers,
and halts within `time` steps with blank work tapes, empty query buffers, the input head back at
position `1`, and `program`'s output appended to the output tape. -/
def ComputesTidily (machine : MultiTapePTM k Bool State Operation) (x : List Bool)
    (time : ℕ)
    (program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)) : Prop :=
  ∀ out₀, machine.RunsWords x (fun _ => []) out₀ time program (fun _ _ => []) id

namespace RunsWords

variable {machine : MultiTapePTM k Bool State Operation} {x : List Bool}
  {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time time' : ℕ}
  {α β : Type}
  {program program' : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
  {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}

/-- Every supported final configuration of a `RunsWords` phase has halted. -/
theorem halted (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (cfg : Config k Bool State Operation x)
    (htapes : cfg.tapes = wordsCfg x (some machine.initial) ws₀ out₀)
    (hbuf : ∀ op, (cfg.channels op).queryBuffer = []) :
    ∀ final ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg)).run s).support,
      final.1.tapes.state = none := by
  intro final hfinal
  have hmap : (final.1.tapes, final.2) ∈
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfg)).run s).map
        (fun (final, s') => (final.tapes, s'))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩
  rw [(h OracleState oracle s cfg htapes hbuf).1] at hmap
  obtain ⟨⟨a, s'⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
  exact (congrArg (fun p => p.1.state) heq).symm

/-- Every supported final configuration of a `RunsWords` phase has the declared tapes and
clean query buffers for some supported value of `program`. -/
theorem mem_support (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) (cfg : Config k Bool State Operation x)
    (htapes : cfg.tapes = wordsCfg x (some machine.initial) ws₀ out₀)
    (hbuf : ∀ op, (cfg.channels op).queryBuffer = [])
    {final : Config k Bool State Operation x} {s' : OracleState}
    (hfinal : (final, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom time cfg)).run s).support) :
    (∃ a, (a, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).support ∧
      final.tapes = wordsCfg x none (ws₁ a) (out₀ ++ emit a)) ∧
    ∀ op, (final.channels op).queryBuffer = [] := by
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg htapes hbuf
  refine ⟨?_, hclean (final, s') hfinal⟩
  have hmap : (final.tapes, s') ∈
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracleConfigFrom time cfg)).run s).map
        (fun (final, s') => (final.tapes, s'))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, s'), hfinal, rfl⟩
  rw [hlaw] at hmap
  obtain ⟨⟨a, s₁⟩, ha, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
  rcases Prod.mk.inj heq with ⟨ht, rfl⟩
  exact ⟨a, ha, ht.symm⟩

/-- Increasing the step budget preserves `RunsWords`. -/
theorem mono (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit) (hle : time ≤ time') :
    machine.RunsWords x ws₀ out₀ time' program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  dsimp only
  rw [run_interpret_runOracleConfigFrom_eq_of_halted machine oracle cfg hle s
    (h.halted oracle s cfg htapes hbuf)]
  exact h OracleState oracle s cfg htapes hbuf

/-- Replace `program` by a stateful-distributionally equivalent program. -/
theorem congr (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (heq : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s : OracleState),
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program').run s) :
    machine.RunsWords x ws₀ out₀ time program' ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  rw [← heq OracleState oracle s]
  exact h OracleState oracle s cfg htapes hbuf

/-- Map a function across the program result when the tape and output maps factor through it. -/
theorem of_map (f : α → β) (ws₁' : β → Fin k → List Bool) (emit' : β → List Bool)
    (h : machine.RunsWords x ws₀ out₀ time program (fun a => ws₁' (f a)) (fun a => emit' (f a))) :
    machine.RunsWords x ws₀ out₀ time (f <$> program) ws₁' emit' := by
  intro OracleState oracle s cfg htapes hbuf
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg htapes hbuf
  refine ⟨?_, hclean⟩
  rw [hlaw, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
  rfl

/-- Lift a deterministic `TransformsTapes` specification to `ofDeterministic`. -/
theorem of_transformsTapes {tm : MultiTapeTM k Bool State}
    {P : List Bool → (Fin k → List Bool) → Prop}
    {Q : List Bool → (Fin k → List Bool) → (Fin k → List Bool) → List Bool → Prop}
    {t s : ℕ} (htm : TransformsTapes tm P Q t s)
    (hP : P x ws₀) {ws' : Fin k → List Bool} {emitted : List Bool}
    (hQ : ∀ ws₁ em, Q x ws₀ ws₁ em → ws₁ = ws' ∧ em = emitted) :
    (ofDeterministic tm : MultiTapePTM k Bool State Operation).RunsWords
      x ws₀ out₀ t (pure ()) (fun _ => ws') (fun _ => emitted) := by
  intro OracleState oracle state cfg htapes hbuf
  obtain ⟨ws₁, em, hrun, hQ₁, _⟩ := transformsTapes_iff_runFrom.mp htm x ws₀ out₀ hP
  obtain ⟨rfl, rfl⟩ := hQ ws₁ em hQ₁
  have htapes' : cfg.tapes = wordsCfg x (some tm.q₀) ws₀ out₀ := htapes
  dsimp only
  rw [run_interpret_runOracleConfigFrom_ofDeterministic, htapes', hrun]
  simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
    PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff, forall_eq, true_and]
  exact hbuf

/-- Sequence two `RunsWords` phases when the first phase's resulting tape/output configuration
uniquely identifies its program value. -/
theorem seq_bind {first : MultiTapePTM k Bool State₀ Operation}
    {second : MultiTapePTM k Bool State₁ Operation}
    {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {prog₂ : α → ProbOracleComp (fun _ : Operation × List Bool => List Bool) β}
    {ws₁ : α → Fin k → List Bool} {emit₁ : α → List Bool}
    {ws₂ : α → β → Fin k → List Bool} {emit₂ : α → β → List Bool}
    (hinj : Function.Injective (fun a => (ws₁ a, emit₁ a)))
    (h₁ : first.RunsWords x ws₀ out₀ t₁ prog₁ ws₁ emit₁)
    (h₂ : ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s s' : OracleState),
      (a, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      second.RunsWords x (ws₁ a) (out₀ ++ emit₁ a) t₂ (prog₂ a) (ws₂ a) (emit₂ a)) :
    (first.seq second).RunsWords x ws₀ out₀ (t₁ + t₂)
      (prog₁ >>= fun a => (fun b => (a, b)) <$> prog₂ a)
      (fun p : α × β => ws₂ p.1 p.2) (fun p : α × β => emit₁ p.1 ++ emit₂ p.1 p.2) := by
  classical
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State₀ Operation x :=
    { tapes := wordsCfg x (some first.initial) ws₀ out₀, channels := cfg.channels }
  have hleft : cfg = Sequential.left second cfg₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    rfl
  let f (a : α) : Cfg k Bool State₀ x := wordsCfg x none (ws₁ a) (out₀ ++ emit₁ a)
  have hf : Function.Injective f := by
    intro a₁ a₂ heq
    obtain ⟨hws, hem⟩ := wordsCfg_injective heq
    exact hinj (Prod.ext hws hem)
  have hhalt₁ := h₁.halted oracle s cfg₀ rfl hbuf
  have hhalt₂ : ∀ result ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (first.runOracleConfigFrom t₁ cfg₀)).run s).support,
      ∀ final ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (second.runOracleConfigFrom t₂ (Sequential.start second result.1))).run result.2).support,
        final.1.tapes.state = none := by
    rintro ⟨mid, s₁⟩ hmid
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    have hstart : (Sequential.start second mid).tapes =
        wordsCfg x (some second.initial) (ws₁ a) (out₀ ++ emit₁ a) := by
      simp [Sequential.start, hmidTapes]
    exact (h₂ a OracleState oracle s s₁ ha).halted oracle s₁ (Sequential.start second mid)
      hstart hmidBuf
  dsimp only
  rw [hleft, run_interpret_runOracleConfigFrom_seq first second oracle cfg₀ t₁ t₂ s hhalt₁ hhalt₂]
  constructor
  · rw [PMF.map_bind]
    let g (p : Cfg k Bool State₀ x × OracleState) :
        PMF (Cfg k Bool (State₀ ⊕ State₁) x × OracleState) :=
      if h : ∃ a, p.1 = f a then
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (prog₂ (Classical.choose h))).run p.2).map
          (fun (b, s₂) =>
            (wordsCfg x none (ws₂ (Classical.choose h) b)
              (out₀ ++ (emit₁ (Classical.choose h) ++ emit₂ (Classical.choose h) b)), s₂))
      else PMF.pure (wordsCfg x none ws₀ out₀, p.2)
    have hg (a : α) (s₁ : OracleState) :
        g (wordsCfg x none (ws₁ a) (out₀ ++ emit₁ a), s₁) =
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
          (first.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result =>
            PMF.map (fun (final, s') => (final.tapes, s'))
              (PMF.map (fun (final, s') => (Sequential.right final, s'))
                ((OracleComp.interpret
                  (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                  (second.runOracleConfigFrom t₂
                    (Sequential.start second result.1))).run result.2))) =
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result => g (result.1.tapes, result.2)) := by
      apply PMF.bind_congr_on_support
      rintro ⟨mid, s₁⟩ hmid
      obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
      have hstart : (Sequential.start second mid).tapes =
          wordsCfg x (some second.initial) (ws₁ a) (out₀ ++ emit₁ a) := by
        simp [Sequential.start, hmidTapes]
      have hsecondLaw := ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
        (Sequential.start second mid) hstart hmidBuf).1
      have hright :
          PMF.map (fun p => (p.1.tapes, p.2))
            (PMF.map (fun p => (Sequential.right (State₀ := State₀) p.1, p.2))
              ((OracleComp.interpret
                (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                (second.runOracleConfigFrom t₂ (Sequential.start second mid))).run s₁)) =
          PMF.map (fun p => (Cfg.mapState (Option.map (Sum.inr (α := State₀))) p.1, p.2))
            (PMF.map (fun p => (p.1.tapes, p.2))
              ((OracleComp.interpret
                (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
                (second.runOracleConfigFrom t₂ (Sequential.start second mid))).run s₁)) := by
        simp only [PMF.map_comp, Function.comp_def, Sequential.right]
      rw [hright, hsecondLaw, hmidTapes, hg a s₁, PMF.map_comp]
      congr 1
      funext ⟨b, s₂⟩
      simp only [Cfg.mapState, List.append_assoc, Function.comp_apply, wordsCfg_state,
        Option.map_none, wordsCfg_inputPos, wordsCfg_output, Prod.mk.injEq, and_true]
      rfl
    rw [hcongr]
    have hmapBind :
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).bind
          (fun result => g (result.1.tapes, result.2)) =
        (((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (first.runOracleConfigFrom t₁ cfg₀)).run s).map
          (fun (final, s') => (final.tapes, s'))).bind g := by
      rw [PMF.bind_map]
      rfl
    rw [hmapBind, (h₁ OracleState oracle s cfg₀ rfl hbuf).1, PMF.bind_map]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_map, StateT.run_bind,
      StateT.run_map, Probability.PMF.monad_bind_eq_bind, PMF.monad_map_eq_map,
      PMF.map_bind, PMF.map_comp, Function.comp_def, hg]
  · intro final hfinal op
    obtain ⟨⟨mid, s₁⟩, hmid, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨final₀, s₂⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    obtain ⟨⟨a, ha, hmidTapes⟩, hmidBuf⟩ := h₁.mem_support oracle s cfg₀ rfl hbuf hmid
    have hstart : (Sequential.start second mid).tapes =
        wordsCfg x (some second.initial) (ws₁ a) (out₀ ++ emit₁ a) := by
      simp [Sequential.start, hmidTapes]
    exact ((h₂ a OracleState oracle s s₁ ha) OracleState oracle s₁
      (Sequential.start second mid) hstart hmidBuf).2 (final₀, s₂) hfinal₀ op

/-- Sequence a deterministic `pure ()` preparation phase before a `RunsWords` continuation. -/
theorem seq_pure_left {first : MultiTapePTM k Bool State₀ Operation}
    {second : MultiTapePTM k Bool State₁ Operation}
    {t₁ t₂ : ℕ} {ws₁ : Fin k → List Bool} {emit₁ : List Bool}
    {prog₂ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) β}
    {ws₂ : β → Fin k → List Bool} {emit₂ : β → List Bool}
    (h₁ : first.RunsWords x ws₀ out₀ t₁ (pure ()) (fun _ => ws₁) (fun _ => emit₁))
    (h₂ : second.RunsWords x ws₁ (out₀ ++ emit₁) t₂ prog₂ ws₂ emit₂) :
    (first.seq second).RunsWords x ws₀ out₀ (t₁ + t₂) prog₂
      ws₂ (fun b => emit₁ ++ emit₂ b) := by
  have hseq := (h₁.seq_bind (Function.injective_of_subsingleton _)
    (fun _ _ _ _ _ _ => h₂)).of_map Prod.snd ws₂ (fun b => emit₁ ++ emit₂ b)
  have hid : (fun a : β => a) = id := rfl
  simpa only [pure_bind, Functor.map_map, hid, id_map] using hseq

/-- Sequence a deterministic `pure ()` cleanup phase after a `RunsWords` phase. -/
theorem seq_pure_right {first : MultiTapePTM k Bool State₀ Operation}
    {second : MultiTapePTM k Bool State₁ Operation}
    {t₁ t₂ : ℕ}
    {prog₁ : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit₁ : α → List Bool}
    {ws₂ : α → Fin k → List Bool} {emit₂ : α → List Bool}
    (hinj : Function.Injective (fun a => (ws₁ a, emit₁ a)))
    (h₁ : first.RunsWords x ws₀ out₀ t₁ prog₁ ws₁ emit₁)
    (h₂ : ∀ a (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s s' : OracleState),
      (a, s') ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        prog₁).run s).support →
      second.RunsWords x (ws₁ a) (out₀ ++ emit₁ a) t₂ (pure ())
        (fun _ => ws₂ a) (fun _ => emit₂ a)) :
    (first.seq second).RunsWords x ws₀ out₀ (t₁ + t₂) prog₁
      ws₂ (fun a => emit₁ a ++ emit₂ a) := by
  have hseq := (h₁.seq_bind hinj h₂).of_map Prod.fst ws₂ (fun a => emit₁ a ++ emit₂ a)
  have hid : (fun a : α => a) = id := rfl
  simpa only [map_pure, bind_pure_comp, Functor.map_map, hid, id_map] using hseq

/-- `RunsWords` for arbitrary `out₀` follows from the `out₀ = []` case by output-prefix
invariance (`runConfigFrom_prependOutput`). -/
theorem of_nil_output (h : machine.RunsWords x ws₀ [] time program ws₁ emit) :
    machine.RunsWords x ws₀ out₀ time program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) ws₀ [], channels := cfg.channels }
  have hprep : cfg = cfg₀.prependOutput out₀ := by
    refine Config.ext ?_ rfl
    rw [htapes]
    exact Cfg.ext rfl rfl rfl rfl (by simp [cfg₀, Config.prependOutput, Cfg.prependOutput])
  have hrun :
      machine.runOracleConfigFrom time cfg =
        (fun final => final.prependOutput out₀) <$> machine.runOracleConfigFrom time cfg₀ := by
    rw [hprep]
    exact MultiTapeMachine.runConfigFrom_prependOutput machine _ _ time cfg₀ out₀
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg₀ rfl hbuf
  dsimp only
  rw [hrun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  constructor
  · have hmap :
        PMF.map (fun (final, s') => (final.tapes, s'))
          (PMF.map (fun (a, s') => (a.prependOutput out₀, s'))
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) =
        PMF.map (fun (tapes, s') => (tapes.prependOutput out₀, s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (machine.runOracleConfigFrom time cfg₀)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, Config.prependOutput]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

/-- If `machine`'s first step from `wordsCfg x (some machine.initial) ws₀ out₀` is a deterministic
no-op transition into `f tm.initial`, and `machine` thereafter simulates `tm` via `f`, then any
`RunsWords` specification of `tm` lifts to `machine` in `time + 1` steps. -/
theorem of_first_step_mapState {S : Type} {tm : MultiTapePTM k Bool S Operation}
    {f : S → State}
    (hfirst : ∀ answer bit,
      machine.tr machine.initial
        (wordsCfg x (some machine.initial) ws₀ out₀).inputSymbol
        (wordsCfg x (some machine.initial) ws₀ out₀).workTapeSymbols
        answer bit =
      .step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (f tm.initial) }
        (fun _ => none) (fun _ => 0))
    (htr : ∀ q inp work answer bit,
      machine.tr (f q) inp work answer bit =
        MultiTapeMachine.Action.mapState f (tm.tr q inp work answer bit))
    (htm : tm.RunsWords x ws₀ out₀ time program ws₁ emit) :
    machine.RunsWords x ws₀ out₀ (time + 1) program ws₁ emit := by
  intro OracleState oracle s cfg htapes hbuf
  let cfg₀ : Config k Bool S Operation x :=
    { tapes := wordsCfg x (some tm.initial) ws₀ out₀, channels := cfg.channels }
  have hstate : cfg.tapes.state = some machine.initial := by
    rw [htapes]; rfl
  have hstep :
      (cfg.step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (f tm.initial) }
        (fun _ => none) (fun _ => 0)) =
      Config.mapState f cfg₀ := by
    refine Config.ext ?_ (by funext op; simp [Config.step, Config.mapState, cfg₀])
    rw [Config.step, htapes]
    exact Cfg.ext rfl
      (by simp [Turing.Action.apply, wordsCfg, Config.mapState, Cfg.mapState, cfg₀])
      (by funext l; simp [Turing.Action.apply, wordsCfg, Config.mapState, Cfg.mapState, cfg₀])
      (by funext l; simp [Turing.Action.apply, wordsCfg, Config.mapState, Cfg.mapState, cfg₀])
      (by simp [Turing.Action.apply, wordsCfg, Config.mapState, Cfg.mapState, cfg₀])
  have htr_step : ∀ bit,
      machine.tr machine.initial cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit =
      MultiTapeMachine.Action.step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some (f tm.initial) }
        (fun _ => none) (fun _ => 0) := by
    intro bit
    rw [htapes]
    exact hfirst cfg.answerSymbols bit
  have hmapRun :
      machine.runOracleConfigFrom time (Config.mapState f cfg₀) =
        Config.mapState f <$> tm.runOracleConfigFrom time cfg₀ := by
    apply MultiTapeMachine.runConfigFrom_mapState
      (Choose := ReaderT Bool Id)
      (spec := probOracleSpec (fun _ : Operation × List Bool => List Bool))
      tm machine
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun g choices => by simp only [Functor.map_map]; rfl)
      (fun op word => ProbOracleComp.query (op, word)) f
      (fun q inp work answer => funext (htr q inp work answer))
      time cfg₀
  dsimp only
  rw [run_interpret_runOracleConfigFrom_succ_step machine oracle time cfg s hstate htr_step,
    hstep, hmapRun, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  obtain ⟨hlaw, hclean⟩ := htm OracleState oracle s cfg₀ rfl hbuf
  constructor
  · have hmap :
        PMF.map (fun (final : Config k Bool State Operation x × OracleState) =>
            (final.1.tapes, final.2))
          (PMF.map (fun (a, s') => (Config.mapState f a, s'))
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (tm.runOracleConfigFrom time cfg₀)).run s)) =
        PMF.map (fun (tapes, s') => (tapes.mapState (Option.map f), s'))
          (PMF.map (fun (final, s') => (final.tapes, s'))
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
              (tm.runOracleConfigFrom time cfg₀)).run s)) := by
      simp only [PMF.map_comp, Function.comp_def, Config.mapState]
    rw [hmap, hlaw, PMF.map_comp]
    congr 1
  · intro final hfinal op
    obtain ⟨⟨final₀, s'⟩, hfinal₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hclean (final₀, s') hfinal₀ op

end RunsWords

/-- `ComputesTidily` is equivalent to `RunsWords` with `out₀ = []`. -/
theorem computesTidily_iff_nil_output {machine : MultiTapePTM k Bool State Operation}
    {x : List Bool} {time : ℕ}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)} :
    machine.ComputesTidily x time program ↔
      machine.RunsWords x (fun _ => []) [] time program (fun _ _ => []) id :=
  ⟨fun h => h [], fun h _ => h.of_nil_output⟩

/-- Over `fuel` steps of `runOracleConfigFrom`, the output tape grows by at most `fuel` symbols. -/
theorem length_output_le_of_mem_support_runOracleConfigFrom {x : List Bool}
    (machine : MultiTapePTM k Bool State Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (fuel : ℕ) (cfg : Config k Bool State Operation x) (s : OracleState)
    {final : Config k Bool State Operation x} {s' : OracleState}
    (hfinal : (final, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracleConfigFrom fuel cfg)).run s).support) :
    final.tapes.output.length ≤ cfg.tapes.output.length + fuel :=
  MultiTapeMachine.length_output_runConfigFrom_le machine
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query
      (spec := fun _ : Operation × List Bool => List Bool) (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
    fuel cfg final s s' hfinal

/-- Any word emitted by a `RunsWords` phase has length at most `time`. -/
theorem RunsWords.length_emit_le {machine : MultiTapePTM k Bool State Operation} {x : List Bool}
    {ws₀ : Fin k → List Bool} {out₀ : List Bool} {time : ℕ}
    {α : Type} {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (h : machine.RunsWords x ws₀ out₀ time program ws₁ emit)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) {a : α} {s' : OracleState}
    (ha : (a, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s).support) :
    (emit a).length ≤ time := by
  let cfg : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) ws₀ out₀
      channels := fun _ => ⟨[], [], 0⟩ }
  obtain ⟨hlaw, _⟩ := h OracleState oracle s cfg rfl (fun _ => rfl)
  have hmem : (wordsCfg x (none : Option State) (ws₁ a) (out₀ ++ emit a), s') ∈
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s).map
        (fun (a, s') => (wordsCfg x (none : Option State) (ws₁ a) (out₀ ++ emit a), s'))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(a, s'), ha, rfl⟩
  rw [← hlaw] at hmem
  obtain ⟨⟨final, s₁⟩, hfinal, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  rcases Prod.mk.inj heq with ⟨htapes, rfl⟩
  have hlen := length_output_le_of_mem_support_runOracleConfigFrom machine oracle time cfg s hfinal
  have hout : final.tapes.output = out₀ ++ emit a := by rw [htapes]; rfl
  have hcfg : cfg.tapes.output = out₀ := rfl
  rw [hout, hcfg, List.length_append] at hlen
  omega

namespace ComputesTidily

variable {machine : MultiTapePTM k Bool State Operation} {x : List Bool} {time time' : ℕ}
  {program program' : ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool)}

/-- Increasing the step budget preserves `ComputesTidily`. -/
theorem mono (h : machine.ComputesTidily x time program) (hle : time ≤ time') :
    machine.ComputesTidily x time' program :=
  fun out₀ => (h out₀).mono hle

/-- Replace `program` by a stateful-distributionally equivalent program. -/
theorem congr (h : machine.ComputesTidily x time program)
    (heq : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s : OracleState),
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program').run s) :
    machine.ComputesTidily x time program' :=
  fun out₀ => (h out₀).congr heq

/-- A tidy machine realizes `program` under `runOracle` from `initialConfig`. -/
theorem runOracle (h : machine.ComputesTidily x time program)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool)) (s : OracleState) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (machine.runOracle time x)).run s =
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s := by
  have hlaw := ((h []) OracleState oracle s (machine.initialConfig x)
    (Cfg.init_eq_wordsCfg machine.initial x) (fun _ => rfl)).1
  have hout := congrArg (PMF.map (fun p => (p.1.output, p.2))) hlaw
  rw [runOracle_eq_map, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  refine Eq.trans ?_ (hout.trans ?_)
  · rw [PMF.map_comp]
    congr 1
  · rw [PMF.map_comp]
    have hcomp :
        ((fun p : Cfg k Bool State x × OracleState => (p.1.output, p.2)) ∘
          fun (a, s') => (wordsCfg x none (fun _ => []) ([] ++ id a), s')) = id := by
      funext ⟨a, s'⟩
      simp
    rw [hcomp, PMF.map_id]

/-- A deterministic tidy machine lifts directly to `ComputesTidily` via `ofDeterministic`. -/
theorem of_deterministic {tm : MultiTapeTM k Bool State} {output : List Bool} {t s : ℕ}
    (htm : tm.ComputesTidilyInTimeAndSpace x output t s) :
    (ofDeterministic tm : MultiTapePTM k Bool State Operation).ComputesTidily
      x t (pure output) := by
  intro out₀
  have h := RunsWords.of_transformsTapes (Operation := Operation) (out₀ := out₀) htm
    ⟨rfl, rfl⟩ (fun _ _ hQ => hQ)
  simpa only [map_pure] using h.of_map (fun _ => output) (fun _ _ => []) id

/-- Any supported output of a `ComputesTidily` machine has length at most `time`. -/
theorem length_output_le (h : machine.ComputesTidily x time program)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (s : OracleState) {w : List Bool} {s' : OracleState}
    (hw : (w, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s).support) :
    w.length ≤ time :=
  (h []).length_emit_le oracle s hw

end ComputesTidily

end Turing.MultiTapePTM
