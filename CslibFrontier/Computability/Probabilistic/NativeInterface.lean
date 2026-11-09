/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual randomized native instructions and pre-response interfaces

[Wang2027], model PDF pp. 4--6, Theorems 5/6 pp. 12--13 and Appendix A.5 p. 16,
condition on the selected query before observing its response. `instruction`
reads the actual native transition table and query buffers using a private bit;
`dispatch` alone samples the stateful response and installs its exact raw word.

Two interface ticks implement one original native instruction, preserving all
hidden tapes, buffers, oracle state, raw records and joint resources. The actual
unbounded stopped interface law is proved equal to native execution, including
divergence, and therefore inherits its constructed behavioral representation.
Saved-coin replay connects the original open PTM program to every clocked law;
no machine-to-process representation identity is an admission hypothesis.

This is a distributional interface refinement of the typed `MultiTapePTM` model.
It is not a compiler or a theorem decoding arbitrary external PTM encodings.
Silent instructions remain explicit. Source oracle-turn stopping epochs, batch
codecs/concurrency/cancellation contracts and quantitative-policy transfer still
need separate proofs. Responses remain discrete PMFs.

## Main results

* `prepare_dispatch`: concrete selected instructions recover the actual native kernel.
* `execute_coins`: the original open program equals its fair saved-coin replay law.
* `selectedResponse_disintegration`: derived joint selection/response conditioning.
* `terminal_native`: complete unbounded interface/native stopped laws, including divergence.
* `terminal_behavioral`: end-to-end constructed behavioral stopped observation law.
* `terminal_outcome`: successful-only admission preserves joint stopped outcomes and resources.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeInterface
open NativeOpenExecution NativeOpenSelection Turing
open scoped ENNReal
variable {Operation Private Control J : Type} {k : ℕ} {input : List Bool}
variable [DecidableEq Operation]

/-- A real native instruction selected before sampling any external response. -/
inductive Instruction (k : ℕ) (Control Operation Private : Type) (input : List Bool) where
  /-- An already halted native world, with its exact output and memory. -/
  | halted (world : World k Control Operation Private input)
  /-- The actual local action has no external response. -/
  | local (next : World k Control Operation Private input)
  /-- A chosen native channel and continuation; its request is the saved buffer. -/
  | query (world : World k Control Operation Private input) (operation : Operation) (next : Control)

variable (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)

/-- Read the actual table on the actual scanned input/work/answer symbols.
Preparing a query does not run the environment or replace private storage. -/
@[expose] def instruction (world : World k Control Operation Private input) (bit : Bool) :
    Instruction k Control Operation Private input :=
  match world.config.tapes.state with
  | none => .halted world
  | some control => match machine.tr control world.config.tapes.inputSymbol
      world.config.tapes.workTapeSymbols world.config.answerSymbols bit with
    | .step action symbol move => .local ⟨world.config.step action symbol move, world.memory⟩
    | .query operation next => .query world operation next

/-- Private fair choice of the actual next instruction, before external sampling. -/
@[expose] def prepare (world : World k Control Operation Private input) :
    PMF (Instruction k Control Operation Private input) :=
  (PMF.uniformOfFintype Bool).map (instruction machine world)

/-- Commit the selected instruction. Only an actual query samples the external
joint word/resource law, retaining the same actual private oracle state. -/
@[expose] def dispatch : Instruction k Control Operation Private input →
    PMF (World k Control Operation Private input)
  | .halted world => PMF.pure world
  | .local next => PMF.pure next
  | .query world op next =>
    (env (op, (world.config.channels op).queryBuffer) world.memory).map fun (reply, privateState) =>
      ⟨world.config.receive op next reply.word,
        world.memory.record (op, (world.config.channels op).queryBuffer) reply privateState⟩

/-- Preparation followed by dispatch is the original actual native transition. -/
theorem prepare_dispatch (world : World k Control Operation Private input) :
    (prepare machine world).bind (dispatch env) = step machine env world := by
  cases hs : world.config.tapes.state with
  | none => simp [prepare, instruction, step, hs, PMF.bind_map, Function.comp_def, dispatch]
  | some control =>
    simp only [prepare, PMF.bind_map, Function.comp_def, instruction, step, hs]
    congr 1
    funext bit
    cases machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
      world.config.answerSymbols bit <;> rfl

/-- Actual open native saved-coin execution; only the external handler is random. -/
@[expose] def replay (coins : List Bool) (world : World k Control Operation Private input) :
    PMF (World k Control Operation Private input) :=
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    (machine.runConfigFromCoins (fun op word => ProbOracleComp.query (op, word))
      coins world.config)).run world.memory).map (fun (config, memory) => ⟨config, memory⟩)

/-- The original open PTM program has the joint law of an independently sampled
fair tape prefix and its actual replay, including every handler effect. -/
theorem execute_coins (fuel : ℕ) (world : World k Control Operation Private input) :
    execute machine env fuel world = (BitString.uniformList fuel).bind
      (fun coins => replay machine env coins world) := by
  unfold execute replay
  have he := MultiTapePTM.run_interpret_runConfigFrom_eq_coins machine
    (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    (by intro memory; rw [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform])
    fuel world.config world.memory
  rw [he, PMF.map_bind]

/-- Public pre-response interface information. No work tape, private oracle
state or unobserved private bit is exported. -/
inductive Signal (Operation : Type) where
  /-- A local native instruction, without a response. -/
  | silent (history : List (Event Operation))
  /-- An already halted native machine. -/
  | halted (history : List (Event Operation))
  /-- The entire selected raw request and prior actual response/resource history. -/
  | query (history : List (Event Operation)) (operation : Operation) (request : List Bool)

/-- Read the selected request before dispatch can obtain any response. -/
@[expose] def signal : Instruction k Control Operation Private input → Signal Operation
  | .halted world => .halted world.memory.events
  | .local next => .silent next.memory.events
  | .query world op _ => .query world.memory.events op (world.config.channels op).queryBuffer

/-- Actual joint pre-response selection and post-response hidden-state law. -/
@[expose] def selectedResponse (prior : PMF (World k Control Operation Private input)) :
    PMF (Signal Operation × World k Control Operation Private input) := do
  let chosen ← prior.bind (prepare machine)
  let next ← dispatch env chosen
  pure (signal chosen, next)

/-- Conditional dispatch law derived from the actual hidden selected-instruction
law. Null public signals use the harmless prior posterior completion. -/
@[expose] def conditionalResponse (prior : PMF (World k Control Operation Private input))
    (selected : Signal Operation) : PMF (World k Control Operation Private input) :=
  (PMF.posterior (prior.bind (prepare machine)) signal selected).bind (dispatch env)

/-- The selected-before-response joint law is disintegrated, not assumed.
Conditioning retains arbitrary hidden memory/randomness and all prior records. -/
theorem selectedResponse_disintegration (prior : PMF (World k Control Operation Private input)) :
    ((prior.bind (prepare machine)).map signal).bind (fun selected =>
      (conditionalResponse machine env prior selected).map (fun next => (selected, next))) =
        selectedResponse machine env prior := by
  have he := PMF.posterior_bind (prior.bind (prepare machine)) signal
    (fun chosen selected => (dispatch env chosen).map (fun next => (selected, next)))
  simpa only [conditionalResponse, selectedResponse, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map, PMF.bind_bind, Function.comp_def] using he

/-- Forgetting the pre-response signal recovers the actual native next-state
law; signals do not resample or reset the hidden world. -/
theorem selectedResponse_native (prior : PMF (World k Control Operation Private input)) :
    (selectedResponse machine env prior).map Prod.snd = prior.bind (step machine env) := by
  simp only [selectedResponse, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  simp only [PMF.bind_pure]
  change ((prior.bind (prepare machine)).bind (dispatch env)) = _
  simp only [PMF.bind_bind, prepare_dispatch]

/-- A native boundary and a selected, still unanswered instruction are distinct. -/
inductive Phase (k : ℕ) (Control Operation Private : Type) (input : List Bool) where
  /-- Native instruction boundary with all hidden state retained. -/
  | ready (world : World k Control Operation Private input)
  /-- Private instruction selected; the external response has not been sampled. -/
  | pending (chosen : Instruction k Control Operation Private input)

/-- Actual two-phase execution: select privately, then dispatch. -/
@[expose] def phaseStep : Phase k Control Operation Private input →
    PMF (Phase k Control Operation Private input)
  | .ready world => if world.config.tapes.state.isNone then PMF.pure (.ready world)
      else (prepare machine world).map Phase.pending
  | .pending chosen => (dispatch env chosen).map Phase.ready

/-- Only a committed native halted configuration is a stopped state. -/
@[expose] def phaseHalted : Phase k Control Operation Private input → Prop
  | .ready world => NativeUnboundedExecution.halted world
  | .pending _ => False

instance : DecidablePred (phaseHalted (k := k) (Control := Control) (Operation := Operation)
    (Private := Private) (input := input)) := fun phase =>
  match phase with
  | .ready world => inferInstanceAs (Decidable (NativeUnboundedExecution.halted world))
  | .pending _ => inferInstanceAs (Decidable False)

/-- Native halting is absorbing in the actual interface refinement. -/
theorem phase_absorbs (phase : Phase k Control Operation Private input)
    (h : phaseHalted phase) : phaseStep machine env phase = PMF.pure phase := by
  cases phase with
  | ready world => simp [phaseStep, show world.config.tapes.state = none from h]
  | pending chosen => exact h.elim

/-- Two interface ticks implement precisely one original native instruction. -/
theorem two_ticks (world : World k Control Operation Private input) :
    ObservedProcess.stateLaw (phaseStep machine env) 2 (.ready world) =
      (step machine env world).map Phase.ready := by
  cases hs : world.config.tapes.state with
  | none => simp [ObservedProcess.stateLaw, phaseStep, step, hs]
  | some control =>
    simp only [ObservedProcess.stateLaw, PMF.pure_bind, phaseStep, hs, Option.isNone_some,
      Bool.false_eq_true, ite_false, PMF.bind_map, Function.comp_def]
    change ((prepare machine world).bind fun chosen => (dispatch env chosen).map Phase.ready) = _
    rw [← PMF.map_bind, prepare_dispatch]

/-- The complete actual configuration/interface law at every even tick agrees
with uninterrupted original PTM execution. -/
theorem even_ticks (fuel : ℕ) (world : World k Control Operation Private input) :
    ObservedProcess.stateLaw (phaseStep machine env) (2 * fuel) (.ready world) =
      (execute machine env fuel world).map Phase.ready := by
  induction fuel generalizing world with
  | zero => simp [ObservedProcess.stateLaw, execute_zero]
  | succ fuel ih =>
    rw [show 2 * (fuel + 1) = (2 * fuel + 1) + 1 by omega]
    simp only [ObservedProcess.stateLaw, ih, PMF.bind_map]
    rw [PMF.bind_bind]
    change ((execute machine env fuel world).bind fun next =>
      ((phaseStep machine env (.ready next)).bind (phaseStep machine env))) = _
    have ht (next : World k Control Operation Private input) :
        (phaseStep machine env (.ready next)).bind (phaseStep machine env) =
          (step machine env next).map Phase.ready := by
      simpa only [ObservedProcess.stateLaw, PMF.pure_bind] using two_ticks machine env next
    simp only [ht]
    rw [← PMF.map_bind]
    rw [execute_add]
    congr 1
    congr 1
    funext next
    exact (execute_one machine env next).symm

/-- Actual stopped interface execution, retaining pending states on divergence
only through missing mass, never as falsely completed native results. -/
@[expose] def terminal (world : World k Control Operation Private input) :
    PMF (Option (Phase k Control Operation Private input)) :=
  StoppedProcess.terminal (phaseStep machine env) phaseHalted (phase_absorbs machine env)
    (.ready world)

private theorem stopped_even (fuel : ℕ) (world next : World k Control Operation Private input) :
    StoppedProcess.stopped (phaseStep machine env) phaseHalted (2 * fuel) (.ready world)
      (.ready next) = StoppedProcess.stopped (step machine env) NativeUnboundedExecution.halted
        fuel world next := by
  classical
  simp only [StoppedProcess.stopped, phaseHalted, even_ticks, execute_eq_stateLaw]
  split_ifs
  · simp [PMF.map_apply]
  · rfl

/-- Cofinal even clocks recover exactly the native halted-state mass. No common
terminating clock, termination probability or equality of limits is supplied. -/
theorem terminal_mass_ready (world next : World k Control Operation Private input) :
    terminal machine env world (some (.ready next)) =
      NativeUnboundedExecution.terminal machine env world (some next) := by
  change (⨆ n, StoppedProcess.stopped (phaseStep machine env) phaseHalted n (.ready world)
    (.ready next)) = ⨆ n, StoppedProcess.stopped (step machine env)
      NativeUnboundedExecution.halted n world next
  have hm := StoppedProcess.stopped_mono (phaseStep machine env) phaseHalted
    (phase_absorbs machine env) (.ready world)
  apply le_antisymm
  · apply iSup_le
    intro n
    calc
      _ ≤ StoppedProcess.stopped (phaseStep machine env) phaseHalted (2 * n)
          (.ready world) (.ready next) := hm (by omega) _
      _ = _ := stopped_even machine env n world next
      _ ≤ _ := le_iSup (fun n => StoppedProcess.stopped (step machine env)
        NativeUnboundedExecution.halted n world next) n
  · apply iSup_le
    intro n
    rw [← stopped_even machine env n world next]
    exact le_iSup (fun n => StoppedProcess.stopped (phaseStep machine env) phaseHalted n
      (.ready world) (.ready next)) (2 * n)

/-- The actual unbounded stopped interface masses come from fair random-tape
prefixes executing the original open PTM program. No uniform terminating tape
length is assumed, and external calls retain their joint stateful law. -/
theorem terminal_coins (world next : World k Control Operation Private input) :
    terminal machine env world (some (.ready next)) =
      ⨆ fuel, if NativeUnboundedExecution.halted next then
        ((BitString.uniformList fuel).bind (fun coins => replay machine env coins world)) next
        else 0 := by
  rw [terminal_mass_ready]
  change (⨆ fuel, StoppedProcess.stopped (step machine env)
    NativeUnboundedExecution.halted fuel world next) = _
  simp only [StoppedProcess.stopped, ← execute_eq_stateLaw, execute_coins]

/-- Complete actual interface/native stopped laws agree, including divergence
and every retained private configuration, event and resource receipt. -/
theorem terminal_native (world : World k Control Operation Private input) :
    terminal machine env world =
      (NativeUnboundedExecution.terminal machine env world).map (Option.map Phase.ready) := by
  classical
  apply StoppedProcess.option_ext
  intro phase
  cases phase with
  | ready next =>
    rw [terminal_mass_ready]
    simp [PMF.map_apply]
  | pending chosen =>
    change (⨆ n, StoppedProcess.stopped (phaseStep machine env) phaseHalted n
      (.ready world) (.pending chosen)) = _
    simp [StoppedProcess.stopped, phaseHalted, PMF.map_apply]

/-- Read back the world carried by an interface state. Only `ready` states can
occur as supported terminal results. This projection is for terminal readback,
not partial-execution acceptance: a pending local action can carry a prospective
halted configuration before its commit tick. -/
@[expose] def worldOf : Phase k Control Operation Private input →
    World k Control Operation Private input
  | .ready world => world
  | .pending (.halted world) => world
  | .pending (.local next) => next
  | .pending (.query world _ _) => world

variable [DecidableEq J]
variable (parse : Operation → List Bool → List Bool → Finset J)
variable (decode : List Bool → Option (Finset J)) (accept : Finset J → Bool)

/-- End-to-end connection: actual table/coin/interface execution has the
constructed unbounded complete-history behavioral stopped-view law. -/
theorem terminal_behavioral (world : World k Control Operation Private input) :
    (terminal machine env world).map
        (Option.map fun phase => view parse decode (worldOf phase)) =
      NativeUnboundedExecution.behavioral machine env parse decode world := by
  rw [terminal_native, PMF.map_comp]
  convert NativeUnboundedExecution.terminal_behavioral_law machine env parse decode world using 1
  congr 1
  funext next
  cases next <;> rfl

/-- Successful-output-only admission transfers to the whole actual interface
execution, retaining the joint path, stopping, success and both resources. -/
theorem terminal_outcome (world : World k Control Operation Private input)
    (h : NativeUnboundedExecution.SelectionOnly machine env parse decode accept world) :
    (terminal machine env world).map
        (Option.map fun phase => outcome accept (view parse decode (worldOf phase))) =
      (NativeUnboundedExecution.terminal machine env world).map (Option.map fun next =>
        outcome accept
          ⟨next.memory.events, next.config.tapes.state.isNone, result decode next⟩) := by
  have he := congrArg (PMF.map (Option.map (outcome accept)))
    (terminal_behavioral machine env parse decode world)
  rw [NativeUnboundedExecution.behavioral_outcome_law machine env parse decode accept world h]
    at he
  rw [PMF.map_comp] at he
  convert he using 1
  congr 1
  funext next
  cases next <;> rfl

end Cslib.Probability.NativeInterface
