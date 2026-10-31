/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time finite configuration operations

Ordinary structure construction, observations, fixed native actions and initialization are
certified in plain polynomial time (`Turing.MultiTapeTM.ComputableInPolyTime`), by composition of
pair, list, table and tape rules. The tidy forms of the closed rules are derived from the plain
ones; channel operations for oracle configurations remain in the tidy calculus. Copying the
input, work tapes, accumulated output and every channel is charged by their encodings.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.finiteCfg_state`, `.finiteCfg_inputSymbol`,
  `.finiteCfg_workTapeSymbols`, `.finiteCfg_output`: plain observations.
* `Turing.MultiTapeTM.ComputableInPolyTime.finiteCfg_step`: execute a fixed native action.
* `Turing.MultiTapeTM.ComputableInPolyTime.finiteCfg_init`: initialize finite storage.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_step`, `.finiteConfig_receive`:
  local transitions and channel reset with a computed reply.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_init`: initialize oracle storage.

## References

Adapts Computability/Probabilistic/Configuration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib.Turing MultiTapeMachine

variable {k : ℕ} {State α : Type} [Finite State] {input : α ↪ List Bool}

/-- Assemble an ordinary configuration from its certified components. -/
@[fun_prop]
theorem finiteCfg_mk {word : α → List Bool} {state : α → Option State}
    {position : ∀ a, Fin ((word a).length + 2)} {work : α → Fin k → BiTape Bool}
    {output : α → List Bool} (hword : ComputableInPolyTime word input encBits)
    (hstate : ComputableInPolyTime state input (encFinite (Option State)))
    (hposition : ComputableInPolyTime (fun a => (position a).val) input encUnary)
    (hwork : ComputableInPolyTime work input (encPi (encBiTape encBool)))
    (houtput : ComputableInPolyTime output input encBits) :
    ComputableInPolyTime (fun a =>
      (⟨word a, state a, position a, work a, output a⟩ : FiniteCfg k Bool State))
      input encFiniteCfg :=
  (hword.prod (hstate.prod (hposition.prod (hwork.prod houtput)))).of_enc_eq (fun _ => rfl)

private theorem finiteCfg_parts : ComputableInPolyTime
    (fun cfg : FiniteCfg k Bool State =>
      (cfg.input, cfg.state, cfg.inputPos.val, cfg.workTapes, cfg.output)) encFiniteCfg
    (encPair encBits (encPair (encFinite (Option State))
      (encPair encUnary (encPair (encPi (encBiTape encBool)) encBits)))) := of_eq fun _ => rfl

/-- Read the stored input word. -/
@[fun_prop]
theorem finiteCfg_input : ComputableInPolyTime (FiniteCfg.input (k := k) (State := State))
    encFiniteCfg encBits := finiteCfg_parts.fst'

/-- Read the finite control. -/
@[fun_prop]
theorem finiteCfg_state : ComputableInPolyTime (FiniteCfg.state (k := k) (State := State))
    encFiniteCfg (encFinite (Option State)) := finiteCfg_parts.snd'.fst'

/-- Read the input head's unary position. -/
@[fun_prop]
theorem finiteCfg_inputPos : ComputableInPolyTime
    (fun cfg : FiniteCfg k Bool State => cfg.inputPos.val) encFiniteCfg encUnary :=
  finiteCfg_parts.snd'.snd'.fst'

/-- Read the complete family of work tapes. -/
@[fun_prop]
theorem finiteCfg_workTapes : ComputableInPolyTime
    (FiniteCfg.workTapes (k := k) (State := State)) encFiniteCfg (encPi (encBiTape encBool)) :=
  finiteCfg_parts.snd'.snd'.snd'.fst'

/-- Read all accumulated output. -/
@[fun_prop]
theorem finiteCfg_output : ComputableInPolyTime (FiniteCfg.output (k := k) (State := State))
    encFiniteCfg encBits := finiteCfg_parts.snd'.snd'.snd'.snd'

/-- Observe the read-only input, including both blank boundary cells. -/
@[fun_prop]
theorem finiteCfg_inputSymbol : ComputableInPolyTime
    (FiniteCfg.inputSymbol (k := k) (State := State)) encFiniteCfg (encFinEnum (Option Bool)) := by
  have hlist : ComputableInPolyTime
      (fun cfg : FiniteCfg k Bool State => none :: cfg.input.map some)
      encFiniteCfg (encList (encFinEnum (Option Bool))) := by
    have hsome : ComputableInPolyTime (some (α := Bool))
        encBool (encFinEnum (Option Bool)) := of_finite _
    exact (const none).cons' ((map hsome).comp (bitsToList.comp finiteCfg_input))
  simpa only [Function.comp_def, List.getD_eq_getElem?_getD,
    ← FiniteCfg.inputSymbol_eq_getD] using
    (listGetD (encA := encFinEnum (Option Bool)) none).comp (hlist.prod finiteCfg_inputPos)

/-- Observe all work heads as a single fixed finite value. -/
@[fun_prop]
theorem finiteCfg_workTapeSymbols : ComputableInPolyTime
    (FiniteCfg.workTapeSymbols (k := k) (State := State)) encFiniteCfg
      (encFinEnum (Fin k → Option Bool)) := by
  have hheads : ComputableInPolyTime
      (fun cfg : FiniteCfg k Bool State => fun tape => (cfg.workTapes tape).head)
      encFiniteCfg (encPi (encOption encBool)) :=
    pi fun tape => (biTape_head encBool).comp ((pi_apply _ tape).comp finiteCfg_workTapes)
  exact (of_finite id).comp hheads

/-- Clamped native input-head movement is efficient on the stored unary position. -/
@[fun_prop]
theorem moveInputPos {word : α → List Bool} {position : ∀ a, Fin ((word a).length + 2)}
    (hword : ComputableInPolyTime word input encBits)
    (hposition : ComputableInPolyTime (fun a => (position a).val) input encUnary)
    (move : SignType) : ComputableInPolyTime
      (fun a => (Turing.moveInputPos (position a) move).val) input encUnary := by
  cases move with
  | neg =>
    apply (unary_sub.comp (hposition.prod (const 1))).of_enc_eq
    intro a
    apply congrArg encUnary
    have h := val_moveInputPos_eq (position a) .neg
    have hp := (position a).isLt
    simp only [SignType.cast, Function.comp_def] at h ⊢
    lia
  | zero => simpa using hposition
  | pos =>
    -- `min x y = x - (x - y)`
    have hnext := unary_add.comp (hposition.prod (const 1))
    have hlast := unary_add.comp ((length_bits.comp hword).prod (const 1))
    apply (unary_sub.comp (hnext.prod (unary_sub.comp (hnext.prod hlast)))).of_enc_eq
    intro a
    apply congrArg encUnary
    have h := val_moveInputPos_eq (position a) .pos
    simp only [SignType.cast, Function.comp_def] at h ⊢
    lia

/-- Execute a fixed ordinary native action, including all retained storage. -/
@[fun_prop]
theorem finiteCfg_step (action : Action k Bool State) : ComputableInPolyTime
    (fun cfg : FiniteCfg k Bool State => cfg.step action) encFiniteCfg encFiniteCfg := by
  refine finiteCfg_mk finiteCfg_input (const _)
    (moveInputPos finiteCfg_input finiteCfg_inputPos action.inputTape)
    (pi fun tape => biTape_step (action.workTapes tape)
      ((pi_apply _ tape).comp finiteCfg_workTapes))
    (bitsAppend finiteCfg_output (const _))

/-- Initialize with the native input-head convention and blank work tapes. -/
@[fun_prop]
theorem finiteCfg_init {word : α → List Bool}
    (hword : ComputableInPolyTime word input encBits) (state : State) :
    ComputableInPolyTime (fun a => FiniteCfg.init (k := k) state (word a))
      input encFiniteCfg := by
  apply finiteCfg_mk hword (const _)
  · simpa using (const (encIn := input) (encOut := encUnary) 1)
  · exact const _
  · exact const _

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

open Cslib.Turing MultiTapeMachine

variable {k : ℕ} {State α : Type} [Finite State] {input : α ↪ List Bool}

/-- Assemble an ordinary configuration from its certified components. -/
@[fun_prop]
theorem finiteCfg_mk {word : α → List Bool} {state : α → Option State}
    {position : ∀ a, Fin ((word a).length + 2)} {work : α → Fin k → BiTape Bool}
    {output : α → List Bool} (hword : ComputableTidilyInPolyTime word input encBits)
    (hstate : ComputableTidilyInPolyTime state input (encFinite (Option State)))
    (hposition : ComputableTidilyInPolyTime (fun a => (position a).val) input encUnary)
    (hwork : ComputableTidilyInPolyTime work input (encPi (encBiTape encBool)))
    (houtput : ComputableTidilyInPolyTime output input encBits) :
    ComputableTidilyInPolyTime (fun a =>
      (⟨word a, state a, position a, work a, output a⟩ : FiniteCfg k Bool State))
      input encFiniteCfg :=
  (hword.prod (hstate.prod (hposition.prod (hwork.prod houtput)))).of_enc_eq (fun _ => rfl)

/-- Read the stored input word. -/
@[fun_prop]
theorem finiteCfg_input : ComputableTidilyInPolyTime (FiniteCfg.input (k := k) (State := State))
    encFiniteCfg encBits := ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_input

/-- Read the finite control. -/
@[fun_prop]
theorem finiteCfg_state : ComputableTidilyInPolyTime (FiniteCfg.state (k := k) (State := State))
    encFiniteCfg (encFinite (Option State)) :=
  ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_state

/-- Read the input head's unary position. -/
@[fun_prop]
theorem finiteCfg_inputPos : ComputableTidilyInPolyTime
    (fun cfg : FiniteCfg k Bool State => cfg.inputPos.val) encFiniteCfg encUnary :=
  ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_inputPos

/-- Read the complete family of work tapes. -/
@[fun_prop]
theorem finiteCfg_workTapes : ComputableTidilyInPolyTime
    (FiniteCfg.workTapes (k := k) (State := State)) encFiniteCfg (encPi (encBiTape encBool)) :=
  ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_workTapes

/-- Read all accumulated output. -/
@[fun_prop]
theorem finiteCfg_output : ComputableTidilyInPolyTime (FiniteCfg.output (k := k) (State := State))
    encFiniteCfg encBits := ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_output

/-- Observe the read-only input, including both blank boundary cells. -/
@[fun_prop]
theorem finiteCfg_inputSymbol : ComputableTidilyInPolyTime
    (FiniteCfg.inputSymbol (k := k) (State := State)) encFiniteCfg (encFinEnum (Option Bool)) :=
  ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_inputSymbol

/-- Observe all work heads as a single fixed finite value. -/
@[fun_prop]
theorem finiteCfg_workTapeSymbols : ComputableTidilyInPolyTime
    (FiniteCfg.workTapeSymbols (k := k) (State := State)) encFiniteCfg
      (encFinEnum (Fin k → Option Bool)) :=
  ComputableInPolyTime.tidy ComputableInPolyTime.finiteCfg_workTapeSymbols

/-- Clamped native input-head movement is efficient on the stored unary position. -/
@[fun_prop]
theorem moveInputPos {word : α → List Bool} {position : ∀ a, Fin ((word a).length + 2)}
    (hword : ComputableTidilyInPolyTime word input encBits)
    (hposition : ComputableTidilyInPolyTime (fun a => (position a).val) input encUnary)
    (move : SignType) : ComputableTidilyInPolyTime
      (fun a => (Turing.moveInputPos (position a) move).val) input encUnary := by
  cases move with
  | neg =>
    apply (unary_sub.comp (hposition.prod (const 1))).of_enc_eq
    intro a
    apply congrArg encUnary
    have h := val_moveInputPos_eq (position a) .neg
    have hp := (position a).isLt
    simp only [SignType.cast, Function.comp_def] at h ⊢
    lia
  | zero => simpa using hposition
  | pos =>
    apply (unary_min.comp ((unary_add.comp (hposition.prod (const 1))).prod
      (unary_add.comp ((length_bits.comp hword).prod (const 1))))).of_enc_eq
    intro a
    apply congrArg encUnary
    have h := val_moveInputPos_eq (position a) .pos
    simp only [SignType.cast, Function.comp_def] at h ⊢
    lia

/-- Execute a fixed ordinary native action, including all retained storage. -/
@[fun_prop]
theorem finiteCfg_step (action : Action k Bool State) : ComputableTidilyInPolyTime
    (fun cfg : FiniteCfg k Bool State => cfg.step action) encFiniteCfg encFiniteCfg :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.finiteCfg_step action)

/-- Initialize with the native input-head convention and blank work tapes. -/
@[fun_prop]
theorem finiteCfg_init {word : α → List Bool}
    (hword : ComputableTidilyInPolyTime word input encBits) (state : State) :
    ComputableTidilyInPolyTime (fun a => FiniteCfg.init (k := k) state (word a))
      input encFiniteCfg := by
  apply finiteCfg_mk hword (const _)
  · simpa using (const (encIn := input) (encMid := encUnary) 1)
  · exact const _
  · exact const _

variable {Oracle : Type} [Fintype Oracle]

/-- Assemble ordinary storage and its family of oracle channels. -/
@[fun_prop]
theorem finiteConfig_mk {tapes : α → FiniteCfg k Bool State}
    {channels : α → Oracle → List Bool × BiTape Bool}
    (htapes : ComputableTidilyInPolyTime tapes input encFiniteCfg)
    (hchannels : ComputableTidilyInPolyTime channels input
      (encPi (encPair encBits (encBiTape encBool)))) :
    ComputableTidilyInPolyTime (fun a => (⟨tapes a, channels a⟩ : FiniteConfig k Bool State Oracle))
      input encFiniteConfig := (htapes.prod hchannels).of_enc_eq (fun _ => rfl)

private theorem finiteConfig_parts : ComputableTidilyInPolyTime
    (fun cfg : FiniteConfig k Bool State Oracle => (cfg.tapes, cfg.channels)) encFiniteConfig
    (encPair encFiniteCfg (encPi (encPair encBits (encBiTape encBool)))) := of_eq fun _ => rfl

/-- Read the ordinary finite storage. -/
@[fun_prop]
theorem finiteConfig_tapes : ComputableTidilyInPolyTime
    (FiniteConfig.tapes (k := k) (State := State) (Oracle := Oracle))
    encFiniteConfig encFiniteCfg := finiteConfig_parts.fst'

/-- Read all query buffers and answer tapes. -/
@[fun_prop]
theorem finiteConfig_channels : ComputableTidilyInPolyTime
    (FiniteConfig.channels (k := k) (State := State) (Oracle := Oracle)) encFiniteConfig
    (encPi (encPair encBits (encBiTape encBool))) := finiteConfig_parts.snd'

/-- Observe every answer head as a single fixed finite value. -/
@[fun_prop]
theorem finiteConfig_answerSymbols : ComputableTidilyInPolyTime
    (FiniteConfig.answerSymbols (k := k) (State := State) (Oracle := Oracle)) encFiniteConfig
      (encFinite (Oracle → Option Bool)) := by
  have hheads : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool State Oracle => fun channel => (cfg.channels channel).2.head)
      encFiniteConfig (encPi (encOption encBool)) := by fun_prop
  exact (of_finite id).comp hheads

/-- Execute a fixed local action, including all pending requests and stored answers. -/
@[fun_prop]
theorem finiteConfig_step (action : Action k Bool State) (symbol : Oracle → Option Bool)
    (move : Oracle → SignType) : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool State Oracle => cfg.step action symbol move)
      encFiniteConfig encFiniteConfig := by
  unfold FiniteConfig.step
  fun_prop

/-- Install a computed reply, clear its selected request and retain all other channels. -/
@[fun_prop]
theorem finiteConfig_receive [DecidableEq Oracle] {cfg : α → FiniteConfig k Bool State Oracle}
    {answer : α → List Bool} (hcfg : ComputableTidilyInPolyTime cfg input encFiniteConfig)
    (hanswer : ComputableTidilyInPolyTime answer input encBits) (channel : Oracle) (next : State) :
    ComputableTidilyInPolyTime (fun a => (cfg a).receive channel next (answer a))
      input encFiniteConfig := by
  have hframed : ComputableTidilyInPolyTime answer input (encList encBool) :=
    bitsToList.comp hanswer
  unfold FiniteConfig.receive
  fun_prop

/-- Initialize every channel with an empty request and blank answer tape. -/
@[fun_prop]
theorem finiteConfig_init {word : α → List Bool}
    (hword : ComputableTidilyInPolyTime word input encBits) (state : State) :
    ComputableTidilyInPolyTime
      (fun a => FiniteConfig.init (k := k) (Oracle := Oracle) state (word a))
      input encFiniteConfig := by
  unfold FiniteConfig.init
  fun_prop

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
