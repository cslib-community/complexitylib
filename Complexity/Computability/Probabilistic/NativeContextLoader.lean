/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeRuntimeContext
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Loading runtime context before actual native open execution

The loader is constructed from a proved pure input-to-context algorithm. It runs
from blank native work tapes, writes its result on the reserved context tape,
clears scratch storage and restores the input head before the consumer starts.
The consumer is actual native code, with no success or representation contract.
Its unbounded joint law, including divergence and oracle resources, is preserved.
This supplies initial storage preparation for [Wang2027], Theorem 5 p. 12/App. A.5
p. 16, rather than a complete source-admitted adaptive selector.

## Main definitions

* `loadedStart`, `extendWorld`: actual loaded consumer storage and scratch embedding.
* `observe`: readback of consumer storage and the same resource ledger.

## Main results

* `exists_load_then`: constructed native loading followed by arbitrary open native code.
* `exists_loaded_runtime`: original-input loading composed with both runtime queries.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeContextLoader
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- The consumer's four ordinary tapes, with only the runtime context tape loaded. -/
@[expose] def loadedStart {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (input context : List Bool) (memory : Memory Unit P) : World 4 S Unit P input :=
  ⟨{ consumer.initialConfig input with
    tapes := wordsCfg input (some consumer.initial)
      (Function.update (fun _ => []) 0 context) [] }, memory⟩

/-- Extra loader scratch tapes remain blank while the actual consumer executes. -/
@[expose] def extendWorld {S P : Type} {input : List Bool} (scratch : ℕ)
    (world : World 4 S Unit P input) : World (4 + scratch) S Unit P input :=
  ⟨world.config.embed (Fin.castAddEmb scratch) (fun _ _ => none) (fun _ => 0), world.memory⟩

private theorem terminal_extend {S P : Type} {input : List Bool}
    (scratch : ℕ) (consumer : MultiTapePTM 4 Bool S Unit) (env : Environment Unit P)
    (world : World 4 S Unit P input) :
    NativeUnboundedExecution.terminal (consumer.extendTapes (Fin.castAddEmb scratch)) env
      (extendWorld scratch world) =
      (NativeUnboundedExecution.terminal consumer env world).map
        (Option.map (extendWorld scratch)) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step consumer env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (NativeOpenExecution.step (consumer.extendTapes (Fin.castAddEmb scratch)) env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (extendWorld scratch) _ _ world
  · intro next
    rw [← execute_one, ← execute_one]
    simp only [execute, extendWorld, MultiTapePTM.runConfigFrom_embed,
      OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
    rfl
  · intro next
    rfl

private def loaderTapes (scratch : ℕ) : Fin (scratch + 1) ↪ Fin (4 + scratch) :=
  Fin.Embedding.snoc (Fin.natAddEmb 4) (a := 0) (by
    rintro ⟨i, hi⟩
    have hz := congrArg Fin.val hi
    change 4 + i.val = 0 at hz
    omega)

private theorem loader_last (scratch : ℕ) : loaderTapes scratch (Fin.last scratch) = 0 :=
  by simp [loaderTapes]

private def prepared {scratch : ℕ} {R P : Type} (input context : List Bool)
    (memory : Memory Unit P) : World (4 + scratch) R Unit P input :=
  ⟨⟨wordsCfg input none (Function.update (fun _ => []) 0 context) [], fun _ => ⟨[], [], 0⟩⟩,
    memory⟩

private theorem loaded_embed {scratch : ℕ} {S P : Type}
    (consumer : MultiTapePTM 4 Bool S Unit) (input context : List Bool)
    (memory : Memory Unit P) :
    extendWorld scratch (loadedStart consumer input context memory) =
      (⟨⟨wordsCfg input (some consumer.initial)
        (Function.update (fun _ => []) 0 context) [], fun _ => ⟨[], [], 0⟩⟩,
        memory⟩ : World (4 + scratch) S Unit P input) := by
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (4 + scratch) S Unit P input))
  apply Config.ext
  · change embed (Fin.castAddEmb scratch)
      (wordsCfg input (some consumer.initial) (Function.update (fun _ => []) 0 context) [])
      (fun _ _ => none) (fun _ => 0) = _
    have hz : (fun _ : Fin (4 + scratch) => fun _ : ℤ => (none : Option Bool)) =
        (fun _ => tapeOfList ([] : List Bool)) := by simp
    rw [hz]
    apply embed_wordsCfg
    · intro j
      by_cases hj : j = 0
      · subst j
        have he : (Fin.castAddEmb scratch) (0 : Fin 4) = 0 := by ext; simp
        rw [he, Function.update_self, Function.update_self]
      · have he : (Fin.castAddEmb scratch) j ≠ 0 := by
          intro he
          apply hj
          exact Fin.ext (congrArg (fun v : Fin (4 + scratch) => v.val) he)
        rw [Function.update_of_ne he, Function.update_of_ne hj]
    · intro j hj
      have hn : j ≠ 0 := by
        intro he
        apply hj
        subst j
        exact ⟨0, rfl⟩
      simp [hn]
  · rfl

private theorem prepare_terminal {scratch : ℕ} {R P : Type}
    (loader : MultiTapeTM (4 + scratch) Bool R) (env : Environment Unit P)
    (input context : List Bool) (memory : Memory Unit P) (time space : ℕ)
    (h : TransformsTapes loader
      (fun word ws => word = input ∧ ws = fun _ => [])
      (fun _ _ ws emitted => ws = Function.update (fun _ => []) 0 context ∧ emitted = [])
      time space) :
    NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic loader) env
      ⟨(MultiTapePTM.ofDeterministic loader).initialConfig input, memory⟩ =
      PMF.pure (some (prepared input context memory)) := by
  obtain ⟨ws, emitted, hr, ⟨rfl, rfl⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp h input (fun _ => []) [] ⟨rfl, rfl⟩
  apply NativeResponseExecution.terminal_of_clock _ env _
    (prepared input context memory) time ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic loader).runOracleConfigFrom time
      ((MultiTapePTM.ofDeterministic loader).initialConfig input))).run memory).map
      (fun p => (⟨p.1, p.2⟩ : World (4 + scratch) R Unit P input)) = _
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  have hi : ((MultiTapePTM.ofDeterministic (Oracle := Unit) loader).initialConfig input).tapes =
      wordsCfg input (some loader.q₀) (fun _ => []) [] := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [MultiTapeMachine.initialConfig, Cfg.init, wordsCfg]
  rw [hi, hr]
  rfl

/-- Construct a loader from a pure algorithm and compose it with actual native
consumer code. All work tapes start blank; no preinstalled context, termination,
consumer-success or machine-to-program representation premise is supplied.
The loader is independent of the consumer, oracle and original input. -/
theorem exists_load_then {A : Type} (encoding : A ↪ List Bool) (context : A → List Bool)
    (hcontext : ComputableInPolyTime context encoding encBits) :
    ∃ (scratch : ℕ) (R : Type) (_ : Finite R)
      (loader : MultiTapeTM (4 + scratch) Bool R),
      ∀ (S P : Type) (consumer : MultiTapePTM 4 Bool S Unit) (env : Environment Unit P)
        (a : A) (memory : Memory Unit P),
      let machine := (MultiTapePTM.ofDeterministic loader).seq
        (consumer.extendTapes (Fin.castAddEmb scratch))
      NativeUnboundedExecution.terminal machine env
        ⟨machine.initialConfig (encoding a), memory⟩ =
        (NativeUnboundedExecution.terminal consumer env
          (loadedStart consumer (encoding a) (context a) memory)).map
          (Option.map fun final => NativeSequential.right (First := R)
            (extendWorld scratch final)) := by
  obtain ⟨t, s, _, _, hc⟩ := hcontext
  obtain ⟨_, ht⟩ := hc.exists_computableTidilyInTimeAndSpace
  obtain ⟨scratch, R, hR, code, hcode⟩ := ht
  let loader := code.outputToWord.extendTapes (loaderTapes scratch)
  refine ⟨scratch, R ⊕ RewindWorkState, inferInstance, loader, ?_⟩
  intro S P consumer env a memory
  have hp := (hcode a).outputToWord_extendTapes (loaderTapes scratch)
  rw [loader_last] at hp
  have hl : NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic loader) env
      ⟨(MultiTapePTM.ofDeterministic loader).initialConfig (encoding a), memory⟩ =
      PMF.pure (some (prepared (encoding a) (context a) memory)) := by
    apply prepare_terminal loader env _ _ memory _ _
    exact hp.imp (fun _ _ h => ⟨h.1, by simp [h.2]⟩)
      (fun _ _ _ _ hP h => by simpa only [hP.2, encBits_apply] using h) le_rfl le_rfl
  have hi : (⟨((MultiTapePTM.ofDeterministic loader).seq
      (consumer.extendTapes (Fin.castAddEmb scratch))).initialConfig (encoding a), memory⟩ :
      World (4 + scratch) _ Unit P (encoding a)) =
      NativeSequential.left (consumer.extendTapes (Fin.castAddEmb scratch))
        ⟨(MultiTapePTM.ofDeterministic loader).initialConfig (encoding a), memory⟩ := rfl
  dsimp only
  rw [hi, NativeSequential.terminal_seq, hl, PMF.pure_bind]
  have he : NativeSequential.resume (consumer.extendTapes (Fin.castAddEmb scratch))
      (prepared (R := R ⊕ RewindWorkState) (encoding a) (context a) memory) =
      extendWorld scratch (loadedStart consumer (encoding a) (context a) memory) := by
    rw [loaded_embed]
    rfl
  change (NativeUnboundedExecution.terminal _ env _).map _ = _
  rw [he, terminal_extend, PMF.map_comp]
  congr 1
  funext result
  cases result <;> rfl

/-- Read the consumer's actual context and resource observations, ignoring only
loader scratch tapes. -/
@[expose] def observe {scratch : ℕ} {S P : Type} {input : List Bool}
    (world : World (4 + scratch) S Unit P input) : NativeRuntimeContext.Observation P :=
  ⟨world.config.tapes.output, world.config.tapes.workTapes 0,
    world.config.tapes.workTapePos 0, world.config.tapes.workTapes 1, world.memory⟩

/-- Readback commutes with actual scratch embedding and native sequential control. -/
theorem observe_extend {scratch : ℕ} {R S P : Type} {input : List Bool}
    (world : World 4 S Unit P input) :
    observe (NativeSequential.right (First := R) (extendWorld scratch world)) =
      NativeRuntimeContext.observe world := by
  have hzero : (Fin.castAddEmb scratch) (0 : Fin 4) = 0 := by ext; simp
  have hone : (Fin.castAddEmb scratch) (1 : Fin 4) = 1 := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < 4 + scratch by omega)]
  simp only [observe, NativeSequential.right, Sequential.right, Cfg.mapState,
    extendWorld, Config.embed, ← hzero, ← hone, embed_workTapes_embed,
    embed_workTapePos_embed, NativeRuntimeContext.observe]
  rfl

/-- The concrete carrier's retained-context entry is exactly its canonical loaded storage. -/
theorem loaded_runtime (input context : List Bool) {P : Type}
    (memory : Memory Unit P) :
    loadedStart NativeRuntimeContext.restoringProgram input context memory =
      NativeRuntimeContext.restoringEntry input context memory := by
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 _ Unit P input))
  apply Config.ext
  · exact (NativeRuntimeContext.restoringEntry_tapes input context memory).symm
  · rfl

/-- One native machine loads its runtime context from the original input before
executing both actual queries and inner cleanup. The machine works for every
original input, oracle/private state and finite response length. -/
theorem exists_loaded_runtime {A : Type} (encoding : A ↪ List Bool) (context : A → List Bool)
    (hcontext : ComputableInPolyTime context encoding encBits) :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (machine : MultiTapePTM (4 + scratch) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (a : A) (memory : Memory Unit P),
      (NativeUnboundedExecution.terminal machine env
        ⟨machine.initialConfig (encoding a), memory⟩).map (Option.map observe) =
        (env ((), encoding a) memory).bind fun (first, next) =>
          let recorded := memory.record ((), encoding a) first next
          (env ((), context a ++ frame first.word) recorded).map fun (second, last) =>
            some (⟨(context a ++ frame first.word) ++ second.word,
              tapeOfList (context a ++ frame first.word), 0, fun _ => none,
              recorded.record ((), context a ++ frame first.word) second last⟩ :
                NativeRuntimeContext.Observation P) := by
  obtain ⟨scratch, R, hR, loader, hl⟩ := exists_load_then encoding context hcontext
  let consumer := NativeRuntimeContext.restoringProgram
  let machine := (MultiTapePTM.ofDeterministic loader).seq
    (consumer.extendTapes (Fin.castAddEmb scratch))
  refine ⟨scratch, _, inferInstance, machine, ?_⟩
  intro P env a memory
  rw [hl, PMF.map_comp, loaded_runtime]
  let C := NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕
    (NativeRuntimeContext.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ NativeQueryAll.Control) ⊕
      RewindState ⊕ MarkWorkState
  have he : (Option.map observe ∘
      Option.map (fun final => NativeSequential.right (First := R)
        (extendWorld scratch final))) =
      Option.map (NativeRuntimeContext.observe (S := C) (P := P) (input := encoding a)) := by
    funext value
    cases value with
    | none => rfl
    | some world => exact congrArg some (observe_extend world)
  rw [he, NativeRuntimeContext.restoring_program_observation]

end Cslib.Probability.NativeContextLoader
