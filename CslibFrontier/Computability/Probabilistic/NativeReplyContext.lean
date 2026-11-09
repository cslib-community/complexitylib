/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeRuntimeContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Native preparation of runtime context and the actual reply

The ordinary runtime context is combined with the complete reply, without emitting
those private bytes. Native instructions erase the old context and restore both
cursors. The result is a canonical input word for a uniform local processor.
This is response-dependent local computation, not a fixed-clock full-reply compiler.
No source batch-admission or complete adaptive selector claim is made here.

## Main definitions

* `splice`: native context/reply assembly with erasure and restored cursors.
* `Observation`, `observe`: named actual storage/output/oracle-memory readback.

## Main results

* `exists_processor`: one uniform local native context-to-context processor.
* `terminal_loaded`: actual blank-tape loader/full-reader/continuation whole-state law.
* `exists_query_processor`: actual blank-tape loading/query/reader/processor joint law.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeReplyContext
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- Copy the retained context and framed reply to a reserved tape, erase the old
context and restore the immutable reply cursor. All output is redirected to storage. -/
def splice := (NativeRuntimeContext.update.outputToWord.seq
    ((rewindWork Bool (some none)).extendTapes (tapeEmb (0 : Fin 3)))).seq
      ((rewindInput Bool).extendTapes (noTapes 3))

private theorem lastCases_three {A : Type} (a b c : A) :
    Fin.lastCases c ![a, b] = ![a, b, c] := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [Fin.lastCases_last]; rfl
  | cast i => rw [Fin.lastCases_castSucc]; fin_cases i <;> rfl

private def entry {input : List Bool} (context : List Bool) :
    Cfg 3 Bool NativeRuntimeContext.Control input :=
  outCfg (NativeRuntimeContext.updateConfig (some .scan) 0 (by omega) context 0 [])

private def afterCopy (input context : List Bool) :
    Cfg 3 Bool RewindWorkState input :=
  ⟨none, ⟨input.length + 1, by omega⟩,
    ![tapeOfList (context ++ frame input), fun _ => none, tapeOfList (context ++ frame input)],
    ![((context ++ frame input).length : ℤ), 0, 0], []⟩

private theorem copy_run (input context : List Bool) :
    NativeRuntimeContext.update.outputToWord.runFrom
      (Sequential.leftCfg
        ((rewindWork Bool).extendTapes (tapeEmb (Fin.last 2)))
        (entry (input := input) context))
        (context.length + 2 * input.length + 2 + ((context ++ frame input).length + 2)) =
      Sequential.rightCfg (afterCopy input context) := by
  have hu : NativeRuntimeContext.update.outputToTape.runFrom
      (entry (input := input) context) (context.length + 2 * input.length + 2) =
      outCfg (NativeRuntimeContext.updateConfig (input := input) none input.length le_rfl
        (context ++ frame input) (context ++ frame input).length
        (context ++ frame input)) := by
    have hs := (step_outCfg NativeRuntimeContext.update).iterate_right
      (context.length + 2 * input.length + 2)
      (NativeRuntimeContext.updateConfig (input := input) (some .scan) 0 (by omega) context 0 [])
    change outCfg (NativeRuntimeContext.update.runFrom _ _) =
      NativeRuntimeContext.update.outputToTape.runFrom _ _ at hs
    rw [NativeRuntimeContext.update_run] at hs
    exact hs.symm
  unfold MultiTapeTM.outputToWord
  apply runFrom_seq hu rfl _ rfl
  rw [runFrom_tapeEmb]
  change embed (input := input) (tapeEmb (Fin.last 2))
    ((rewindWork Bool).runFrom
      ⟨some (rewindWork Bool).q₀, ⟨input.length + 1, by omega⟩,
        fun _ => tapeOfList (context ++ frame input),
        fun _ => ((context ++ frame input).length : ℤ), []⟩ _)
    _ _ = _
  rw [runFrom_rewindWork_none (w := context ++ frame input) _ _ _ rfl le_rfl]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; fin_cases i <;>
      simp [afterCopy, embed_tapeEmb, outCfg, NativeRuntimeContext.updateConfig,
        Cfg.withState, lastCases_three]
  · funext i; fin_cases i <;>
      simp [afterCopy, embed_tapeEmb, outCfg, NativeRuntimeContext.updateConfig,
        Cfg.withState, lastCases_three]

private def erased (input context : List Bool) : Cfg 3 Bool RewindWorkState input :=
  ⟨none, ⟨input.length + 1, by omega⟩,
    ![fun _ => none, fun _ => none, tapeOfList (context ++ frame input)], fun _ => 0, []⟩

private theorem erase_run (input context : List Bool) :
    ((rewindWork Bool (some none)).extendTapes (tapeEmb (0 : Fin 3))).runFrom
      ((afterCopy input context).withState (some (rewindWork Bool (some none)).q₀))
        ((context ++ frame input).length + 2) = erased input context := by
  rw [runFrom_tapeEmb]
  have hc : oneTapeCfg (0 : Fin 3)
      ((afterCopy input context).withState (some (rewindWork Bool (some none)).q₀)) =
      (⟨some (rewindWork Bool (some none)).q₀, ⟨input.length + 1, by omega⟩,
        fun _ => tapeOfList (context ++ frame input),
        fun _ => ((context ++ frame input).length : ℤ), []⟩ :
          Cfg 1 Bool RewindWorkState input) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; fin_cases i; simp [oneTapeCfg, afterCopy, Cfg.withState]
    · funext i; fin_cases i; simp [oneTapeCfg, afterCopy, Cfg.withState]
  rw [hc]
  rw [runFrom_rewindWork_erase (w := context ++ frame input) _ _ _ rfl]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; fin_cases i <;> simp [erased, afterCopy, embed_tapeEmb, Cfg.withState]
  · funext i; fin_cases i <;> simp [erased, afterCopy, embed_tapeEmb, Cfg.withState]

/-- The actual splice terminates with only tape two occupied, old context erased,
no output, and all heads restored. Its clock depends on the complete received word. -/
theorem splice_run (input context : List Bool) :
    splice.runFrom
      (wordsCfg input (some splice.q₀) ![context, [], []] [])
      (context.length + 2 * input.length + 2 + (context ++ frame input).length + 2 +
        ((context ++ frame input).length + 2) + (input.length + 2)) =
      wordsCfg input none ![[], [], context ++ frame input] [] := by
  have hcopy := copy_run input context
  have herase := erase_run input context
  have hfirst := runFrom_seq
    (tm₁ := (rewindWork Bool (some none)).extendTapes (tapeEmb (0 : Fin 3)))
    hcopy rfl
    (by simpa [Sequential.rightCfg, Cfg.mapState, afterCopy, Cfg.withState] using herase) rfl
  have hrewind : ((rewindInput Bool).extendTapes
      (noTapes 3)).runFrom
        ((erased input context).withState (some (rewindInput Bool).q₀))
        (input.length + 2) =
      wordsCfg input none ![[], [], context ++ frame input] [] := by
    rw [runFrom_noTapes]
    let cfg := (erased input context).withState (some (rewindInput Bool).q₀)
    have he := runFrom_rewindInput (Symbol := Bool) (input := input)
      cfg.inputPos (noTapesCfg cfg).workTapes (noTapesCfg cfg).workTapePos cfg.output
    have hc : noTapesCfg cfg =
        (⟨some (rewindInput Bool).q₀, cfg.inputPos,
          (noTapesCfg cfg).workTapes, (noTapesCfg cfg).workTapePos, cfg.output⟩ :
            Cfg 0 Bool RewindState input) := by
      apply Cfg.ext <;> rfl
    have ht : cfg.inputPos.val - 1 + 2 = input.length + 2 := by simp [cfg, erased]
    rw [ht] at he
    change _ = _ at he
    rw [hc, he]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i; fin_cases i <;> simp [wordsCfg, erased, Cfg.withState]
  have hlast := runFrom_seq
    (tm₁ := (rewindInput Bool).extendTapes (noTapes 3))
    hfirst rfl
    (by simpa [Sequential.rightCfg, Cfg.mapState, erased, Cfg.withState] using hrewind) rfl
  convert hlast using 1
  · congr 1
    · apply Cfg.ext
      · simp [splice, Sequential.leftCfg, Cfg.mapState, wordsCfg, entry,
          MultiTapeTM.outputToWord, NativeRuntimeContext.update, MultiTapeTM.seq,
          MultiTapeTM.outputToTape, outCfg,
          NativeRuntimeContext.updateConfig]
      · rfl
      · funext i; fin_cases i <;> simp [Sequential.leftCfg, Cfg.mapState, entry, outCfg, wordsCfg,
          NativeRuntimeContext.updateConfig, lastCases_three]
      · funext i; fin_cases i <;> simp [Sequential.leftCfg, Cfg.mapState, entry, outCfg, wordsCfg,
          NativeRuntimeContext.updateConfig, lastCases_three]
      · rfl
    · simp; omega
  · rfl

/-- The raw reply component is framed, so the native splice is exactly a pair ABI. -/
@[expose] def framedBits : List Bool ↪ List Bool := ⟨frame, frame_injective⟩

private def spliceTime (reply context : List Bool) : ℕ :=
  context.length + 2 * reply.length + 2 + (context ++ frame reply).length + 2 +
    ((context ++ frame reply).length + 2) + (reply.length + 2)

private theorem splice_spec (reply context : List Bool) :
    TransformsTapes splice
      (fun input ws => input = reply ∧ ws = Function.update (fun _ => []) 0 context)
      (fun _ _ ws' emitted =>
        ws' = Function.update (fun _ => []) 2 (context ++ frame reply) ∧ emitted = [])
      (spliceTime reply context) (3 * (spliceTime reply context + 1)) := by
  rw [transformsTapes_iff_nil_output]
  rintro input ws ⟨hi, hw⟩
  subst input
  subst ws
  let p := MultiTapeNTM.RunPath.ofDeterministic splice
    (wordsCfg reply (some splice.q₀) (Function.update (fun _ => []) 0 context) [])
    (spliceTime reply context)
  refine ⟨_, [], ⟨rfl, rfl⟩, p, rfl, ?_, le_rfl, p.space_le_mul_time_add_one⟩
  change splice.runFrom _ _ = _
  have hin : Function.update (fun _ : Fin 3 => []) 0 context = ![context, [], []] := by
    funext i; fin_cases i <;> simp
  have hout : Function.update (fun _ : Fin 3 => []) 2 (context ++ frame reply) =
      ![[], [], context ++ frame reply] := by
    funext i; fin_cases i <;> simp
  rw [hin, hout]
  exact splice_run reply context

private theorem splice_extend (k : ℕ) (reply context : List Bool) :
    TransformsTapes (splice.extendTapes (Fin.castAddEmb k))
      (fun input ws => input = reply ∧ ws = Function.update (fun _ => []) 0 context)
      (fun _ _ ws' emitted =>
        ws' = Function.update (fun _ => []) 2 (context ++ frame reply) ∧ emitted = [])
      (spliceTime reply context) (3 * (spliceTime reply context + 1) + ((3 + k) - 3)) := by
  refine ((splice_spec reply context).extendTapes (Fin.castAddEmb k)).imp
    (fun _ ws h => ⟨h.1, ?_⟩) (fun _ ws ws' emitted h h' => ?_) le_rfl le_rfl
  · rw [h.2]
    have hz : Fin.castAddEmb k (0 : Fin 3) = 0 := Fin.ext rfl
    funext j
    by_cases hj : j = 0
    · subst j; rw [hz, Function.update_self, Function.update_self]
    · change Function.update (fun _ => []) 0 context (Fin.castAddEmb k j) = _
      rw [Function.update_of_ne (show Fin.castAddEmb k j ≠ 0 from
        fun he => hj ((Fin.castAddEmb k).injective (he.trans hz.symm))),
        Function.update_of_ne hj]
  · obtain ⟨⟨hv, he⟩, hx⟩ := h'
    refine ⟨funext fun i => ?_, he⟩
    by_cases hi : i.val < 3
    · let j : Fin 3 := ⟨i.val, hi⟩
      have hj : Fin.castAddEmb k j = i := Fin.ext rfl
      have hh := congrFun hv j
      rw [hj] at hh
      simpa [Function.update_apply, Fin.ext_iff, j, Fin.val_ofNat,
        Nat.mod_eq_of_lt (show 2 < 3 + k by omega)] using hh
    · rw [hx i (by rintro ⟨j, rfl⟩; exact hi j.isLt), h.2]
      have hn0 : i ≠ 0 := by intro he; subst i; simp at hi
      have hn2 : i ≠ 2 := by
        intro he
        have hv := congrArg Fin.val he
        change i.val = 2 % (3 + k) at hv
        have hm : 2 % (3 + k) = 2 := Nat.mod_eq_of_lt (by omega)
        omega
      simp [hn0, hn2]


private def processorTapes (k : ℕ) : Fin (k + 1 + 2) ↪ Fin (3 + k) :=
  ⟨fun i => ⟨if i.val < k then 3 + i.val
    else if i.val = k then 0 else if i.val = k + 1 then 2 else 1, by
      split_ifs <;> omega⟩, by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega⟩

private theorem processor_input (k : ℕ) :
    processorTapes k (Fin.natAdd (k + 1) 0) = 2 := by
  apply Fin.ext
  change (if k + 1 < k then 3 + (k + 1) else
    if k + 1 = k then 0 else if k + 1 = k + 1 then 2 else 1) = 2 % (3 + k)
  simp [Nat.mod_eq_of_lt (show 2 < 3 + k by omega)]

private theorem processor_output (k : ℕ) :
    processorTapes k ((Fin.last k).castAdd 2) = 0 := by
  apply Fin.ext
  change (if k < k then 3 + k else if k = k then 0 else
    if k = k + 1 then 2 else 1) = 0
  simp

/-- Construct one native local program for all runtime contexts and complete replies.
It splices the actual reply, runs the supplied pure algorithm, writes its result
back to tape zero, and clears the consumed input/flag/scratch tapes. The premise
concerns only the pure algorithm; no native realization or stopping law is supplied. -/
theorem exists_processor {A : Type} (encoding : A ↪ List Bool)
    (process : A × List Bool → List Bool)
    (hprocess : ComputableInPolyTime process (encPair encoding framedBits) encBits) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (code : MultiTapeTM (3 + k) Bool S),
      ∀ (a : A) (reply : List Bool), ∃ time space : ℕ,
        TransformsTapes code
          (fun input ws => input = reply ∧
            ws = Function.update (fun _ => []) 0 (frame (encoding a)))
          (fun _ _ ws' emitted =>
            ws' = Function.update (fun _ => []) 0 (process (a, reply)) ∧ emitted = [])
          time space := by
  obtain ⟨t, s, _, _, hc⟩ := hprocess
  obtain ⟨_, ht⟩ := hc.exists_computableTidilyInTimeAndSpace
  obtain ⟨k, S, hS, code, hcode⟩ := ht
  let localCode := (splice.extendTapes (Fin.castAddEmb k)).seq
    (((code.onWords true).extendTapes (processorTapes k)).seq
      ((clearWork Bool).extendTapes (tapeEmb (2 : Fin (3 + k)))))
  refine ⟨k, _, inferInstance, localCode, ?_⟩
  intro a reply
  have hinput : encPair encoding framedBits (a, reply) =
      frame (encoding a) ++ frame reply := rfl
  have hp := (hcode (a, reply)).onWords_extendTapes true
    (processor_input k) (processor_output k)
  rw [hinput, encBits_apply] at hp
  have hne : (0 : Fin (3 + k)) ≠ 2 := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = 2 % (3 + k) at hv
    have hm : 2 % (3 + k) = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hclear := (transformsTapes_clearWork_tapeEmb (2 : Fin (3 + k))
    (frame (encoding a) ++ frame reply))
  have hc' : TransformsTapes
      ((clearWork Bool).extendTapes (tapeEmb (2 : Fin (3 + k))))
      (fun _ ws => ws = Function.update
        (Function.update (fun _ => []) 2 (frame (encoding a) ++ frame reply))
        0 (process (a, reply)))
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) 0 (process (a, reply)) ∧ em = [])
      _ _ := hclear.imp (fun _ ws h => by simp [h, hne.symm]) (fun _ ws ws' em h hh => by
        rw [hh.1, h]
        refine ⟨?_, hh.2⟩
        funext i
        by_cases hi : i = 0 <;> by_cases hj : i = 2 <;> simp_all) le_rfl le_rfl
  have hp' := hp.imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) 2
      (frame (encoding a) ++ frame reply))
    (Q' := fun _ _ ws' em => ws' = Function.update
      (Function.update (fun _ => []) 2 (frame (encoding a) ++ frame reply))
      0 (process (a, reply)) ∧ em = [])
    (fun _ ws h => h)
    (fun _ ws ws' em h hh => ⟨by rw [hh.1, h], hh.2⟩) le_rfl le_rfl
  have hpost := hp'.seq_eq hc'
  have hfull := (splice_extend k reply (frame (encoding a))).seq_eq hpost
  exact ⟨_, _, by simpa only [List.append_nil, List.nil_append] using hfull⟩

/-- Named observations of the updated native storage and the same oracle ledger. -/
structure Observation (P : Type) where
  /-- Actual two-sided reserved context tape after local processing. -/
  contextTape : ℤ → Option Bool
  /-- Ordinary native output, separate from private context bytes. -/
  output : List Bool
  /-- Joint hidden state and complete query/resource history. -/
  memory : Memory Unit P

/-- Read a selected native runtime tape, ordinary output and shared oracle memory. -/
@[expose] def observe {k : ℕ} {S P : Type} {input : List Bool}
    (context : Fin k) (world : World k S Unit P input) : Observation P :=
  ⟨world.config.tapes.workTapes context, world.config.tapes.output, world.memory⟩

/-- Actual readback ignores only control relabeling, not storage or oracle memory. -/
theorem observe_mapControl {k : ℕ} {S T P : Type} {input : List Bool}
    (i : Fin k) (f : S → T) (world : World k S Unit P input) :
    observe i (NativeSequential.mapControl f world) = observe i world := rfl

/-- Readback at an embedded context tape preserves its exact contents and ledger. -/
theorem observe_embedStorage {k width : ℕ} {S P : Type} {input : List Bool}
    (i : Fin k) (e : Fin k ↪ Fin width) (world : World k S Unit P input) :
    observe (e i) (NativeSequential.embedStorage e world) = observe i world := by
  simp [observe, NativeSequential.embedStorage, Config.embed, MultiTapeTM.embed]

/-- Virtual-input redirection leaves ordinary context/output/ledger observations unchanged. -/
theorem observe_inputWorld {k : ℕ} {S P : Type} {word : List Bool}
    (i : Fin k) (world : World k S Unit P word) (input : List Bool)
    (position : Fin (input.length + 2)) :
    observe (i.castAdd 2) (NativeResponseExecution.inputWorld world input position) =
      observe i world := by
  simp [observe, NativeResponseExecution.inputWorld, InputFromTape.config, inCfg]

/-- Canonical ordinary word storage with explicit native channels and oracle memory. -/
@[expose] def wordWorld {k : ℕ} {S P : Type} (input : List Bool)
    (state : Option S) (words : Fin k → List Bool) (channels : Unit → Channel Bool)
    (memory : Memory Unit P) : World k S Unit P input :=
  ⟨⟨wordsCfg input state words [], channels⟩, memory⟩

/-- Canonical context storage embeds exactly when its reserved zero tape is preserved. -/
theorem wordWorld_embed_zero {k width : ℕ} [NeZero k] [NeZero width] {S P : Type}
    (e : Fin k ↪ Fin width) (he : e 0 = 0) (input word : List Bool)
    (state : Option S) (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    NativeSequential.embedStorage e
      (wordWorld input state (Function.update (fun _ => []) 0 word) channels memory) =
      wordWorld input state (Function.update (fun _ => []) 0 word) channels memory := by
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World width S Unit P input))
  apply Config.ext
  · change MultiTapeTM.embed e
      (wordsCfg input state (Function.update (fun _ => []) 0 word) [])
      (fun _ _ => none) (fun _ => 0) = _
    have hz : (fun _ : Fin width => fun _ : ℤ => (none : Option Bool)) =
        (fun _ => tapeOfList ([] : List Bool)) := by simp
    rw [hz]
    apply embed_wordsCfg
    · intro j
      by_cases hj : j = 0
      · subst j; simp [he]
      · have hn : e j ≠ 0 := fun h => hj (e.injective (h.trans he.symm))
        simp [hj, hn]
    · intro j hj
      have hn : j ≠ 0 := fun h => hj ⟨0, he.trans h.symm⟩
      simp [hn]
  · rfl

/-- A proved deterministic tape transformation has its actual native terminal law. -/
theorem terminal_transform {k : ℕ} {S P : Type}
    (code : MultiTapeTM k Bool S) (env : Environment Unit P)
    (input : List Bool) (words result : Fin k → List Bool)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) (time space : ℕ)
    (h : TransformsTapes code
      (fun inp ws => inp = input ∧ ws = words)
      (fun _ _ ws' emitted => ws' = result ∧ emitted = []) time space) :
    NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic code) env
      (wordWorld input (some code.q₀) words channels memory) =
      PMF.pure (some (wordWorld input (S := S) none result channels memory)) := by
  obtain ⟨ws, emitted, hr, ⟨hw, hem⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp h input words [] ⟨rfl, rfl⟩
  subst ws
  subst emitted
  apply NativeResponseExecution.terminal_of_clock _ env _
    (wordWorld input (S := S) none result channels memory) time ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic code).runOracleConfigFrom time
      (wordWorld input (some code.q₀) words channels memory).config)).run memory).map _ = _
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  change PMF.pure (⟨⟨code.runFrom (wordsCfg input (some code.q₀) words []) time,
    channels⟩, memory⟩ : World k S Unit P input) = _
  rw [hr]
  rfl

/-- Actual blank-tape loading before the full reader and a native continuation. -/
def loadedMachine {width : ℕ} {S : Type}
    (continuation : MultiTapePTM width Bool S Unit) :=
  (MultiTapePTM.ofDeterministic (loadWord Bool (0 : Fin (width + 2)))).seq
    (NativeResponseExecution.machine continuation)

/-- The actual loader/full-reader compiler preserves the continuation's entire
unbounded law. Its retained context is the query word, not a supplied realization. -/
theorem terminal_loaded {width : ℕ} [NeZero width] {S P : Type}
    (continuation : MultiTapePTM width Bool S Unit) (env : Environment Unit P)
    (input : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (loadedMachine continuation) env
      ⟨(loadedMachine continuation).initialConfig input, memory⟩ =
      (env ((), input) memory).bind fun (reply, next) =>
        (NativeUnboundedExecution.terminal continuation env
          (NativeResponseExecution.localStartFrom continuation input memory reply next
            (NativeResponseExecution.Workspace.words
              (Function.update (fun _ => []) 0 input)))).map
          (Option.map fun final => NativeSequential.right
            (First := (Unit ⊕ RewindState) ⊕ RewindWorkState)
            (NativeResponseExecution.resultWorld input final)) := by
  have hwidth : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  let reader := NativeResponseExecution.machine continuation
  let loader := loadWord Bool (0 : Fin (width + 2))
  let program := (MultiTapePTM.ofDeterministic loader).seq reader
  let words : Fin (width + 2) → List Bool := Function.update (fun _ => []) 0 input
  have hload := transformsTapes_loadWord (0 : Fin (width + 2)) input
  have hload' := hload.imp
    (P' := fun inp ws => inp = input ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' emitted => ws' = words ∧ emitted = [])
    (fun _ _ h => ⟨h.1, by rw [h.2]⟩)
    (fun _ ws ws' emitted h hh => ⟨by rw [hh.1, h.2], hh.2⟩) le_rfl le_rfl
  have ht := terminal_transform loader env input (fun _ => []) words
    (fun _ => ⟨[], [], 0⟩) memory _ _ hload'
  have hi : (⟨program.initialConfig input, memory⟩ : World _ _ Unit P input) =
      NativeSequential.left reader
        (wordWorld input (some loader.q₀) (fun _ => []) (fun _ => ⟨[], [], 0⟩) memory) := by
    apply congrArg (fun cfg => (⟨cfg, memory⟩ : World _ _ Unit P input))
    apply Config.ext
    · apply Cfg.ext
      · rfl
      · rfl
      · funext i; simp [MultiTapeMachine.initialConfig, Cfg.init, wordWorld,
                  Sequential.left, Cfg.mapState, wordsCfg]
      · rfl
      · rfl
    · rfl
  change NativeUnboundedExecution.terminal program env ⟨program.initialConfig input, memory⟩ = _
  rw [hi, NativeSequential.terminal_seq, ht, PMF.pure_bind]
  dsimp only
  have he : NativeSequential.resume reader
      (wordWorld input (S := (Unit ⊕ RewindState) ⊕ RewindWorkState)
        none words (fun _ => ⟨[], [], 0⟩) memory) =
      NativeResponseExecution.startFrom continuation input memory
        (NativeResponseExecution.Workspace.words
          (Function.update (fun _ => []) 0 input)) := by
    apply congrArg (fun cfg => (⟨cfg, memory⟩ : World _ _ Unit P input))
    apply Config.ext
    · apply Cfg.ext
      · rfl
      · rfl
      · simp only [Sequential.start, wordWorld,
          NativeResponseExecution.Workspace.words, wordsCfg, Cfg.withState]
        funext i
        cases i using Fin.addCases with
        | left j =>
          rw [Fin.append_left]
          by_cases hj : j = 0
          · subst j
            have hz : (0 : Fin width).castAdd 2 = 0 := Fin.ext rfl
            simp [words, hz]
          · have hn : j.castAdd 2 ≠ (0 : Fin (width + 2)) := by
              intro h; apply hj
              exact Fin.ext (congrArg (fun i : Fin (width + 2) => i.val) h)
            simp only [words, Function.update_of_ne hn, Function.update_of_ne hj]
        | right j =>
          rw [Fin.append_right]
          have hn : Fin.natAdd width j ≠ 0 := by
            intro h
            have hv := congrArg Fin.val h
            change width + j.val = 0 at hv
            omega
          simp only [words, Function.update_of_ne hn]
          fin_cases j <;> simp
      · simp only [Sequential.start, wordWorld,
          NativeResponseExecution.Workspace.words, wordsCfg, Cfg.withState]
        funext i
        cases i using Fin.addCases with
        | left j => rw [Fin.append_left]
        | right j => rw [Fin.append_right]; fin_cases j <;> rfl
      · rfl
    · rfl
  rw [he, NativeResponseExecution.terminal_from, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro pair _
  rw [PMF.map_comp]
  congr 1
  funext result
  cases result <;> rfl

/-- Blank-tape native execution loads its original context, issues the query, reads
its entire reply and executes the same uniform postprocessor. The actual updated
context, output and joint resource-bearing oracle memory have the displayed law.
This is one phase, not a guarded repeated selector or a source batch codec. -/
theorem exists_query_processor {A : Type} (encoding : A ↪ List Bool)
    (process : A × List Bool → List Bool)
    (hprocess : ComputableInPolyTime process (encPair encoding framedBits) encBits) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (program : MultiTapePTM ((3 + k) + 2) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (a : A) (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (frame (encoding a)), memory⟩).map
          (Option.map (observe 0)) =
          (env ((), frame (encoding a)) memory).map fun (reply, next) =>
            some (⟨tapeOfList (process (a, reply.word)), [],
              memory.record ((), frame (encoding a)) reply next⟩ : Observation P) := by
  obtain ⟨k, S, hS, localCode, hl⟩ := exists_processor encoding process hprocess
  let localProgram := MultiTapePTM.ofDeterministic (Oracle := Unit) localCode
  let program := loadedMachine localProgram
  refine ⟨k, _, inferInstance, program, ?_⟩
  intro P env a memory
  let input := frame (encoding a)
  rw [terminal_loaded, PMF.map_bind]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨reply, next⟩ := pair
  obtain ⟨time, space, hs⟩ := hl a reply.word
  have hp := terminal_transform localCode env reply.word
    (Function.update (fun _ => []) 0 input)
    (Function.update (fun _ => []) 0 (process (a, reply.word)))
    ((NativeQueryAll.finish (k := 3 + k) () input memory reply next).config.channels)
    (memory.record ((), input) reply next) time space hs
  have hc : NativeResponseExecution.localStartFrom localProgram input memory reply next
      (NativeResponseExecution.Workspace.words (Function.update (fun _ => []) 0 input)) =
      wordWorld reply.word (some localCode.q₀) (Function.update (fun _ => []) 0 input)
        ((NativeQueryAll.finish (k := 3 + k) () input memory reply next).config.channels)
        (memory.record ((), input) reply next) := by
    apply congrArg (fun cfg => (⟨cfg, memory.record ((), input) reply next⟩ :
      World _ _ Unit P reply.word))
    apply Config.ext
    · apply Cfg.ext rfl rfl rfl rfl rfl
    · rfl
  change ((NativeUnboundedExecution.terminal localProgram env _).map _).map _ = _
  rw [hc, hp, PMF.pure_map, PMF.pure_map]
  simp [NativeSequential.right, Sequential.right, Cfg.mapState,
    NativeResponseExecution.resultWorld,
    InputFromTape.config, inCfg, wordWorld, wordsCfg, Fin.append, Fin.addCases,
    Fin.castLT, input, observe]


end Cslib.Probability.NativeReplyContext
