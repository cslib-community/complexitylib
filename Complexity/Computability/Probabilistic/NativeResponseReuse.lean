/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeReplyContext
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Exact cleanup after clockless native response execution

The actual buffered reply and its negative-cell boundary marker are erased by
native instructions. Ordinary words, live channels and the full oracle ledger
survive; all work heads and the real input cursor are restored. The clock depends
on the complete received word. No uniform reply clock or supplied restart law is used.

## Main definitions

* `cleanup`, `ready`: actual erasure/restoration code and its canonical whole-world result.
* `phase`, `entry`: one reusable actual query/processor/cleanup phase with live channels.

## Main results

* `terminal_cleanup`: full-configuration cleanup of an actual virtual-input result.
* `terminal_phase`: actual query/processor execution returns the complete ready invariant.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeResponseReuse
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- Restore the real input cursor, then erase the marker left of the flag head. -/
def restore (k : ℕ) :=
  ((rewindInput Bool).extendTapes (noTapes (k + 2))).seq
    ((markWork Bool none).extendTapes (tapeEmb (Fin.natAdd k (1 : Fin 2))))

/-- Restore cursors/marker and actually clear the complete reply buffer. -/
def cleanup (k : ℕ) := (MultiTapePTM.ofDeterministic (Oracle := Unit) (restore k)).seq
  (MultiTapePTM.ofDeterministic
    ((clearWork Bool).extendTapes (tapeEmb (Fin.natAdd k (0 : Fin 2)))))

/-- All ordinary runtime words survive; both reserved buffers are blank and all
heads, including the immutable original-input cursor, are in canonical position. -/
@[expose] def ready {k : ℕ} {S P : Type} (input : List Bool) (state : Option S)
    (words : Fin k → List Bool) (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    World (k + 2) S Unit P input :=
  NativeReplyContext.wordWorld input state (Fin.append words ![[], []]) channels memory

private def marked {k : ℕ} {S : Type} (input reply : List Bool)
    (position : Fin (input.length + 2)) (state : Option S) (words : Fin k → List Bool) :
    Cfg (k + 2) Bool S input :=
  ⟨state, position, Fin.append (fun i => tapeOfList (words i))
    ![tapeOfList reply, Function.update (fun _ => none) (-1) (some true)], fun _ => 0, []⟩

private def withReply {k : ℕ} {S : Type} (input reply : List Bool) (state : Option S)
    (words : Fin k → List Bool) : Cfg (k + 2) Bool S input :=
  wordsCfg input state (Fin.append words ![reply, []]) []

private theorem restore_run {k : ℕ} (input reply : List Bool)
    (position : Fin (input.length + 2)) (words : Fin k → List Bool) :
    (restore k).runFrom (marked input reply position (some (restore k).q₀) words)
      (position.val - 1 + 2 + 2) = withReply input reply none words := by
  let rewind := (rewindInput Bool).extendTapes (noTapes (k + 2))
  let marker := (markWork Bool none).extendTapes (tapeEmb (Fin.natAdd k (1 : Fin 2)))
  have hr : rewind.runFrom
      (marked input reply position (some rewind.q₀) words) (position.val - 1 + 2) =
      marked input reply 1 none words := by
    rw [runFrom_noTapes]
    change embed (noTapes (k + 2))
      ((rewindInput Bool).runFrom _ _) _ _ = _
    simp only [noTapesCfg, marked, rewind, extendTapes_q₀]
    rw [runFrom_rewindInput]
    rfl
  have hm : marker.runFrom
      (marked input reply 1 (some marker.q₀) words) 2 = withReply input reply none words := by
    simp only [marker, runFrom_tapeEmb, oneTapeCfg, marked, runFrom_markWork,
      extendTapes_q₀]
    simp only [Fin.append_right, Matrix.cons_val_one, Matrix.cons_val_zero,
      zero_sub]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      cases i using Fin.addCases with
      | left j => simp [embed_tapeEmb, withReply, wordsCfg, Fin.castAdd_ne_natAdd]
      | right j => fin_cases j <;> simp [embed_tapeEmb, withReply, wordsCfg]
    · funext i
      cases i using Fin.addCases with
      | left j => simp [embed_tapeEmb, withReply, wordsCfg]
      | right j => fin_cases j <;> simp [embed_tapeEmb, withReply, wordsCfg]
    · rfl
  have hs := runFrom_seq hr rfl hm rfl
  exact hs

private theorem restore_terminal {k : ℕ} {T P : Type} (env : Environment Unit P)
    (input reply : List Bool) (position : Fin (input.length + 2)) (words : Fin k → List Bool)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic (restore k)) env
      (NativeSequential.resume
      (MultiTapePTM.ofDeterministic (Oracle := Unit) (restore k))
        (NativeResponseExecution.inputWorld
          (NativeReplyContext.wordWorld
            reply (S := T) none words channels memory) input position)) =
      PMF.pure (some (NativeReplyContext.wordWorld input
        (S := RewindState ⊕ MarkWorkState) none
        (Fin.append words ![reply, []]) channels memory)) := by
  let code := MultiTapePTM.ofDeterministic (Oracle := Unit) (restore k)
  have hi : (NativeSequential.resume code
      (NativeResponseExecution.inputWorld
        (NativeReplyContext.wordWorld reply (S := T) none words channels memory) input position)) =
      (⟨⟨marked input reply position (some (restore k).q₀) words, channels⟩, memory⟩ :
        World (k + 2) _ Unit P input) := by
    apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (k + 2) _ Unit P input))
    apply Config.ext
    · apply Cfg.ext
      · rfl
      · rfl
      · rfl
      · funext i
        cases i using Fin.addCases with
        | left j => simp [Sequential.start,
            NativeResponseExecution.inputWorld, NativeReplyContext.wordWorld, wordsCfg,
            InputFromTape.config, inCfg, marked, Cfg.withState]
        | right j => fin_cases j <;> simp [Sequential.start,
            NativeResponseExecution.inputWorld, NativeReplyContext.wordWorld, wordsCfg,
            InputFromTape.config, inCfg, marked, Cfg.withState]
      · rfl
    · rfl
  rw [hi]
  apply NativeResponseExecution.terminal_of_clock _ env _
    (NativeReplyContext.wordWorld input (S := RewindState ⊕ MarkWorkState) none
      (Fin.append words ![reply, []]) channels memory)
    (position.val - 1 + 2 + 2) ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic (Oracle := Unit) (restore k)).runOracleConfigFrom
      (position.val - 1 + 2 + 2) ⟨marked input reply position (some (restore k).q₀) words,
        channels⟩)).run memory).map
      (fun pair => (⟨pair.1, pair.2⟩ : World (k + 2) _ Unit P input)) = _
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  have hr := restore_run input reply position words
  congr 1
  change (⟨⟨(restore k).runFrom _ _, channels⟩, memory⟩ : World _ _ Unit P input) = _
  rw [hr]
  rfl

/-- The actual cleanup accepts a genuine virtual-input continuation result. It
preserves every ordinary runtime word and live channel, erases both buffer and
negative-cell marker, and establishes the entire canonical next-entry configuration. -/
theorem terminal_cleanup {k : ℕ} {T P : Type} (env : Environment Unit P)
    (input reply : List Bool) (position : Fin (input.length + 2)) (words : Fin k → List Bool)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (cleanup k) env
      (NativeSequential.resume (cleanup k)
        (NativeResponseExecution.inputWorld
          (NativeReplyContext.wordWorld
            reply (S := T) none words channels memory) input position)) =
      PMF.pure (some (ready input (S := (RewindState ⊕ MarkWorkState) ⊕
        (Unit ⊕ RewindWorkState)) none words channels memory)) := by
  let clear := MultiTapePTM.ofDeterministic (Oracle := Unit)
    ((clearWork Bool).extendTapes (tapeEmb (Fin.natAdd k (0 : Fin 2))))
  have hi : NativeSequential.resume (cleanup k)
      (NativeResponseExecution.inputWorld
        (NativeReplyContext.wordWorld reply (S := T) none words channels memory) input position) =
      NativeSequential.left clear
        (NativeSequential.resume
          (MultiTapePTM.ofDeterministic (Oracle := Unit) (restore k))
          (NativeResponseExecution.inputWorld
            (NativeReplyContext.wordWorld
              reply (S := T) none words channels memory) input position)) :=
    rfl
  rw [hi, cleanup, NativeSequential.terminal_seq, restore_terminal, PMF.pure_bind]
  dsimp only
  have hc := (transformsTapes_clearWork_tapeEmb (Fin.natAdd k (0 : Fin 2)) reply).imp
    (P' := fun inp ws => inp = input ∧ ws = Fin.append words ![reply, []])
    (Q' := fun _ _ ws' emitted => ws' = Fin.append words ![[], []] ∧ emitted = [])
    (fun _ ws h => by rw [h.2]; simp)
    (fun _ ws ws' emitted h hh => by
      refine ⟨?_, hh.2⟩
      rw [hh.1, h.2]
      funext i
      cases i using Fin.addCases with
      | left j => simp [Fin.castAdd_ne_natAdd]
      | right j => fin_cases j <;> simp)
    le_rfl le_rfl
  have hp := NativeReplyContext.terminal_transform
    ((clearWork Bool).extendTapes (tapeEmb (Fin.natAdd k (0 : Fin 2)))) env input
    (Fin.append words ![reply, []]) (Fin.append words ![[], []]) channels memory _ _ hc
  simp only [extendTapes_q₀] at hp
  rw [show NativeSequential.resume clear
      (NativeReplyContext.wordWorld input (S := RewindState ⊕ MarkWorkState) none
        (Fin.append words ![reply, []]) channels memory) =
      NativeReplyContext.wordWorld input (some (clearWork Bool).q₀)
        (Fin.append words ![reply, []]) channels memory from rfl, hp, PMF.pure_map]
  rfl

/-- Native reader, local continuation and actual cleanup control. -/
abbrev PhaseControl (S : Type) :=
  (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ S) ⊕
    ((RewindState ⊕ MarkWorkState) ⊕ (Unit ⊕ RewindWorkState))

/-- One actual reader/update phase followed by full response-buffer/cursor cleanup. -/
def phase {k : ℕ} {S : Type} (code : MultiTapeTM k Bool S) :
    MultiTapePTM (k + 2) Bool (PhaseControl S) Unit :=
  (NativeResponseExecution.machine (MultiTapePTM.ofDeterministic code)).seq (cleanup k)

/-- Enter the same phase on retained runtime words and actual previous channels. -/
@[expose] def entry {k : ℕ} {S P : Type} (code : MultiTapeTM k Bool S)
    (request : List Bool) (words : Fin k → List Bool)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    World (k + 2) (PhaseControl S) Unit P request :=
  NativeSequential.left (cleanup k) (NativeResponseExecution.startWithChannels
    (MultiTapePTM.ofDeterministic code) request memory
      (NativeResponseExecution.Workspace.words words) channels)

/-- The same actual native phase accepts and returns fully specified runtime
storage. Local clocks may depend on the entire reply; previous answer channels,
hidden-state correlation and all accumulated bill/duration records are preserved.
The premise is a proved deterministic tape algorithm, not a native restart law. -/
theorem terminal_phase {k : ℕ} {S P : Type} (code : MultiTapeTM k Bool S)
    (env : Environment Unit P) (request : List Bool) (words : Fin k → List Bool)
    (after : List Bool → Fin k → List Bool)
    (hcode : ∀ reply, ∃ time space, TransformsTapes code
      (fun input ws => input = reply ∧ ws = words)
      (fun _ _ ws' emitted => ws' = after reply ∧ emitted = []) time space)
    (channels : Unit → Channel Bool) (hb : (channels ()).queryBuffer = [])
    (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (phase code) env
      (entry code request words channels memory) =
      (env ((), request) memory).map fun (reply, next) =>
        some (ready request (S := PhaseControl S) none (after reply.word)
          (NativeQueryAll.finish (k := k) () request memory reply next).config.channels
          (memory.record ((), request) reply next)) := by
  rw [phase, entry, NativeSequential.terminal_seq,
    NativeResponseExecution.terminal_from_channels _ _ _ _ _ _ hb, PMF.bind_bind]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨reply, next⟩ := pair
  dsimp only
  rw [PMF.bind_map]
  let channels' := (NativeQueryAll.finish (k := k) () request memory reply next).config.channels
  let ledger := memory.record ((), request) reply next
  have hl : NativeResponseExecution.localStartFrom (MultiTapePTM.ofDeterministic code)
      request memory reply next (NativeResponseExecution.Workspace.words words) =
      NativeReplyContext.wordWorld reply.word (some code.q₀) words channels' ledger := by
    apply congrArg (fun cfg => (⟨cfg, ledger⟩ : World k S Unit P reply.word))
    apply Config.ext
    · apply Cfg.ext <;> rfl
    · rfl
  obtain ⟨time, space, hc⟩ := hcode reply.word
  have hp := NativeReplyContext.terminal_transform code env reply.word words
    (after reply.word) channels' ledger time space hc
  rw [hl, hp, PMF.pure_bind]
  simp only [Function.comp_apply, Option.map_some]
  have hr : NativeSequential.resume (cleanup k)
      (NativeResponseExecution.resultWorld request
        (NativeReplyContext.wordWorld reply.word (S := S) none
          (after reply.word) channels' ledger)) =
      NativeSequential.resume (cleanup k) (NativeResponseExecution.inputWorld
        (NativeReplyContext.wordWorld reply.word (S := S) none
          (after reply.word) channels' ledger) request ⟨request.length + 1, by omega⟩) := rfl
  rw [hr, terminal_cleanup, PMF.pure_map]
  rfl

private theorem append_context {k : ℕ} [NeZero k] (word : List Bool) :
    Fin.append (Function.update (fun _ : Fin k => []) 0 word) ![[], []] =
      Function.update (fun _ : Fin (k + 2) => []) 0 word := by
  funext i
  cases i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    by_cases hj : j = 0
    · subst j
      have hz : (0 : Fin k).castAdd 2 = 0 := Fin.ext rfl
      simp [hz]
    · have hn : j.castAdd 2 ≠ 0 := by
        intro h
        apply hj
        exact Fin.ext (congrArg (fun i : Fin (k + 2) => i.val) h)
      simp [hj, hn]
  | right j =>
    rw [Fin.append_right]
    have hn : Fin.natAdd k j ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      have hk := Nat.pos_of_ne_zero (NeZero.ne k)
      change k + j.val = 0 at hv
      omega
    rw [Function.update_of_ne hn]
    fin_cases j <;> simp

/-- Canonical retained context is also a canonical reusable phase entry. -/
theorem entry_context {k : ℕ} [NeZero k] {S P : Type} (code : MultiTapeTM k Bool S)
    (request word : List Bool) (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    entry code request (Function.update (fun _ => []) 0 word) channels memory =
      NativeReplyContext.wordWorld request (some (phase code).initial)
        (Function.update (fun _ => []) 0 word) channels memory := by
  unfold entry NativeSequential.left NativeResponseExecution.startWithChannels
    NativeResponseExecution.startFrom
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (k + 2) _ Unit P request))
  apply Config.ext
  · apply Cfg.ext
    · rfl
    · rfl
    · have h := append_context (k := k) word
      have ht := congrArg (fun words => fun i => tapeOfList (words i)) h
      funext i
      have hi := congrFun ht i
      cases i using Fin.addCases with
      | left j => simpa [NativeReplyContext.wordWorld, wordsCfg, Sequential.left,
          Cfg.mapState, NativeResponseExecution.Workspace.words] using hi
      | right j => fin_cases j <;> simpa
          [NativeReplyContext.wordWorld, wordsCfg, Sequential.left, Cfg.mapState,
            NativeResponseExecution.Workspace.words] using hi
    · funext i
      cases i using Fin.addCases with
      | left j => simp [wordsCfg, Sequential.left, Cfg.mapState, MultiTapeMachine.initialConfig,
          Cfg.init, NativeResponseExecution.Workspace.words]
      | right j => fin_cases j <;> simp
          [wordsCfg, Sequential.left, Cfg.mapState, MultiTapeMachine.initialConfig,
          Cfg.init, NativeResponseExecution.Workspace.words]
    · rfl
  · rfl

/-- Ready context has no hidden residual response tape or displaced work head. -/
theorem ready_context {k : ℕ} [NeZero k] {S P : Type} (input word : List Bool)
    (state : Option S) (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    ready input state (Function.update (fun _ : Fin k => []) 0 word) channels memory =
      NativeReplyContext.wordWorld input state
        (Function.update (fun _ : Fin (k + 2) => []) 0 word) channels memory := by
  unfold ready
  rw [append_context]

end Cslib.Probability.NativeResponseReuse
