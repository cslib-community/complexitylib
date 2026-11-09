/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.NativeRetention.GuardedStartup
public import Complexity.Computability.Probabilistic.NativeResponseReuse
public import Complexity.Computability.Probabilistic.NativeFeedbackLoop
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
import Mathlib.Tactic

/-!
# Native feedback on the updated runtime context

One finite native program loads original input, tests computed stopping before each
query, processes actual full reports, clears both reply/query buffers and their
negative-cell markers, restores every head, and restarts on the updated runtime
State. No state is compiled into a continuation or supplied between turns. Native
local time may depend on the complete reply. The same consistent environment and
actual answer channels survive across rounds.

This is the concrete append-private-word/rational-retention controller in the raw
State transport ABI. Its scalar opportunity/reservation counts are not a labeled
source used-set or measured physical clock. Source-admitted concurrent batch
planning and Theorem 5 upper/optimum transfer remain open, as do the broader source
representation and Theorem 6 specialization gaps. The source conventions are
[Wang2027], model pp. 4--6, Theorem 5 p. 12/Appendix A.5 p. 16.

## Main definitions

* `Outcome`, `run`: named final data and the mathematical kernel stating the native law.

## Main results

* `exists_round`: actual native runtime preparation/query/update with the whole ready invariant.
* `exists_native_controller`: actual same-code feedback from original blank-tape input.
* `run_stopped`, `run_history_matches`, `run_call_bounds`: computed stopping, authenticated
  raw histories and bounds by each scalar allowance.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.Feedback
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

private def queryWord (packet : List Bool) : List Bool := dropFrame packet.tail

private theorem queryWord_packet (state : RuntimeControl.State) :
    queryWord (RuntimeControl.packet state) = frame (RuntimeControl.encoding state) := by
  simp [queryWord, RuntimeControl.packet, NativeStopGuard.packet, dropFrame_frame_append]

private theorem queryWord_computable : ComputableInPolyTime queryWord encBits encBits :=
  ComputableInPolyTime.dropFrame.comp ComputableInPolyTime.bitsTail

private def preparerTapes (base scratch : ℕ) :
    Fin (scratch + 1 + 2) ↪ Fin (base + scratch + 3 + 2) :=
  ⟨fun i => ⟨if i.val < scratch then i.val + 1
    else if i.val = scratch then base + scratch + 3
    else if i.val = scratch + 1 then 0 else base + scratch + 3 + 1, by
      split_ifs <;> omega⟩, by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega⟩

private def copyTapes {width : ℕ} (hwidth : 0 < width) : Fin 3 ↪ Fin (width + 2) :=
  ⟨fun i => ⟨if i.val = 0 then 0 else if i.val = 1 then width else width + 1, by
    split_ifs <;> omega⟩, by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega⟩

private theorem exists_prepare (base : ℕ) :
    ∃ (width : ℕ) (_ : base ≤ width) (_ : 0 < width) (R : Type) (_ : Finite R)
      (code : MultiTapeTM (width + 2) Bool R), ∀ word : List Bool, ∃ time space,
        TransformsTapes code
          (fun _ ws => ws = Function.update (fun _ => []) 0 word)
          (fun _ _ ws' emitted => ws' = Function.update
            (Function.update (fun _ => []) 0 (queryWord word))
            (Fin.natAdd width (0 : Fin 2)) (queryWord word) ∧ emitted = []) time space := by
  obtain ⟨t, s, _, _, hc⟩ := queryWord_computable
  obtain ⟨_, ht⟩ := ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace hc
  obtain ⟨scratch, R, hR, processor, hp⟩ := ht
  let width := base + scratch + 3
  have hw : 0 < width := by dsimp [width]; omega
  let e := preparerTapes base scratch
  let q : Fin (width + 2) := Fin.natAdd width 0
  let f : Fin (width + 2) := Fin.natAdd width 1
  let copy := copyTapes hw
  have hq : e ((Fin.last scratch).castAdd 2) = q := by
    apply Fin.ext
    change (if scratch < scratch then scratch + 1 else
      if scratch = scratch then base + scratch + 3 else
      if scratch = scratch + 1 then 0 else base + scratch + 3 + 1) = base + scratch + 3
    simp
  have hin : e (Fin.natAdd (scratch + 1) 0) = 0 := by
    apply Fin.ext
    change (if scratch + 1 < scratch then scratch + 1 + 1 else
      if scratch + 1 = scratch then base + scratch + 3 else
      if scratch + 1 = scratch + 1 then 0 else base + scratch + 3 + 1) = 0
    simp
  have hc0 : copy 0 = 0 := Fin.ext (by simp [copy, copyTapes])
  have hc1 : copy 1 = q := Fin.ext (by simp [copy, copyTapes, q])
  have hc2 : copy 2 = f := Fin.ext (by simp [copy, copyTapes, f])
  let first := (processor.onWords true).extendTapes e
  let clear := (clearWork Bool).extendTapes (tapeEmb (0 : Fin (width + 2)))
  let move := copyWord copy true
  let code := (first.seq clear).seq move
  refine ⟨width, by dsimp [width]; omega, hw, _, inferInstance, code, ?_⟩
  intro word
  have hproc := (hp word).onWords_extendTapes true hin hq
  have hnq : q ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change width = 0 at hv
    omega
  have hnf : f ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change width + 1 = 0 at hv
    omega
  have hfq : f ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change width + 1 = width at hv
    omega
  have hp' := hproc.imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) 0 word)
    (Q' := fun _ _ ws' em => ws' = Function.update
      (Function.update (fun _ => []) 0 word) q (queryWord word) ∧ em = [])
    (fun _ _ h => h) (fun _ ws ws' em h hh => by simpa only [h, encBits_apply] using hh)
    le_rfl le_rfl
  have hclear := (transformsTapes_clearWork_tapeEmb (0 : Fin (width + 2)) word).imp
    (P' := fun _ ws => ws = Function.update
      (Function.update (fun _ => []) 0 word) q (queryWord word))
    (Q' := fun _ _ ws' em => ws' = Function.update (fun _ => []) q (queryWord word) ∧ em = [])
    (fun _ ws h => by simp [h, hnq.symm])
    (fun _ ws ws' em h hh => by
      refine ⟨?_, hh.2⟩
      rw [hh.1, h]
      funext i
      by_cases hi : i = 0 <;> by_cases hq : i = q <;> simp_all)
    le_rfl le_rfl
  have hcopy := (transformsTapes_copyWord copy true (queryWord word)).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) q (queryWord word))
    (Q' := fun _ _ ws' em => ws' = Function.update
      (Function.update (fun _ => []) 0 (queryWord word)) q (queryWord word) ∧ em = [])
    (fun _ ws h => by simp [h, hc0, hc1, hc2, hnq.symm, hfq])
    (fun _ ws ws' em h hh => by
      refine ⟨?_, hh.2⟩
      rw [hh.1, h, hc0]
      exact Function.update_comm hnq _ _ _)
    le_rfl le_rfl
  exact ⟨_, _, (hp'.seq_eq hclear).seq_eq hcopy⟩

private theorem prepare_words {width : ℕ} [NeZero width] (hw : 0 < width) (word : List Bool) :
    Function.update (Function.update (fun _ : Fin (width + 2) => []) 0 word)
      (Fin.natAdd width (0 : Fin 2)) word =
      Fin.append (Function.update (fun _ : Fin width => []) 0 word) ![word, []] := by
  funext i
  cases i using Fin.addCases with
  | left j =>
    rw [Fin.append_left, Function.update_of_ne (Fin.castAdd_ne_natAdd j 0)]
    by_cases hj : j = 0
    · subst j
      have hz : (0 : Fin width).castAdd 2 = 0 := Fin.ext rfl
      simp [hz]
    · have hn : j.castAdd 2 ≠ 0 := by
        intro h
        exact hj (Fin.ext (congrArg (fun i : Fin (width + 2) => i.val) h))
      simp [hj, hn]
  | right j =>
    rw [Fin.append_right]
    have hn : Fin.natAdd width j ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      change width + j.val = 0 at hv
      omega
    by_cases hj : j = 0
    · subst j; simp
    · rw [Function.update_of_ne (show Fin.natAdd width j ≠ Fin.natAdd width 0 from
        fun h => hj ((Fin.natAddEmb width).injective h)), Function.update_of_ne hn]
      fin_cases j <;> simp_all

private def marker (width : ℕ) :=
  (markWork Bool (some true)).extendTapes (tapeEmb (Fin.natAdd width (1 : Fin 2)))

private theorem mark_terminal {width : ℕ} [NeZero width] (hw : 0 < width) {P : Type}
    (env : Environment Unit P) (input request : List Bool)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic (marker width)) env
      (NativeReplyContext.wordWorld input (some (marker width).q₀)
        (Function.update (Function.update (fun _ => []) 0 request)
          (Fin.natAdd width (0 : Fin 2)) request) channels memory) =
      PMF.pure (some (NativeResponseExecution.inputWorld
        (NativeReplyContext.wordWorld request (S := MarkWorkState) none
          (Function.update (fun _ : Fin width => []) 0 request) channels memory) input 1)) := by
  apply NativeResponseExecution.terminal_of_clock _ env _
    (NativeResponseExecution.inputWorld
      (NativeReplyContext.wordWorld request (S := MarkWorkState) none
        (Function.update (fun _ : Fin width => []) 0 request) channels memory) input 1)
    2 ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic (Oracle := Unit) (marker width)).runOracleConfigFrom 2
      (NativeReplyContext.wordWorld input (some (marker width).q₀)
        (Function.update (Function.update (fun _ => []) 0 request)
          (Fin.natAdd width (0 : Fin 2)) request) channels memory).config)).run memory).map
      (fun pair => (⟨pair.1, pair.2⟩ : World (width + 2) _ Unit P input)) = _
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (width + 2) _ Unit P input))
  apply Config.ext
  · simp only [prepare_words hw, marker, runFrom_tapeEmb, oneTapeCfg,
      NativeReplyContext.wordWorld, wordsCfg, extendTapes_q₀, runFrom_markWork]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      cases i using Fin.addCases with
      | left j => simp [embed_tapeEmb, InputFromTape.config, inCfg, Fin.castAdd_ne_natAdd]
      | right j => fin_cases j <;> simp [embed_tapeEmb, InputFromTape.config, inCfg]
    · funext i
      cases i using Fin.addCases with
      | left j => simp [embed_tapeEmb, InputFromTape.config, inCfg]
      | right j => fin_cases j <;> simp [embed_tapeEmb, InputFromTape.config, inCfg]
    · rfl
  · rfl

/-- Construct one native round on actual runtime packets. The returned entire
configuration is a canonical updated packet with every scratch/buffer/marker
cleared, every head restored, and actual response channels and ledger retained.
This round is unguarded; a surrounding native loop must test the packet first. -/
theorem exists_round :
    ∃ (width : ℕ) (_ : 4 ≤ width) (R : Type) (_ : Finite R)
      (body : MultiTapePTM (width + 2) Bool R Unit),
      ∀ (P : Type) (env : Environment Unit P) (input : List Bool)
        (state : RuntimeControl.State) (channels : Unit → Channel Bool)
        (_ : (channels ()).queryBuffer = []) (memory : Memory Unit P),
        NativeUnboundedExecution.terminal body env
          (NativeReplyContext.wordWorld input (some body.initial)
            (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory) =
        (env ((), frame (RuntimeControl.encoding state)) memory).map fun (reply, next) =>
          some (NativeReplyContext.wordWorld input (S := R) none
            (Function.update (fun _ => []) 0
              (RuntimeControl.packet (RuntimeControl.afterReply state reply.word)))
            (NativeQueryAll.finish (k := 0) () (frame (RuntimeControl.encoding state))
              memory reply next).config.channels
            (memory.record ((), frame (RuntimeControl.encoding state)) reply next)) := by
  obtain ⟨k, S, hS, processor, hprocessor⟩ := RuntimeControl.exists_native_processor
  obtain ⟨width, hwidth, hw, R, hR, prepare, hprepare⟩ := exists_prepare ((3 + k) + 2)
  have : NeZero width := ⟨by omega⟩
  let e : Fin ((3 + k) + 2) ↪ Fin width := Fin.castLEEmb hwidth
  let source := NativeResponseReuse.phase processor
  let extended := source.extendTapes e
  let virtual := extended.inputFromTape
  let tail := virtual.seq (NativeResponseReuse.cleanup width)
  let post := (MultiTapePTM.ofDeterministic (Oracle := Unit) (marker width)).seq tail
  let body := (MultiTapePTM.ofDeterministic (Oracle := Unit) prepare).seq post
  refine ⟨width, by omega, _, inferInstance, body, ?_⟩
  intro P env input state channels hb memory
  let request := frame (RuntimeControl.encoding state)
  obtain ⟨time, space, hp⟩ := hprepare (RuntimeControl.packet state)
  have hp' := hp.imp
    (P' := fun inp ws => inp = input ∧
      ws = Function.update (fun _ => []) 0 (RuntimeControl.packet state))
    (Q' := fun _ _ ws' emitted => ws' = Function.update
      (Function.update (fun _ => []) 0 request)
        (Fin.natAdd width (0 : Fin 2)) request ∧ emitted = [])
    (fun _ _ h => h.2) (fun _ _ _ _ _ h => by simpa only [queryWord_packet] using h)
    le_rfl le_rfl
  have hpure := NativeReplyContext.terminal_transform prepare env input
    (Function.update (fun _ => []) 0 (RuntimeControl.packet state))
    (Function.update (Function.update (fun _ => []) 0 request)
      (Fin.natAdd width (0 : Fin 2)) request) channels memory time space hp'
  have hi : NativeReplyContext.wordWorld input (some body.initial)
      (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory =
      NativeSequential.left post (NativeReplyContext.wordWorld input (some prepare.q₀)
        (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory) := rfl
  rw [hi, NativeSequential.terminal_seq, hpure, PMF.pure_bind]
  dsimp only
  have hr : NativeSequential.resume post (NativeReplyContext.wordWorld input (S := R) none
      (Function.update (Function.update (fun _ => []) 0 request)
        (Fin.natAdd width (0 : Fin 2)) request) channels memory) =
      NativeSequential.left tail (NativeReplyContext.wordWorld input (some (marker width).q₀)
        (Function.update (Function.update (fun _ => []) 0 request)
          (Fin.natAdd width (0 : Fin 2)) request) channels memory) := rfl
  rw [hr, NativeSequential.terminal_seq, mark_terminal hw, PMF.pure_bind]
  dsimp only
  have hv : NativeSequential.resume tail (NativeResponseExecution.inputWorld
      (NativeReplyContext.wordWorld request (S := MarkWorkState) none
        (Function.update (fun _ : Fin width => []) 0 request) channels memory) input 1) =
      NativeSequential.left (NativeResponseReuse.cleanup width)
        (NativeResponseExecution.inputWorld (NativeReplyContext.wordWorld request
          (some extended.initial) (Function.update (fun _ : Fin width => []) 0 request)
          channels memory) input 1) := rfl
  have hs : NativeUnboundedExecution.terminal extended env
      (NativeReplyContext.wordWorld request (some extended.initial)
        (Function.update (fun _ : Fin width => []) 0 request) channels memory) =
      (env ((), request) memory).map fun (reply, next) =>
        some (NativeReplyContext.wordWorld request (S := NativeResponseReuse.PhaseControl S) none
          (Function.update (fun _ : Fin width => []) 0
            (RuntimeControl.packet (RuntimeControl.afterReply state reply.word)))
          (NativeQueryAll.finish (k := 3 + k) () request memory reply next).config.channels
          (memory.record ((), request) reply next)) := by
    change NativeUnboundedExecution.terminal (source.extendTapes e) env
      (NativeReplyContext.wordWorld request (some source.initial)
        (Function.update (fun _ : Fin width => []) 0 request) channels memory) = _
    rw [← NativeReplyContext.wordWorld_embed_zero e (Fin.ext rfl),
      ← NativeResponseReuse.entry_context processor request request channels memory,
      NativeSequential.terminal_embedStorage,
      NativeResponseReuse.terminal_phase _ _ _ _ _ (hprocessor state) _ hb,
      PMF.map_comp]
    apply congrArg (fun f => (env ((), request) memory).map f)
    funext pair
    obtain ⟨reply, next⟩ := pair
    dsimp only [Function.comp_apply, Option.map_some]
    rw [NativeResponseReuse.ready_context,
      NativeReplyContext.wordWorld_embed_zero e (Fin.ext rfl)]
    rfl
  rw [hv, NativeSequential.terminal_seq, NativeResponseExecution.terminal_inputWorld, hs,
    PMF.map_comp, PMF.bind_map]
  conv_rhs => rw [PMF.map]
  rw [PMF.map_bind, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨reply, next⟩ := pair
  dsimp only [Function.comp_apply, Option.map_some]
  rw [NativeResponseReuse.terminal_cleanup, PMF.pure_map, NativeResponseReuse.ready_context]
  simp only [PMF.pure_map, Function.comp_apply, Option.map_some]
  rfl

/-- Final runtime state, live channels and the full actual oracle/resource ledger. -/
structure Outcome (P : Type) where
  /-- Updated instance/history/private-word/counter data. -/
  state : RuntimeControl.State
  /-- Actual hidden oracle state and all recorded events. -/
  memory : Memory Unit P
  /-- Retained actual answer channels, never replaced by a reset assumption. -/
  channels : Unit → Channel Bool

/-- The finite mathematical kernel used to state the native feedback law. It is
not an execution implementation: `exists_native_controller` constructs and proves the
same-code native implementation independently of this recursion. -/
@[expose] def run {P : Type} (env : Environment Unit P) :
    ℕ → RuntimeControl.State → (Unit → Channel Bool) → Memory Unit P → PMF (Outcome P)
  | 0, state, channels, memory => PMF.pure ⟨state, memory, channels⟩
  | fuel + 1, state, channels, memory =>
    if RuntimeControl.stopped state then PMF.pure ⟨state, memory, channels⟩ else do
      let (reply, next) ← env ((), frame (RuntimeControl.encoding state)) memory
      run env fuel (RuntimeControl.afterReply state reply.word)
        (NativeQueryAll.finish (k := 0) () (frame (RuntimeControl.encoding state))
          memory reply next).config.channels
        (memory.record ((), frame (RuntimeControl.encoding state)) reply next)

/-- A computed stop is absorbing for every remaining turn budget. -/
theorem run_of_stopped {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool) (memory : Memory Unit P)
    (hs : RuntimeControl.stopped state = true) :
    run env fuel state channels memory = PMF.pure ⟨state, memory, channels⟩ := by
  cases fuel <;> simp [run, hs]

private theorem finish_buffer {P : Type} (request : List Bool) (memory : Memory Unit P)
    (reply : Reply) (next : P) :
    ((NativeQueryAll.finish (k := 0) () request memory reply next).config.channels ()).queryBuffer =
      [] := by simp [NativeQueryAll.finish, NativeQueryAll.finishFrom]

/-- With enough remaining turns, the mathematical kernel ends only at an actual
computed completion or exhausted policy allowance. -/
theorem run_stopped {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool) (memory : Memory Unit P)
    (hf : state.turns ≤ fuel) (outcome : Outcome P)
    (ho : outcome ∈ (run env fuel state channels memory).support) :
    RuntimeControl.stopped outcome.state = true := by
  induction fuel generalizing state channels memory outcome with
  | zero =>
    have ht : state.turns = 0 := by omega
    simp only [run, PMF.mem_support_pure_iff] at ho
    cases ho
    simp [RuntimeControl.stopped, ht]
  | succ fuel ih =>
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp only [run, hs, ↓reduceIte, PMF.mem_support_pure_iff] at ho
      cases ho
      exact hs
    | false =>
      simp only [run, hs, Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind] at ho
      rw [PMF.mem_support_bind_iff] at ho
      obtain ⟨⟨reply, next⟩, _, ho⟩ := ho
      exact ih _ _ _ (by simp only [RuntimeControl.afterReply]; omega) _ ho

private theorem terminal_loop {width : ℕ} {R P : Type}
    (body : MultiTapePTM (width + 2) Bool R Unit)
    (hbody : ∀ (P : Type) (env : Environment Unit P) (input : List Bool)
      (state : RuntimeControl.State) (channels : Unit → Channel Bool)
      (_ : (channels ()).queryBuffer = []) (memory : Memory Unit P),
      NativeUnboundedExecution.terminal body env
        (NativeReplyContext.wordWorld input (some body.initial)
          (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory) =
      (env ((), frame (RuntimeControl.encoding state)) memory).map fun (reply, next) =>
        some (NativeReplyContext.wordWorld input (S := R) none
          (Function.update (fun _ => []) 0
            (RuntimeControl.packet (RuntimeControl.afterReply state reply.word)))
          (NativeQueryAll.finish (k := 0) () (frame (RuntimeControl.encoding state))
            memory reply next).config.channels
          (memory.record ((), frame (RuntimeControl.encoding state)) reply next)))
    (env : Environment Unit P) (input : List Bool) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool)
    (hb : (channels ()).queryBuffer = []) (memory : Memory Unit P) (hf : state.turns ≤ fuel) :
    NativeUnboundedExecution.terminal (NativeFeedbackLoop.machine 0 body) env
      (NativeFeedbackLoop.check (NativeReplyContext.wordWorld input (S := R) none
        (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory)) =
      (run env fuel state channels memory).map fun outcome =>
        some (NativeReplyContext.wordWorld input (S := R ⊕ Unit) none
          (Function.update (fun _ => []) 0 (RuntimeControl.packet outcome.state))
          outcome.channels outcome.memory) := by
  induction fuel generalizing state channels memory with
  | zero =>
    have ht : state.turns = 0 := by omega
    have hs : RuntimeControl.stopped state = true := by simp [RuntimeControl.stopped, ht]
    rw [NativeFeedbackLoop.terminal_check]
    simp [NativeReplyContext.wordWorld, wordsCfg, Cfg.workTapeSymbols, RuntimeControl.packet,
      NativeStopGuard.packet, tapeOfList_zero, hs, run, NativeFeedbackLoop.stopped,
      NativeFeedbackLoop.check, Cfg.withState]
  | succ fuel ih =>
    rw [NativeFeedbackLoop.terminal_check]
    have hw : (NativeReplyContext.wordWorld input (S := R) none
        (Function.update (fun _ : Fin (width + 2) => []) 0 (RuntimeControl.packet state))
        channels memory).config.tapes.workTapeSymbols 0 = some (RuntimeControl.stopped state) := by
      simp [NativeReplyContext.wordWorld, wordsCfg, Cfg.workTapeSymbols, RuntimeControl.packet,
        NativeStopGuard.packet, tapeOfList_zero]
    rw [hw]
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp [run, hs, NativeFeedbackLoop.stopped, NativeFeedbackLoop.check,
        NativeReplyContext.wordWorld, wordsCfg, Cfg.withState]
    | false =>
      simp only [run, hs, Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind, PMF.map_bind]
      have he : NativeSequential.resume body
          (NativeReplyContext.wordWorld input (S := R) none
            (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory) =
          NativeReplyContext.wordWorld input (some body.initial)
            (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory := rfl
      rw [he, hbody P env input state channels hb memory, PMF.bind_map]
      apply PMF.bind_congr_on_support
      intro pair _
      obtain ⟨reply, next⟩ := pair
      dsimp only [Function.comp_apply]
      exact ih _ _ (finish_buffer _ _ _ _) _ (by
        simp only [RuntimeControl.afterReply]
        omega)

private theorem emit_terminal {width : ℕ} [NeZero width] {P : Type}
    (g : Fin 4 ↪ Fin width) (hg : g 0 = 0) (env : Environment Unit P)
    (input : List Bool) (state : RuntimeControl.State) (hs : RuntimeControl.stopped state = true)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    let emit := (NativeStopGuard.machine
      (MultiTapePTM.ofDeterministic (Oracle := Unit) (nop 4 Bool))).extendTapes g
    (NativeUnboundedExecution.terminal emit env
      (NativeReplyContext.wordWorld input (some emit.initial)
        (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory)).map
        (Option.map (NativeReplyContext.observe 0)) =
      PMF.pure (some (⟨tapeOfList (RuntimeControl.packet state), RuntimeControl.result state,
        memory⟩ : NativeReplyContext.Observation P)) := by
  let stop := NativeStopGuard.machine
    (MultiTapePTM.ofDeterministic (Oracle := Unit) (nop 4 Bool))
  dsimp only
  rw [← NativeReplyContext.wordWorld_embed_zero g hg,
    NativeSequential.terminal_embedStorage, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal stop env
    (NativeReplyContext.wordWorld input (some stop.initial)
      (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory)).map
      (Option.map (NativeReplyContext.observe 0))
  · congr 1
    funext result
    cases result with
    | none => rfl
    | some world =>
      rw [← hg]
      exact congrArg some (NativeReplyContext.observe_embedStorage 0 g world)
  · have hi : NativeReplyContext.wordWorld input (some stop.initial)
        (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory =
        (⟨{ (NativeContextLoader.loadedStart stop input (RuntimeControl.packet state) memory).config
          with channels := channels }, memory⟩ : World 4 _ Unit P input) := rfl
    rw [hi]
    simp only [RuntimeControl.packet, hs]
    rw [NativeStopGuard.terminal_stop_channels, PMF.pure_map]
    simp [NativeReplyContext.observe, NativeStopGuard.stopped]

/-- One actual finite native program starts on original encoded input with blank
work tapes, executes repeated feedback on the updated State, and emits only the
computed final mask/failure word. It uses one consistent stateful environment and
preserves the complete request/reply/invoice/duration ledger. This is the concrete
raw-State transport controller, not source batch admission or an arbitrary Scheduler
compiler; its reservation counter does not measure physical time. -/
theorem exists_native_controller :
    ∃ (width : ℕ) (R : Type) (_ : Finite R)
      (program : MultiTapePTM width Bool R Unit) (context : Fin width),
      ∀ (P : Type) (env : Environment Unit P) (data : GuardedStartup.Input)
        (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (GuardedStartup.encoding data), memory⟩).map
          (Option.map (NativeReplyContext.observe context)) =
        let state := GuardedStartup.state data
        (run env state.turns state (fun _ => ⟨[], [], 0⟩) memory).map fun outcome =>
          some (⟨tapeOfList (RuntimeControl.packet outcome.state),
            RuntimeControl.result outcome.state,
            outcome.memory⟩ : NativeReplyContext.Observation P) := by
  obtain ⟨width, hw, R, hR, body, hbody⟩ := exists_round
  let loop := NativeFeedbackLoop.machine (0 : Fin (width + 2)) body
  let g : Fin 4 ↪ Fin (width + 2) := Fin.castLEEmb (by omega)
  let emit := (NativeStopGuard.machine
    (MultiTapePTM.ofDeterministic (Oracle := Unit) (nop 4 Bool))).extendTapes g
  let consumer := loop.seq emit
  have hconsumer (P : Type) (env : Environment Unit P) (data : GuardedStartup.Input)
      (memory : Memory Unit P) :
      (NativeUnboundedExecution.terminal consumer env
        (NativeContextLoader.loadedStart consumer (GuardedStartup.encoding data)
          (RuntimeControl.packet (GuardedStartup.state data)) memory)).map
          (Option.map (NativeReplyContext.observe 0)) =
      (run env (GuardedStartup.state data).turns (GuardedStartup.state data)
        (fun _ => ⟨[], [], 0⟩) memory).map fun outcome =>
          some (⟨tapeOfList (RuntimeControl.packet outcome.state),
            RuntimeControl.result outcome.state,
            outcome.memory⟩ : NativeReplyContext.Observation P) := by
    let state := GuardedStartup.state data
    let input := GuardedStartup.encoding data
    let words : Fin (width + 2) → List Bool :=
      Function.update (fun _ => []) 0 (RuntimeControl.packet state)
    let channels : Unit → Channel Bool := fun _ => ⟨[], [], 0⟩
    have hi : NativeContextLoader.loadedStart consumer input (RuntimeControl.packet state) memory =
        NativeSequential.left emit (NativeFeedbackLoop.check
          (NativeReplyContext.wordWorld input (S := R) none words channels memory)) := by
      exact congrArg (fun q : R ⊕ Unit => NativeReplyContext.wordWorld input
        (S := (R ⊕ Unit) ⊕ (Fin 3 ⊕ Unit)) (some (.inl q)) words channels memory)
        (NativeFeedbackLoop.machine_initial 0 body)
    rw [hi, NativeSequential.terminal_seq,
      terminal_loop body hbody env input state.turns state channels rfl memory le_rfl,
      PMF.bind_map, PMF.map_bind]
    conv_rhs => rw [PMF.map]
    apply PMF.bind_congr_on_support
    intro outcome ho
    dsimp only [Function.comp_apply, Option.map_some]
    have hs := run_stopped env state.turns state channels memory le_rfl outcome ho
    trans (NativeUnboundedExecution.terminal emit env
      (NativeReplyContext.wordWorld input (some emit.initial)
        (Function.update (fun _ => []) 0 (RuntimeControl.packet outcome.state))
        outcome.channels outcome.memory)).map (Option.map (NativeReplyContext.observe 0))
    · rw [PMF.map_comp]
      congr 1
      funext result
      cases result <;> rfl
    · exact emit_terminal g (Fin.ext rfl) env input outcome.state hs outcome.channels outcome.memory
  have hinit : ComputableInPolyTime
      (fun data => RuntimeControl.packet (GuardedStartup.state data))
      GuardedStartup.encoding encBits :=
    RuntimeControl.computable_packet.comp GuardedStartup.computable_state
  obtain ⟨scratch, T, hT, loader, hloader⟩ := NativeContextLoader.exists_load_then
    GuardedStartup.encoding (fun data => RuntimeControl.packet (GuardedStartup.state data))
    hinit (width + 2)
  let program := (MultiTapePTM.ofDeterministic (Oracle := Unit) loader).seq
    (consumer.extendTapes (Fin.castAddEmb scratch))
  refine ⟨_, _, inferInstance, program, (0 : Fin (width + 2)).castAdd scratch, ?_⟩
  intro P env data memory
  rw [hloader, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal consumer env
    (NativeContextLoader.loadedStart consumer (GuardedStartup.encoding data)
      (RuntimeControl.packet (GuardedStartup.state data)) memory)).map
      (Option.map (NativeReplyContext.observe 0))
  · congr 1
    funext result
    cases result with
    | none => rfl
    | some world =>
      exact congrArg some (NativeReplyContext.observe_embedStorage
        0 (Fin.castAddEmb scratch) world)
  · exact hconsumer P env data memory

/-- Actual raw event histories/private bytes remain authenticated through every
round of the mathematical kernel used by the native correspondence theorem. -/
theorem run_history_matches {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (seed : List Bool) (state : RuntimeControl.State) (channels : Unit → Channel Bool)
    (memory : Memory Unit P) (hh : RuntimeControl.HistoryMatches seed state memory.events)
    (outcome : Outcome P) (ho : outcome ∈ (run env fuel state channels memory).support) :
    RuntimeControl.HistoryMatches seed outcome.state outcome.memory.events := by
  induction fuel generalizing state channels memory outcome with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at ho
    cases ho
    exact hh
  | succ fuel ih =>
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp only [run, hs, ↓reduceIte, PMF.mem_support_pure_iff] at ho
      cases ho
      exact hh
    | false =>
      simp only [run, hs, Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind] at ho
      rw [PMF.mem_support_bind_iff] at ho
      obtain ⟨⟨reply, next⟩, _, ho⟩ := ho
      exact ih _ _ _
        (RuntimeControl.afterReply_history_matches seed state memory reply next hh) _ ho

/-- Guarded feedback issues no more turns than any initial scalar allowance.
This is an actual-call count bound, not a labeled source-opportunity used-set or
measured physical deadline guarantee. -/
theorem run_call_bounds {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool) (memory : Memory Unit P)
    (outcome : Outcome P) (ho : outcome ∈ (run env fuel state channels memory).support) :
    outcome.memory.events.length ≤ memory.events.length + state.turns ∧
    outcome.memory.events.length ≤ memory.events.length + state.opportunities ∧
    outcome.memory.events.length ≤ memory.events.length + state.allotments := by
  induction fuel generalizing state channels memory outcome with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at ho
    cases ho
    simp
  | succ fuel ih =>
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp only [run, hs, ↓reduceIte, PMF.mem_support_pure_iff] at ho
      cases ho
      simp
    | false =>
      have ht : state.turns ≠ 0 := by intro h; simp [RuntimeControl.stopped, h] at hs
      have hp : state.opportunities ≠ 0 := by intro h; simp [RuntimeControl.stopped, h] at hs
      have ha : state.allotments ≠ 0 := by intro h; simp [RuntimeControl.stopped, h] at hs
      simp only [run, hs, Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind] at ho
      rw [PMF.mem_support_bind_iff] at ho
      obtain ⟨⟨reply, next⟩, _, ho⟩ := ho
      have bounds := ih _ _ _ _ ho
      simp only [RuntimeControl.afterReply, Memory.record, List.length_cons] at bounds
      omega

end Cslib.Probability.StochasticOracle.NativeRetention.Feedback
