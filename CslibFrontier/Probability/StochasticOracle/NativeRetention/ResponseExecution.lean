/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Packets
public import CslibFrontier.Computability.Probabilistic.NativeResponseExecution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# A native query followed by actual raw-response retention

The generated continuation parses the real complete reply, updates the fixed
context's raw history, computes exact rational retention and emits the source mask
on computed completion. The full query/mark/rewind/virtual-input/processor program
has the derived joint native law, with response-dependent local execution.

Context is fixed at code construction. A uniform runtime-context scheduler and
adaptive restart loop remain open, as do the native quantitative upper endpoint
and common-oracle optimum comparison. This is a concrete implementation connection
for [Wang2027], Theorem 5 p. 12/App. A.5 p. 16, not its complete native realization.
No new public tidy interface or common full-reply clock is used.

## Main results

* `exists_query_retention`: a constructed native query/parser/retention program
  for each fixed context, emitting the computed source mask with the exact joint law.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.ResponseExecution
open Turing Turing.MultiTapeTM NativeOpenExecution NativeResponseExecution

/-- Recompute exact retention after prepending the actual raw response. -/
@[expose] def afterReply (context : Packets.Work) (packet : ConcurrentBatch.Word) :
    ConcurrentBatch.Word :=
  let data := Packets.assemble { context with history := packet :: context.history }
  if complete data then output data else []

private theorem computable_afterReply (context : Packets.Work) :
    ComputableInPolyTime (afterReply context) encBits encBits := by
  have hp : ComputableInPolyTime
      (fun p : NativeRetention.Input × ℕ × List ConcurrentBatch.Word =>
        Packets.Work.mk p.1 p.2.1 p.2.2)
      (encPair encInput (encPair encUnary (encList encBits))) Packets.encWork :=
    .of_eq fun _ => rfl
  have hs : ComputableInPolyTime (fun _ : ConcurrentBatch.Word => context.system)
      encBits encInput := .const context.system
  have hn : ComputableInPolyTime (fun _ : ConcurrentBatch.Word => context.opportunities)
      encBits encUnary := .const context.opportunities
  have hh : ComputableInPolyTime
      (fun packet : ConcurrentBatch.Word => packet :: context.history)
      encBits (encList encBits) :=
    ComputableInPolyTime.cons' ComputableInPolyTime.id' (.const context.history)
  have htuple := hs.prod (hn.prod hh)
  have hu0 := hp.comp htuple
  have hu : ComputableInPolyTime
      (fun packet : ConcurrentBatch.Word => { context with history := packet :: context.history })
      encBits Packets.encWork := hu0
  have hd := Packets.computable_decision.comp hu
  have hr := ComputableInPolyTime.ite hd.fst' hd.snd'
    (ComputableInPolyTime.const ([] : ConcurrentBatch.Word))
  change ComputableInPolyTime (fun packet =>
    if complete (Packets.assemble { context with history := packet :: context.history }) then
      output (Packets.assemble { context with history := packet :: context.history }) else [])
    encBits encBits
  exact hr

/-- A genuinely constructed native query/retention program, with the actual full
response buffer passed to the compiled parser and rational processor. Context is
fixed when this code is constructed; this does not realize the adaptive scheduler
or a uniform runtime-context loop. No successful cover or native realization is
an assumption. The program emits the actual source mask on computed completion,
or the empty failure word otherwise. -/
theorem exists_query_retention (context : Packets.Work) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (continuation : MultiTapePTM k Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (request : List Bool) (memory : Memory Unit P),
      (NativeUnboundedExecution.terminal (machine continuation) env
        ⟨(machine continuation).initialConfig request, memory⟩).map
          (Option.map fun final => (final.config.tapes.output, final.memory)) =
        (env ((), request) memory).map fun (reply, next) =>
          some (afterReply context reply.word,
            memory.record ((), request) reply next) := by
  obtain ⟨t, s, _, _, k, S, hS, code, hcode⟩ := computable_afterReply context
  let continuation : MultiTapePTM k Bool S Unit := MultiTapePTM.ofDeterministic code
  refine ⟨k, S, hS, continuation, ?_⟩
  intro P env request memory
  rw [terminal_machine, PMF.map_bind]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨reply, next⟩ := pair
  obtain ⟨clock, hh, ho⟩ := (hcode reply.word).1
  let initial := localStart continuation request memory reply next
  let final : World k S Unit P reply.word :=
    ⟨{ initial.config with tapes := code.runFrom initial.config.tapes clock }, initial.memory⟩
  have he : execute continuation env clock initial = PMF.pure final := by
    unfold execute
    change ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
      ((MultiTapePTM.ofDeterministic code).runOracleConfigFrom clock initial.config)).run
        initial.memory).map _ = _
    rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  have hhalt : NativeUnboundedExecution.halted final := hh
  have ht := terminal_of_clock continuation env initial final clock he hhalt
  change ((NativeUnboundedExecution.terminal continuation env initial).map
    (Option.map (resultWorld request))).map _ = _
  rw [ht, PMF.pure_map, PMF.pure_map]
  have hout : final.config.tapes.output = afterReply context reply.word := ho
  change PMF.pure (some (final.config.tapes.output, initial.memory)) = _
  rw [hout]
  rfl

end Cslib.Probability.StochasticOracle.NativeRetention.ResponseExecution
