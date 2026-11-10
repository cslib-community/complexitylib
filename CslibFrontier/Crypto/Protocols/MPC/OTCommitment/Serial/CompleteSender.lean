/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Serial
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.CompleteSender
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Complete senders in the common serial world

The honest receiver supplies its next private selection immediately after each submitted table,
before the complete sender resumes. This scheduler is part of the adapter; the execution equality
is not a claim about arbitrary interleavings. The adversary sees only its own empty replies.

## Main definitions

* `senderSchedule`, `senderAdapter`: a complete sender and its honest-receiver scheduler.

## Main results

* `eval_senderAdapter`: exact equality with the existing complete real execution.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment.Serial

open Probability Crypto.Protocols.Commitment

/-- One sender command, followed by the honest receiver before the sender resumes. The private
index advances only when a pending row is actually consumed. -/
def senderSchedule (choices : List Bool) (request : SenderOperation × List Bool) :
    StateT ℕ (ProbOracleComp (senderSpec ⊕ₒ receiverSpec)) (List Bool) := fun index => do
  let _ ← Interactive.liftProver (ProbOracleComp.query (spec := senderSpec) request)
  match request.1 with
  | .table _ =>
      let value ← Interactive.liftVerifier (ProbOracleComp.query (spec := receiverSpec)
        (.select (boolPairToFin4 (false, choices.getD index false))))
      return ([], if value.isSome then index + 1 else index)
  | _ => return ([], index)

/-- The complete sender sees no receiver call or answer. The honest receiver retains its private
selection index across calls and consumes each accepted table before the sender resumes. -/
noncomputable def senderAdapter {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    ProbOracleComp (senderSpec ⊕ₒ receiverSpec)
      (Phased.Observation × Phased.Observation × Output) := do
  let choices ← ProbOracleComp.sample (BitString.sampleList k)
  let (out, _) ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (senderSchedule choices)) program).run 0
  let (received, final) ← Interactive.liftVerifier
    (ProbOracleComp.query (spec := receiverSpec) .poll)
  return (received, final, out)

private def senderReceipts (tables : List (Fin 4 → Bool)) (choices : List Bool) :
    List (Fin 4 × Bool) :=
  (tables.zip choices).map fun (t, c) =>
    (boolPairToFin4 (false, c), t (boolPairToFin4 (false, c)))

private def senderStore (choices : List Bool) (s : Session) : Store :=
  { session := s, receipts := senderReceipts s.tables choices }

private noncomputable def scheduledHandler (k : ℕ) (choices : List Bool)
    (request : SenderOperation × List Bool) (state : ℕ × Store) :
    PMF (List Bool × ℕ × Store) :=
  (ProbOracleComp.runWith (world k).impl ((senderSchedule choices request).run state.1)
    state.2).map fun ((reply, index), store) => (reply, index, store)

private theorem senderReceipts_append (tables : List (Fin 4 → Bool)) (choices : List Bool)
    (t : Fin 4 → Bool) (h : tables.length < choices.length) :
    senderReceipts (tables ++ [t]) choices = senderReceipts tables choices ++
      [(boolPairToFin4 (false, choices.getD tables.length false),
        t (boolPairToFin4 (false, choices.getD tables.length false)))] := by
  induction tables generalizing choices with
  | nil =>
      cases choices with
      | nil => simp at h
      | cons c cs => rfl
  | cons t' ts ih =>
      cases choices with
      | nil => simp at h
      | cons c cs =>
          simp only [List.cons_append, senderReceipts, List.zip_cons_cons, List.map_cons,
            List.length_cons, List.getD_cons_succ]
          exact congrArg (List.cons _) (ih cs (by simpa using h))

private theorem scheduledHandler_step (k : ℕ) (choices : List Bool)
    (hchoices : choices.length = k) (request : SenderOperation × List Bool) (s : Session) :
    scheduledHandler k choices request (s.tables.length, senderStore choices s) =
      pure ([], (s.advance k request).tables.length,
        senderStore choices (s.advance k request)) := by
  rcases request with ⟨op, word⟩
  cases ht : s.stopped <;> cases hc : s.sealed <;> cases op <;>
    simp only [scheduledHandler, senderSchedule, StateT.run, Interactive.liftProver,
      Interactive.liftVerifier, ProbOracleComp.interpret_query,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure, ProbOracleComp.runWith_query,
      world, handler, Store.send, senderStore, Session.advance, OracleComp.sumHandler,
      ht, hc, Bool.true_or, Bool.false_or, Bool.false_eq_true, ite_false, ite_true,
      ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map, Option.isSome_none]
  all_goals try rfl
  all_goals split <;> simp_all [ot14World, ot14Answer, senderReceipts_append]
  all_goals rfl

private theorem senderStore_observations (k : ℕ) (choices : List Bool)
    (hchoices : choices.length = k) (s : Session)
    (hs : s.sealed = true → s.tables.length = k) :
    (senderStore choices s).observations k =
      (s.receipt, s.observation k choices (selectedBits s.tables choices)) := by
  have ha : (senderReceipts s.tables choices).map Prod.snd = selectedBits s.tables choices := by
    simp only [senderReceipts, selectedBits, List.map_map, Function.comp_def]
  by_cases hc : s.sealed = true
  · have hi : (senderReceipts s.tables choices).map
        (fun r => (fin4ToBoolPair r.1).2) = choices := by
      simp only [senderReceipts, List.map_map, Function.comp_def,
        fin4ToBoolPair_boolPairToFin4]
      exact List.map_snd_zip (by rw [hchoices, hs hc])
    simp only [Store.observations, senderStore, ha, hi]
  · simp [Store.observations, senderStore, Session.observation, hc]

private theorem run_senderSchedule {Output : Type} (k : ℕ) (choices : List Bool)
    (hchoices : choices.length = k) (program : WordOracleComp SenderOperation Output) :
    ProbOracleComp.runWith (world k).impl
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (senderSchedule choices)) program).run 0) {} =
      (ProbComp.eval (sessionProgram k program)).map (fun (out, s) =>
        ((out, s.tables.length), senderStore choices s)) := by
  have h := ProbOracleComp.run_interpret_map_state
    (fun request (s : Session) => PMF.pure ([], s.advance k request))
    (scheduledHandler k choices) (fun s => (s.tables.length, senderStore choices s))
    (fun request s => by
      rw [scheduledHandler_step k choices hchoices]
      simp) program .initial
  have hh := congrArg (PMF.map (fun (out, index, store) => ((out, index), store))) h
  rw [PMF.map_comp] at hh
  delta scheduledHandler at hh
  dsimp only [ProbOracleComp.runWith, OracleComp.runWith] at hh
  simp only [ProbOracleComp.runWith, OracleComp.runWith]
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [sessionProgram, ProbOracleComp.eval_run_interpret, ProbComp.eval_pure,
    Function.comp_def, Session.initial, senderStore, senderReceipts,
    List.zip_nil_left, List.map_nil,
    List.length_nil] at hh ⊢
  convert hh.symm using 1

private theorem run_senderTail {Output : Type} (k : ℕ) (choices : List Bool)
    (hchoices : choices.length = k) (program : WordOracleComp SenderOperation Output) :
    (ProbOracleComp.runWith (world k).impl (do
      let (out, _) ← (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (senderSchedule choices)) program).run 0
      let (received, final) ← Interactive.liftVerifier
        (ProbOracleComp.query (spec := receiverSpec) .poll)
      pure (received, final, out)) {}).map Prod.fst =
      (ProbComp.eval (sessionProgram k program)).map (fun (out, s) =>
        (s.receipt, s.observation k choices (selectedBits s.tables choices), out)) := by
  rw [ProbOracleComp.runWith_bind, run_senderSchedule k choices hchoices]
  simp only [PMF.bind_map, Interactive.liftVerifier, ProbOracleComp.interpret_query,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
    world, handler, OracleComp.sumHandler, ProbComp.eval_pure, PMF.pure_bind,
    PMF.map_bind]
  apply PMF.bind_congr_on_support
  rintro ⟨out, s⟩ hs
  dsimp only [Function.comp_def]
  rw [senderStore_observations k choices hchoices s (sessionProgram_length k program out s hs).2]
  exact PMF.pure_map _ _

/-- The existing complete real execution is exactly the common world's execution under the
explicit honest-receiver scheduler. The equality retains receipt, final observation and arbitrary
adversary output; it does not quantify over other interleavings. -/
theorem eval_senderAdapter {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    (world k).eval (senderAdapter k program) = ProbComp.eval (completeSenderReal k program) := by
  rw [Interactive.World.eval, senderAdapter, ProbOracleComp.runWith_bind]
  simp only [pmf_norm, ProbOracleComp.runWith_sample, BitString.eval_sampleList,
    BitString.uniformList]
  simp_rw [run_senderTail k (List.ofFn _) List.length_ofFn program]
  rw [eval_completeSenderReal]
  simp only [PMF.map, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  exact PMF.bind_comm _ _ _

end Cslib.Crypto.Protocols.MPC.OTCommitment.Serial
