/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Session
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.EventBind

/-!
# Complete corrupted-sender executions

An original single-session command interface for the OT commitment. One complete word-oracle
program supplies tables, seals the commitment, and attempts an opening. Every sender reply is
empty. The receiver's private choices therefore cannot influence subsequent sender commands.

Sealing requires exactly the prescribed number of tables. Excess tables and premature sealing
abort. Early opening is ignored, as in the phased commitment world. Tables and repeated seals
after sealing are ignored. The first opening attempt after sealing is terminal, including a
malformed or rejected opening; subsequent commands cannot retry or retract it. Explicit abort
is terminal. A program that never seals and never aborts leaves the receiver idle.

The opening payload contains the first component of every pair followed by all second components.
Its length must be exactly twice the round count. Operation names carry a fixed four-bit table
or a bit, so this is a typed word interface, not a general network-message parser.

## Main definitions

* `sessionProgram`: the complete adversary with constant replies and retained session state.

## Main results

* `completeSender_coupled`: actual complete real/ideal execution within the extraction error.
* `completeSender_coupled_two_mul`: the growing schedule `k = 2n` has error `2⁻ⁿ`.

The global receiver adapter, common two-sided corruption contract, composition and malicious MPC
remain separate objectives. No new security or admissibility predicate is introduced here.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Probability Crypto.Protocols.Commitment MeasureTheory

/-- Constant sender replies preserve the actual command sequence and adversary output. -/
def sessionProgram {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) : ProbComp (Output × Session) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
      (fun request s => pure ([], s.advance k request))) program).run .initial

/-- Execute each accepted row against the existing OT world. Choices remain private, and only
the sender's unit answer is discarded; the honest receiver keeps its selected bit. -/
def realSenderHandler (k : ℕ) (choices : List Bool)
    (request : SenderOperation × List Bool) : StateT (Session × List Bool) ProbComp (List Bool) :=
  fun (s, received) => do
    let next := s.advance k request
    match request.1 with
    | .table values =>
        if s.stopped || s.sealed then return ([], next, received)
        else if s.tables.length < k then
          let answer ← ot14World () (Fin.cases values (fun _ =>
            boolPairToFin4 (false, choices.getD s.tables.length false)))
          return ([], next, received ++ [show Bool from answer 1])
        else return ([], next, received)
    | _ => return ([], next, received)

/-- The ideal simulator issues the actual phased command at the time of the corresponding
sender request. In particular, extraction is committed at seal, before the adversary resumes.
The first opening attempt calls open or abort and is terminal regardless of acceptance. -/
def idealSenderHandler (k : ℕ) (choices : List Bool)
    (request : SenderOperation × List Bool) :
    StateT (Session × Phased.Store) ProbComp (List Bool) :=
  fun (s, store) => do
    let next := s.advance k request
    let command := if s.stopped then none else
      if next.stopped then
        some (if next.sealed &&
          (openPairs choices (selectedBits next.tables choices) (next.opening k) ==
            some next.extracted) then Phased.Command.open else .abort)
      else if !s.sealed && next.sealed then some (.commit next.extracted) else none
    let (_, store') ← match command with
      | none => pure ((), store)
      | some cmd => Phased.handler (.inl cmd) store
    return ([], next, store')

/-- Execute a complete adversary in the real OT receiver, retaining the shared phase-history
receipt `s.receipt`, the terminal receiver observation, and the adversary output. Unary `k` is
charged by the uniform certificate. -/
noncomputable def completeSenderReal {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    ProbComp (Phased.Observation × Phased.Observation × Output) := do
  let choices ← BitString.sampleList k
  let (out, s, received) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
      (realSenderHandler k choices)) program).run (.initial, [])
  return (s.receipt, s.observation k choices received, out)

/-- Execute the simulator and actual phased functionality together from idle. The adversary
receives empty replies; the receipt component `s.receipt` comes from the shared phase history `s`
(rather than a functionality poll), while the terminal observation is `Phased.observe store`, and
final functionality storage and the simulator's choice coins remain private. -/
noncomputable def completeSenderIdeal {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    ProbComp (Phased.Observation × Phased.Observation × Output) := do
  let choices ← BitString.sampleList k
  let (out, s, store) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
      (idealSenderHandler k choices)) program).run (.initial, .idle)
  return (s.receipt, Phased.observe store, out)

private theorem selectedBits_append (tables : List (Fin 4 → Bool)) (choices : List Bool)
    (t : Fin 4 → Bool) (h : tables.length < choices.length) :
    selectedBits (tables ++ [t]) choices = selectedBits tables choices ++
      [t (boolPairToFin4 (false, choices.getD tables.length false))] := by
  induction tables generalizing choices with
  | nil =>
      cases choices with
      | nil => simp at h
      | cons c cs => rfl
  | cons t' ts ih =>
      cases choices with
      | nil => simp at h
      | cons c cs =>
          simp only [List.cons_append, selectedBits, List.zip_cons_cons, List.map_cons,
            List.length_cons, List.getD_cons_succ]
          exact congrArg (List.cons _) (ih cs (by simpa using h))

private theorem realSenderHandler_selected (k : ℕ) (choices : List Bool)
    (hchoices : choices.length = k) (request : SenderOperation × List Bool) (s : Session) :
    realSenderHandler k choices request (s, selectedBits s.tables choices) =
      pure ([], s.advance k request, selectedBits (s.advance k request).tables choices) := by
  rcases request with ⟨op, word⟩
  cases ht : s.stopped <;> cases hc : s.sealed <;> cases op <;>
    simp only [realSenderHandler, Session.advance, ht, hc, Bool.true_or, Bool.false_or,
      Bool.false_eq_true, ite_false, ite_true]
  all_goals split <;> simp_all [ot14World, ot14Answer, selectedBits_append]
  all_goals rfl

private theorem idealSenderHandler_store (k : ℕ) (choices : List Bool)
    (request : SenderOperation × List Bool) (s : Session) :
    idealSenderHandler k choices request
      (s, s.idealStore k choices (selectedBits s.tables choices)) =
      pure ([], s.advance k request,
        (s.advance k request).idealStore k choices
          (selectedBits (s.advance k request).tables choices)) := by
  rcases request with ⟨op, word⟩
  cases ht : s.stopped <;> cases hc : s.sealed <;> cases op <;>
    simp only [idealSenderHandler, Session.advance, ht, hc, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
  all_goals simp only [Session.idealStore, ht, hc, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals (try split_ifs) <;> simp_all only [Session.opening, openPairs,
    Bool.false_and, Bool.false_eq_true, ite_false, ite_true, bind_pure_comp,
    Phased.handler, OracleComp.sumHandler, Phased.advance, map_pure]
  all_goals first | rfl | contradiction

/-- Every supported complete execution respects the enforced table budget. This is a property
of the handler, not an admissibility hypothesis on the adversary. -/
theorem sessionProgram_length {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) (out : Output) (s : Session)
    (h : (out, s) ∈ (ProbComp.eval (sessionProgram k program)).support) :
    s.tables.length ≤ k ∧ (s.sealed = true → s.tables.length = k) := by
  simp only [sessionProgram, ProbOracleComp.eval_run_interpret_eq_runWith, ProbComp.eval_pure] at h
  apply ProbOracleComp.runWith_invariant _
    (fun s : Session => s.tables.length ≤ k ∧ (s.sealed = true → s.tables.length = k))
    (fun request st hst value next hnext => ?_) program .initial (by simp [Session.initial])
    out s h
  simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hnext
  rcases hnext with ⟨rfl, rfl⟩
  exact st.advance_length k request hst

private theorem eval_realSenderHandler {Output : Type} (k : ℕ) (choices : List Bool)
    (hchoices : choices.length = k) (program : WordOracleComp SenderOperation Output) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
        (realSenderHandler k choices)) program).run (.initial, [])) =
      (ProbComp.eval (sessionProgram k program)).map (fun (out, s) =>
        (out, s, selectedBits s.tables choices)) := by
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  have h := ProbOracleComp.runWith_map_state
    (fun request (s : Session) => PMF.pure ([], s.advance k request))
    (fun request st => ProbComp.eval (realSenderHandler k choices request st))
    (fun s => (s, selectedBits s.tables choices))
    (fun request s => by
      rw [realSenderHandler_selected k choices hchoices request s]
      simp) program .initial
  simpa only [sessionProgram, ProbOracleComp.eval_run_interpret_eq_runWith, ProbComp.eval_pure,
    Session.initial, selectedBits, List.zip_nil_left, List.map_nil] using h.symm

private theorem eval_idealSenderHandler {Output : Type} (k : ℕ) (choices : List Bool)
    (program : WordOracleComp SenderOperation Output) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
        (idealSenderHandler k choices)) program).run (.initial, .idle)) =
      (ProbComp.eval (sessionProgram k program)).map (fun (out, s) =>
        (out, s, s.idealStore k choices (selectedBits s.tables choices))) := by
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  have h := ProbOracleComp.runWith_map_state
    (fun request (s : Session) => PMF.pure ([], s.advance k request))
    (fun request st => ProbComp.eval (idealSenderHandler k choices request st))
    (fun s => (s, s.idealStore k choices (selectedBits s.tables choices)))
    (fun request s => by rw [idealSenderHandler_store]; simp)
    program .initial
  simpa only [sessionProgram, ProbOracleComp.eval_run_interpret_eq_runWith, ProbComp.eval_pure,
    Session.initial, Session.idealStore, Bool.false_eq_true, ite_false] using h.symm

/-- Real execution factors through the choice-independent complete sender session. The
normal form is a consequence of actual row execution, not an assumption about the sender. -/
theorem eval_completeSenderReal {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    ProbComp.eval (completeSenderReal k program) = (do
      let (out, s) ← ProbComp.eval (sessionProgram k program)
      let choices ← PMF.uniformOfFintype (Fin k → Bool)
      pure (s.receipt,
        s.observation k (List.ofFn choices) (selectedBits s.tables (List.ofFn choices)), out)) := by
  simp only [completeSenderReal, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, Function.comp_def]
  conv_lhs =>
    arg 2
    ext c
    rw [eval_realSenderHandler k (List.ofFn c) List.length_ofFn, PMF.bind_map]
  exact PMF.bind_comm _ _ _

/-- The same complete sender session determines ideal execution. The online handler still
commits at seal, before later commands; this equality only reorders independent private coins. -/
theorem eval_completeSenderIdeal {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    ProbComp.eval (completeSenderIdeal k program) = (do
      let (out, s) ← ProbComp.eval (sessionProgram k program)
      let choices ← PMF.uniformOfFintype (Fin k → Bool)
      pure (s.receipt, Phased.observe
        (s.idealStore k (List.ofFn choices) (selectedBits s.tables (List.ofFn choices))),
        out)) := by
  simp only [completeSenderIdeal, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, BitString.uniformList, PMF.bind_map,
    eval_idealSenderHandler]
  exact PMF.bind_comm _ _ _

open scoped ENNReal

private theorem Session.disagreement_le (k : ℕ) (s : Session)
    (hs : s.sealed = true → s.tables.length = k) :
    (PMF.uniformOfFintype (Fin k → Bool)).toOuterMeasure {c |
      s.observation k (List.ofFn c) (selectedBits s.tables (List.ofFn c)) ≠
        Phased.observe (s.idealStore k (List.ofFn c) (selectedBits s.tables (List.ofFn c)))} ≤
      (2 : ℝ≥0∞)⁻¹ ^ (k - k / 2) := by
  classical
  by_cases ht : s.stopped = true
  · by_cases hc : s.sealed = true
    · have hlen := hs hc
      subst k
      let ts : Fin s.tables.length → Fin 4 → Bool := fun i => s.tables[i]
      have hts : List.ofFn ts = s.tables := List.ofFn_getElem
      have hext : s.extracted = extract ts := by
        unfold Session.extracted
        conv_lhs => arg 1; arg 2; rw [← hts]
        simpa only [List.map_ofFn, Function.comp_def] using extractPairs_ofFn ts
      have hopen (c : Fin s.tables.length → Bool) :
          openPairs (List.ofFn c) (selectedBits s.tables (List.ofFn c))
            (s.opening s.tables.length) =
          openResult c (fun i => ts i (boolPairToFin4 (false, c i)))
            (decodeOpening s.tables.length (s.opening s.tables.length)) := by
        simpa only [← selectedBits_ofFn, hts] using
          openPairs_decodeOpening c (fun i => ts i (boolPairToFin4 (false, c i)))
            (s.opening s.tables.length)
      refine (measure_mono ?_).trans
        (openResult_disagreement_le ts (decodeOpening s.tables.length (s.opening s.tables.length)))
      intro c hne
      contrapose hne
      simp only [Set.mem_ofPred_eq, not_not] at hne
      have he := congrArg (fun result : Option Bool =>
        result.elim Phased.Observation.aborted Phased.Observation.opened) hne
      by_cases hr : openResult c (fun i => ts i (boolPairToFin4 (false, c i)))
          (decodeOpening s.tables.length (s.opening s.tables.length)) = some (extract ts)
      · simp [Session.observation, Session.idealStore, ht, hc, hext, hopen, Phased.observe, hr]
      · simpa [Session.observation, Session.idealStore, ht, hc, hext, hopen,
          Phased.observe, hr] using he
    · simp [Session.observation, Session.idealStore, ht, hc, Phased.observe]
  · cases hc : s.sealed <;>
      simp [Session.observation, Session.idealStore, Session.receipt, ht, hc, Phased.observe]

/-- One complete arbitrary adversary, including all its private computation and output, admits
the majority-extraction coupling. No callback decomposition or state-growth premise occurs. -/
theorem completeSender_coupled {Output : Type} (k : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    Probability.PMF.CoupledWithin (ProbComp.eval (completeSenderReal k program))
      (ProbComp.eval (completeSenderIdeal k program)) ((2 : ℝ≥0∞)⁻¹ ^ (k - k / 2)) := by
  rw [eval_completeSenderReal, eval_completeSenderIdeal]
  let joint := do
    let (out, s) ← ProbComp.eval (sessionProgram k program)
    let c ← PMF.uniformOfFintype (Fin k → Bool)
    let received := selectedBits s.tables (List.ofFn c)
    pure ((s.receipt, s.observation k (List.ofFn c) received, out),
      (s.receipt, Phased.observe (s.idealStore k (List.ofFn c) received), out))
  refine ⟨joint, ?_, ?_, ?_⟩
  · simp [joint, PMF.map_bind]
  · simp [joint, PMF.map_bind]
  · simp only [joint, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure]
    refine (Probability.PMF.toOuterMeasure_bind_failure_le _ _ Set.univ _
      ((2 : ℝ≥0∞)⁻¹ ^ (k - k / 2)) ?_).trans
      (by simp)
    rintro ⟨out, s⟩ hs _
    change ((PMF.uniformOfFintype (Fin k → Bool)).map _).toOuterMeasure _ ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    simpa only [Set.preimage_ofPred_eq, ne_eq, Prod.mk.injEq, true_and, and_true] using
      s.disagreement_le k (sessionProgram_length k program out s hs).2

/-- A concrete growing schedule has error `2⁻ⁿ`; the existing geometric negligibility law
applies. This covers one complete sender, not composition or both corruption adapters. -/
theorem completeSender_coupled_two_mul {Output : Type} (n : ℕ)
    (program : WordOracleComp SenderOperation Output) :
    Probability.PMF.CoupledWithin (ProbComp.eval (completeSenderReal (2 * n) program))
      (ProbComp.eval (completeSenderIdeal (2 * n) program)) ((2 : ℝ≥0∞)⁻¹ ^ n) := by
  have hcount : 2 * n - (2 * n) / 2 = n := by omega
  simpa only [hcount] using completeSender_coupled (2 * n) program

end Cslib.Crypto.Protocols.MPC.OTCommitment
