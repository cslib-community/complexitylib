/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.World
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.PolyTime
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

/-!
# Programs for the delayed-opening receiver simulation

The callbacks here are closed probabilistic programs. They cannot call the commitment world.
The common receiver recursion specializes to these programs without changing the semantic
`Receiver` interface. The prefix has no committed-bit input. A typed oracle driver performs
commit, receipt poll, open or abort, and terminal poll, and retains the full list-encoded view.

This is the same single-session fixed schedule as `receiverIdeal`. Program realization does not
by itself imply strict PPT: the separate runtime certificate requires uniformly efficient
callbacks and supported additive state growth.

## Main definitions

* `receiverOfPrograms`: semantic interpretation of program callbacks.
* `receiverCommitProgram`, `receiverViewProgram`: the common recursion and its list observation.
* `receiverPrefixProgram`, `receiverIdealProgram`: typed phased-world programs.
* `receiverClosedProgram`: close the actual finite world handler, starting idle.

## Main results

* `eval_receiverCommitProgram`, `eval_receiverViewProgram`: exact semantic interpretations.
* `eval_receiverClosedProgram_eq_real`: exact joint law of honest OT and the closed simulator.
* `receiverIdealProgram_schedule`, `receiverIdealProgram_queryBound`: exactly four actual
  public calls and an oracle-independent structural budget.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Probability Crypto.Protocols.Commitment

variable {State Later Output : Type}

/-- Interpret the supplied closed programs, retaining the existing semantic receiver interface. -/
noncomputable def receiverOfPrograms
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) : Receiver State where
  choose k st := ProbComp.eval (choose k st)
  receive st answer := ProbComp.eval (receive st answer)

/-- Program specialization of the common receiver recursion, using the existing ideal OT world. -/
noncomputable def receiverCommitProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State) :
    ProbComp ((Fin k → Bool) × (Fin k → Fin 4 × Bool) × State) :=
  receiverCommitWith choose receive (ProbComp.uniform Bool)
    (fun ts j => ot14World () (Fin.cases ts (fun _ => j))) b k st

/-- Program interpretation preserves the actual OT execution, including private receiver state. -/
theorem eval_receiverCommitProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State) :
    ProbComp.eval (receiverCommitProgram choose receive b k st) =
      receiverCommit (receiverOfPrograms choose receive) b k st := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    simp only [receiverCommitProgram, receiverCommitWith, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, receiverCommit_succ,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      receiverOfPrograms, transfer]
    exact congrArg ((ProbComp.eval (choose k st)).bind) (funext fun js =>
      congrArg ((PMF.uniformOfFintype Bool).bind) (funext fun r =>
        congrArg ((transfer (table b r) js.1).bind) (funext fun answers =>
          congrArg ((ProbComp.eval (receive js.2 (answers 1))).bind)
            (funext fun next => by rw [← receiverCommitProgram, ih]; rfl))))

/-- Bit-free receiver view with an explicit receipt list; growing transcripts are not hidden in
an unencoded function type. -/
noncomputable def receiverViewProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (k : ℕ) (st : State) :
    ProbComp (List (Fin 4 × Bool) × State) :=
  (fun (_, transcript, final) => (List.ofFn transcript, final)) <$>
    receiverCommitProgram choose receive false k st

/-- The list observation is exactly the bit-independent semantic receiver view. -/
theorem eval_receiverViewProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (k : ℕ) (st : State) :
    ProbComp.eval (receiverViewProgram choose receive k st) =
      (receiverRun (receiverOfPrograms choose receive) false k st).map
        (fun (transcript, final) => (List.ofFn transcript, final)) := by
  simp [receiverViewProgram, eval_receiverCommitProgram, receiverRun, PMF.map_comp,
    Function.comp_def]

/-- A list view has no effects at zero rounds. -/
theorem receiverViewProgram_zero
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (st : State) :
    receiverViewProgram choose receive 0 st = pure ([], st) := rfl

/-- One round of the bit-free program: arbitrary index, fresh fair answer, state update, then
remaining rounds. All four slots carry the fresh mask when the auxiliary bit is false. -/
theorem receiverViewProgram_succ
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (k : ℕ) (st : State) :
    receiverViewProgram choose receive (k + 1) st = (do
      let (j, next) ← choose k st
      let answer ← ProbComp.uniform Bool
      let next ← receive next answer
      let (rest, final) ← receiverViewProgram choose receive k next
      return ((j, answer) :: rest, final)) := by
  have answer (r : Bool) (j : Fin 4) :
      ot14Answer (Fin.cases (table false r) (fun _ => j)) 1 = r := by
    change table false r j = r
    simp [table]
  simp [receiverViewProgram, receiverCommitProgram, receiverCommitWith, ot14World,
    answer, map_bind, List.ofFn_succ]

/-- Poll a receipt and sample the private receiver view. This callable prefix has no bit input. -/
noncomputable def receiverPrefixProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (k : ℕ) (st : State) :
    ProbOracleComp (Phased.senderSpec ⊕ₒ Phased.receiverSpec)
      (Phased.Observation × List (Fin 4 × Bool) × State) := do
  let received ← ProbOracleComp.query (.inr ())
  let (transcript, final) ← ProbOracleComp.sample (receiverViewProgram choose receive k st)
  return (received, transcript, final)

/-- Four phased-world calls surround closed receiver-local computations. The plan sees only
prefix data; reconstruction uses only the later public observation. The continuation receives
that observation separately, so zero rounds still retain the opened bit. -/
noncomputable def receiverIdealProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output) :
    ProbOracleComp (Phased.senderSpec ⊕ₒ Phased.receiverSpec)
      (Phased.Observation × Phased.Observation × List (Fin 4 × Bool) ×
        State × Later × Output) := do
  ProbOracleComp.query (spec := Phased.senderSpec ⊕ₒ Phased.receiverSpec) (.inl (.commit b))
  let (received, transcript, final) ← receiverPrefixProgram choose receive k st
  let (release, later) ← ProbOracleComp.sample (plan transcript final)
  ProbOracleComp.query (spec := Phased.senderSpec ⊕ₒ Phased.receiverSpec)
    (.inl (if release then .open else .abort))
  let observed ← ProbOracleComp.query (.inr ())
  let pairs := match observed with
    | .opened bit => some (equivocatePairs bit transcript)
    | _ => none
  let out ← ProbOracleComp.sample (finish transcript final later observed pairs)
  return (received, observed, transcript, final, later, out)

/-- Closing the simulator starts the actual functionality idle and hides only its final store. -/
noncomputable def receiverClosedProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output) :
    ProbComp (Phased.Observation × Phased.Observation × List (Fin 4 × Bool) ×
      State × Later × Output) :=
  Prod.fst <$> ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) Phased.handler)
      (receiverIdealProgram choose receive b k st plan finish)).run .idle)

/-- Unfolding the actual finite handler exposes the closed local computation. The opening branch
uses the bit released by the terminal poll, and abort passes no pairs. -/
theorem receiverClosedProgram_eq
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output) :
    receiverClosedProgram choose receive b k st plan finish = (do
      let (transcript, final) ← receiverViewProgram choose receive k st
      let (release, later) ← plan transcript final
      let observed := if release then Phased.Observation.opened b else .aborted
      let pairs := if release then some (equivocatePairs b transcript) else none
      let out ← finish transcript final later observed pairs
      return (Phased.Observation.receipt, observed, transcript, final, later, out)) := by
  simp only [receiverClosedProgram, receiverIdealProgram, receiverPrefixProgram,
    OracleComp.interpret_bind, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, Phased.interpret_sample]
  simp only [StateT.run_bind, StateT.run_pure]
  simp only [StateT.lift, StateT.run, Phased.handler, OracleComp.sumHandler,
    Phased.advance, Phased.observe, bind_assoc, pure_bind, map_bind, map_pure]
  apply congrArg (Bind.bind (receiverViewProgram choose receive k st))
  apply funext
  rintro ⟨transcript, final⟩
  apply congrArg (Bind.bind (plan transcript final))
  apply funext
  rintro ⟨release, later⟩
  cases release <;> simp

/-- Exact joint interpretation in the existing phased-world driver. Explicit lists retain all
indices, answers and opening pairs; only the final functionality store is projected away. -/
theorem eval_receiverClosedProgram
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output) :
    ProbComp.eval (receiverClosedProgram choose receive b k st plan finish) =
      (receiverIdeal (receiverOfPrograms choose receive) b k st
        (fun transcript final => ProbComp.eval (plan (List.ofFn transcript) final))
        (fun transcript final later observed pairs => ProbComp.eval
          (finish (List.ofFn transcript) final later observed
            (pairs.map (fun o => List.ofFn (fun i => (o i false, o i true)))))) .idle).map
        (fun ((received, observed, transcript, final, later, out), _) =>
          (received, observed, List.ofFn transcript, final, later, out)) := by
  rw [receiverClosedProgram_eq]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, eval_receiverViewProgram,
    PMF.bind_map]
  change _ = PMF.map _ ((receiverIdeal _ _ _ _ _ _).run .idle)
  simp only [receiverIdeal, receiverPrefix, StateT.run_bind, StateT.run_pure]
  simp only [StateT.lift, StateT.run, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
    Phased.handler, OracleComp.sumHandler, Phased.advance, Phased.observe]
  apply congrArg ((receiverRun (receiverOfPrograms choose receive) false k st).bind)
  apply funext
  rintro ⟨transcript, final⟩
  apply congrArg ((ProbComp.eval (plan (List.ofFn transcript) final)).bind)
  apply funext
  rintro ⟨release, later⟩
  cases release <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    change _ = PMF.map _ (StateT.run (m := PMF) _ _)
  all_goals simp only [StateT.run_bind, StateT.run_pure]
  all_goals simp [StateT.run, StateT.lift, PMF.bind_bind, PMF.map_bind,
    equivocatePairs_ofFn]

/-- End-to-end exact simulation of honest OT, with actual retained opening masks and arbitrary
program callbacks. No final functionality state is exposed by either side. -/
theorem eval_receiverClosedProgram_eq_real
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output) :
    ProbComp.eval (receiverClosedProgram choose receive b k st plan finish) =
      (receiverReal (receiverOfPrograms choose receive) b k st
        (fun transcript final => ProbComp.eval (plan (List.ofFn transcript) final))
        (fun transcript final later observed pairs => ProbComp.eval
          (finish (List.ofFn transcript) final later observed
            (pairs.map (fun o => List.ofFn (fun i => (o i false, o i true))))))).map
        (fun (received, observed, transcript, final, later, out) =>
          (received, observed, List.ofFn transcript, final, later, out)) := by
  rw [eval_receiverClosedProgram, ← receiverIdeal_eq_real, PMF.map_comp]
  rfl

/-- Exact public schedule in the actual world's reverse-chronological transcript. Private
sampling and all four callbacks add no entries. The only choice is open versus abort. -/
theorem receiverIdealProgram_schedule
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output)
    {result : Phased.Observation × Phased.Observation × List (Fin 4 × Bool) ×
      State × Later × Output} {store : Phased.Store}
    {log : OracleComp.Transcript (Phased.senderSpec ⊕ₒ Phased.receiverSpec)}
    (h : (result, store, log) ∈ (ProbOracleComp.runWith
      (OracleComp.withTranscript Phased.world.impl)
      (receiverIdealProgram choose receive b k st plan finish) (.idle, [])).support) :
    ∃ release : Bool, log.map Sigma.fst =
      [.inr (), .inl (if release then .open else .abort), .inr (), .inl (.commit b)] := by
  simp only [receiverIdealProgram, receiverPrefixProgram,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure,
    OracleComp.withTranscript, Phased.handler, OracleComp.sumHandler,
    Phased.advance, Phased.observe,
    Probability.PMF.monad_pure_eq_pure, PMF.pure_map, PMF.pure_bind,
    PMF.bind_map, PMF.bind_bind, Function.comp_def] at h
  simp only [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨transcript, final⟩, _, ⟨release, later⟩, _, h⟩ := h
  refine ⟨release, ?_⟩
  cases release <;>
    simp only [Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at h
  all_goals obtain ⟨out, _, heq⟩ := h
  all_goals cases heq
  all_goals rfl

/-- The structural external-call budget is independent of all receiver callback runtimes and
private draws. The four calls are commit, receipt poll, release-or-abort, and terminal poll. -/
theorem receiverIdealProgram_queryBound
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output) :
    ProbOracleComp.IsQueryBounded
      (receiverIdealProgram choose receive b k st plan finish) 4 := by
  unfold receiverIdealProgram receiverPrefixProgram
  apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 3)
  intro _
  apply OracleComp.IsCostBounded.bind (n := 1) (m := 2)
  · apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 0)
    intro _
    apply (ProbOracleComp.IsQueryBounded.sample _).bind (m := 0)
    intro _
    exact .pure _ 0
  · rintro ⟨_, transcript, final⟩
    apply (ProbOracleComp.IsQueryBounded.sample _).bind (m := 2)
    rintro ⟨release, later⟩
    apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 1)
    intro _
    apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 0)
    intro observed
    apply (ProbOracleComp.IsQueryBounded.sample _).bind (m := 0)
    intro _
    exact .pure _ 0

end Cslib.Crypto.Protocols.MPC.OTCommitment
