/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.CompleteSender
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.SenderProgram.PolyTime
public import CslibFrontier.Computability.Probabilistic.OracleSimulation
public import CslibFrontier.Computability.Probabilistic.QueryBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Native complete-sender execution

The adversary is one globally certified word-oracle program. Its actual input contains the unary
round count and charged auxiliary input. Only the session handler has a storage-growth proof;
there is no premise about intermediate states or callbacks inside the adversary.

## Main definitions

* `encSession`: honest list encoding of the retained tables and first opening attempt.

## Main results

* `sessionProgram_isPPT`: efficient interpretation of a complete adversary with constant replies.
* `completeSender_isPPT`: both actual complete executions are strict PPT, including full output.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Probability Turing.MultiTapeTM Crypto.Protocols.Commitment

/-- Encoding of a single-session state as the tuple of its fields: the tables as a list of
`Fin 4 → Bool` values (each framed), the sealed and stopped flags, then the first opening attempt as
an optional framed pair of a bit and a bit word. The fixed table carrier and every byte of the
unbounded opening word are charged. -/
enc_structure encSession : Session where
  tables : (encList (encFinEnum (Fin 4 → Bool))), sealed : encBool, stopped : encBool,
  submission : (encOption (encPair encBool encBits))

private theorem sessionAdvance_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × (SenderOperation × List Bool) × Session => p.2.2.advance p.1 p.2.1)
      (encPair encUnary (encPair (encPair (encFinite SenderOperation) encBits) encSession))
      encSession := by
  refine ComputableInPolyTime.finite_cases
    (tag := fun p : ℕ × (SenderOperation × List Bool) × Session => p.2.1.1)
    (branch := fun op p => p.2.2.advance p.1 (op, p.2.1.2))
    (show ComputableInPolyTime _ _ (encFinite SenderOperation) by fun_prop) ?_
  intro op
  cases op <;> unfold Session.advance <;> fun_prop

private theorem sessionAdvance_length (k : ℕ) (request : SenderOperation × List Bool)
    (s : Session) :
    (encSession (s.advance k request)).length ≤
      (encSession s).length + 2 * request.2.length + 64 := by
  rcases request with ⟨op, word⟩
  cases hs : s.stopped <;> cases hc : s.sealed <;> cases op <;>
    simp only [Session.advance, hs, hc, Bool.false_eq_true, ite_false, ite_true]
  all_goals first
    | omega
    | (try split) <;>
        simp only [encSession_apply, length_encPair,
          encBool_apply, List.length_cons, List.length_nil, encOption_none, encOption_some,
          encBits_apply,
          encList_append, encList_cons, encList_nil, List.length_append, length_frame]
  all_goals try omega
  all_goals
    rename_i values hlt
    have h := length_encFinEnum_lt values
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    omega

/-- A complete globally oracle-PPT sender is efficient under the real constant-reply interface.
The unary round count is part of the actual adversary input. No local adversary-state bound is
assumed: the global certificate already charges all of its internal computation and queries. -/
theorem sessionProgram_isPPT {Input Output : Type}
    (input : Input ↪ List Bool) (output : Output ↪ List Bool)
    (program : (ℕ × Input) → WordOracleComp SenderOperation Output)
    (hprogram : IsOraclePPTOn (encPair encUnary input) output program) :
    IsPPTOn (encPair encUnary input) (encPair output encSession)
      (fun p => sessionProgram p.1 (program p)) := by
  apply hprogram.run_interpret_preprocess
    (operationEncoding := encFinite SenderOperation)
    (prepare := id) (initial := fun _ => Session.initial)
    (resources := fun _ word => 2 * word.length + 64)
    (by fun_prop) ?_ (by fun_prop) (fun _ _ => True) (by simp) (by fun_prop) ?_
  · apply ComputableInPolyTime.isPPTOn
    exact (ComputableInPolyTime.const ([] : List Bool)).prod
      (sessionAdvance_polyTime.comp (g := fun p :
        (ℕ × Input) × (SenderOperation × List Bool) × Session => (p.1.1, p.2)) (by fun_prop))
  · intro a request state _ result hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    refine ⟨trivial, by simp, ?_⟩
    simpa only [Nat.add_assoc] using sessionAdvance_length a.1 request state

private theorem sessionOpening_polyTime :
    ComputableInPolyTime (fun p : ℕ × Session => p.2.opening p.1)
      (encPair encUnary encSession)
      (encOption (encPair encBool (encList (encPair encBool encBool)))) := by
  let encInput := encPair encUnary encSession
  let encSubmission := encPair encBool encBits
  have hinput := ComputableInPolyTime.fst encInput encSubmission
  have hvalue := ComputableInPolyTime.snd encInput encSubmission
  have hcount := (ComputableInPolyTime.fst encUnary encSession).comp hinput
  have hbit := (ComputableInPolyTime.fst encBool encBits).comp hvalue
  have hword := (ComputableInPolyTime.snd encBool encBits).comp hvalue
  have htake := ComputableInPolyTime.bitsToList.comp
    (ComputableInPolyTime.bitsTakeWithInput hword hcount)
  have hdrop := ComputableInPolyTime.bitsToList.comp
    (ComputableInPolyTime.bitsDropWithInput hword hcount)
  have hpairs := (ComputableInPolyTime.zip encBool encBool).comp (htake.prod hdrop)
  have hlength := (ComputableInPolyTime.length_bits.comp hword).decide_eq'
    (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hcount))
  have hbody := hlength.ite_decide
    ((ComputableInPolyTime.optionSome (encPair encBool (encList (encPair encBool encBool)))).comp
      (hbit.prod hpairs)) (ComputableInPolyTime.const none)
  unfold Session.opening
  convert ComputableInPolyTime.optionElimWithInput
    (body := fun p value => if value.2.length = 2 * p.1 then
      some (value.1, (value.2.take p.1).zip (value.2.drop p.1)) else none)
    (encSession_submission_polyTime (ComputableInPolyTime.snd encUnary encSession))
    (ComputableInPolyTime.const none) (by simpa only [Function.comp_def] using hbody) using 1
  funext p
  dsimp only [Function.comp_def]
  cases p.2.submission with
  | none => rfl
  | some value => cases value; rfl

private theorem sessionExtracted_polyTime :
    ComputableInPolyTime Session.extracted encSession encBool := by
  apply extractPairs_polyTime.comp
  apply ComputableInPolyTime.mapWithInput (encA := encFinEnum (Fin 4 → Bool))
    (encSession_tables_polyTime ComputableInPolyTime.id')
  exact (ComputableInPolyTime.of_finite
    (fun t : Fin 4 → Bool =>
      (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true))))).comp (.snd _ _)

private theorem sessionView_polyTime (ideal : Bool) :
    ComputableInPolyTime (fun p : ℕ × List Bool × Session =>
      (p.2.2.receipt, if ideal then
        Phased.observe (p.2.2.idealStore p.1 p.2.1 (selectedBits p.2.2.tables p.2.1))
      else p.2.2.observation p.1 p.2.1 (selectedBits p.2.2.tables p.2.1)))
      (encPair encUnary (encPair encBits encSession))
      (encPair (encFinite Phased.Observation) (encFinite Phased.Observation)) := by
  let encInput := encPair encUnary (encPair encBits encSession)
  have hcount := ComputableInPolyTime.fst encUnary (encPair encBits encSession)
  have hchoices := (ComputableInPolyTime.snd encUnary (encPair encBits encSession)).fst'
  have hstate := (ComputableInPolyTime.snd encUnary (encPair encBits encSession)).snd'
  have hreceived := selectedBits_polyTime.comp ((encSession_tables_polyTime hstate).prod hchoices)
  have hopening := sessionOpening_polyTime.comp (hcount.prod hstate)
  have hresult := openPairs_polyTime.comp (hchoices.prod (hreceived.prod hopening))
  have hsealed := encSession_sealed_polyTime hstate
  have hstopped := encSession_stopped_polyTime hstate
  have hextracted := sessionExtracted_polyTime.comp hstate
  have hreceipt : ComputableInPolyTime
      (fun sealed : Bool => if sealed then Phased.Observation.receipt else .idle)
      encBool (encFinite Phased.Observation) := .of_finite _
  have hterminal : ComputableInPolyTime
      (fun p : Bool × Bool × Option Bool × Bool =>
        if ideal then Phased.observe (if p.2.1 then
          if p.1 && (p.2.2.1 == some p.2.2.2) then .opened p.2.2.2 else .aborted
        else if p.1 then .committed p.2.2.2 else .idle)
        else if p.2.1 then if p.1 then p.2.2.1.elim .aborted .opened else .aborted
        else if p.1 then .receipt else .idle)
      (encPair encBool (encPair encBool (encPair (encOption encBool) encBool)))
      (encFinite Phased.Observation) := .of_finite _
  exact (hreceipt.comp hsealed).prod
    (hterminal.comp (hsealed.prod (hstopped.prod (hresult.prod hextracted))))

private noncomputable def completeSenderPost {Input Output : Type} (ideal : Bool)
    (program : (ℕ × Input) → WordOracleComp SenderOperation Output) (p : ℕ × Input) :
    ProbComp (Phased.Observation × Phased.Observation × Output) := do
  let (out, s) ← sessionProgram p.1 (program p)
  let choices ← BitString.sampleList p.1
  return (s.receipt, if ideal then
    Phased.observe (s.idealStore p.1 choices (selectedBits s.tables choices))
    else s.observation p.1 choices (selectedBits s.tables choices), out)

private theorem completeSenderPost_isPPT {Input Output : Type} (ideal : Bool)
    (input : Input ↪ List Bool) (output : Output ↪ List Bool)
    (program : (ℕ × Input) → WordOracleComp SenderOperation Output)
    (hprogram : IsOraclePPTOn (encPair encUnary input) output program) :
    IsPPTOn (encPair encUnary input)
      (encPair (encFinite Phased.Observation) (encPair (encFinite Phased.Observation) output))
      (completeSenderPost ideal program) := by
  unfold completeSenderPost
  apply (sessionProgram_isPPT input output program hprogram).bind_with
  apply IsPPTOn.bind_with (left := encBits)
  · exact isPPTOn_sampleList.preprocess
      (prepare := fun p : (ℕ × Input) × (Output × Session) => p.1.1) (by fun_prop)
  apply ComputableInPolyTime.isPPTOn
  have hprepare : ComputableInPolyTime
      (fun p : ((ℕ × Input) × (Output × Session)) × List Bool =>
        (p.1.1.1, p.2, p.1.2.2))
      (encPair (encPair (encPair encUnary input) (encPair output encSession)) encBits)
      (encPair encUnary (encPair encBits encSession)) := by fun_prop
  have hview := (sessionView_polyTime ideal).comp hprepare
  exact hview.fst'.prod (hview.snd'.prod (by fun_prop))

/-- Both actual complete executions are uniformly strict PPT from the adversary's existing
global certificate alone. Unary `k`, all auxiliary input, query words, internal computation,
the honest handler's storage and the complete output are charged. -/
theorem completeSender_isPPT {Input Output : Type}
    (input : Input ↪ List Bool) (output : Output ↪ List Bool)
    (program : (ℕ × Input) → WordOracleComp SenderOperation Output)
    (hprogram : IsOraclePPTOn (encPair encUnary input) output program) :
    IsPPTOn (encPair encUnary input)
        (encPair (encFinite Phased.Observation) (encPair (encFinite Phased.Observation) output))
        (fun p => completeSenderReal p.1 (program p)) ∧
      IsPPTOn (encPair encUnary input)
        (encPair (encFinite Phased.Observation) (encPair (encFinite Phased.Observation) output))
        (fun p => completeSenderIdeal p.1 (program p)) := by
  constructor
  · refine (completeSenderPost_isPPT false input output program hprogram).congr fun p => ?_
    simp [completeSenderPost, eval_completeSenderReal, ProbComp.eval_bind,
      BitString.eval_sampleList, BitString.uniformList, PMF.map, PMF.bind_bind, Function.comp_def]
  · refine (completeSenderPost_isPPT true input output program hprogram).congr fun p => ?_
    simp [completeSenderPost, eval_completeSenderIdeal, ProbComp.eval_bind,
      BitString.eval_sampleList, BitString.uniformList, PMF.map, PMF.bind_bind, Function.comp_def]

end Cslib.Crypto.Protocols.MPC.OTCommitment
