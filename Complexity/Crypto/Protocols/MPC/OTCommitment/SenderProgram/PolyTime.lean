/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.SenderProgram
public import Complexity.Computability.Probabilistic.Fold
public import Complexity.Computability.Probabilistic.PPT.Capture
public import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PPT

/-!
# Uniform runtime of the corrupted-sender simulator

The input charges the unary round count and initial state. Tables use one fixed encoding of the
16-element type `Fin 4 → Bool`, and the growing transcript is an honestly encoded list. Supplied
choose, update and finish callbacks have uniform certificates on their complete inputs.

The growth premise bounds the combined round's final state on every supported choice. The
intermediate state's polynomial size is charged by fixed callback composition; it need not obey
a separate additive bound. Individually efficient callbacks alone do not bound iterated growth.

## Main results

* `senderViewProgram_isPPT`: uniform strict PPT under supported combined round growth.
* `senderClosedProgram_isPPT`: uniform strict PPT of the actual closed four-call simulator,
  including complete observations, sender state and auxiliary output.

These restrictions do not quantify over all globally PPT adversaries. A common protocol execution
contract for both corruption adapters, arbitrary scheduling, composition and full MPC remain open.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Probability Turing.MultiTapeTM Crypto.Protocols.Commitment

variable {State : Type}

private noncomputable def senderLoopStep
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State)
    (acc : ℕ × State × List (Fin 4 → Bool)) (_ : Unit) :
    ProbComp (ℕ × State × List (Fin 4 → Bool)) := do
  let (t, middle) ← choose (acc.1 - 1) acc.2.1
  return (acc.1 - 1, receive middle (), t :: acc.2.2)

private theorem senderLoop_eq
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (acc : List (Fin 4 → Bool)) :
    (List.replicate k ()).foldlM (senderLoopStep choose receive) (k, st, acc) =
      (fun (tables, final) => (0, final, tables.reverse ++ acc)) <$>
        senderViewProgram choose receive k st := by
  induction k generalizing st acc with
  | zero => simp [senderViewProgram_zero]
  | succ k ih =>
    simp only [List.replicate_succ, List.foldlM_cons, senderLoopStep,
      Nat.add_sub_cancel, bind_assoc, pure_bind, ih, senderViewProgram_succ, map_bind]
    apply congrArg (Bind.bind (choose k st))
    apply funext
    rintro ⟨t, middle⟩
    simp [List.reverse_cons, List.append_assoc]

/-- Native list transcript generation, uniformly in the unary count and charged initial state.
Only the combined round's final state needs additive growth on supported choices. -/
theorem senderViewProgram_isPPT (stateEncoding : State ↪ List Bool)
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State)
    (hchoose : IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encFinEnum (Fin 4 → Bool)) stateEncoding) (fun p => choose p.1 p.2))
    (hreceive : ComputableInPolyTime (fun st => receive st ()) stateEncoding stateEncoding)
    (growth : ℕ)
    (hgrowth : ∀ k st t middle, (t, middle) ∈ (ProbComp.eval (choose k st)).support →
      (stateEncoding (receive middle ())).length ≤ (stateEncoding st).length + growth) :
    IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encList (encFinEnum (Fin 4 → Bool))) stateEncoding)
      (fun p => senderViewProgram choose receive p.1 p.2) := by
  let tableEncoding := encFinEnum (Fin 4 → Bool)
  let accEncoding := encPair encUnary (encPair stateEncoding (encList tableEncoding))
  have hstep : IsPPTOn (encPair accEncoding (encFinite Unit)) accEncoding
      (Function.uncurry (senderLoopStep choose receive)) := by
    unfold senderLoopStep Function.uncurry
    dsimp only [accEncoding, tableEncoding]
    ppt
  have hbound : ∀ acc item, ∀ next ∈
      (ProbComp.eval (senderLoopStep choose receive acc item)).support,
      (accEncoding next).length ≤ (accEncoding acc).length + (2 * growth + 31) := by
    rintro ⟨count, st, tables⟩ _ next hnext
    simp only [senderLoopStep, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hnext
    obtain ⟨⟨t, middle⟩, ht, rfl⟩ := hnext
    have hstate := hgrowth (count - 1) st t middle ht
    have htable := length_encFinEnum_lt t
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] at htable
    simp only [accEncoding, tableEncoding, length_encPair, encUnary_apply,
      List.length_replicate, encList_cons, List.length_append, length_frame]
    omega
  have hloop : IsPPTOn (encPair encUnary stateEncoding) accEncoding
      (fun p : ℕ × State => (List.replicate p.1 ()).foldlM
        (senderLoopStep choose receive) (p.1, p.2, [])) :=
    IsPPTOn.foldlM_of_bounded_growth () (by fun_prop) (by fun_prop) hstep hbound
  have hresult := hloop.map
    (show ComputableInPolyTime
      (fun p : ℕ × State × List (Fin 4 → Bool) => (p.2.2.reverse, p.2.1))
      accEncoding (encPair (encList tableEncoding) stateEncoding) by
        dsimp only [accEncoding, tableEncoding]
        fun_prop)
  simpa [senderLoop_eq, Function.comp_def] using hresult

/-- Selected OT answers from explicitly encoded fixed-size tables and raw choice bits. -/
theorem selectedBits_polyTime :
    ComputableInPolyTime (fun p : List (Fin 4 → Bool) × List Bool => selectedBits p.1 p.2)
      (encPair (encList (encFinEnum (Fin 4 → Bool))) encBits) encBits := by
  let encTable := encFinEnum (Fin 4 → Bool)
  let encInput := encPair (encList encTable) encBits
  have hzip := (ComputableInPolyTime.zip encTable encBool).comp
    ((ComputableInPolyTime.fst (encList encTable) encBits).prod
      ((bits_encList_polyTime encBool).1.comp
        (ComputableInPolyTime.snd (encList encTable) encBits)))
  have hlookup : ComputableInPolyTime
      (fun p : (Fin 4 → Bool) × Bool => p.1 (boolPairToFin4 (false, p.2)))
      (encPair encTable encBool) encBool := .of_finite _
  exact hzip.mapToBitsWithInput (hlookup.comp (.snd encInput (encPair encTable encBool)))

/-- The complete simulator is uniformly strict PPT. The one-time finish callback can grow its
output polynomially; the extra additive premise applies only to repeated rounds. -/
theorem senderClosedProgram_isPPT {Output : Type}
    (stateEncoding : State ↪ List Bool) (outputEncoding : Output ↪ List Bool)
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output))
    (hchoose : IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encFinEnum (Fin 4 → Bool)) stateEncoding) (fun p => choose p.1 p.2))
    (hreceive : ComputableInPolyTime (fun st => receive st ()) stateEncoding stateEncoding)
    (hfinish : IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encOption (encPair encBool (encList (encPair encBool encBool)))) outputEncoding)
      (fun p => finish p.1 p.2))
    (growth : ℕ)
    (hgrowth : ∀ k st t middle, (t, middle) ∈ (ProbComp.eval (choose k st)).support →
      (stateEncoding (receive middle ())).length ≤ (stateEncoding st).length + growth) :
    IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encFinite Phased.Observation)
        (encPair (encFinite Phased.Observation) (encPair stateEncoding outputEncoding)))
      (fun p => senderClosedProgram choose receive p.1 p.2 finish) := by
  have hview := senderViewProgram_isPPT stateEncoding choose receive hchoose hreceive growth hgrowth
  have hselected := selectedBits_polyTime
  have hopen := openPairs_polyTime
  have hextract : ComputableInPolyTime
      (fun tables : List (Fin 4 → Bool) => extractPairs (tables.map fun t =>
        (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true)))))
      (encList (encFinEnum (Fin 4 → Bool))) encBool := by
    apply extractPairs_polyTime.comp
    apply ComputableInPolyTime.mapWithInput (encA := encFinEnum (Fin 4 → Bool)) .id'
    exact (ComputableInPolyTime.of_finite
      (fun t : Fin 4 → Bool =>
        (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true))))).comp (.snd _ _)
  have hobserve : ComputableInPolyTime
      (fun p : Option Bool × Bool =>
        if p.1 == some p.2 then Phased.Observation.opened p.2 else .aborted)
      (encPair (encOption encBool) encBool) (encFinite Phased.Observation) := .of_finite _
  simp only [senderClosedProgram_eq]
  apply hview.bind_with
  apply IsPPTOn.bind_with (left := encBits)
  · exact isPPTOn_sampleList.preprocess (by fun_prop)
  apply IsPPTOn.bind_with
  · exact hfinish.preprocess
      (prepare := fun p : ((ℕ × State) × (List (Fin 4 → Bool) × State)) × List Bool =>
        (p.1.1.1, p.1.2.2)) (by fun_prop)
  apply ComputableInPolyTime.isPPTOn
  let encTables := encList (encFinEnum (Fin 4 → Bool))
  let encSubmission := encOption (encPair encBool (encList (encPair encBool encBool)))
  let encContext := encPair
    (encPair (encPair encUnary stateEncoding) (encPair encTables stateEncoding)) encBits
  have hcontext := ComputableInPolyTime.fst encContext (encPair encSubmission outputEncoding)
  have hresult := ComputableInPolyTime.snd encContext (encPair encSubmission outputEncoding)
  have hchoices := hcontext.snd'
  have htables := hcontext.fst'.snd'.fst'
  have hstate := hcontext.fst'.snd'.snd'
  have hresultBit := hopen.comp
    (hchoices.prod ((hselected.comp (htables.prod hchoices)).prod hresult.fst'))
  have hobs := hobserve.comp (hresultBit.prod (hextract.comp htables))
  exact (ComputableInPolyTime.const Phased.Observation.receipt).prod
    (hobs.prod (hstate.prod hresult.snd'))

end Cslib.Crypto.Protocols.MPC.OTCommitment
