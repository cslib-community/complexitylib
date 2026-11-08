/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Program
public import CslibFrontier.Computability.Probabilistic.Fold
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
public import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Tactic.PPT

/-!
# Uniform runtime of the receiver simulator

The round count is unary and the initial receiver state is charged input. Both receiver actions
have uniform joint-input strict-PPT certificates. Separate supported additive growth bounds cover
the intermediate state returned by `choose` and the final state returned by `receive`.
Efficient individual callbacks alone would not bound iterated state growth.

The finite OT index has constant-size encoding, while every receipt and opening pair occurs in
an explicit framed list. The loop reuses the generic probabilistic list-fold certificate; its
semantic bridge identifies it with the one common receiver recursion.

## Main results

* `receiverViewProgram_isPPT`: uniform strict PPT of the bit-free receiver view.
* `receiverClosedProgram_isPPT`: uniform strict PPT of the complete fixed-schedule simulator,
  including both public observations, retained private states and explicit transcript lists.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Probability Turing.MultiTapeTM Crypto.Protocols.Commitment

variable {State : Type}

private noncomputable def receiverLoopStep
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State)
    (acc : ℕ × State × List (Fin 4 × Bool)) (_ : Unit) :
    ProbComp (ℕ × State × List (Fin 4 × Bool)) := do
  let (j, next) ← choose (acc.1 - 1) acc.2.1
  let answer ← ProbComp.uniform Bool
  let next ← receive next answer
  return (acc.1 - 1, next, (j, answer) :: acc.2.2)

private theorem receiverLoop_eq
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (k : ℕ) (st : State)
    (acc : List (Fin 4 × Bool)) :
    (List.replicate k ()).foldlM (receiverLoopStep choose receive) (k, st, acc) =
      (fun (transcript, final) => (0, final, transcript.reverse ++ acc)) <$>
        receiverViewProgram choose receive k st := by
  induction k generalizing st acc with
  | zero => simp [receiverViewProgram_zero]
  | succ k ih =>
    simp only [List.replicate_succ, List.foldlM_cons, receiverLoopStep,
      Nat.add_sub_cancel, bind_assoc, pure_bind, ih, receiverViewProgram_succ, map_bind]
    apply congrArg (Bind.bind (choose k st))
    apply funext
    rintro ⟨j, next⟩
    apply congrArg (Bind.bind (ProbComp.uniform Bool))
    funext answer
    apply congrArg (Bind.bind (receive next answer))
    funext next
    simp [List.reverse_cons, List.append_assoc]

/-- Uniform strict PPT of the receiver's list view. The supported additive hypotheses cover
both states that can grow during a round. The initial state and unary count are actual inputs. -/
theorem receiverViewProgram_isPPT (stateEncoding : State ↪ List Bool)
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State)
    (hchoose : IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encFinEnum (Fin 4)) stateEncoding) (fun p => choose p.1 p.2))
    (hreceive : IsPPTOn (encPair stateEncoding encBool) stateEncoding
      (fun p => receive p.1 p.2))
    (chooseGrowth receiveGrowth : ℕ)
    (hchooseGrowth : ∀ k st j next, (j, next) ∈ (ProbComp.eval (choose k st)).support →
      (stateEncoding next).length ≤ (stateEncoding st).length + chooseGrowth)
    (hreceiveGrowth : ∀ st answer next,
      next ∈ (ProbComp.eval (receive st answer)).support →
      (stateEncoding next).length ≤ (stateEncoding st).length + receiveGrowth) :
    IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encList (encPair (encFinEnum (Fin 4)) encBool)) stateEncoding)
      (fun p => receiverViewProgram choose receive p.1 p.2) := by
  let receiptEncoding := encPair (encFinEnum (Fin 4)) encBool
  let accEncoding := encPair encUnary (encPair stateEncoding (encList receiptEncoding))
  have hstep : IsPPTOn (encPair accEncoding (encFinite Unit)) accEncoding
      (Function.uncurry (receiverLoopStep choose receive)) := by
    unfold receiverLoopStep Function.uncurry
    dsimp only [accEncoding, receiptEncoding]
    ppt
  have hgrowth : ∀ acc item, ∀ next ∈
      (ProbComp.eval (receiverLoopStep choose receive acc item)).support,
      (accEncoding next).length ≤ (accEncoding acc).length +
        (2 * chooseGrowth + 2 * receiveGrowth + 17) := by
    rintro ⟨count, st, receipts⟩ _ next hnext
    simp only [receiverLoopStep, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hnext
    obtain ⟨⟨j, middle⟩, hj, answer, _, final, hfinal, rfl⟩ := hnext
    have hmiddle := hchooseGrowth (count - 1) st j middle hj
    have hfinal := hreceiveGrowth middle answer final hfinal
    have hindex := length_encFinEnum_lt j
    simp only [Nat.card_fin] at hindex
    simp only [accEncoding, receiptEncoding, length_encPair, encUnary_apply,
      List.length_replicate, encList_cons, List.length_append, length_frame,
      encBool_apply, List.length_singleton]
    omega
  have hloop : IsPPTOn (encPair encUnary stateEncoding) accEncoding
      (fun p : ℕ × State => (List.replicate p.1 ()).foldlM
        (receiverLoopStep choose receive) (p.1, p.2, [])) :=
    IsPPTOn.foldlM_of_bounded_growth () (by fun_prop) (by fun_prop) hstep hgrowth
  have hresult := hloop.map
    (show ComputableInPolyTime
      (fun p : ℕ × State × List (Fin 4 × Bool) => (p.2.2.reverse, p.2.1))
      accEncoding (encPair (encList receiptEncoding) stateEncoding) by
        dsimp only [accEncoding, receiptEncoding]
        fun_prop)
  simpa [receiverLoop_eq, Function.comp_def] using hresult

/-- Uniform strict PPT of the complete closed receiver simulator. All private states, every
receipt and both observations are written to the honestly encoded output. The plan and final
continuation run once and need ordinary joint-input certificates; only the repeated callbacks
need the additional growth hypotheses. -/
theorem receiverClosedProgram_isPPT {Later Output : Type}
    (stateEncoding : State ↪ List Bool) (laterEncoding : Later ↪ List Bool)
    (outputEncoding : Output ↪ List Bool)
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State)
    (plan : List (Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : List (Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (List (Bool × Bool)) → ProbComp Output)
    (hchoose : IsPPTOn (encPair encUnary stateEncoding)
      (encPair (encFinEnum (Fin 4)) stateEncoding) (fun p => choose p.1 p.2))
    (hreceive : IsPPTOn (encPair stateEncoding encBool) stateEncoding
      (fun p => receive p.1 p.2))
    (hplan : IsPPTOn
      (encPair (encList (encPair (encFinEnum (Fin 4)) encBool)) stateEncoding)
      (encPair encBool laterEncoding) (fun p => plan p.1 p.2))
    (hfinish : IsPPTOn
      (encPair (encList (encPair (encFinEnum (Fin 4)) encBool))
        (encPair stateEncoding (encPair laterEncoding
          (encPair (encFinite Phased.Observation)
            (encOption (encList (encPair encBool encBool)))))))
      outputEncoding (fun p => finish p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (chooseGrowth receiveGrowth : ℕ)
    (hchooseGrowth : ∀ k st j next, (j, next) ∈ (ProbComp.eval (choose k st)).support →
      (stateEncoding next).length ≤ (stateEncoding st).length + chooseGrowth)
    (hreceiveGrowth : ∀ st answer next,
      next ∈ (ProbComp.eval (receive st answer)).support →
      (stateEncoding next).length ≤ (stateEncoding st).length + receiveGrowth) :
    IsPPTOn (encPair encBool (encPair encUnary stateEncoding))
      (encPair (encFinite Phased.Observation) (encPair (encFinite Phased.Observation)
        (encPair (encList (encPair (encFinEnum (Fin 4)) encBool))
          (encPair stateEncoding (encPair laterEncoding outputEncoding)))))
      (fun p => receiverClosedProgram choose receive p.1 p.2.1 p.2.2 plan finish) := by
  have hview := receiverViewProgram_isPPT stateEncoding choose receive hchoose hreceive
    chooseGrowth receiveGrowth hchooseGrowth hreceiveGrowth
  have hopen := equivocatePairs_polyTime
  have hobs : ComputableInPolyTime
      (fun p : Bool × Bool => if p.1 then Phased.Observation.opened p.2 else .aborted)
      (encPair encBool encBool) (encFinite Phased.Observation) := .of_finite _
  simp only [receiverClosedProgram_eq]
  ppt

end Cslib.Crypto.Protocols.MPC.OTCommitment
