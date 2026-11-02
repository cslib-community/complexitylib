/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower

/-!
# Native controller routines for inductive counting

The certificates charge the full encoded arguments and apply to every state, including malformed
register contents. Width is supplied in unary: writing the binary register bound `2 ^ width`
then takes only linear space in that argument.

Unary conversion and fixed-list dispatch use the plain charged-space calculus.

## Main results

* `Turing.InductiveCounting.instruction_budget`: the local controller instruction.
* `Turing.InductiveCounting.advance_budget`: the instruction with storage and rank checks.
* `Turing.InductiveCounting.advance_inSpace`: the complete routine on its encoded input tuple.
* `Turing.InductiveCounting.query_budget`: the explicit edge or bad-vertex request.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM ComputableInSpace Cslib.InductiveCounting

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

/-- Converting a unary counter to binary needs only linear space. -/
theorem unaryToBinary_inSpace :
    ComputableInSpace (fun n : ℕ => n) encUnary encNat fun n => (encUnary n).length := by
  have hlist : ComputableInSpace (fun n : ℕ => List.replicate n true)
      encUnary encBits fun n => (encUnary n).length :=
    of_inO (.of_linear (.of_eq fun _ => rfl))
  have hstep : ComputableInSpace (fun p : ℕ × Bool => p.1 + 1)
      (encPair encNat encBool) encNat fun p => (encPair encNat encBool p).length :=
    budget_natSucc (fst _ _)
  have h := foldl (encA := encBool) (encL := encBits) (step := fun n _ => n + 1)
    hlist (const 0) hstep
    (Q := fun n => 2 * n + 2) (B := fun n => n)
    (fun n i hi => by
      simp only [List.foldl_const, List.length_take, List.length_replicate,
        ComputableInO.iterate_succ_eq, zero_add, length_encPair, encBool_apply,
        List.length_singleton]
      have := length_encNat_le_self (min i n)
      omega)
    (fun n i hi => by
      simp only [List.foldl_const, List.length_take, List.length_replicate,
        ComputableInO.iterate_succ_eq, zero_add]
      exact (length_encNat_le_self _).trans (Nat.min_le_right _ _))
  refine (h.weaken (.of_le_linear 6 6 fun n => ?_)).of_enc_eq fun n => ?_
  · simp only [encUnary_apply, encBits_apply, List.length_replicate]
    have := length_encNat_le_self n
    omega
  · simp [List.foldl_const, ComputableInO.iterate_succ_eq]

/-- Binary powers of two from unary exponents, without an exponential unary intermediate. -/
theorem unaryTwoPow_inSpace :
    ComputableInSpace (fun n : ℕ => 2 ^ n) encUnary encNat
      fun n => (encUnary n).length := by
  simpa only [encUnary_apply, List.length_replicate] using
    (of_inO (ComputableInDegree.two_pow_length encUnary).inO_one)

/-- Reading the encoded product underlying a controller state. -/
theorem stateData_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => stateData (s a)) enc
      (encPair encNat (encPair (encList encNat) (encPair encBool encBool))) S :=
  hs.of_enc_eq fun _ => rfl

/-- Reading the finite instruction label as its fixed natural code. -/
theorem phaseCode_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => phaseCode (s a).phase) enc encNat S :=
  (stateData_budget hs).fst'

/-- Reading the ten binary registers. -/
theorem registers_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => registers (s a)) enc (encList encNat) S :=
  (stateData_budget hs).snd'.fst'

/-- Reading the predicate flag. -/
theorem hit_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).hit) enc encBool S :=
  (stateData_budget hs).snd'.snd'.fst'

/-- Reading the final-scan flag. -/
theorem finalScan_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).finalScan) enc encBool S :=
  (stateData_budget hs).snd'.snd'.snd'

/-- A fixed register projection preserves the common budget. -/
theorem register_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) (i : ℕ) :
    ComputableInSpace (fun a => ((registers (s a)).drop i).headD 0) enc encNat S := by
  have hdrop : ∀ i, ComputableInSpace
      (fun a => (registers (s a)).drop i) enc (encList encNat) S := by
    intro i
    induction i with
    | zero => exact registers_budget hs
    | succ i ih => simpa only [List.tail_drop] using budget_tail ih
  exact budget_headD 0 (hdrop i)

private theorem and_budget {f g : α → Bool}
    (hf : ComputableInSpace f enc encBool S)
    (hg : ComputableInSpace g enc encBool S) :
    ComputableInSpace (fun a => f a && g a) enc encBool S :=
  budget_finite (fun p : Bool × Bool => p.1 && p.2) (budget_prod hf hg)

private theorem or_budget {f g : α → Bool}
    (hf : ComputableInSpace f enc encBool S)
    (hg : ComputableInSpace g enc encBool S) :
    ComputableInSpace (fun a => f a || g a) enc encBool S :=
  budget_finite (fun p : Bool × Bool => p.1 || p.2) (budget_prod hf hg)

private theorem dispatch_budget {κ β : Type} {encB : β ↪ List Bool}
    (l : List κ) (d : κ) (F : κ → α → β)
    (hF : ∀ p, ComputableInSpace (F p) enc encB S) {i : α → ℕ}
    (hi : ComputableInSpace i enc encNat S)
    (_hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => F (l.getD (i a) d) a) enc encB S := by
  induction l generalizing i with
  | nil => simpa using hF d
  | cons p l ih =>
    refine (budget_ite (budget_natIsZero hi) (hF p) (ih (budget_natPred hi))).of_enc_eq
      fun a => ?_
    rcases i a with _ | n <;> simp

/-- Case distinction on the finite phase, retaining an arbitrary common budget. -/
theorem phaseCases_budget {β : Type} {encB : β ↪ List Bool} {s : α → State}
    (hs : ComputableInSpace s enc encState S) (F : Phase → α → β)
    (hF : ∀ p, ComputableInSpace (F p) enc encB S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => F (s a).phase a) enc encB S := by
  refine (dispatch_budget
    [.round, .target, .candidate, .walk, .guess, .edge, .observe, .done, .accept, .reject]
    .reject F hF (phaseCode_budget hs) hin).of_enc_eq fun a => ?_
  cases (s a).phase <;> rfl

/-- Constructing a state from its finite label, ten binary registers and two flags. -/
theorem state_budget {s : α → State}
    (hp : ComputableInSpace (fun a => phaseCode (s a).phase) enc encNat S)
    (hround : ComputableInSpace (fun a => (s a).round) enc encNat S)
    (hcount : ComputableInSpace (fun a => (s a).count) enc encNat S)
    (htarget : ComputableInSpace (fun a => (s a).target) enc encNat S)
    (hnext : ComputableInSpace (fun a => (s a).nextCount) enc encNat S)
    (hcandidate : ComputableInSpace (fun a => (s a).candidate) enc encNat S)
    (hselected : ComputableInSpace (fun a => (s a).selected) enc encNat S)
    (hremaining : ComputableInSpace (fun a => (s a).remaining) enc encNat S)
    (hcurrent : ComputableInSpace (fun a => (s a).current) enc encNat S)
    (hguess : ComputableInSpace (fun a => (s a).guess) enc encNat S)
    (hbits : ComputableInSpace (fun a => (s a).bits) enc encNat S)
    (hhit : ComputableInSpace (fun a => (s a).hit) enc encBool S)
    (hfinal : ComputableInSpace (fun a => (s a).finalScan) enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace s enc encState S := by
  have hregs := budget_cons hround (budget_cons hcount (budget_cons htarget
    (budget_cons hnext (budget_cons hcandidate (budget_cons hselected
    (budget_cons hremaining (budget_cons hcurrent (budget_cons hguess
    (budget_cons hbits (budget_const [] hin))))))))))
  exact (budget_prod hp (budget_prod hregs (budget_prod hhit hfinal))).of_enc_eq fun _ => rfl

/-- Reading the `round` register preserves the common budget. -/
theorem round_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).round) enc encNat S :=
  (register_budget hs 0).of_enc_eq fun _ => rfl

/-- Reading the `count` register preserves the common budget. -/
theorem count_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).count) enc encNat S :=
  (register_budget hs 1).of_enc_eq fun _ => rfl

/-- Reading the `target` register preserves the common budget. -/
theorem target_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).target) enc encNat S :=
  (register_budget hs 2).of_enc_eq fun _ => rfl

/-- Reading the `nextCount` register preserves the common budget. -/
theorem nextCount_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).nextCount) enc encNat S :=
  (register_budget hs 3).of_enc_eq fun _ => rfl

/-- Reading the `candidate` register preserves the common budget. -/
theorem candidate_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).candidate) enc encNat S :=
  (register_budget hs 4).of_enc_eq fun _ => rfl

/-- Reading the `selected` register preserves the common budget. -/
theorem selected_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).selected) enc encNat S :=
  (register_budget hs 5).of_enc_eq fun _ => rfl

/-- Reading the `remaining` register preserves the common budget. -/
theorem remaining_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).remaining) enc encNat S :=
  (register_budget hs 6).of_enc_eq fun _ => rfl

/-- Reading the `current` register preserves the common budget. -/
theorem current_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).current) enc encNat S :=
  (register_budget hs 7).of_enc_eq fun _ => rfl

/-- Reading the `guess` register preserves the common budget. -/
theorem guess_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).guess) enc encNat S :=
  (register_budget hs 8).of_enc_eq fun _ => rfl

/-- Reading the `bits` register preserves the common budget. -/
theorem bits_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S) :
    ComputableInSpace (fun a => (s a).bits) enc encNat S :=
  (register_budget hs 9).of_enc_eq fun _ => rfl

private theorem iteProp_budget {c : α → Prop} [DecidablePred c] {β : Type}
    {encB : β ↪ List Bool} {f g : α → β}
    (hc : ComputableInSpace (fun a => decide (c a)) enc encBool S)
    (hf : ComputableInSpace f enc encB S)
    (hg : ComputableInSpace g enc encB S) :
    ComputableInSpace (fun a => if c a then f a else g a) enc encB S := by
  exact (budget_ite hc hf hg).of_enc_eq fun a => by simp

private theorem natBEq_budget {f g : α → ℕ}
    (hf : ComputableInSpace f enc encNat S)
    (hg : ComputableInSpace g enc encNat S) :
    ComputableInSpace (fun a => f a == g a) enc encBool S :=
  (budget_natEq hf hg).of_enc_eq fun a => by
    congr 1

private theorem toNat_budget {f : α → Bool}
    (hf : ComputableInSpace f enc encBool S) :
    ComputableInSpace (fun a => (f a).toNat) enc encNat S :=
  budget_finite Bool.toNat hf

private theorem not_budget {f : α → Bool}
    (hf : ComputableInSpace f enc encBool S) :
    ComputableInSpace (fun a => !(f a)) enc encBool S :=
  budget_finite Bool.not hf

/-- Halt detection reads only the finite phase. -/
theorem halted_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => halted (s a)) enc encBool S := by
  refine (phaseCases_budget hs (fun p _ => p == .accept || p == .reject)
    (fun p => budget_const _ hin) hin).of_enc_eq fun _ => rfl

/-- Acceptance detection reads only the finite phase. -/
theorem accepting_budget {s : α → State}
    (hs : ComputableInSpace s enc encState S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => (s a).phase == .accept) enc encBool S :=
  phaseCases_budget hs (fun p _ => p == .accept) (fun _ => budget_const _ hin) hin

variable {N width source : α → ℕ} {s : α → State} {answer choice : α → Bool}

/-- A unary width can also be used as a binary register in the same budget. -/
theorem widthBinary_budget (hw : ComputableInSpace width enc encUnary S) :
    ComputableInSpace width enc encNat S :=
  budget_comp_linear (f := width) unaryToBinary_inSpace hw

/-- The complete register bound, with unary width, uses linear space on all inputs. -/
theorem registerBound_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encUnary S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => registerBound (N a) (width a)) enc encNat S :=
  budget_natAdd (budget_natAdd (budget_natAdd hN
    (budget_comp_linear unaryTwoPow_inSpace hw)) (widthBinary_budget hw))
    (budget_const 2 hin)

/-- A native certificate for the underlying local instruction, with no validity assumption. -/
theorem instruction_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encNat S)
    (hsource : ComputableInSpace source enc encNat S)
    (hs : ComputableInSpace s enc encState S)
    (hanswer : ComputableInSpace answer enc encBool S)
    (hchoice : ComputableInSpace choice enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace
      (fun a => instruction (N a) (width a) (source a) (s a) (answer a) (choice a))
      enc encState S := by
  have h_round := round_budget hs
  have h_count := count_budget hs
  have h_target := target_budget hs
  have h_nextCount := nextCount_budget hs
  have h_candidate := candidate_budget hs
  have h_selected := selected_budget hs
  have h_remaining := remaining_budget hs
  have h_current := current_budget hs
  have h_guess := guess_budget hs
  have h_bits := bits_budget hs
  have h_hit := hit_budget hs
  have h_finalScan := finalScan_budget hs
  have hguessStep := budget_natAdd (budget_natMul (budget_const 2 hin) h_guess)
    (toNat_budget hchoice)
  have hhitStep := or_budget (or_budget h_hit hanswer)
    (and_budget (not_budget h_finalScan) (natBEq_budget h_candidate h_target))
  have hbranches (p : Phase) : ComputableInSpace
      (fun a => instruction (N a) (width a) (source a)
        { s a with phase := p } (answer a) (choice a)) enc encState S := by
    cases p with
    | round =>
      exact (iteProp_budget (budget_natLt (budget_natSucc h_round) hN)
        (state_budget (budget_const 1 hin)
          h_round h_count (budget_const 0 hin) (budget_const 0 hin) h_candidate h_selected
            h_remaining h_current h_guess h_bits h_hit (budget_const false hin) hin)
        (state_budget (budget_const 2 hin)
          h_round h_count h_target h_nextCount (budget_const 0 hin) (budget_const 0 hin)
            h_remaining h_current h_guess h_bits (budget_const false hin) (budget_const true hin)
            hin))
    | target =>
      exact (iteProp_budget (budget_natLt h_target hN)
        (state_budget (budget_const 2 hin)
          h_round h_count h_target h_nextCount (budget_const 0 hin) (budget_const 0 hin)
            h_remaining h_current h_guess h_bits (budget_const false hin) h_finalScan hin)
        (state_budget (budget_const 0 hin)
          (budget_natSucc h_round) h_nextCount h_target h_nextCount h_candidate h_selected
            h_remaining h_current h_guess h_bits h_hit h_finalScan hin))
    | candidate =>
      exact (iteProp_budget (budget_natLt h_candidate hN)
        (budget_ite hchoice
        (state_budget (budget_const 3 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_round hsource h_guess
            h_bits h_hit h_finalScan hin)
        (state_budget (budget_const 2 hin)
          h_round h_count h_target h_nextCount (budget_natSucc h_candidate) h_selected h_remaining
            h_current h_guess h_bits h_hit h_finalScan hin))
        (state_budget (budget_const 7 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
            h_guess h_bits h_hit h_finalScan hin))
    | walk =>
      exact (iteProp_budget (budget_natIsZero h_remaining)
        (iteProp_budget (budget_natEq h_current h_candidate)
        (state_budget (budget_const 6 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
            h_guess h_bits h_hit h_finalScan hin)
        (budget_const reject hin))
        (state_budget (budget_const 4 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
            (budget_const 0 hin) hw h_hit h_finalScan hin))
    | guess =>
      exact (iteProp_budget (budget_natIsZero h_bits)
        (iteProp_budget (budget_natLt h_guess hN)
        (state_budget (budget_const 5 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
            h_guess h_bits h_hit h_finalScan hin)
        (budget_const reject hin))
        (state_budget (budget_const 4 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
          hguessStep (budget_natPred h_bits) h_hit h_finalScan hin))
    | edge =>
      exact (budget_ite (or_budget (natBEq_budget h_current h_guess) hanswer)
        (state_budget (budget_const 3 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected (budget_natPred h_remaining)
            h_guess h_guess h_bits h_hit h_finalScan hin)
        (budget_const reject hin))
    | observe =>
      exact (state_budget (budget_const 2 hin)
          h_round h_count h_target h_nextCount (budget_natSucc h_candidate)
          (budget_natSucc h_selected) h_remaining h_current h_guess h_bits
          hhitStep h_finalScan hin)
    | done =>
      exact (iteProp_budget (budget_natEq h_selected h_count)
        (budget_ite h_finalScan
        (budget_ite h_hit
        (budget_const reject hin)
        (budget_const accept hin))
        (state_budget (budget_const 1 hin)
          h_round h_count (budget_natSucc h_target)
            (budget_natAdd h_nextCount (toNat_budget h_hit)) h_candidate h_selected h_remaining
            h_current h_guess h_bits h_hit h_finalScan hin))
        (budget_const reject hin))
    | accept =>
      exact (state_budget (budget_const 8 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
            h_guess h_bits h_hit h_finalScan hin)
    | reject =>
      exact (state_budget (budget_const 9 hin)
          h_round h_count h_target h_nextCount h_candidate h_selected h_remaining h_current
            h_guess h_bits h_hit h_finalScan hin)
  refine (phaseCases_budget hs _ hbranches hin).of_enc_eq fun a => ?_
  cases s a
  rfl

/-- The candidate cost is a fixed arithmetic expression in the supplied parameters. -/
theorem candidateCost_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => candidateCost (N a) (width a)) enc encNat S :=
  budget_natAdd (budget_natMul hN (budget_natAdd hw (budget_const 3 hin))) (budget_const 4 hin)

/-- The target cost uses a fixed number of binary arithmetic operations. -/
theorem targetCost_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => targetCost (N a) (width a)) enc encNat S :=
  budget_natAdd (budget_natMul (budget_natSucc hN) (candidateCost_budget hN hw hin))
    (budget_const 6 hin)

/-- The round cost uses a fixed number of binary arithmetic operations. -/
theorem roundCost_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => roundCost (N a) (width a)) enc encNat S :=
  budget_natAdd (budget_natMul (budget_natSucc hN) (targetCost_budget hN hw hin))
    (budget_const 2 hin)

/-- The full progress measure is computed in the common budget on arbitrary states. -/
theorem rank_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encNat S)
    (hs : ComputableInSpace s enc encState S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => rank (N a) (width a) (s a)) enc encNat S := by
  have hc := candidateCost_budget hN hw hin
  have ht := targetCost_budget hN hw hin
  have hr := roundCost_budget hN hw hin
  have h_round := round_budget hs
  have h_target := target_budget hs
  have h_candidate := candidate_budget hs
  have h_remaining := remaining_budget hs
  have h_bits := bits_budget hs
  have h_finalScan := finalScan_budget hs
  have hbranches (p : Phase) : ComputableInSpace
      (fun a => rank (N a) (width a) { s a with phase := p }) enc encNat S := by
    have hb := budget_ite h_finalScan (budget_const (encB := encNat) 0 hin)
      (budget_natAdd
        (budget_natMul (budget_natPred (budget_natSub hN h_round)) hr)
        (budget_natMul (budget_natPred (budget_natSub hN h_target)) ht))
    have hu := budget_natMul (budget_natPred (budget_natSub hN h_candidate)) hc
    have hw3 := budget_natAdd hw (budget_const 3 hin)
    cases p with
    | round =>
      exact budget_natAdd (budget_natMul (budget_natSub hN h_round) hr) (budget_const 1 hin)
    | target =>
      exact budget_natAdd (budget_natAdd
        (budget_natMul (budget_natPred (budget_natSub hN h_round)) hr)
        (budget_natMul (budget_natSub hN h_target) ht)) (budget_const 2 hin)
    | candidate =>
      exact budget_natAdd (budget_natAdd hb
        (budget_natMul (budget_natSub hN h_candidate) hc)) (budget_const 4 hin)
    | walk =>
      exact budget_natAdd (budget_natAdd (budget_natAdd hb hu)
        (budget_natMul h_remaining hw3)) (budget_const 6 hin)
    | guess =>
      exact budget_natAdd (budget_natAdd (budget_natAdd (budget_natAdd hb hu)
        (budget_natMul (budget_natPred h_remaining) hw3)) h_bits) (budget_const 8 hin)
    | edge =>
      exact budget_natAdd (budget_natAdd (budget_natAdd hb hu)
        (budget_natMul (budget_natPred h_remaining) hw3)) (budget_const 7 hin)
    | observe => exact budget_natAdd (budget_natAdd hb hu) (budget_const 5 hin)
    | done => exact budget_natAdd hb (budget_const 3 hin)
    | accept => exact budget_const 0 hin
    | reject => exact budget_const 0 hin
  refine (phaseCases_budget hs _ hbranches hin).of_enc_eq fun a => ?_
  cases s a
  rfl

/-- All ten storage checks are executable within the budget, including on malformed states. -/
theorem bounded_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encUnary S)
    (hs : ComputableInSpace s enc encState S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => decide (Bounded (N a) (width a) (s a)))
      enc encBool S := by
  have hB := registerBound_budget hN hw hin
  have h := and_budget (budget_natLt (round_budget hs) hB)
    (and_budget (budget_natLt (count_budget hs) hB)
    (and_budget (budget_natLt (target_budget hs) hB)
    (and_budget (budget_natLt (nextCount_budget hs) hB)
    (and_budget (budget_natLt (candidate_budget hs) hB)
    (and_budget (budget_natLt (selected_budget hs) hB)
    (and_budget (budget_natLt (remaining_budget hs) hB)
    (and_budget (budget_natLt (current_budget hs) hB)
    (and_budget (budget_natLt (guess_budget hs) hB)
    (budget_natLt (bits_budget hs) hB)))))))))
  exact h.of_enc_eq fun a => by
    congr 1

/-- One checked controller step: this certificate includes both the complete storage test and
the comparison of the old and new ranks. Width is unary, so the bound remains linear on all
arguments, without any register-validity hypothesis. -/
theorem advance_budget (hN : ComputableInSpace N enc encNat S)
    (hw : ComputableInSpace width enc encUnary S)
    (hsource : ComputableInSpace source enc encNat S)
    (hs : ComputableInSpace s enc encState S)
    (hanswer : ComputableInSpace answer enc encBool S)
    (hchoice : ComputableInSpace choice enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace
      (fun a => advance (N a) (width a) (source a) (s a) (answer a) (choice a))
      enc encState S := by
  have hw' := widthBinary_budget hw
  have hi := instruction_budget hN hw' hsource hs hanswer hchoice hin
  have hb := bounded_budget hN hw hi hin
  have hr := budget_natLt (rank_budget hN hw' hi hin) (rank_budget hN hw' hs hin)
  have hcheck := (and_budget hb hr).of_enc_eq (encC := encBool)
    (g := fun a => decide (Bounded (N a) (width a)
      (instruction (N a) (width a) (source a) (s a) (answer a) (choice a)) ∧
      rank (N a) (width a)
        (instruction (N a) (width a) (source a) (s a) (answer a) (choice a)) <
      rank (N a) (width a) (s a))) (fun a => by
        congr 1)
  exact (budget_ite (halted_budget hs hin) hs
    (iteProp_budget hcheck hi (budget_const reject hin))).of_enc_eq fun _ => rfl

/-- Initializing the controller includes its source-range check. -/
theorem initial_budget (hN : ComputableInSpace N enc encNat S)
    (hsource : ComputableInSpace source enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => initial (N a) (source a)) enc encState S := by
  exact iteProp_budget (budget_natLt hsource hN) (budget_const ({} : State) hin)
    (budget_const reject hin)

/-- Tagged binary data for one edge or bad-vertex request. -/
def queryData : Query → Bool × ℕ × ℕ
  | .edge u v => (false, u, v)
  | .bad u => (true, u, 0)

theorem queryData_injective : Function.Injective queryData := by
  intro q r h
  cases q <;> cases r <;> simp_all [queryData]

/-- An oracle request stores its tag and at most two binary vertices. -/
def encQuery : Query ↪ List Bool :=
  ⟨fun q => encPair encBool (encPair encNat encNat) (queryData q),
    fun _ _ h => queryData_injective
      ((encPair encBool (encPair encNat encNat)).injective h)⟩

/-- The explicit request, including the finite-phase and final-scan selection. -/
theorem query_budget (hs : ComputableInSpace s enc encState S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => query (s a)) enc (encOption encQuery) S := by
  have hedge {u v : α → ℕ} (hu : ComputableInSpace u enc encNat S)
      (hv : ComputableInSpace v enc encNat S) :
      ComputableInSpace (fun a => Query.edge (u a) (v a)) enc encQuery S :=
    (budget_prod (budget_const false hin) (budget_prod hu hv)).of_enc_eq fun _ => rfl
  have hbad := (budget_prod (budget_const true hin)
    (budget_prod (candidate_budget hs) (budget_const (encB := encNat) 0 hin))).of_enc_eq
    (g := fun a => Query.bad (s a).candidate) (encC := encQuery) (fun _ => rfl)
  have hsome {q : α → Query} (hq : ComputableInSpace q enc encQuery S) :
      ComputableInSpace (fun a => some (q a)) enc (encOption encQuery) S :=
    budget_comp_linear
      (of_inO (ComputableInDegree.optionSome (enc₁ := encQuery)).inO_one) hq
  have hbranches (p : Phase) : ComputableInSpace
      (fun a => query { s a with phase := p }) enc (encOption encQuery) S := by
    cases p <;> dsimp only [query] <;> try exact budget_const none hin
    · exact hsome (hedge (current_budget hs) (guess_budget hs))
    · exact hsome (budget_ite (finalScan_budget hs) hbad
        (hedge (candidate_budget hs) (target_budget hs)))
  refine (phaseCases_budget hs _ hbranches hin).of_enc_eq fun a => ?_
  cases s a
  rfl

/-- Full routine inputs: `N`, unary width, source, state, answer and choice. -/
def encAdvanceInput : (ℕ × ℕ × ℕ × State × Bool × Bool) ↪ List Bool :=
  encPair encNat (encPair encUnary (encPair encNat (encPair encState (encPair encBool encBool))))

/-- An unconditional native linear-space certificate for the complete checked routine. -/
theorem advance_inSpace :
    ComputableInSpace
      (fun a : ℕ × ℕ × ℕ × State × Bool × Bool =>
        advance a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2)
      encAdvanceInput encState fun a => (encAdvanceInput a).length := by
  have hN := fst encNat
    (encPair encUnary (encPair encNat (encPair encState (encPair encBool encBool))))
  have hrest := snd encNat
    (encPair encUnary (encPair encNat (encPair encState (encPair encBool encBool))))
  exact advance_budget hN hrest.fst' hrest.snd'.fst' hrest.snd'.snd'.fst'
    hrest.snd'.snd'.snd'.fst' hrest.snd'.snd'.snd'.snd' (.refl _)

end Turing.InductiveCounting
