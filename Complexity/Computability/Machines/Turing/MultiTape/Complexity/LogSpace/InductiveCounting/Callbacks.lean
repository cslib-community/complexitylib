/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Routines
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Native callbacks for the complete counting query machine

The callbacks receive only the encoded runtime state, current input symbol and choice bit as
needed. Their workspace is linear in these short arguments, including on malformed states. The
radix is stored in binary, so the graph routines receive it as an argument; the next radix is
four times the current one.

## Main results

* `Turing.InductiveCounting.query_inSpace`: the complete runtime input address.
* `Turing.InductiveCounting.next_inSpace`: bootstrap, radix changes and checked controller
  advance.
* `Turing.InductiveCounting.halted_inSpace`: complete runtime halt detection.
* `Turing.InductiveCounting.accept_inSpace`: complete runtime acceptance detection.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM ComputableTidilyInSpace MultiTapeNTM.ConfigurationGraph

/-- One unary output bit per input bit. -/
def unaryLengthT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [true])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem unaryLengthT_run (w : List Bool) :
    unaryLengthT.run () w = List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [Transducer.run_cons, ih]; rfl

/-- Reading binary digits and emitting one true bit per digit computes their width in linear
time and space; there is no unary expansion of the original number. -/
private theorem sizeUnary_inSpace : ComputableTidilyInSpace Nat.size encNat encUnary
    fun n => (encNat n).length := by
  have h : ComputableTidilyInDegree Nat.size encNat encUnary 1 1 :=
    .of_linear (unaryLengthT.computableTidilyInLinearTimeAndSpace fun n => by
      rw [encUnary_apply, unaryLengthT_run, encNat_apply, Nat.size_eq_bits_len])
  exact of_inO h.inO_one

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

/-- The runtime as its product of fields. -/
private theorem runtimeData_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S) :
    ComputableTidilyInSpace (fun a => ((s a).length, (s a).radix, (s a).checked, (s a).counting))
      enc (encPair encNat (encPair encNat (encPair encBool (encOption encState)))) S :=
  hs.of_enc_eq fun _ => rfl

/-- Read the binary input-length field from the runtime encoding. -/
private theorem runtimeLength_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S) :
    ComputableTidilyInSpace (fun a => (s a).length) enc encNat S :=
  (runtimeData_budget hs).fst'

/-- Read the binary radix field. -/
private theorem runtimeRadix_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S) :
    ComputableTidilyInSpace (fun a => (s a).radix) enc encNat S :=
  (runtimeData_budget hs).snd'.fst'

/-- Read the mode flag. -/
private theorem runtimeChecked_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S) :
    ComputableTidilyInSpace (fun a => (s a).checked) enc encBool S :=
  (runtimeData_budget hs).snd'.snd'.fst'

/-- Read the optional counting-state field without retaining a choice history. -/
private theorem runtimeCounting_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S) :
    ComputableTidilyInSpace (fun a => (s a).counting) enc (encOption encState) S :=
  (runtimeData_budget hs).snd'.snd'.snd'

/-- Construct runtime data from its certified fields. -/
private theorem runtime_budget {n B : α → ℕ} {chk : α → Bool}
    {c : α → Option Cslib.InductiveCounting.State}
    (hn : ComputableTidilyInSpace n enc encNat S) (hB : ComputableTidilyInSpace B enc encNat S)
    (hchk : ComputableTidilyInSpace chk enc encBool S)
    (hc : ComputableTidilyInSpace c enc (encOption encState) S) :
    ComputableTidilyInSpace (fun a => (⟨n a, B a, chk a, c a⟩ : Runtime)) enc encRuntime S :=
  (budget_prod hn (budget_prod hB (budget_prod hchk hc))).of_enc_eq fun _ => rfl

private theorem optionSome_budget {β : Type} {encB : β ↪ List Bool} {f : α → β}
    (hf : ComputableTidilyInSpace f enc encB S) :
    ComputableTidilyInSpace (fun a => some (f a)) enc (encOption encB) S :=
  budget_comp_linear (of_inO (ComputableTidilyInDegree.optionSome (enc₁ := encB)).inO_one) hf

private theorem optionIsSome_budget {β : Type} {encB : β ↪ List Bool} {f : α → Option β}
    (hf : ComputableTidilyInSpace f enc (encOption encB) S) :
    ComputableTidilyInSpace (fun a => (f a).isSome) enc encBool S :=
  budget_comp_linear (of_inO (ComputableTidilyInDegree.isSome encB).inO_one) hf

private theorem and_budget {f g : α → Bool}
    (hf : ComputableTidilyInSpace f enc encBool S) (hg : ComputableTidilyInSpace g enc encBool S) :
    ComputableTidilyInSpace (fun a => f a && g a) enc encBool S :=
  budget_finite (fun p : Bool × Bool => p.1 && p.2) (budget_prod hf hg)

private theorem or_budget {f g : α → Bool}
    (hf : ComputableTidilyInSpace f enc encBool S) (hg : ComputableTidilyInSpace g enc encBool S) :
    ComputableTidilyInSpace (fun a => f a || g a) enc encBool S :=
  budget_finite (fun p : Bool × Bool => p.1 || p.2) (budget_prod hf hg)

private theorem controller_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S) :
    ComputableTidilyInSpace
      (fun a => (s a).counting.getD Cslib.InductiveCounting.reject) enc encState S :=
  budget_comp_linear
    (of_inO (ComputableTidilyInDegree.getD (enc₁ := encState)
      Cslib.InductiveCounting.reject).inO_one) (runtimeCounting_budget hs)

/-- Test the finite phase against a fixed one. -/
private theorem phaseEq_budget {s : α → Cslib.InductiveCounting.State}
    (hs : ComputableTidilyInSpace s enc encState S) (p : Cslib.InductiveCounting.Phase)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => (s a).phase == p) enc encBool S :=
  phaseCases_budget hs (fun q _ => q == p) (fun _ => budget_const _ hin) hin

/-- Detect a complete final count check meeting a bad vertex. -/
private theorem overflowed_budget {s : α → Cslib.InductiveCounting.State}
    (hs : ComputableTidilyInSpace s enc encState S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => overflowed (s a)) enc encBool S :=
  (and_budget (and_budget (and_budget (phaseEq_budget hs .done hin) (finalScan_budget hs))
    (budget_natEq (selected_budget hs) (count_budget hs))) (hit_budget hs)).of_enc_eq
    fun a => by simp only [overflowed, Bool.beq_eq_decide_eq]

variable {k : ℕ} {State : Type} [Fintype State]

/-- The controller's input address on arbitrary states: the position of the first vertex of its
request. -/
private theorem controllerQuery_budget {B : α → ℕ} {s : α → Cslib.InductiveCounting.State}
    (hB : ComputableTidilyInSpace B enc encNat S)
    (hs : ComputableTidilyInSpace s enc encState S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => controllerQuery k (B a) (s a)) enc encNat S := by
  have hbranches (p : Cslib.InductiveCounting.Phase) : ComputableTidilyInSpace
      (fun a => controllerQuery k (B a) { s a with phase := p }) enc encNat S := by
    cases p <;> dsimp only [controllerQuery, Cslib.InductiveCounting.query] <;>
      try exact budget_const 0 hin
    · exact (queryIndex_budget hB.computableInSpace (current_budget hs).computableInSpace).tidy
    · exact (queryIndex_budget hB.computableInSpace
        (candidate_budget hs).computableInSpace).tidy.of_enc_eq fun a => by
        cases (s a).finalScan <;> rfl
  refine (phaseCases_budget hs _ hbranches hin).of_enc_eq fun a => ?_
  cases s a
  rfl

/-- The local answer uses one supplied symbol and linear workspace on every state. -/
private theorem localAnswer_budget (ntm : MultiTapeNTM k Bool State)
    {B n : α → ℕ} {chk : α → Bool} {s : α → Cslib.InductiveCounting.State}
    {symbol : α → Option Bool}
    (hB : ComputableTidilyInSpace B enc encNat S)
    (hn : ComputableTidilyInSpace n enc encNat S)
    (hchk : ComputableTidilyInSpace chk enc encBool S)
    (hs : ComputableTidilyInSpace s enc encState S)
    (hsymbol : ComputableTidilyInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => localAnswer ntm (B a) (n a) (chk a) (s a) (symbol a))
      enc encBool S := by
  have hmode : ComputableTidilyInSpace
      (fun a => modeBad ntm (B a) (n a) (chk a) (s a).candidate (symbol a)) enc encBool S :=
    (budget_ite hchk
      (bad_budget hB.computableInSpace hn.computableInSpace
        (candidate_budget hs).computableInSpace hin).tidy
      (overflow_budget ntm hB.computableInSpace hn.computableInSpace
        (candidate_budget hs).computableInSpace hsymbol.computableInSpace hin).tidy).of_enc_eq
      fun a => by
        cases chk a <;> rfl
  have hbranches (p : Cslib.InductiveCounting.Phase) : ComputableTidilyInSpace
      (fun a => localAnswer ntm (B a) (n a) (chk a) { s a with phase := p } (symbol a))
      enc encBool S := by
    cases p <;> dsimp only [localAnswer, Cslib.InductiveCounting.query] <;>
      try exact budget_const false hin
    · exact (edgeWithSymbol_budget ntm hB.computableInSpace hn.computableInSpace
        (current_budget hs).computableInSpace (guess_budget hs).computableInSpace
        hsymbol.computableInSpace hin).tidy
    · exact (budget_ite (finalScan_budget hs) hmode
        (edgeWithSymbol_budget ntm hB.computableInSpace hn.computableInSpace
          (candidate_budget hs).computableInSpace (target_budget hs).computableInSpace
          hsymbol.computableInSpace hin).tidy
      ).of_enc_eq fun a => by cases (s a).finalScan <;> rfl
  refine (phaseCases_budget hs _ hbranches hin).of_enc_eq fun a => ?_
  cases s a
  rfl

/-- Runtime input lookup preserves any common budget covering the encoded arguments. -/
private theorem runtimeQuery_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => runtimeQuery k (s a)) enc encNat S := by
  exact (budget_ite (optionIsSome_budget (runtimeCounting_budget hs))
    (controllerQuery_budget (k := k) (runtimeRadix_budget hs) (controller_budget hs) hin)
    (runtimeLength_budget hs)).of_enc_eq fun a => by
      cases h : (s a).counting <;> simp [runtimeQuery, h]

/-- Halt detection includes the bootstrap phase and accepts arbitrary runtime data. -/
private theorem runtimeHalted_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => runtimeHalted (s a)) enc encBool S := by
  have hc := controller_budget hs
  exact (budget_ite (optionIsSome_budget (runtimeCounting_budget hs))
    (or_budget (phaseEq_budget hc .reject hin)
      (and_budget (runtimeChecked_budget hs) (phaseEq_budget hc .accept hin)))
    (budget_const false hin)).of_enc_eq fun a => by
      cases h : (s a).counting <;> simp [runtimeHalted, h]

/-- Acceptance detection includes the bootstrap phase and accepts arbitrary runtime data. -/
private theorem runtimeAccept_budget {s : α → Runtime}
    (hs : ComputableTidilyInSpace s enc encRuntime S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => runtimeAccept (s a)) enc encBool S := by
  exact (and_budget (runtimeChecked_budget hs)
    (budget_ite (optionIsSome_budget (runtimeCounting_budget hs))
      (accepting_budget (controller_budget hs) hin) (budget_const false hin))).of_enc_eq
    fun a => by cases h : (s a).counting <;> simp [runtimeAccept, h]

/-- Installing the controller on a computed radix. -/
private theorem install_budget (ntm : MultiTapeNTM k Bool State) {B : α → ℕ}
    (hB : ComputableTidilyInSpace B enc encNat S) (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => install ntm (B a)) enc encState S :=
  initial_budget (vertexBound_budget hB.computableInSpace hin).tidy
    (startID_budget ntm hB.computableInSpace hin).tidy hin

/-- The complete next-state callback, including bootstrap, radix changes, graph evaluation and
checked advance, uses the common budget without assuming that the runtime is reachable or well
formed. -/
private theorem runtimeNext_budget (ntm : MultiTapeNTM k Bool State)
    {s : α → Runtime} {symbol : α → Option Bool} {choice : α → Bool}
    (hs : ComputableTidilyInSpace s enc encRuntime S)
    (hsymbol : ComputableTidilyInSpace symbol enc (encOption encBool) S)
    (hchoice : ComputableTidilyInSpace choice enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace
      (fun a => runtimeNext ntm (s a) (symbol a) (choice a)) enc encRuntime S := by
  have hn := runtimeLength_budget hs
  have hB := runtimeRadix_budget hs
  have hchk := runtimeChecked_budget hs
  have hc := controller_budget hs
  have hN := (vertexBound_budget (k := k) hB.computableInSpace hin).tidy
  have hw := budget_comp_linear sizeUnary_inSpace hN
  have hsource := (startID_budget ntm hB.computableInSpace hin).tidy
  have ha := localAnswer_budget ntm hB hn hchk hc hsymbol hin
  have hadvance := runtime_budget hn hB hchk
    (optionSome_budget (advance_budget hN hw hsource hc ha hchoice hin))
  have hB₄ := budget_natMul (budget_const 4 hin) hB
  have hgrow := runtime_budget hn hB₄ (budget_const false hin)
    (optionSome_budget (install_budget ntm hB₄ hin))
  have hcheck := runtime_budget hn hB (budget_const true hin)
    (optionSome_budget (install_budget ntm hB hin))
  have hnot := budget_finite (encC := encBool) Bool.not hchk
  have hcounting := budget_ite (and_budget hnot (overflowed_budget hc hin)) hgrow
    (budget_ite (and_budget hnot (phaseEq_budget hc .accept hin)) hcheck hadvance)
  have hstart := budget_natMul (budget_natAdd hn (budget_const 2 hin))
    (budget_const (2 ^ (Fintype.card (Option State) + 2)) hin)
  have hscan := budget_ite (budget_finite Option.isSome hsymbol)
    (runtime_budget (budget_natSucc hn) hB hchk (budget_const none hin))
    (runtime_budget hn hstart (budget_const false hin)
      (optionSome_budget (install_budget ntm hstart hin)))
  exact (budget_ite (optionIsSome_budget (runtimeCounting_budget hs)) hcounting hscan).of_enc_eq
    fun a => by
      cases h : (s a).counting <;> simp [runtimeNext, h, vertexWidth, startRadix]

/-- Native linear workspace for the full runtime input-address callback. -/
theorem query_inSpace :
    ComputableTidilyInSpace (runtimeQuery k) encRuntime encNat
      (fun s => (encRuntime s).length) :=
  runtimeQuery_budget (of_inO (.of_linear (.of_eq fun _ => rfl))) (.refl _)

/-- Native linear workspace for the full next-state callback on its exact input tuple. -/
theorem next_inSpace (ntm : MultiTapeNTM k Bool State) :
    ComputableTidilyInSpace
      (fun p : Runtime × Option Bool × Bool => runtimeNext ntm p.1 p.2.1 p.2.2)
      (encPair encRuntime (encPair (encOption encBool) encBool)) encRuntime
      (fun p => (encPair encRuntime (encPair (encOption encBool) encBool) p).length) := by
  have hs := fst encRuntime (encPair (encOption encBool) encBool)
  have hrest := snd encRuntime (encPair (encOption encBool) encBool)
  exact runtimeNext_budget ntm hs hrest.fst' hrest.snd' (.refl _)

/-- Native linear workspace for full runtime halt detection. -/
theorem halted_inSpace :
    ComputableTidilyInSpace runtimeHalted encRuntime encBool
      (fun s => (encRuntime s).length) :=
  runtimeHalted_budget (of_inO (.of_linear (.of_eq fun _ => rfl))) (.refl _)

/-- Native linear workspace for full runtime acceptance detection. -/
theorem accept_inSpace :
    ComputableTidilyInSpace runtimeAccept encRuntime encBool
      (fun s => (encRuntime s).length) :=
  runtimeAccept_budget (of_inO (.of_linear (.of_eq fun _ => rfl))) (.refl _)

end Turing.InductiveCounting
