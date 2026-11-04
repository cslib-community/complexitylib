/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeDecode
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.WidthSpace
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.EncodedTree
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Header-only decisions for encoded block-tree roots

A malformed word, FAIL or a live control state gives no decision. A halted state gives the exact
accept/reject bit of the existing output summary. Only the control rank and output-summary bits
are inspected; no head residues or work-window cells are parsed or stored. Unused control ranks
retain the semantic decoder's convention of representing halted control.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.RootDecision

open Cslib Cslib.BitString MultiTapeTM MultiTapeTM.ComputableInSpace
open MultiTapeNTM.ChoiceTable

variable {k s b : ℕ} {Q : Type}

/-- Actual block width and stored Boolean root word. -/
abbrev Args := ℕ × List Bool

/-- Reuse the native decoder's actual binary-width/word encoding. -/
abbrev encArgs : Args ↪ List Bool := Encoding.NativeDecode.encArgs

/-- The semantic outcome of a decoded root: only halted views return a decision. -/
@[expose] def decision : Option (View k Q b) → Option Bool
  | none => none
  | some ((control, _, track), _) =>
    if control.isNone then some (decide (track = OutputTrack.accept)) else none

/-- Classify the stored root using its control header and two output-summary bits only. -/
@[expose] def classify (k : ℕ) (e : Q ≃ Fin s) : Args → Option Bool := fun (b, word) =>
  if b = 0 ∨ word.length ≠ Encoding.width k s b then none
  else if word.headD false then
    if (Encoding.NativeDecode.state e
        (Encoding.NativeDecode.readNat word 1 (s + 1).size)).isNone then
      let offset := Encoding.NativeDecode.trackOffset k s b
      some (word.getD offset false && !word.getD (offset + 1) false)
    else none
  else none

/-- Header-only classification agrees with the existing parser's semantic view. -/
theorem classify_eq_decision_parse (e : Q ≃ Fin s) (b : ℕ) (word : List Bool) :
    classify k e (b, word) = decision (k := k)
      ((Encoding.NativeDecode.parse (k := k) e (b, word)).map
        (QueryReplay.RawResult.toView b)) := by
  classical
  by_cases hbad : b = 0 ∨ word.length ≠ Encoding.width k s b
  · simp [classify, Encoding.NativeDecode.parse, hbad, decision]
  · by_cases htag : word.headD false = true
    · simp only [classify, Encoding.NativeDecode.parse, hbad, htag, ↓reduceIte,
        Option.map_some, Encoding.NativeDecode.payload, QueryReplay.RawResult.toView, decision]
      split
      · cases hfirst : word.getD (Encoding.NativeDecode.trackOffset k s b) false <;>
          cases hsecond : word.getD (Encoding.NativeDecode.trackOffset k s b + 1) false <;>
          simp_all
      · rfl
    · simp only [classify, Encoding.NativeDecode.parse, hbad, htag, Bool.false_eq_true, ↓reduceIte,
        Option.map_none, decision]

/-- Stored width-correct roots have exactly the existing decoder's semantic decision. -/
theorem classify_ofFn_eq_decision_decode (e : Q ≃ Fin s) (b : ℕ) [NeZero b]
    (bits : BitString (Encoding.width k s b)) :
    classify k e (b, List.ofFn bits) = decision (Encoding.decode e bits) := by
  rw [classify_eq_decision_parse, Encoding.NativeDecode.parse_ofFn]

variable [Finite Q]

/-- Root classification is native in space linear in the actual stored word and binary width. -/
theorem classify_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (classify k e) encArgs (encOption encBool)
      (fun a => (encArgs a).length) := by
  classical
  have hb := fst encNat encBits
  have hw := snd encNat encBits
  have hwordLength : ComputableInSpace List.length encBits encNat
      (fun word => (encBits word).length) :=
    Encoding.NativeDecode.wordLength_inSpace
  have hlength := budget_comp_linear hwordLength hw
  have hwidth := budget_comp_linear (Encoding.width_inSpace k s) hb
  have hshape := budget_finite (encC := encBool)
    (fun pair : Bool × Bool => pair.1 || !pair.2)
    (budget_prod (budget_natIsZero hb) (budget_natEq hlength hwidth))
  have htag := budget_comp_linear Encoding.NativeDecode.bit_inSpace
    (budget_prod hw (budget_const (encB := encNat) 0 (.refl _)))
  have hrank := budget_comp_linear Encoding.NativeDecode.readNat_inSpace
    (budget_prod hw (budget_prod (budget_const (encB := encNat) 1 (.refl _))
      (budget_const (encB := encNat) (s + 1).size (.refl _))))
  have hcontrol := budget_comp_linear (Encoding.NativeDecode.state_inSpace e) hrank
  have hhalt := budget_finite (encC := encBool) (Option.isNone : Option Q → Bool) hcontrol
  have hoffset := Encoding.NativeDecode.trackOffset_inSpace (k := k) (s := s)
  have hfirst := budget_comp_linear Encoding.NativeDecode.bit_inSpace (budget_prod hw hoffset)
  have hsecond := budget_comp_linear Encoding.NativeDecode.bit_inSpace
    (budget_prod hw (budget_natSucc hoffset))
  have haccept := budget_finite (encC := encBool)
    (fun pair : Bool × Bool => pair.1 && !pair.2) (budget_prod hfirst hsecond)
  have hsome := budget_comp_linear (encC := encOption encBool)
    (of_inO (ComputableInDegree.optionSome (enc₁ := encBool)).inO_one) haccept
  have hnone := budget_const (encIn := encArgs) (encB := encOption encBool) none (.refl _)
  refine (budget_ite hshape hnone
    (budget_ite htag (budget_ite hhalt hsome hnone) hnone)).of_enc_eq ?_
  rintro ⟨b, word⟩
  rw [show word.getD 0 false = word.headD false from by
    cases word <;> rfl]
  by_cases hzero : b = 0 <;>
    by_cases hlength : word.length = Encoding.width k s b <;>
    simp [classify, hzero, hlength]

end Turing.MultiTapePTM.BlockComputation.RootDecision
