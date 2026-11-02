/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi

/-!
# Native verification of local block motion

Work-head positions use the three explicitly stored blocks. Input-head positions use the native
padded coordinates, including physical position zero for the blank left boundary. The original
input-block origin is supplied as positive and negative binary parts. The verifier compares the
expected schedule directions using binary division and addition; it rejects zero block width.
Schedule directions form a fixed finite family; origins and head coordinates remain binary.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Motion

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k : ℕ} {Q : Type}

/-- The three neighboring block indices, relative to the leftmost stored block. -/
@[expose] def code : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

/-- Compare the input head against its expected displacement from a signed origin.
Physical position zero has native head coordinate `-1`, whose positive-width block is `-1`. -/
@[expose] def inputMatches (b positive negative position : ℕ) (label : SignType) : Bool :=
  if position = 0 then decide (positive + code label = negative)
  else decide ((position - 1) / b + negative + 1 = positive + code label)

/-- A work head lies in the expected one of the three stored blocks. -/
@[expose] def workMatches (b relative : ℕ) (label : SignType) : Bool :=
  decide (relative / b = code label)

/-- Signed input origin, fixed tape-direction family and the returned explicit replay state. -/
abbrev Args (k : ℕ) (Q : Type) := ℕ × ℕ × (Option (Fin k) → SignType) × Config k Q

/-- Check the input direction and every work-tape direction at a positive runtime width. -/
@[expose] def valid : Args k Q → Bool :=
  fun (positive, negative, expected, q) =>
    (decide (0 < q.width) && inputMatches q.width positive negative q.inputPos (expected none)) &&
      decide (∀ h : Fin k, workMatches q.width (q.heads h) (expected (some h)) = true)

variable [Finite Q]

/-- Binary origin registers, a fixed finite direction family and all actual replay storage. -/
@[expose] noncomputable def encArgs : Args k Q ↪ List Bool :=
  encPair encNat (encPair encNat
    (encPair (encPi (Index := Option (Fin k)) (encFinite SignType)) encConfig))

/-- Uniform native motion verification. Constants depend only on the fixed tape/control types;
widths, origins, positions and windows are runtime data charged by their actual encodings. -/
theorem valid_inSpace : ComputableInSpace (valid (k := k) (Q := Q)) encArgs encBool
    (fun a => (encArgs a).length) := by
  classical
  have hp := fst encNat (encPair encNat
    (encPair (encPi (Index := Option (Fin k)) (encFinite SignType)) (encConfig (k := k) (Q := Q))))
  have hrest := snd encNat (encPair encNat
    (encPair (encPi (Index := Option (Fin k)) (encFinite SignType)) (encConfig (k := k) (Q := Q))))
  have hn := hrest.fst'
  have hexpected := hrest.snd'.fst'
  have hstate := hrest.snd'.snd'
  have hb := budget_comp_linear width_inSpace hstate
  have hposition := budget_comp_linear inputPos_inSpace hstate
  have hheads := budget_comp_linear
    (equivProd_inSpace (k := k) (Q := Q)).snd'.snd'.snd'.snd'.snd'.fst' hstate
  have hinputTag := budget_comp_linear
    (of_inO (ComputableInO.pi_apply (encFinite SignType) (none : Option (Fin k)))) hexpected
  have hinputCode := budget_finite (encC := encNat) code hinputTag
  have hright := budget_natAdd hp hinputCode
  have hleft := budget_natSucc (budget_natAdd
    (budget_natDiv (budget_natPred hposition) hb) hn)
  have hinput : ComputableInSpace
      (fun a : Args k Q => inputMatches a.2.2.2.width a.1 a.2.1 a.2.2.2.inputPos
        (a.2.2.1 none)) encArgs encBool (fun a => (encArgs a).length) := by
    refine (budget_ite (budget_natIsZero hposition) (budget_natEq hright hn)
      (budget_natEq hleft hright)).of_enc_eq ?_
    intro a
    simp only [inputMatches, Bool.decide_iff]
  have hwork := pi_linear (Index := Fin k) fun h =>
    budget_natEq (budget_natDiv
      (budget_comp_linear (of_inO (ComputableInO.pi_apply encNat h)) hheads) hb)
      (budget_finite (encC := encNat) code (budget_comp_linear
        (of_inO (ComputableInO.pi_apply (encFinite SignType) (some h))) hexpected))
  have hall := budget_finite (encC := encBool)
    (fun f : Fin k → Bool => decide (∀ h, f h = true)) hwork
  have hguard := budget_natLt (budget_const (encB := encNat) 0 (.refl _)) hb
  have hinputGuard := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hguard hinput)
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hinputGuard hall)).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Motion
