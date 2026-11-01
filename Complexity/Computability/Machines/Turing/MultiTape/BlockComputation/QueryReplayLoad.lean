/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAccess
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi

/-!
# Native loading of a decoded local block

The loader receives runtime binary input length, block width and the positive and negative parts
of the input block origin. The supplied explicit windows are retained exactly. Work heads are
centered in the middle block, and the input head uses the native blank boundary convention.
No runtime-width list or table is allocated from the binary width.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Load

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k : ℕ} {Q : Type}

/-- Input length, local width, signed input-block origin and decoded explicit local data. -/
abbrev Args (k : ℕ) (Q : Type) := ℕ × ℕ × (ℕ × ℕ) × RawResult k Q

/-- Native input-head coordinate. An out-of-range signed coordinate is the blank left boundary.
Zero width is supported by the arithmetic, although semantic block replay uses positive widths. -/
@[expose] def inputPos (N b positive negative residue : ℕ) : ℕ :=
  let lo := b * negative
  let hi := b * positive + residue % b + 1
  if lo ≤ hi ∧ hi - lo < N + 2 then hi - lo else 0

/-- Load exactly the supplied windows, with binary positions and a runtime duration counter. -/
@[expose] def load : Args k Q → Config k Q :=
  fun (N, b, (positive, negative), (control, residues, track, cells)) =>
    { inputLength := N
      width := b
      remaining := b
      inputPos := inputPos N b positive negative (residues none)
      control := control
      heads := fun h => b + residues (some h) % b
      cells := cells
      track := track }

variable [Finite Q]

/-- Every numeric argument is binary; the decoded windows remain explicit fixed tape families. -/
@[expose] noncomputable def encArgs : Args k Q ↪ List Bool :=
  encPair encNat (encPair encNat (encPair (encPair encNat encNat) encRawResult))

/-- All initialization is charged to actual encoded arguments. The certificate is uniform in
input length, block width and both binary parts of the signed origin. -/
theorem load_inSpace : ComputableInSpace (load (k := k) (Q := Q)) encArgs encConfig
    (fun a => (encArgs a).length) := by
  classical
  have hN := fst encNat (encPair encNat (encPair (encPair encNat encNat)
    (encRawResult (k := k) (Q := Q))))
  have hrest := snd encNat (encPair encNat (encPair (encPair encNat encNat)
    (encRawResult (k := k) (Q := Q))))
  have hb := hrest.fst'
  have horigin := hrest.snd'.fst'
  have hp := horigin.fst'
  have hn := horigin.snd'
  have hraw := hrest.snd'.snd'
  have hcontrol := hraw.fst'
  have hresidues := hraw.snd'.fst'
  have htrack := hraw.snd'.snd'.fst'
  have hcells := hraw.snd'.snd'.snd'
  have hinputResidue := budget_comp_linear
    (of_inO (ComputableInO.pi_apply encNat (none : Option (Fin k)))) hresidues
  have hlo := budget_natMul hb hn
  have hhi := budget_natSucc (budget_natAdd (budget_natMul hb hp)
    (budget_natMod hinputResidue hb))
  have hcoordinate := budget_natSub hhi hlo
  have hnonnegative := budget_finite (encC := encBool) Bool.not (budget_natLt hhi hlo)
  have hinRange := budget_natLt hcoordinate (budget_natAdd hN (budget_const 2 (.refl _)))
  have hvalid := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hnonnegative hinRange)
  have hpos := budget_ite hvalid hcoordinate (budget_const (encB := encNat) 0 (.refl _))
  have hheads := pi_linear (Index := Fin k) fun h =>
    budget_natAdd hb (budget_natMod (budget_comp_linear
      (of_inO (ComputableInO.pi_apply encNat (some h))) hresidues) hb)
  refine (budget_prod hN (budget_prod hb (budget_prod hb (budget_prod hpos
    (budget_prod hcontrol (budget_prod hheads (budget_prod hcells htrack))))))).of_enc_eq ?_
  intro a
  rcases a with ⟨N, b, ⟨positive, negative⟩, ⟨control, residues, track, cells⟩⟩
  simp only [load, inputPos, encConfig, Config.equivProd, encOfEquiv_apply, Equiv.coe_fn_mk,
    Bool.and_eq_true, Bool.not_eq_true', Bool.decide_iff]
  by_cases hnonneg : b * negative ≤ b * positive + residues none % b + 1
  · have hnot : ¬b * positive + residues none % b + 1 < b * negative := by omega
    simp [hnonneg, hnot]
  · have hlt : b * positive + residues none % b + 1 < b * negative := by omega
    simp [hnonneg, hlt]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Load
