/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi

/-!
# Native extraction of a local replay result

`RawResult` stores the finite control and output tags, binary head residues and the explicit
local tape lists. Its type is independent of the runtime block width. `rawResult` is computed
in linear encoded-state space; casting its residues and decoding its cells gives precisely the
existing semantic `result` at positive widths. The original input pointer zero represents the
blank left boundary, whose residue is `width - 1`, rather than zero.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay

open MultiTapeTM MultiTapeTM.ComputableInSpace MultiTapeNTM.ChoiceTable

variable {k : ℕ} {Q : Type}

/-- Runtime-width local data, with the input head indexed by `none`. -/
abbrev RawResult (k : ℕ) (Q : Type) :=
  Option Q × (Option (Fin k) → ℕ) × OutputTrack × (Fin k → List ℕ)

/-- A work-head residue, with zero as the guarded zero-width result. -/
@[expose] def workResidue (width position : ℕ) : ℕ :=
  if width = 0 then 0 else position % width

/-- The original input uses physical coordinates with a blank boundary at zero. -/
@[expose] def inputResidue (width position : ℕ) : ℕ :=
  if width = 0 then 0 else if position = 0 then width - 1 else (position - 1) % width

/-- Extract returned local data without a width-indexed runtime type. -/
@[expose] def rawResult (s : Config k Q) : RawResult k Q :=
  (s.control, fun h => match h with
    | none => inputResidue s.width s.inputPos
    | some i => workResidue s.width (s.heads i), s.track, s.cells)

/-- Interpret explicit returned data at a positive block width. -/
@[expose] def RawResult.toView (width : ℕ) : RawResult k Q → View k Q width :=
  fun (control, residues, track, cells) =>
    ((control, fun h => (residues h : ZMod width), track),
      fun h d r => cellOfCode ((cells h).getD (d * width + r.val) 0))

@[simp] theorem workResidue_cast (width position : ℕ) [NeZero width] :
    (workResidue width position : ZMod width) = (position : ZMod width) := by
  simp only [workResidue, NeZero.ne width, ↓reduceIte, ZMod.natCast_mod]

@[simp] theorem inputResidue_cast (width position : ℕ) [NeZero width] :
    (inputResidue width position : ZMod width) = (((position : ℤ) - 1 : ℤ) : ZMod width) := by
  have hw : 1 ≤ width := Nat.one_le_iff_ne_zero.mpr (NeZero.ne width)
  cases position with
  | zero => simp [inputResidue, NeZero.ne width, Nat.cast_sub hw]
  | succ n => simp [inputResidue, NeZero.ne width]

/-- Native result extraction agrees with the existing semantic view, including both input
boundaries and every explicitly stored work-window cell. -/
theorem toView_rawResult (s : Config k Q) (width : ℕ) [NeZero width]
    (hwidth : s.width = width) :
    (rawResult s).toView width = result width s := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext h
        cases h <;> simp [RawResult.toView, rawResult, result, hwidth]
      · rfl
  · rfl

/-- The guarded work residue never exceeds the runtime block width. -/
theorem workResidue_le (width position : ℕ) : workResidue width position ≤ width := by
  by_cases hw : width = 0
  · simp [workResidue, hw]
  · simpa only [workResidue, hw, ↓reduceIte] using
      (Nat.mod_lt position (Nat.pos_of_ne_zero hw)).le

/-- The guarded input residue never exceeds the runtime block width. -/
theorem inputResidue_le (width position : ℕ) : inputResidue width position ≤ width := by
  by_cases hw : width = 0
  · simp [inputResidue, hw]
  · by_cases hp : position = 0
    · simp [inputResidue, hw, hp]
    · simpa only [inputResidue, hw, hp, ↓reduceIte] using
        (Nat.mod_lt (position - 1) (Nat.pos_of_ne_zero hw)).le

variable [Finite Q]

/-- Finite tags, binary residues and explicit lists, without a runtime-width finite lookup. -/
@[expose] noncomputable def encRawResult : RawResult k Q ↪ List Bool :=
  encPair (encFinite (Option Q)) (encPair (encPi encNat)
    (encPair (encFinite OutputTrack) (encPi (encList encNat))))

private theorem configParts : ComputableInSpace (Config.equivProd (k := k) (Q := Q))
    encConfig (encPair encNat (encPair encNat (encPair encNat
      (encPair encNat (encPair (encFinite (Option Q)) (encPair (encPi encNat)
        (encPair (encPi (encList encNat)) (encFinite OutputTrack))))))))
    (fun s => (encConfig s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private theorem workResidue_inSpace : ComputableInSpace
    (fun p : ℕ × ℕ => workResidue p.1 p.2) (encPair encNat encNat) encNat
    (fun p => (encPair encNat encNat p).length) := by
  have hw := fst encNat encNat
  have hp := snd encNat encNat
  refine (budget_ite (budget_natIsZero hw) (budget_const 0 (.refl _))
    (budget_natMod hp hw)).of_enc_eq ?_
  intro p
  simp only [workResidue, Bool.decide_iff]

private theorem inputResidue_inSpace : ComputableInSpace
    (fun p : ℕ × ℕ => inputResidue p.1 p.2) (encPair encNat encNat) encNat
    (fun p => (encPair encNat encNat p).length) := by
  have hw := fst encNat encNat
  have hp := snd encNat encNat
  refine (budget_ite (budget_natIsZero hw) (budget_const 0 (.refl _))
    (budget_ite (budget_natIsZero hp) (budget_natPred hw)
      (budget_natMod (budget_natPred hp) hw))).of_enc_eq ?_
  intro p
  simp only [inputResidue, Bool.decide_iff]

/-- Uniform native extraction of the state-returning local replay result. -/
theorem rawResult_inSpace : ComputableInSpace (rawResult (k := k) (Q := Q)) encConfig
    encRawResult (fun s => (encConfig s).length) := by
  classical
  have hcontrol := (configParts (k := k) (Q := Q)).snd'.snd'.snd'.snd'.fst'
  have hheads := (configParts (k := k) (Q := Q)).snd'.snd'.snd'.snd'.snd'.fst'
  have hcells := (configParts (k := k) (Q := Q)).snd'.snd'.snd'.snd'.snd'.snd'.fst'
  have htrack := (configParts (k := k) (Q := Q)).snd'.snd'.snd'.snd'.snd'.snd'.snd'
  have hres (h : Option (Fin k)) : ComputableInSpace
      (fun s : Config k Q => (rawResult s).2.1 h) encConfig encNat
      (fun s => (encConfig s).length) := by
    cases h with
    | none =>
      exact budget_comp_linear inputResidue_inSpace
        (budget_prod width_inSpace inputPos_inSpace)
    | some i =>
      have hhead := budget_comp_linear (of_inO (ComputableInO.pi_apply encNat i)) hheads
      exact budget_comp_linear workResidue_inSpace (budget_prod width_inSpace hhead)
  choose T hT using fun i => (hres i).exists_inO
  have hr := (of_inO (ComputableInO.pi hT)).weaken
    (show (fun s => (encConfig s).length +
      ∑ _i : Option (Fin k), (encConfig s).length) ≼ fun s => (encConfig s).length from
        ⟨Fintype.card (Option (Fin k)) + 1, fun s => by simp; nlinarith⟩)
  exact (budget_prod hcontrol (budget_prod hr (budget_prod htrack hcells))).of_enc_eq
    fun _ => rfl

/-- Returned data fits in linear local-window space. Its type and encoding do not contain the
original input, and all head residues are bounded by the runtime width. -/
theorem length_encRawResult_le (s : Config k Q)
    (hcells : ∀ h, (s.cells h).length ≤ 3 * s.width)
    (hcodes : ∀ h n, n ∈ s.cells h → n ≤ 2) :
    (encRawResult (rawResult s)).length ≤ 128 * (k + 1) *
      (s.width + Nat.card (Option Q) + Nat.card OutputTrack + 1) := by
  have hnat (n : ℕ) : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  have hq := (length_encFinite_lt s.control).le
  have ht := (length_encFinite_lt s.track).le
  have hres (h : Option (Fin k)) : (encNat ((rawResult s).2.1 h)).length ≤ s.width := by
    apply (hnat _).trans
    cases h
    · exact inputResidue_le _ _
    · exact workResidue_le _ _
  have hh : (encPi encNat (rawResult s).2.1).length ≤ (k + 1) * (2 * s.width + 1) := by
    simpa only [Fintype.card_option, Fintype.card_fin] using
      length_encPi_le encNat (rawResult s).2.1 hres
  have hw : (encPi (encList encNat) s.cells).length ≤ k * (30 * s.width + 1) := by
    have hl (h : Fin k) : (encList encNat (s.cells h)).length ≤ 15 * s.width := by
      have hl' := length_encList_le encNat (s.cells h)
        (fun n hn => (hnat n).trans (hcodes h n hn))
      nlinarith [hcells h]
    simpa only [Fintype.card_fin, ← Nat.mul_assoc] using
      length_encPi_le (encList encNat) s.cells hl
  change (encPair (encFinite (Option Q)) (encPair (encPi encNat)
    (encPair (encFinite OutputTrack) (encPi (encList encNat)))) (rawResult s)).length ≤ _
  simp only [length_encPair, rawResult]
  simp only [rawResult] at hh
  nlinarith

end Turing.MultiTapePTM.BlockComputation.QueryReplay
