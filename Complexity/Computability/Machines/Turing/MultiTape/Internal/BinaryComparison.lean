/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
import Mathlib.Tactic.Linarith

/-! # Quadratic schoolbook binary subtraction and comparison

The existing borrow algorithm runs through consuming input-word cursors, so every round costs
only a linear amount and there are at most as many rounds as input digits. The plain machine
certificate retains quadratic time and linear output-charged workspace, independently of the
numeric operands. Comparison tests that same result; no qualitative polynomial-time bridge is
used to establish either resource bound.

## Main results

* `ComputableInO.natSub`: truncated subtraction in quadratic time and linear charged space.
* `ComputableInO.natLt`: strict comparison with the same independent resource bounds.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

private abbrev encCursor :=
  encPair (encPair encBits encBits) (encPair encBool encBits)

private theorem cursorStep_inO :
    ComputableInO (fun p => BinarySub.cursorStep p.1 p.2) (encPair encCursor encBool) encCursor
      (fun p => (encPair encCursor encBool p).length)
      (fun p => (encPair encCursor encBool p).length) := by
  have hs := ComputableInDegree.fst encCursor encBool
  have hw := (ComputableInDegree.fst (encPair encBits encBits)
    (encPair encBool encBits)).comp hs
  have hl := (ComputableInDegree.fst encBits encBits).comp hw
  have hr := (ComputableInDegree.snd encBits encBits).comp hw
  have ha := (ComputableInDegree.snd (encPair encBits encBits)
    (encPair encBool encBits)).comp hs
  have hc := (ComputableInDegree.fst encBool encBits).comp ha
  have hout := (ComputableInDegree.snd encBool encBits).comp ha
  have hheads := (Internal.DecoderWords.bool_degree.comp hl).prod
    (Internal.DecoderWords.bool_degree.comp hr)
  have hflags := (ComputableInDegree.of_finite
    (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encPair encBool encBool) fun q : Bool × (Bool × Bool) =>
      (BinarySub.borrow q.1 q.2.1 q.2.2, q.1 ^^ q.2.1 ^^ q.2.2)).comp (hc.prod hheads)
  have hborrow := (ComputableInDegree.fst encBool encBool).comp hflags
  have hdigit := (ComputableInDegree.snd encBool encBool).comp hflags
  have hround := ((Internal.DecoderWords.tail_degree.comp hl).prod
    (Internal.DecoderWords.tail_degree.comp hr)).prod
    (hborrow.prod (hout.append hdigit (encOut := encBits) fun _ => rfl))
  exact (show ComputableInDegree (fun p => BinarySub.cursorStep p.1 p.2)
    (encPair encCursor encBool) encCursor 1 1 from hround.mono).inO_one

/-- **Truncated subtraction in binary**, `b - a` from `(a, b)`. -/
public theorem natSub :
    ComputableInO (fun p : ℕ × ℕ => p.2 - p.1) (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 := by
  let clock (p : ℕ × ℕ) := p.2.bits ++ p.1.bits
  let init (p : ℕ × ℕ) := ((p.2.bits, p.1.bits), (false, ([] : List Bool)))
  have hbits : ComputableInO Nat.bits encNat encBits (fun n => (encNat n).length)
      (fun n => (encNat n).length) := of_eq fun _ => rfl
  have hl := hbits.comp_linear (snd encNat encNat)
  have hr := hbits.comp_linear (fst encNat encNat)
  have hclock := hl.append hr (encOut := encBits) (g := clock) fun _ => rfl
  have hinit := (hl.prod hr).prod
    (const (encMid := encPair encBool encBits) (false, ([] : List Bool)))
  have hstate (p : ℕ × ℕ) (i : ℕ) :
      (encCursor (((clock p).take i).foldl BinarySub.cursorStep (init p))).length ≤
        8 * (encPair encNat encNat p).length + 10 := by
    obtain ⟨hl, hr, ho⟩ := BinarySub.cursorStep_lengths ((clock p).take i)
      p.2.bits p.1.bits (false, [])
    have ht : ((clock p).take i).length ≤ p.2.bits.length + p.1.bits.length :=
      (List.length_take_le' i (clock p)).trans_eq (by simp only [clock, List.length_append])
    simp only [encCursor, init, length_encPair, encBits_apply, encBool_apply,
      List.length_singleton, encNat_apply]
    simp only [List.length_nil, Nat.zero_add] at ho
    omega
  have hround (p : ℕ × ℕ) (i : ℕ) (hi : i < (clock p).length) :
      (encPair encCursor encBool
        (((clock p).take i).foldl BinarySub.cursorStep (init p), (clock p)[i])).length ≤
        20 * (encPair encNat encNat p).length + 30 := by
    have := hstate p i
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have hfold := (foldl hclock hinit cursorStep_inO
    (R := fun p => 20 * (encPair encNat encNat p).length + 30)
    (Q := fun p => 20 * (encPair encNat encNat p).length + 30)
    (B := fun p => 8 * (encPair encNat encNat p).length + 10)
    hround hround (fun p i _ => hstate p i)).mono
    (T' := fun p => ((encPair encNat encNat p).length + 1) ^ 2)
    (S' := fun p => (encPair encNat encNat p).length + 1) 100
    (fun p => by
      simp only [clock, encBits_apply, List.length_append, length_encPair, encNat_apply]
      nlinarith)
    (fun p => by
      simp only [clock, encBits_apply, List.length_append, length_encPair, encNat_apply]
      omega)
  have hacc := hfold.snd'
  have heq (p : ℕ × ℕ) : ((clock p).foldl BinarySub.cursorStep (init p)).2 =
      (BinarySub.digitPairs (p.2, p.1)).foldl BinarySub.subStep (false, []) := by
    rw [BinarySub.foldl_cursorStep]
    simp only [clock, List.length_append, BinarySub.digitPairs]
  have h := hacc.fst'.ite (const 0) (bitsToNat.comp_linear hacc.snd')
  refine (h.mono 3 (fun p => ?_) (fun p => ?_)).of_enc_eq fun p => ?_
  · split_ifs <;> simp only [length_encPair, encNat_apply] <;> nlinarith
  · split_ifs <;> omega
  · change encNat (p.2 - p.1) = encNat
      (if ((clock p).foldl BinarySub.cursorStep (init p)).2.1 then 0
        else ofBits ((clock p).foldl BinarySub.cursorStep (init p)).2.2)
    rw [heq]
    exact congrArg encNat (BinarySub.sub_eq (p.2, p.1))

/-- **The strict order in binary.** -/
public theorem natLt :
    ComputableInO (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 := by
  have hnot : ComputableInO (fun b : Bool => !b) encBool encBool
      (fun b => (encBool b).length) fun b => (encBool b).length :=
    (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) _).inO_one
  refine (hnot.comp_linear (natIsZero.comp_linear natSub)).of_enc_eq fun p => ?_
  simp only [Function.comp_apply]
  congr 1
  by_cases h : p.1 < p.2 <;> simp [h] <;> omega


end Turing.MultiTapeTM.ComputableInO
