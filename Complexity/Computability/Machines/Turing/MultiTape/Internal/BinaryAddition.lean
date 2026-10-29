/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives
import Mathlib.Tactic.Linarith

/-!
# Quadratic schoolbook binary addition

The existing `NatAdd.addStep` fold consumes the first input's bits and the remaining bits of the
second input, emitting one sum digit per round. A second consuming fold adds the carry to the
remaining second input. Both folds have linear-sized states and linear-cost rounds, so addition
takes quadratic time and independent linear output-charged workspace in the encoded input length.
No iteration by the numeric operands or normalization of the result is needed.

## Main results

* `ComputableInO.natAdd`: binary addition in quadratic time and linear charged workspace.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

private abbrev encAdd := encPair encBool (encPair encBits encBits)

private theorem addStep_inO :
    ComputableInO (fun p => NatAdd.addStep p.1 p.2) (encPair encAdd encBool) encAdd
      (fun p => (encPair encAdd encBool p).length)
      (fun p => (encPair encAdd encBool p).length) := by
  have hs := ComputableInDegree.fst encAdd encBool
  have hrest := (ComputableInDegree.snd encBool (encPair encBits encBits)).comp hs
  have hr := (ComputableInDegree.fst encBits encBits).comp hrest
  have hflag := (ComputableInDegree.fst encBool (encPair encBits encBits)).comp hs
  have hout := (ComputableInDegree.snd encBits encBits).comp hrest
  have habc := (ComputableInDegree.snd encAdd encBool).prod
    (Internal.DecoderWords.bool_degree.comp hr |>.prod hflag)
  have hcarry := (ComputableInDegree.of_finite
    (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encBool) fun t : Bool × Bool × Bool => NatAdd.carry t.1 t.2.1 t.2.2).comp habc
  have hdigit := (ComputableInDegree.of_finite
    (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encBool) fun t : Bool × Bool × Bool => t.1 ^^ (t.2.1 ^^ t.2.2)).comp habc
  exact (show ComputableInDegree (fun p => NatAdd.addStep p.1 p.2)
    (encPair encAdd encBool) encAdd 1 1 from
      (hcarry.prod ((Internal.DecoderWords.tail_degree.comp hr).prod
        (hout.append hdigit (encOut := encBits) fun _ => rfl))).mono).inO_one

private theorem finish_inO :
    ComputableInO (fun s : Bool × List Bool × List Bool =>
      NatSucc.succFinish (s.2.1.foldl NatSucc.succStep (s.1, s.2.2))) encAdd encBits
      (fun s => ((encAdd s).length + 1) ^ 2) (fun s => (encAdd s).length + 1) := by
  have hs : ComputableInO id encAdd encAdd (fun s => (encAdd s).length)
      (fun s => (encAdd s).length) := of_eq fun _ => rfl
  have hstate (s : Bool × List Bool × List Bool) (i : ℕ) :
      (encPair encBool encBits ((s.2.1.take i).foldl NatSucc.succStep (s.1, s.2.2))).length ≤
        (encAdd s).length + 3 := by
    simp only [NatSucc.length_foldl_succStep, encAdd, length_encPair, encBool_apply,
      List.length_singleton, encBits_apply]
    have := List.length_take_le' i s.2.1
    omega
  have hround (s : Bool × List Bool × List Bool) (i : ℕ) (hi : i < s.2.1.length) :
      (encPair (encPair encBool encBits) encBool
        ((s.2.1.take i).foldl NatSucc.succStep (s.1, s.2.2), s.2.1[i])).length ≤
        2 * (encAdd s).length + 8 := by
    have := hstate s i
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have hfold := (foldl hs.snd'.fst' (hs.fst'.prod hs.snd'.snd') succStep
    (R := fun s => 2 * (encAdd s).length + 8)
    (Q := fun s => 2 * (encAdd s).length + 8) (B := fun s => (encAdd s).length + 3)
    hround hround (fun s i _ => hstate s i)).mono
    (T' := fun s => ((encAdd s).length + 1) ^ 2)
    (S' := fun s => (encAdd s).length + 1) 20
    (fun s => by
      simp only [encAdd, encBits_apply, length_encPair, encBool_apply, List.length_singleton,
        id_eq]
      nlinarith)
    (fun s => by
      simp only [encAdd, encBits_apply, length_encPair, encBool_apply, List.length_singleton,
        id_eq]
      omega)
  exact succFinish.comp_linear hfold

/-- **Binary addition**, using the existing consuming carry folds. Time is quadratic and charged
workspace linear in the framed input length, independently of the numeric operands. -/
theorem natAdd :
    ComputableInO (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      (fun p => (encPair encNat encNat p).length + 1) := by
  have hbits : ComputableInO Nat.bits encNat encBits (fun n => (encNat n).length)
      (fun n => (encNat n).length) := of_eq fun _ => rfl
  have hlist := hbits.comp_linear (fst encNat encNat)
  have hinit := (const (encMid := encBool) false).prod
    ((hbits.comp_linear (snd encNat encNat)).prod (const (encMid := encBits) []))
  have hstate (p : ℕ × ℕ) (i : ℕ) :
      (encAdd ((p.1.bits.take i).foldl NatAdd.addStep (false, p.2.bits, []))).length ≤
        2 * (encPair encNat encNat p).length + 4 := by
    obtain ⟨hr, ho⟩ := NatAdd.length_foldl_addStep (p.1.bits.take i) (false, p.2.bits, [])
    have := List.length_take_le' i p.1.bits
    dsimp only at hr ho
    simp only [List.length_nil, Nat.zero_add] at ho
    simp only [encAdd, length_encPair, encBool_apply, List.length_singleton, encBits_apply,
      encNat_apply]
    omega
  have hround (p : ℕ × ℕ) (i : ℕ) (hi : i < p.1.bits.length) :
      (encPair encAdd encBool
        ((p.1.bits.take i).foldl NatAdd.addStep (false, p.2.bits, []), p.1.bits[i])).length ≤
        4 * (encPair encNat encNat p).length + 10 := by
    have := hstate p i
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have hfold := (foldl hlist hinit addStep_inO
    (R := fun p => 4 * (encPair encNat encNat p).length + 10)
    (Q := fun p => 4 * (encPair encNat encNat p).length + 10)
    (B := fun p => 2 * (encPair encNat encNat p).length + 4)
    hround hround (fun p i _ => hstate p i)).mono
    (T' := fun p => ((encPair encNat encNat p).length + 1) ^ 2)
    (S' := fun p => (encPair encNat encNat p).length + 1) 30
    (fun p => by
      simp only [encBits_apply, length_encPair, encNat_apply, Function.comp_apply]
      nlinarith)
    (fun p => by
      simp only [encBits_apply, length_encPair, encNat_apply, Function.comp_apply]
      omega)
  refine ((finish_inO.comp hfold).mono 30 (fun p => ?_) (fun p => ?_)).of_enc_eq fun p => ?_
  · have := hstate p p.1.bits.length
    rw [List.take_length] at this
    simp only [Function.comp_apply]
    nlinarith
  · have := hstate p p.1.bits.length
    rw [List.take_length] at this
    simp only [Function.comp_apply]
    omega
  · simp only [Function.comp_apply, encBits_apply, encNat_apply]
    rw [NatSucc.succFinish_foldl, ← NatAdd.foldl_addStep, List.nil_append, NatAdd.addBits_bits]
    rfl

end Turing.MultiTapeTM.ComputableInO
