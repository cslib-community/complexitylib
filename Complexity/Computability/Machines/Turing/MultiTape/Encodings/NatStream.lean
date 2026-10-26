/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import Mathlib.Tactic.Linarith

/-!
# The successor in binary, as a streaming fold

The successor on `Turing.MultiTapeTM.encNat` reads the digits once, least significant first,
keeping the carry as its state: it emits each digit plus the carry and, at the end, a final carry
digit. As a streaming fold (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold`) it is
tidily computable in linear time and constant space.

## Main results

* `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_succ_stream`: the successor is tidily
  computable in linear time and constant space.
-/

namespace Turing.MultiTapeTM

namespace NatStream

open NatSucc

/-- Reads one digit and emits it. -/
def digitReader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩

/-- The carry after a digit. -/
def carry (p : Bool × Bool) : Bool := p.1 && p.2

/-- The digit plus the carry. -/
def sumDigit (p : Bool × Bool) : Bool := p.1 ^^ p.2

/-- The final carry digit. -/
def finalDigit (c : Bool) : List Bool := if c then [true] else []

lemma streamEmit_append_finalDigit (c : Bool) (l : List Bool) :
    streamEmit carry (fun p => encBool (sumDigit p)) c l ++
      encBits (finalDigit (streamState c carry l l.length)) = incr c l := by
  induction l generalizing c with
  | nil => cases c <;> rfl
  | cons b l ih =>
    have h := ih (c && b)
    simp only [streamEmit, streamState, List.length_cons, List.take_succ_cons, List.foldl_cons,
      List.take_length] at h ⊢
    cases c <;> cases b <;> simp_all [incr, carry, sumDigit]

open ComputableTidilyInLinearTimeAndSpace in
/-- The parts of a round, on the carry and a digit, in linear time and space. -/
lemma linear_parts :
    ComputableTidilyInLinearTimeAndSpace carry (encPair encBool encBool) encBool ∧
      ComputableTidilyInLinearTimeAndSpace sumDigit (encPair encBool encBool) encBool := by
  have hc : ComputableTidilyInLinearTimeAndSpace Prod.fst (encPair encBool encBool) encBool :=
    Internal.NormalForm.linear (PairEncoding.fst encBool)
  have hd : ComputableTidilyInLinearTimeAndSpace Prod.snd (encPair encBool encBool) encBool :=
    Internal.NormalForm.linear (PairEncoding.snd encBool)
  have hnot : ComputableTidilyInLinearTimeAndSpace (fun p : Bool × Bool => !p.1)
      (encPair encBool encBool) encBool := by
    convert hc.ite ((const false).restrict _) ((const true).restrict _) using 1
    funext ⟨a, b⟩
    cases a <;> rfl
  refine ⟨?_, ?_⟩
  · convert hd.ite (hc.restrict _) ((const false).restrict _) using 1
    funext ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · convert hd.ite (hnot.restrict _) (hc.restrict _) using 1
    funext ⟨a, b⟩
    cases a <;> cases b <;> rfl

open ComputableTidilyInLinearTimeAndSpace in
lemma linear_finalDigit : ComputableTidilyInLinearTimeAndSpace finalDigit encBool encBits := by
  convert (of_eq (f := id) (encIn := encBool) (encMid := encBool) fun _ => rfl).ite
    ((const [true]).restrict _) ((const []).restrict _) using 1
  funext c
  cases c <;> rfl

end NatStream

open NatSucc NatStream in
/-- The successor is tidily computable in linear time and constant space, in the binary encoding
`encNat`. -/
public theorem computableTidilyInTimeAndSpace_succ_stream :
    ∃ c, ComputableTidilyInTimeAndSpace (· + 1) encNat encNat
      (fun n => c * ((encNat n).length + 1)) (fun _ => c) := by
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (encIn := encNat) (encOut := encBool) true
  obtain ⟨⟨cN, hN⟩, ⟨cE, hE⟩⟩ := linear_parts
  obtain ⟨cF, hF⟩ := linear_finalDigit
  have hpair (p : Bool × Bool) : (encPair encBool encBool p).length = 4 := by simp
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold (g := (· + 1)) (encOut := encNat)
    digitReader (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [digitReader, InputReader.read])
    Nat.bits (fun n => by simp) hI.computableTidilyInTimeAndSpace hN hE hF
    (fun n => by
      change (n + 1).bits = _
      rw [bits_succ, ← streamEmit_append_finalDigit]
      rfl)
    (tMax := fun _ => 5 * (cN + cE)) (sMax := fun _ => 5 * (cN + cE)) (lMax := fun _ => 4)
    (fun _ _ _ => by simp only [hpair]; omega) (fun _ _ _ => by simp only [hpair]; omega)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  refine ⟨c * (2 * cI + 2 * cF + 5 * (cN + cE) + 20), h.mono (fun n => ?_) (fun n => ?_)⟩
  · simp only [encBool_apply, List.length_singleton, encNat_apply]
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left c ?_
    nlinarith
  · simp only [encBool_apply, List.length_singleton]
    exact Nat.mul_le_mul_left c (by omega)

end Turing.MultiTapeTM
