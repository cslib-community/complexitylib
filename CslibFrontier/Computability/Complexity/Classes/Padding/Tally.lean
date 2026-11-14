/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Padding
public import CslibFrontier.Computability.Complexity.Classes.Tally
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Unpair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Tally padding: easy tally `NP` collapses exponential time

If every tally problem in `NP` is in `P`, then `EXP = NEXP` and `E = NE`
[Arora and Barak, Exercise 2.23][AroraBarak07]; this is one direction of the theorem of Hartmanis,
Immerman and Sewelson that `E = NE` exactly when every tally problem in `NP` is in `P`.

The proof shows that the hypothesis makes `NP` easy on exponentially padded instances
(`Cslib.Complexity.ExpPaddedNPEasy`), from which the padding argument of
`CslibFrontier.Computability.Complexity.Classes.Padding` concludes. An exponentially padded word
`frame u ++ 1^m`, with `2 ^ |u| ≤ m`, is written in unary as the number
`Nat.pair (tallyCode u) m`, where `tallyCode u` is the number whose binary digits, least
significant first, are `u` followed by a one (`Cslib.Complexity.tallyCode`). Since
`tallyCode u < 2 ^ (|u| + 1) ≤ 2 * m`, this number is polynomial in the length of the padded word,
and conversely the padded word is short compared to it.

* The tally problem `Cslib.Complexity.tallyOf B` of a problem `B ∈ NP` consists of the words
  `1^N` whose decoded word `Cslib.Complexity.tallyDecode N` is in `B`. It is in `NP`
  (`Cslib.Complexity.tallyOf_mem_NP`).
* By hypothesis it is in `P`. The padded word `w` is mapped to `1^N` in polynomial time, where the
  code of `unframe w` is capped at `2 * |w|` so that the map is polynomial on every word
  (`Cslib.Complexity.tallyEncode`). The preimage of the tally problem is in `P` and agrees with `B`
  on exponentially padded words.

## Main definitions

* `Cslib.Complexity.tallyCode`, `Cslib.Complexity.tallyDecode`, `Cslib.Complexity.tallyEncode`:
  writing padded words as unary numbers and back.
* `Cslib.Complexity.tallyOf`: the tally problem of a problem on bit words.

## Main results

* `Cslib.Complexity.expPaddedNPEasy_of_tally`: easy tally `NP` makes `NP` easy on exponentially
  padded instances.
* `Cslib.Complexity.EXP_eq_NEXP_of_tally`, `Cslib.Complexity.E_eq_NE_of_tally`: if every tally
  problem in `NP` is in `P`, then `EXP = NEXP` and `E = NE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
* [J. Hartmanis, N. Immerman, V. Sewelson, *Sparse sets in NP − P: EXPTIME versus
  NEXPTIME*][HartmanisImmermanSewelson1985]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The number whose binary digits, least significant first, are `u` followed by a one. -/
def tallyCode (u : List Bool) : ℕ :=
  ofBits (u ++ [true])

theorem bits_tallyCode (u : List Bool) : (tallyCode u).bits = u ++ [true] := by
  rw [tallyCode, bits_ofBits]
  simp

theorem tallyCode_lt (u : List Bool) : tallyCode u < 2 ^ (u.length + 1) := by
  simpa [tallyCode] using ofBits_lt_two_pow (u ++ [true])

/-- The word written in unary by the number `N`: the pair `N.unpair` gives the code of a word `u`
and a length `m`, and the word is `frame u ++ 1^m`. -/
def tallyDecode (N : ℕ) : List Bool :=
  frame N.unpair.1.bits.dropLast ++ List.replicate N.unpair.2 true

theorem tallyDecode_pair_tallyCode (u : List Bool) (m : ℕ) :
    tallyDecode (Nat.pair (tallyCode u) m) = frame u ++ List.replicate m true := by
  simp [tallyDecode, bits_tallyCode]

/-- The unary number of a word `w`, read as a padded word `frame u ++ 1^m`: the pair of the code of
`u`, capped at `2 * |w|`, and `m`. -/
def tallyEncode (w : List Bool) : ℕ :=
  Nat.pair (min (2 * w.length) (tallyCode (unframe w)))
    (w.length - (2 * (unframe w).length + 1))

/-- The tally problem of `B`: the words `1^N` such that `tallyDecode N ∈ B`. -/
def tallyOf (B : Set (List Bool)) : Set (List Bool) :=
  {x | (∀ b ∈ x, b = true) ∧ tallyDecode x.length ∈ B}

theorem tallyOf_mem_TALLY (B : Set (List Bool)) : tallyOf B ∈ TALLY :=
  fun _ hx => hx.1

theorem computableInPolyTime_tallyDecode :
    ComputableInPolyTime tallyDecode encUnary encBits := by
  have hbits : ComputableInPolyTime (fun n : ℕ => n.bits) encUnary encBits :=
    .of_tidy (ComputableTidilyInPolyTime.natBits.comp ComputableTidilyInPolyTime.unary_to_binary)
  have hu : ComputableInPolyTime (fun N : ℕ => N.unpair.1.bits.reverse.tail.reverse)
      encUnary encBits := by
    have hp : ComputableInPolyTime (fun N : ℕ => N.unpair.1) encUnary encUnary := by fun_prop
    have := hbits.comp hp
    fun_prop
  have h : tallyDecode = fun N => frame N.unpair.1.bits.reverse.tail.reverse ++
      List.replicate N.unpair.2 true := by
    funext N
    rw [tallyDecode, List.tail_reverse, List.reverse_reverse]
  rw [h]
  fun_prop

/-- The capped code, read most significant digit first with a saturating accumulator. -/
private theorem min_tallyCode_eq (L : ℕ) (u : List Bool) :
    min L (tallyCode u) = BitString.boundedBinaryValue L (u ++ [true]).reverse := by
  rw [BitString.boundedBinaryValue_eq, ← bits_tallyCode, BitString.binaryValue_reverse_bits]

theorem computableInPolyTime_tallyEncode :
    ComputableInPolyTime tallyEncode encBits encUnary := by
  have h : tallyEncode = fun w => Nat.pair
      (BitString.boundedBinaryValue (2 * w.length) (unframe w ++ [true]).reverse)
      (w.length - (2 * (unframe w).length + 1)) := by
    funext w
    rw [tallyEncode, min_tallyCode_eq]
  rw [h]
  fun_prop

/-- The tally problem of a problem in `NP` is in `NP`: check that the word is all ones, and decode
it in polynomial time. -/
theorem tallyOf_mem_NP {B : Set (List Bool)} (hB : B ∈ NP encBits) : tallyOf B ∈ NP encBits := by
  have hones : {x : List Bool | ∀ b ∈ x, b = true} ∈ P encBits :=
    ⟨fun x => decide (x = List.replicate x.length true), by fun_prop, fun x => by
      simp [List.eq_replicate_iff]⟩
  have hdec : PolyTimeReducible encBits encBits
      {x : List Bool | tallyDecode x.length ∈ B} B := by
    have := computableInPolyTime_tallyDecode
    exact ⟨fun x => tallyDecode x.length, by fun_prop, fun _ => Iff.rfl⟩
  exact inter_mem_NP (P_subset_NP hones) (hdec.mem_NP hB)

theorem tallyEncode_frame_append {u : List Bool} {m : ℕ} (hm : 2 ^ u.length ≤ m) :
    tallyEncode (frame u ++ List.replicate m true) = Nat.pair (tallyCode u) m := by
  have hc := tallyCode_lt u
  rw [pow_succ] at hc
  simp only [tallyEncode, unframe_frame_append, List.length_append, length_frame,
    List.length_replicate]
  congr 1
  · exact Nat.min_eq_right (by omega)
  · omega

/-- **Easy tally `NP` makes `NP` easy on exponentially padded instances.** -/
theorem expPaddedNPEasy_of_tally
    (h : ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits) : ExpPaddedNPEasy := by
  intro B hB
  refine ⟨(fun w => List.replicate (tallyEncode w) true) ⁻¹' tallyOf B,
    PolyTimeReducible.mem_P (B := tallyOf B) ⟨_, ?_, fun _ => Iff.rfl⟩
      (h (tallyOf B) (tallyOf_mem_TALLY B) (tallyOf_mem_NP hB)), fun u m hm => ?_⟩
  · have := computableInPolyTime_tallyEncode
    fun_prop
  · simp [tallyOf, tallyEncode_frame_append hm, tallyDecode_pair_tallyCode]

/-- **If every tally problem in `NP` is in `P`, then `EXP = NEXP`**
[Arora and Barak, Exercise 2.23][AroraBarak07]. -/
theorem EXP_eq_NEXP_of_tally {α : Type} {enc : α ↪ List Bool}
    (h : ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits) : EXP enc = NEXP enc :=
  EXP_subset_NEXP.antisymm (NEXP_subset_EXP_of_expPaddedNPEasy (expPaddedNPEasy_of_tally h))

/-- **If every tally problem in `NP` is in `P`, then `E = NE`** [Hartmanis, Immerman and
Sewelson][HartmanisImmermanSewelson1985]. -/
theorem E_eq_NE_of_tally {α : Type} {enc : α ↪ List Bool}
    (h : ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits) : E enc = NE enc :=
  E_subset_NE.antisymm (NE_subset_E_of_expPaddedNPEasy (expPaddedNPEasy_of_tally h))

end Cslib.Complexity
