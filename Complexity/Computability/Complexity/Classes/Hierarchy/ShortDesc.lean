/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Data.Nat.Size
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Short descriptions

The time and space hierarchy theorems diagonalize only over inputs whose framed description is
*short*: `2 ^ |unframe x| ≤ |x|` (`Cslib.Complexity.Diagonal.shortDesc`). Decoding a description
of `L` bits then takes time polynomial in `L`, of a degree fixed by the decoder, hence `O(2 ^ L)`,
which is `O(|x|)`. Padded descriptions are short.

## Main definitions

* `Cslib.Complexity.Diagonal.shortDesc`: whether the framed description at the start of a word is
  short.

## Main results

* `Cslib.Complexity.Diagonal.shortDesc_eq_decide`: shortness compares the length of the
  description with the number of binary digits of the length of the word.
* `Cslib.Complexity.Diagonal.computableInO_shortDesc`: shortness is decided within quadratic
  time and linear space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorems 9.3 and 9.10][Sipser2013]:
  the padded descriptions in the proofs of the hierarchy theorems.
-/

@[expose] public section

namespace Cslib.Complexity.Diagonal

open Turing Turing.MultiTapeTM

/-- The description framed at the start of `x` is *short*: `2 ^ |unframe x| ≤ |x|`. -/
def shortDesc (x : List Bool) : Bool := decide (2 ^ (unframe x).length ≤ x.length)

/-- Shortness compares the length of the description with the number of binary digits of the
length of the word. -/
theorem shortDesc_eq_decide (x : List Bool) :
    shortDesc x = decide ((unframe x).length + 1 ≤ (encNat x.length).length) := by
  rw [shortDesc, encNat_apply, Nat.size_eq_bits_len]
  exact decide_eq_decide.mpr (Nat.lt_size.symm.trans Nat.lt_iff_add_one_le)

/-- Shortness is decided within quadratic time and linear space. -/
theorem computableInO_shortDesc :
    ComputableInO shortDesc encBits encBool (fun x => (x.length + 1) ^ 2)
      fun x => x.length + 1 := by
  have this : ComputableTidilyInO shortDesc encBits encBool (fun x => (x.length + 1) ^ 2) fun x =>
      x.length + 1 := by
    have hu : ComputableTidilyInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
      ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)
    have ha := ComputableTidilyInDegree.unary_succ.inO_one.comp
      (ComputableTidilyInO.lengthUnary.comp hu)
    have hb := ComputableTidilyInO.lengthUnary.comp
      (ComputableTidilyInO.lengthNat.of_enc_eq (encOut := encBits)
        (g := fun x : List Bool => encNat x.length) fun _ => rfl)
    have h := ComputableTidilyInO.unaryLe.comp (ha.prod hb)
    refine (h.mono 64 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
    · have h₁ := length_unframe_le x
      have h₂ := Universal.length_encNat_le x.length
      simp only [Function.comp_apply, length_encPair, encUnary_apply,
        List.length_replicate] at h₁ h₂ ⊢
      nlinarith
    · have h₁ := length_unframe_le x
      have h₂ := Universal.length_encNat_le x.length
      simp only [Function.comp_apply, length_encPair, encUnary_apply,
        List.length_replicate] at h₁ h₂ ⊢
      omega
    · simp only [Function.comp_apply, shortDesc_eq_decide]
  simpa only [computableInO_iff_computableTidilyInO] using this

end Cslib.Complexity.Diagonal
