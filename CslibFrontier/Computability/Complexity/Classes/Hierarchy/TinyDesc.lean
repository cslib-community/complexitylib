/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Tiny descriptions

The space hierarchy below linear space diagonalizes only over inputs whose framed description is
*tiny*: `2 ^ |unframe x| ≤ Nat.size |x|`, that is, at most `log₂ |x| + 1`
(`Cslib.Complexity.Diagonal.tinyDesc`). Decoding a description of `L` bits takes space polynomial
in `L`, of a degree fixed by the decoder, hence `O(2 ^ L)`, which is `O(log |x|)`. So a diagonal
reading its input in place decodes its description in logarithmic space
(`Cslib.Complexity.Diagonal.computableInLogSpace_decodeDesc_tinyCut`). Padded descriptions are tiny
once the padding is doubly exponential in the description.

## Main definitions

* `Cslib.Complexity.Diagonal.tinyDesc`: whether the framed description at the start of a word is
  tiny.
* `Cslib.Complexity.Diagonal.tinyCut`: the framed description at the start of a word when it is
  tiny, and the empty word otherwise.

## Main results

* `Cslib.Complexity.Diagonal.tinyDesc_frame_append`: a description padded to doubly exponential
  length is tiny.
* `Cslib.Complexity.Diagonal.computableInLogSpace_tinyDesc`,
  `Cslib.Complexity.Diagonal.computableInLogSpace_tinyCut`: tininess is decided, and tiny
  descriptions are cut out, in logarithmic space.
* `Cslib.Complexity.Diagonal.computableInLogSpace_decodeDesc_tinyCut`: tiny descriptions are decoded
  in logarithmic space.
* `Cslib.Complexity.Diagonal.exists_length_eDesc_decodeDesc_tinyCut_le`: the decoded tiny
  description has `O(log |x|)` bits.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 9.3][Sipser2013]: the padded
  descriptions in the proof of the space hierarchy theorem.
-/

public section

namespace Cslib.Complexity.Diagonal

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- The description framed at the start of `x` is *tiny*: `2 ^ |unframe x| ≤ Nat.size |x|`, the
number of binary digits of the length of `x`. -/
@[expose] def tinyDesc (x : List Bool) : Bool := decide (2 ^ (unframe x).length ≤ x.length.size)

/-- Tininess compares the length of the description with the binary length of the binary length of
the word. -/
theorem tinyDesc_eq_decide (x : List Bool) :
    tinyDesc x = decide ((unframe x).length < x.length.size.size) :=
  decide_eq_decide.mpr Nat.lt_size.symm

/-- The description framed at the start of `x` when it is tiny, and the empty word otherwise. -/
def tinyCut (x : List Bool) : List Bool := if tinyDesc x then unframe x else []

theorem tinyCut_of_tinyDesc {x : List Bool} (h : tinyDesc x = true) : tinyCut x = unframe x := by
  simp [tinyCut, h]

/-- A cut description is tiny: `2 ^ |tinyCut x| ≤ log₂ |x| + 1`. -/
theorem two_pow_length_tinyCut_le (x : List Bool) :
    2 ^ (tinyCut x).length ≤ Nat.log2 x.length + 1 := by
  have h := Nat.log2_eq_size_sub_one x.length
  unfold tinyCut
  split_ifs with hx
  · have := of_decide_eq_true hx
    omega
  · simp

/-- **A description padded to doubly exponential length is tiny.** -/
theorem tinyDesc_frame_append {w pad : List Bool} (h : 2 ^ 2 ^ w.length ≤ pad.length) :
    tinyDesc (frame w ++ pad) = true := by
  rw [tinyDesc, unframe_frame_append, decide_eq_true_eq]
  exact (Nat.lt_size.mpr (h.trans (by rw [List.length_append]; omega))).le

/-! ### Tiny descriptions in logarithmic space -/

/-- **Tininess is decided in logarithmic space**, by comparing unary numbers. -/
theorem computableInLogSpace_tinyDesc : ComputableInLogSpace tinyDesc encBits encBool := by
  have hu : ComputableInLogSpace (fun x : List Bool => (unframe x).length) encBits encUnary :=
    ComputableInLogSpace.bitsLength.comp (ComputableInLogSpace.of_unframe (encIn := encBits)
      (encOut := encBits) (f := unframe) fun _ => rfl)
  have hn := ComputableInLogSpace.unarySize
    (ComputableInLogSpace.unarySize ComputableInLogSpace.bitsLength)
  exact (ComputableInLogSpace.unaryLt hu hn).congr_fun tinyDesc_eq_decide

/-- **Tiny descriptions are cut out in logarithmic space.** -/
theorem computableInLogSpace_tinyCut : ComputableInLogSpace tinyCut encBits encBits :=
  ComputableInLogSpace.ite computableInLogSpace_tinyDesc
    (ComputableInLogSpace.of_unframe fun _ => rfl) (ComputableInLogSpace.const [])

/-- **Tiny descriptions are decoded in logarithmic space.** Decoding takes space polynomial in the
length `L` of the description, which is `O(2 ^ L) = O(log n)` on a tiny description, and the
cut description is recomputed whenever the decoder reads it
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space`). -/
theorem computableInLogSpace_decodeDesc_tinyCut :
    ComputableInLogSpace (fun x => decodeDesc (tinyCut x)) encBits eDesc := by
  obtain ⟨dd, -, ⟨td, sd, -, ⟨cs, hcs⟩, hdec⟩, -⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨tc, cc, hcut⟩ := computableInLogSpace_tinyCut
  obtain ⟨c, h⟩ := ComputableInTimeAndSpace.comp_space hcut hdec
  obtain ⟨A, hA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
    (by fun_prop)
  refine ⟨_, c * (cc + cs * A + 4), h.mono (fun _ => le_rfl) fun x => ?_⟩
  simp only [encBits_apply]
  have hL := two_pow_length_tinyCut_le x
  have hs : sd (tinyCut x) ≤ cs * A * (Nat.log2 x.length + 1) := by
    have h₁ := hcs (tinyCut x)
    have h₂ := hA (tinyCut x).length
    simp only [encBits_apply] at h₁
    calc sd (tinyCut x) ≤ cs * (A * 2 ^ (tinyCut x).length) := h₁.trans (Nat.mul_le_mul_left _ h₂)
      _ ≤ cs * (A * (Nat.log2 x.length + 1)) := by gcongr
      _ = _ := by ring
  have hn : (encNat (x.length + 1)).length ≤ Nat.log2 x.length + 2 :=
    length_encNat_le_log2_add_two le_rfl
  have hm : (encNat ((tinyCut x).length + 1)).length ≤ Nat.log2 x.length + 1 := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    have := Nat.lt_two_pow_self (n := (tinyCut x).length)
    exact (Nat.size_le_self _).trans (by omega)
  generalize Nat.log2 x.length = l at *
  have : c * (cc * (l + 1) + sd (tinyCut x) + (encNat (x.length + 1)).length +
      (encNat ((tinyCut x).length + 1)).length + 1) ≤ c * ((cc + cs * A + 4) * (l + 1)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  simpa only [mul_assoc] using this

/-- **Tiny descriptions decode to short descriptions**: the decoded cut description has encoded
length `O(log n)`, since decoding `L` bits gives a description of length polynomial in `L`. -/
theorem exists_length_eDesc_decodeDesc_tinyCut_le :
    ∃ c, ∀ x, (eDesc (decodeDesc (tinyCut x))).length ≤ c * (Nat.log2 x.length + 1) := by
  obtain ⟨_, e, -, ce, hce⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨A, hA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ e)
    (by fun_prop)
  refine ⟨ce * A, fun x => ?_⟩
  have h₁ := hce (tinyCut x)
  simp only [encBits_apply] at h₁
  calc _ ≤ ce * (A * 2 ^ (tinyCut x).length) := h₁.trans (Nat.mul_le_mul_left _ (hA _))
    _ ≤ ce * (A * (Nat.log2 x.length + 1)) := by gcongr; exact two_pow_length_tinyCut_le x
    _ = _ := by ring

end Cslib.Complexity.Diagonal
