/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LocallyDecodable.Basic
public import CslibFrontier.Foundations.Data.Code.Hadamard
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.Linarith

/-!
# The Hadamard code is a two-query locally decodable code

The Hadamard code `BitString.hadamardCode x a = x ⬝ᵥ a` of a message `x : ι → Bool` has a local
decoder making two queries: to recover the bit `x i` from a received word `y`, draw a uniform
`r : ι → Bool`, read `y r` and `y (eᵢ + r)`, and output their exclusive or
(`BitString.hadamardDecoder`). Each of the two positions read is uniform, so a word that differs
from the codeword on a fraction `δ` of the positions corrupts either read with probability at most
`δ`, and the decoder fails with probability at most `2 δ`
(`BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply`). It is therefore a
`(2, δ, 1 / 2 - 2 δ)` local decoder for every `δ`, and a `(2, 2, 1 / 2)` smooth decoder
[Arora and Barak, Chapters 11 and 19][AroraBarak09], [Yekhanin, Chapter 1][Yekhanin2012].

## Main definitions

* `Cslib.BitString.hadamardDecoder`: the two-query local decoder.

## Main results

* `Cslib.BitString.isLocalDecoder_hadamardDecoder`: a `(2, δ, 1 / 2 - 2 δ)` local decoder.
* `Cslib.BitString.isSmoothDecoder_hadamardDecoder`: a `(2, 2, 1 / 2)` smooth decoder.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapters 11
  and 19
* [S. Yekhanin, *Locally decodable codes*][Yekhanin2012], Chapter 1
-/

public section

open scoped ENNReal

namespace Cslib.BitString

open Code Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The two-query local decoder of the Hadamard code: to decode the bit `i`, draw a uniform `r`,
read the received word at `r` and at `eᵢ + r`, and output the exclusive or of the two symbols. -/
noncomputable def hadamardDecoder : LocalDecoder ι (ι → Bool) Bool := fun i =>
  nonadaptive (ProbComp.uniform (ι → Bool)) (fun r => ![r, Pi.single i true + r])
    (fun _ a => a 0 ^^ a 1)

theorem decodeLaw_hadamardDecoder (i : ι) (y : (ι → Bool) → Bool) :
    decodeLaw (hadamardDecoder i) y =
      (PMF.uniformOfFintype (ι → Bool)).map (selfCorrect y (Pi.single i true)) := by
  rw [hadamardDecoder, decodeLaw_nonadaptive, ProbComp.eval_uniform]
  rfl

/-- Both reads of the Hadamard decoder are uniform positions. -/
theorem map_hadamardDecoder_query (i : ι) (k : Fin 2) :
    (ProbComp.eval (ProbComp.uniform (ι → Bool))).map
        (fun r => ![r, Pi.single i true + r] k) = PMF.uniformOfFintype (ι → Bool) := by
  rw [ProbComp.eval_uniform]
  fin_cases k
  · exact PMF.map_id _
  · exact PMF.uniformOfFintype_map_equiv (Equiv.addLeft (Pi.single i true : ι → Bool))

/-- The reads of the Hadamard decoder do not depend on the received word. -/
theorem hasObliviousReads_hadamardDecoder (i : ι) : HasObliviousReads (hadamardDecoder i) :=
  hasObliviousReads_nonadaptive _ _ _

/-- **The Hadamard code is locally decodable with two queries**: from a word that differs from the
codeword on a fraction `δ` of the positions, the decoder outputs each bit of the message with
probability at least `1 - 2 δ`. -/
theorem isLocalDecoder_hadamardDecoder (δ : ℝ) :
    IsLocalDecoder hadamardCode 2 δ (1 / 2 - 2 * δ) (hadamardDecoder (ι := ι)) where
  isQueryBounded _ := isQueryBounded_nonadaptive _ _ _
  correct x y i hy := by
    have hcard : (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι := by simp
    rw [hcard] at hy
    have h := one_sub_two_mul_le_expect_selfCorrect_eq_apply (f := y) (x := x)
      ((div_le_iff₀ (by positivity)).mpr hy) i
    rw [Fintype.expect_boole] at h
    rw [decodeLaw_hadamardDecoder, PMF.toReal_uniformOfFintype_map_apply]
    linarith

/-- **The Hadamard code is a smooth code with two queries**: its decoder reads each of the
`2 ^ |ι|` positions `2 / 2 ^ |ι|` times in expectation and decodes codewords exactly. -/
theorem isSmoothDecoder_hadamardDecoder :
    IsSmoothDecoder hadamardCode 2 2 (1 / 2) (hadamardDecoder (ι := ι)) :=
  isSmoothDecoder_nonadaptive_of_uniform _ _ _ (fun i => map_hadamardDecoder_query i)
    fun x i => by
      have h := (isLocalDecoder_hadamardDecoder (ι := ι) 0).correct x (hadamardCode x) i
        (by simp)
      have hε : (1 / 2 + (1 / 2 - 2 * 0) : ℝ) = 1 / 2 + 1 / 2 := by norm_num
      rw [hε] at h
      exact h

end Cslib.BitString
