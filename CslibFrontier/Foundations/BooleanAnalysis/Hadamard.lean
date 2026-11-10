/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Linearity
public import CslibFrontier.Foundations.Data.Code.Hadamard

/-!
# Decoding the Hadamard code from the BLR linearity test

Hadamard codewords (`BitString.hadamardCode`) are parities, so they pass the Blum–Luby–Rubinfeld
linearity test with probability one (`BitString.blrAcceptance_hadamardCode`). Conversely, by the
Fourier soundness of the test (`BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`), a
Boolean function that passes the test with probability at least `1 - ε` is within relative Hamming
distance `ε` of the Hadamard encoding of some message
(`BitString.exists_hammingDist_hadamardCode_le_of_le_blrAcceptance`), and when `ε < 1/4` that
message is unique (`BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance`)
[O'Donnell, Section 1.6][ODonnell2014], [Arora and Barak, Section 11.5][AroraBarak09].

## Main results

* `Cslib.BitString.blrAcceptance_hadamardCode`: Hadamard codewords pass the BLR test with
  probability one.
* `Cslib.BitString.exists_hammingDist_hadamardCode_le_of_le_blrAcceptance`,
  `Cslib.BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance`: decoding a
  function that passes the linearity test.

## References

* [M. Blum, M. Luby, R. Rubinfeld, *Self-testing/correcting with applications to numerical
  problems*][BlumLubyRubinfeld1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hadamard codewords pass the BLR test with probability one. -/
@[simp] theorem blrAcceptance_hadamardCode (x : ι → Bool) :
    blrAcceptance (hadamardCode x) = 1 := by
  rw [hadamardCode_eq_parityOn, blrAcceptance_parityOn]

/-- **Decoding from the BLR test**: if the test accepts `f` with probability at least `1 - ε`,
then `f` is within relative distance `ε` of the Hadamard encoding of some bit string. -/
theorem exists_hammingDist_hadamardCode_le_of_le_blrAcceptance {f : (ι → Bool) → Bool} {ε : ℝ}
    (h : 1 - ε ≤ blrAcceptance f) :
    ∃ x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨S, hS⟩ := exists_hammingDist_parityOn_le_of_le_blrAcceptance h
  exact ⟨fun i => decide (i ∈ S), by rwa [hadamardCode_decide_mem]⟩

/-- **Unique decoding from the BLR test**: if the test accepts `f` with probability at least
`1 - ε` and `ε < 1/4`, then exactly one bit string has its Hadamard encoding within relative
distance `ε` of `f`. -/
theorem existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance {f : (ι → Bool) → Bool}
    {ε : ℝ} (hε : ε < 1 / 4) (h : 1 - ε ≤ blrAcceptance f) :
    ∃! x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε :=
  let ⟨x, hx⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance h
  ⟨x, hx, fun _ hy => eq_of_hammingDist_hadamardCode_le hε hy hx⟩

end Cslib.BitString
