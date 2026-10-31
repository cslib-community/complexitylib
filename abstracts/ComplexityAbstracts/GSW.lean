/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract foundations)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Randomized

/-! # GSW matrix words and sampling laws

Residues modulo `2 ^ w` are written as `w`-bit words, least significant bit first. A public key is
the matrix `[B t + e | B]` in row-major order, with its noisy column first; a secret key lists the
`n` residues of `t`; and a ciphertext lists every bit of the square matrix `μ G + R A`, with rows
indexed by `(i, k)` and columns by `(j, l)`. These words are the direct bitstring inputs and
outputs of the native GSW algorithms.

Honest key generation and encryption draw independent uniform residues in `0, …, 2 ^ w - 1` and
independent centered-binomial signed errors supported on `[-noiseWidth, noiseWidth]`.
-/

namespace ComplexityTests.Abstracts.GSW

/-- Write exactly `w` digits, least significant first, including leading zeros. -/
def lowBits (w value : ℕ) : List Bool := (List.range w).map value.testBit

/-- The leading entry of `[B t + e | B]`, reduced by signed Euclidean remainder. -/
def rowHead (n w : ℕ) (inputs : List ℕ × (List (List ℕ) × List ℤ)) (i : ℕ) : ℕ :=
  (((((List.range n).map fun j =>
    (inputs.2.1.getD i []).getD j 0 * inputs.1.getD j 0).sum : ℕ) +
      inputs.2.2.getD i 0 : ℤ) % (2 ^ w : ℤ)).toNat

/-- Row-major serialization of the public matrix, with its noisy column first. -/
def publicWord (n m w : ℕ) (inputs : List ℕ × (List (List ℕ) × List ℤ)) : List Bool :=
  (List.range m).flatMap fun i =>
    lowBits w (rowHead n w inputs i) ++
      (List.range n).flatMap fun j => lowBits w ((inputs.2.1.getD i []).getD j 0 % 2 ^ w)

/-- Serialize the secret residues; these bits are not given to the adversary. -/
def secretWord (n w : ℕ) (secret : List ℕ) : List Bool :=
  (List.range n).flatMap fun j => lowBits w (secret.getD j 0 % 2 ^ w)

/-- Read a fixed-width matrix entry. Missing bits are zero, and excess bits are ignored. -/
def matrixEntry (cols w : ℕ) (word : List Bool) (i j : ℕ) : ℕ :=
  ((word.drop ((i * cols + j) * w) ++ List.replicate w false).take w).foldr Nat.bit 0

/-- An entry of `message * G + R * A`, before binary decomposition. -/
def ciphertextEntry (n m w : ℕ) (publicKey : List Bool) (message : Bool)
    (coins : List (List (List Bool))) (i k j : ℕ) : ℕ :=
  ((if i = j then message.toNat * 2 ^ k else 0) +
    ((List.range m).map fun r =>
      if ((coins.getD i []).getD k []).getD r false then
        matrixEntry (n + 1) w publicKey r j else 0).sum) % 2 ^ w

/-- Write every bit of the square ciphertext. Its row order is `(i, k)` and column order
`(j, l)`; this is the bit decomposition of `message * G + R * A`, which equals GSW's
`Flatten(μ I_N + BitDecomp(R A))`. -/
def ciphertextWord (n m w : ℕ) (publicKey : List Bool) (message : Bool)
    (coins : List (List (List Bool))) : List Bool :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range w).flatMap fun k =>
      (List.range (n + 1)).flatMap fun j =>
        lowBits w (ciphertextEntry n m w publicKey message coins i k j)

/-- Collect independent draws in their original order; the empty list requires no draw. -/
noncomputable def independentList {α : Type} (count : ℕ) (law : PMF α) : PMF (List α) :=
  (List.replicate count ()).mapM (fun _ => law)

/-- A canonical residue representative chosen uniformly from `0, …, 2 ^ w - 1`. -/
noncomputable def residueLaw (w : ℕ) : PMF ℕ :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin (2 ^ w))).map Fin.val

/-- The signed noise is the difference of the counts of ones in two independent uniform words
of length `noiseWidth`. Its support is `[-noiseWidth, noiseWidth]`; this is a centered binomial
law, not a discrete Gaussian. -/
noncomputable def errorLaw (noiseWidth : ℕ) : PMF ℤ := do
  let positive ← Randomized.uniformBits noiseWidth
  let negative ← Randomized.uniformBits noiseWidth
  return (positive.count true : ℤ) - negative.count true

end ComplexityTests.Abstracts.GSW

/--
info: abstract audit passed for `ComplexityTests.Abstracts.GSW`:
11 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.GSW allowing [
  ComplexityAbstracts.Randomized
]
