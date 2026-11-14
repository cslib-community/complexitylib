/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128

/-!
# ML-KEM seed-expansion byte boundaries

FIPS 203 expands ML-KEM's 32-byte seeds through two different SHAKE interfaces. `SampleNTT`
absorbs `rho || j || i` into SHAKE128, with the matrix column byte before its row byte. The noise
PRF absorbs a seed and one counter byte into SHAKE256; its width parameter changes only the
requested output length.

This module fixes those byte conventions and the three-byte rejection parser independently of the
coefficient-level K-PKE model. `sampleNTTPrefix` intentionally parses only a supplied finite byte
prefix. It does not claim that a fixed prefix always yields 256 accepted values, terminate an
unbounded rejection loop, or establish uniformity of SHAKE-derived coefficients.

## Main definitions

* `Cslib.Crypto.MLKEM.Seed32`: an exact 32-byte seed.
* `Cslib.Crypto.MLKEM.matrixXofInput`, `matrixXofBytes`: the `rho || j || i` SHAKE128 bridge.
* `Cslib.Crypto.MLKEM.NoiseWidth`, `prfInput`, `prf`: the FIPS 203 SHAKE256 PRF boundary.
* `Cslib.Crypto.MLKEM.sampleNTTCandidates`, `sampleNTTChunk`, `sampleNTTPrefix`: the finite
  three-byte rejection parser from Algorithm 7.

## Main results

* `Cslib.Crypto.MLKEM.length_matrixXofBytes`, `length_prf`: exact output lengths.
* `Cslib.Crypto.MLKEM.take_matrixXofBytes`, `prf_two_eq_take_three`: XOF prefix laws.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 4.1, Equations
  (4.3) and (4.6), Section 4.2.2, Algorithm 7, and Section 5.1, Algorithm 13][NISTFIPS203].
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Cslib

/-- An exact 32-byte ML-KEM seed. -/
abbrev Seed32 := FixedBytes 32

/-- The 34 bytes absorbed for matrix entry `(i,j)`: `rho || j || i`.

The arguments are named in matrix order, while the two-byte suffix is deliberately column first,
as required by FIPS 203 Algorithm 13, line 5. -/
def matrixXofInput (rho : Seed32) (row column : Byte) : FixedBytes 34 :=
  FixedBytes.append rho fun index : Fin 2 => if index.val = 0 then column else row

/-- The matrix XOF input contains exactly 34 bytes. -/
@[simp] theorem length_matrixXofInput (rho : Seed32) (row column : Byte) :
    (matrixXofInput rho row column).toList.length = 34 := by
  simp

/-- A finite prefix of the SHAKE128 stream for matrix entry `(row,column)`. -/
def matrixXofBytes (rho : Seed32) (row column : Byte) (outputBytes : ℕ) : List Byte :=
  Keccak.shake128 (matrixXofInput rho row column).toList outputBytes

/-- Matrix seed expansion returns exactly the requested finite prefix length. -/
@[simp] theorem length_matrixXofBytes (rho : Seed32) (row column : Byte) (outputBytes : ℕ) :
    (matrixXofBytes rho row column outputBytes).length = outputBytes := by
  simp [matrixXofBytes]

/-- Longer matrix XOF requests preserve every byte of a shorter request. -/
theorem take_matrixXofBytes (rho : Seed32) (row column : Byte) {m n : ℕ} (h : m ≤ n) :
    (matrixXofBytes rho row column n).take m = matrixXofBytes rho row column m := by
  exact Keccak.take_shake128 _ h

/-- The FIPS 203 centered-binomial widths supported by the noise PRF. -/
structure NoiseWidth where
  /-- The centered-binomial width and SHAKE256 output-length multiplier. -/
  val : ℕ
  /-- FIPS 203 permits exactly widths 2 and 3. -/
  supported : val = 2 ∨ val = 3
  deriving DecidableEq

/-- Noise width 2. -/
def eta2 : NoiseWidth := ⟨2, Or.inl rfl⟩

/-- Noise width 3. -/
def eta3 : NoiseWidth := ⟨3, Or.inr rfl⟩

/-- The 33 bytes absorbed by `PRF_eta`: the seed followed by the one-byte counter.

The width `eta` is deliberately absent because FIPS 203 Equation (4.3) uses it only to choose the
SHAKE256 output length, not for domain separation. -/
def prfInput (seed : Seed32) (counter : Byte) : FixedBytes 33 :=
  FixedBytes.append seed fun _ : Fin 1 => counter

/-- The PRF input contains exactly 33 bytes. -/
@[simp] theorem length_prfInput (seed : Seed32) (counter : Byte) :
    (prfInput seed counter).toList.length = 33 := by
  simp

/-- FIPS 203 Equation (4.3), returning `64 * eta` SHAKE256 bytes. -/
def prf (eta : NoiseWidth) (seed : Seed32) (counter : Byte) : List Byte :=
  Keccak.shake256 (prfInput seed counter).toList (64 * eta.val)

/-- `PRF_eta` returns exactly `64 * eta` bytes. -/
@[simp] theorem length_prf (eta : NoiseWidth) (seed : Seed32) (counter : Byte) :
    (prf eta seed counter).length = 64 * eta.val := by
  simp [prf]

/-- Widths 2 and 3 absorb identical bytes; width 2 returns the first 128 bytes of width 3. -/
theorem prf_two_eq_take_three (seed : Seed32) (counter : Byte) :
    (prf eta3 seed counter).take 128 = prf eta2 seed counter := by
  simpa [prf, eta2, eta3] using
    (Keccak.take_shake256 (prfInput seed counter).toList (m := 128) (n := 192) (by decide))

/-- Parse one three-byte SampleNTT block into its low- and high-nibble 12-bit candidates. -/
def sampleNTTCandidates (c0 c1 c2 : Byte) : ℕ × ℕ :=
  (c0.val + 256 * (c1.val % 16), c1.val / 16 + 16 * c2.val)

/-- Keep the candidates from one SampleNTT block that are below the ML-KEM modulus 3329. -/
def sampleNTTChunk (c0 c1 c2 : Byte) : List ℕ :=
  let candidates := sampleNTTCandidates c0 c1 c2
  [candidates.1, candidates.2].filter fun candidate => decide (candidate < 3329)

/-- Parse accepted SampleNTT candidates from complete three-byte blocks in a finite stream.

An incomplete final block is ignored. This is a finite parser, not the standard's unbounded loop. -/
def sampleNTTPrefix : List Byte → List ℕ
  | c0 :: c1 :: c2 :: rest => sampleNTTChunk c0 c1 c2 ++ sampleNTTPrefix rest
  | _ => []

/-- Expand and parse a finite number of SHAKE128 bytes for one matrix entry. -/
def matrixAcceptedPrefix (rho : Seed32) (row column : Byte) (outputBytes : ℕ) : List ℕ :=
  sampleNTTPrefix (matrixXofBytes rho row column outputBytes)

end Cslib.Crypto.MLKEM
