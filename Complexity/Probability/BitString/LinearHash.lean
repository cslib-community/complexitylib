/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Ring.BooleanRing
public import Complexity.Probability.UniversalHash
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Probability.Uniform
import Complexity.Probability.PMF.Map

/-!
# Binary linear hashing

A uniformly random Boolean matrix is a two-universal family: hashing a nonzero input gives a
uniform output. Prefixes of one public matrix supply every shorter hash length, including zero.
The list implementation reads fixed-width rows, pads missing seed bits with `false`, and takes
an AND/XOR fold. It reuses the existing block representation and ordinary list operations.

## Main definitions

* `Cslib.BitString.LinearHash.hash`: matrix hashing on finite bit strings.
* `Cslib.BitString.LinearHash.wordHash`: its total list implementation.

## Main results

* `Cslib.BitString.LinearHash.isDeltaUniversalHash`, `Cslib.BitString.LinearHash.isTwoUniversal`:
  the uniform matrix family is `2⁻ᵐ`-XOR-universal, hence universal.
* `Cslib.BitString.LinearHash.isTwoUniversal_prefix`: universality with unused public rows.
* `Cslib.BitString.LinearHash.wordHash_eq_ofFn`: exact agreement of the two representations.

## References

* [I. Haitner, S. Vadhan, *The Many Entropies in One-Way Functions*][HaitnerVadhan2017],
  Section 2.4.1, the Boolean-matrix example following Definition 4.
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3, Lemma 1. Matrix hashing uses more seed bits than
  the cited field-multiplication family, while retaining polynomial seed length.

Adapted from Probability/LinearHash.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, in the shared bit-string namespace.
-/

@[expose] public section

namespace Cslib.BitString.LinearHash

open Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

/-- Hash an `n`-bit input to `m` bits using the `m` rows of a Boolean matrix. -/
def hash {n m : ℕ} (rows : Fin m → BitString n) (input : BitString n) : BitString m :=
  fun i => rows i ⬝ᵥ input

/-- Hashing any nonzero input by a uniform matrix gives a uniform output. -/
theorem uniform_hash_nonzero {n m : ℕ} (input : BitString n) (hinput : input ≠ 0) :
    (PMF.uniformOfFintype (Fin m → BitString n)).map (fun rows => hash rows input) =
      PMF.uniformOfFintype (BitString m) := by
  let transform : (Fin m → BitString n) →+ BitString m := {
    toFun := fun rows => hash rows input
    map_zero' := by ext i; simp [hash]
    map_add' := by intros; ext i; simp [hash, add_dotProduct] }
  apply uniformOfFintype_map_addHom transform
  obtain ⟨j, hj⟩ : ∃ j, input j ≠ false := by
    by_contra! h
    exact hinput (funext h)
  have hj : input j = true := by cases h : input j <;> simp_all
  intro output
  refine ⟨fun i => Pi.single j (output i), ?_⟩
  ext i
  simp [transform, hash, single_dotProduct, hj, Bool.mul_eq_and]

/-- The difference of the hashes of distinct inputs is uniform. -/
theorem uniform_hash_sub {n m : ℕ} (x y : BitString n) (hxy : x ≠ y) :
    (PMF.uniformOfFintype (Fin m → BitString n)).map
        (fun rows => hash rows x - hash rows y) = PMF.uniformOfFintype (BitString m) := by
  have hsub (rows : Fin m → BitString n) : hash rows x - hash rows y = hash rows (x - y) := by
    ext i
    exact (dotProduct_sub _ _ _).symm
  simp only [hsub]
  exact uniform_hash_nonzero (x - y) (sub_ne_zero.mpr hxy)

/-- Uniform Boolean matrices are a `2⁻ᵐ`-Δ-universal hash family: the bitwise XOR of two hashes
of distinct inputs is uniform. -/
theorem isDeltaUniversalHash (n m : ℕ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (Fin m → BitString n)) hash
      (Fintype.card (BitString m) : ℝ≥0∞)⁻¹ :=
  IsDeltaUniversalHash.of_map_sub_eq_uniform fun x y hxy => uniform_hash_sub x y hxy

/-- Uniform Boolean matrices are a universal hash family, including zero-width outputs. -/
theorem isTwoUniversal (n m : ℕ) :
    IsTwoUniversal (PMF.uniformOfFintype (Fin m → BitString n)) hash :=
  (isDeltaUniversalHash n m).isTwoUniversal

/-- Any initial block of a uniform matrix is itself uniform. Unused rows may remain public. -/
private theorem uniform_prefix {n m count : ℕ} (h : m ≤ count) :
    (PMF.uniformOfFintype (Fin count → BitString n)).map
        (fun rows => rows ∘ Fin.castLE h) =
      PMF.uniformOfFintype (Fin m → BitString n) := by
  let restrict : (Fin count → BitString n) →+ (Fin m → BitString n) := {
    toFun := fun rows => rows ∘ Fin.castLE h
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact uniformOfFintype_map_addHom restrict
    (Fin.castLE_injective h).surjective_comp_right

/-- Prefixes of one public matrix give universal hashes at every shorter output length. -/
theorem isTwoUniversal_prefix {n m count : ℕ} (h : m ≤ count) :
    IsTwoUniversal (PMF.uniformOfFintype (Fin count → BitString n))
      (fun rows => hash (rows ∘ Fin.castLE h)) := by
  apply IsUniversalHash.precompose_seed
  rw [uniform_prefix]
  exact isTwoUniversal n m

/-- A uniformly sampled flat matrix gives the usual two-universal family. -/
theorem isTwoUniversal_flat (inputBits outputBits : ℕ) :
    IsTwoUniversal (PMF.uniformOfFintype (BitString (outputBits * inputBits)))
      (fun seed => hash (blocksEquiv (m := outputBits) (k := inputBits) seed)) := by
  apply IsUniversalHash.precompose_seed
  rw [PMF.uniformOfFintype_map_equiv]
  exact isTwoUniversal inputBits outputBits

/-- A word implementation of binary matrix hashing. Missing seed bits are zero. -/
def wordHash (count : ℕ) (seed input : List Bool) : List Bool :=
  (listRows count input.length seed).map
    (fun row => (row.zipWith Bool.and input).foldl Bool.xor false)

/-- Every row contributes one output bit, including when the input has length zero. -/
@[simp] theorem length_wordHash (count : ℕ) (seed input : List Bool) :
    (wordHash count seed input).length = count := by
  simp [wordHash, listRows]

/-- On a fixed-length source word, the executable hash is exactly the finite matrix hash. -/
theorem wordHash_eq_ofFn {n m : ℕ} (seed : List Bool) (input : BitString n) :
    wordHash m seed (List.ofFn input) =
      List.ofFn (hash (block (ofList (m * n) seed)) input) := by
  unfold wordHash hash
  simp only [List.length_ofFn, listRows_eq_ofFn, List.map_ofFn, Function.comp_def,
    ← dotProduct_eq_foldl]

end Cslib.BitString.LinearHash
