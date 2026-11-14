/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Single
public import CslibFrontier.Foundations.Data.Code.ParityCheck

/-!
# Binary regular syndrome decoding

The regular syndrome decoding relation used by SD-in-the-Head partitions a binary word into
equally sized chunks and requires each chunk to be an elementary vector: it has exactly one
nonzero coordinate. A witness additionally satisfies the ordinary parity-check relation
`y = H *ᵥ x` [SDitH2026, Sections 2.2 and 3.1.1].

The chunked index type `Fin chunks × Fin chunkSize` makes the source requirement that the word
length is `chunks * chunkSize` explicit. This module reuses `Cslib.Code.syndrome`; it
does not introduce a second parity-check or code API.

## Main definitions

* `Cslib.Code.regularWord`: concatenate one elementary word per chunk.
* `Cslib.Code.IsRegularWord`: every chunk is a Boolean unit vector.
* `Cslib.Code.IsRegularSyndromeSolution`: a regular word with a prescribed syndrome.

## Main results

* `Cslib.Code.hammingNorm_eq_sum_chunks`: decompose total Hamming weight by chunks.
* `Cslib.Code.isRegularWord_iff_exists_positions`: the weight-one predicate is exactly the
  source's concatenation of elementary words.
* `Cslib.Code.IsRegularWord.hammingNorm_eq`: every regular word has total Hamming weight equal
  to the number of chunks.
* `Cslib.Code.isRegular_regularWord`: choosing one position per chunk constructs a regular
  word.

## References

* [*The Syndrome Decoding in the Head Signature Scheme*, v3.0][SDitH2026]
-/

public section

namespace Cslib.Code

open Matrix

/-- Concatenate one elementary word per chunk. This is the binary regular word determined by
`positions`. -/
@[expose]
def regularWord {chunks chunkSize : ℕ} (positions : Fin chunks → Fin chunkSize) :
    Fin chunks × Fin chunkSize → Bool :=
  fun p => (Pi.single (positions p.1) true : Fin chunkSize → Bool) p.2

/-- A binary word is regular when each chunk is a Boolean unit vector. -/
@[expose]
def IsRegularWord {chunks chunkSize : ℕ} (x : Fin chunks × Fin chunkSize → Bool) : Prop :=
  ∀ i, Cslib.BitString.IsSingle fun j => x (i, j)

instance {chunks chunkSize : ℕ} (x : Fin chunks × Fin chunkSize → Bool) :
    Decidable (IsRegularWord x) :=
  inferInstanceAs (Decidable (∀ i, Cslib.BitString.IsSingle fun j => x (i, j)))

/-- A regular syndrome-decoding witness for public parity-check matrix `H` and syndrome
`y`. -/
@[expose]
def IsRegularSyndromeSolution {checks chunks chunkSize : ℕ}
    (H : Matrix (Fin checks) (Fin chunks × Fin chunkSize) Bool)
    (y : Fin checks → Bool) (x : Fin chunks × Fin chunkSize → Bool) : Prop :=
  IsRegularWord x ∧ syndrome H x = y

instance {checks chunks chunkSize : ℕ}
    (H : Matrix (Fin checks) (Fin chunks × Fin chunkSize) Bool)
    (y : Fin checks → Bool) (x : Fin chunks × Fin chunkSize → Bool) :
    Decidable (IsRegularSyndromeSolution H y x) :=
  inferInstanceAs (Decidable (IsRegularWord x ∧ syndrome H x = y))

@[simp]
theorem regularWord_eq_true_iff {chunks chunkSize : ℕ}
    {positions : Fin chunks → Fin chunkSize} {i : Fin chunks} {j : Fin chunkSize} :
    regularWord positions (i, j) = true ↔ j = positions i := by
  by_cases h : j = positions i <;> simp [regularWord, h]

/-- Total Hamming weight is the sum of the Hamming weights of the chunks. -/
theorem hammingNorm_eq_sum_chunks {chunks chunkSize : ℕ}
    (x : Fin chunks × Fin chunkSize → Bool) :
    hammingNorm x = ∑ i, hammingNorm (fun j => x (i, j)) := by
  classical
  let e :
      {p : Fin chunks × Fin chunkSize // x p ≠ 0} ≃
        Σ i : Fin chunks, {j : Fin chunkSize // x (i, j) ≠ 0} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hammingNorm, ← Fintype.card_subtype]
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_subtype, hammingNorm]

@[simp]
theorem isRegular_regularWord {chunks chunkSize : ℕ}
    (positions : Fin chunks → Fin chunkSize) : IsRegularWord (regularWord positions) := by
  intro i
  exact ⟨positions i, rfl⟩

/-- The per-chunk unit-vector predicate is equivalent to the source's description as a
concatenation of elementary words. -/
theorem isRegularWord_iff_exists_positions {chunks chunkSize : ℕ}
    (x : Fin chunks × Fin chunkSize → Bool) :
    IsRegularWord x ↔ ∃ positions : Fin chunks → Fin chunkSize, x = regularWord positions := by
  classical
  constructor
  · intro hx
    choose positions hpositions using hx
    refine ⟨positions, funext fun p => ?_⟩
    exact congrFun (hpositions p.1) p.2
  · rintro ⟨positions, rfl⟩
    exact isRegular_regularWord positions

/-- Every binary regular word has exactly one nonzero coordinate per chunk. -/
theorem IsRegularWord.hammingNorm_eq {chunks chunkSize : ℕ}
    {x : Fin chunks × Fin chunkSize → Bool} (hx : IsRegularWord x) :
    hammingNorm x = chunks := by
  rw [hammingNorm_eq_sum_chunks]
  have hweight : ∀ i, hammingNorm (fun j => x (i, j)) = 1 :=
    fun i => (Cslib.BitString.hammingNorm_eq_one_iff_isSingle _).mpr (hx i)
  simp_rw [hweight]
  simp

@[simp]
theorem hammingNorm_regularWord {chunks chunkSize : ℕ}
    (positions : Fin chunks → Fin chunkSize) :
    hammingNorm (regularWord positions) = chunks :=
  (isRegular_regularWord positions).hammingNorm_eq

/-- The canonical word constructed from `positions` solves the syndrome instance obtained by
applying `H` to that word. -/
theorem isRegularSyndromeSolution_regularWord {checks chunks chunkSize : ℕ}
    (H : Matrix (Fin checks) (Fin chunks × Fin chunkSize) Bool)
    (positions : Fin chunks → Fin chunkSize) :
    IsRegularSyndromeSolution H (syndrome H (regularWord positions))
      (regularWord positions) := by
  exact ⟨isRegular_regularWord positions, rfl⟩

/-- A regular syndrome solution has the source-required total Hamming weight. -/
theorem IsRegularSyndromeSolution.hammingNorm_eq {checks chunks chunkSize : ℕ}
    {H : Matrix (Fin checks) (Fin chunks × Fin chunkSize) Bool} {y : Fin checks → Bool}
    {x : Fin chunks × Fin chunkSize → Bool} (hx : IsRegularSyndromeSolution H y x) :
    hammingNorm x = chunks :=
  hx.1.hammingNorm_eq

end Cslib.Code
