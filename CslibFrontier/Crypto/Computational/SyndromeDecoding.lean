/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ParityCheck

/-!
# Binary regular syndrome decoding

The regular syndrome decoding relation used by SD-in-the-Head partitions a binary word into
equally sized chunks and requires each chunk to be an elementary vector: it has exactly one
nonzero coordinate. A witness additionally satisfies the ordinary parity-check relation
`y = H *ᵥ x` [SDitH2026, Sections 2.2 and 3.1.1].

The chunked index type `Fin chunks × Fin chunkSize` makes the source requirement that the word
length is `chunks * chunkSize` explicit. This module reuses `Cslib.Code.syndrome`; it does not
introduce a second parity-check or code API.

## Main definitions

* `Cslib.Crypto.SyndromeDecoding.elementaryWord`: the binary elementary vector at a position.
* `Cslib.Crypto.SyndromeDecoding.regularWord`: concatenate one elementary word per chunk.
* `Cslib.Crypto.SyndromeDecoding.IsRegularWord`: every chunk has Hamming weight one.
* `Cslib.Crypto.SyndromeDecoding.IsRegularSyndromeSolution`: a regular word with a prescribed
  syndrome.

## Main results

* `Cslib.Crypto.SyndromeDecoding.hammingNorm_eq_sum_chunks`: decompose total Hamming weight by
  chunks.
* `Cslib.Crypto.SyndromeDecoding.isRegularWord_iff_exists_positions`: the weight-one predicate is
  exactly the source's concatenation of elementary words.
* `Cslib.Crypto.SyndromeDecoding.IsRegularWord.hammingNorm_eq`: every regular word has total
  Hamming weight equal to the number of chunks.
* `Cslib.Crypto.SyndromeDecoding.isRegular_regularWord`: choosing one position per chunk constructs
  a regular word.

## References

* [*The Syndrome Decoding in the Head Signature Scheme*, v3.0][SDitH2026]
-/

public section

namespace Cslib.Crypto.SyndromeDecoding

open Matrix

/-- The elementary binary word with its unique `true` entry at `position`. -/
def elementaryWord {chunkSize : ℕ} (position : Fin chunkSize) : Fin chunkSize → Bool :=
  fun j => decide (j = position)

/-- Concatenate one elementary word per chunk. This is the binary regular word determined by
`positions`. -/
def regularWord {chunks chunkSize : ℕ} (positions : Fin chunks → Fin chunkSize) :
    Fin chunks × Fin chunkSize → Bool :=
  fun p => elementaryWord (positions p.1) p.2

/-- A binary word is regular when each chunk has Hamming weight one. -/
def IsRegularWord {chunks chunkSize : ℕ} (x : Fin chunks × Fin chunkSize → Bool) : Prop :=
  ∀ i, hammingNorm (fun j => x (i, j)) = 1

/-- A regular syndrome-decoding witness for public parity-check matrix `H` and syndrome `y`. -/
def IsRegularSyndromeSolution {checks chunks chunkSize : ℕ}
    (H : Matrix (Fin checks) (Fin chunks × Fin chunkSize) Bool)
    (y : Fin checks → Bool) (x : Fin chunks × Fin chunkSize → Bool) : Prop :=
  IsRegularWord x ∧ Cslib.Code.syndrome H x = y

@[simp]
theorem elementaryWord_apply {chunkSize : ℕ} (position j : Fin chunkSize) :
    elementaryWord position j = decide (j = position) := by
  rfl

theorem elementaryWord_eq_true_iff {chunkSize : ℕ} {position j : Fin chunkSize} :
    elementaryWord position j = true ↔ j = position := by
  simp [elementaryWord]

@[simp]
theorem regularWord_eq_true_iff {chunks chunkSize : ℕ}
    {positions : Fin chunks → Fin chunkSize} {i : Fin chunks} {j : Fin chunkSize} :
    regularWord positions (i, j) = true ↔ j = positions i := by
  exact elementaryWord_eq_true_iff

@[simp]
theorem hammingNorm_elementaryWord {chunkSize : ℕ} (position : Fin chunkSize) :
    hammingNorm (elementaryWord position) = 1 := by
  rw [hammingNorm, Finset.card_eq_one]
  refine ⟨position, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  change (decide (j = position) ≠ false ↔ j = position)
  simp only [Bool.eq_true_eq_not_eq_false, decide_eq_true_eq]

/-- A binary word has Hamming weight one exactly when it is an elementary word. -/
theorem hammingNorm_eq_one_iff_exists_elementaryWord {chunkSize : ℕ}
    (x : Fin chunkSize → Bool) :
    hammingNorm x = 1 ↔ ∃ position, x = elementaryWord position := by
  classical
  constructor
  · rw [hammingNorm, Finset.card_eq_one]
    rintro ⟨position, hposition⟩
    refine ⟨position, funext fun j => ?_⟩
    by_cases hj : j = position
    · subst j
      have hposition_mem :=
        (Finset.ext_iff.mp hposition position).mpr
          (by simp : position ∈ ({position} : Finset (Fin chunkSize)))
      have hxne : x position ≠ 0 := by simpa using hposition_mem
      have hxtrue : x position = true := by cases h : x position <;> simp_all
      simpa [elementaryWord] using hxtrue
    · have hxzero : x j = 0 := not_ne_iff.mp fun hxne => hj <| by
        have hright := (Finset.ext_iff.mp hposition j).mp (by simpa using hxne)
        simpa using hright
      change x j = false at hxzero
      simpa [elementaryWord, hj] using hxzero
  · rintro ⟨position, rfl⟩
    exact hammingNorm_elementaryWord position

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
  simpa only [regularWord] using hammingNorm_elementaryWord (positions i)

/-- The per-chunk weight-one predicate is equivalent to the source's description as a
concatenation of elementary words. -/
theorem isRegularWord_iff_exists_positions {chunks chunkSize : ℕ}
    (x : Fin chunks × Fin chunkSize → Bool) :
    IsRegularWord x ↔ ∃ positions : Fin chunks → Fin chunkSize, x = regularWord positions := by
  classical
  constructor
  · intro hx
    rw [IsRegularWord] at hx
    have hex : ∀ i, ∃ position, (fun j => x (i, j)) = elementaryWord position :=
      fun i => (hammingNorm_eq_one_iff_exists_elementaryWord _).mp (hx i)
    choose positions hpositions using hex
    refine ⟨positions, funext fun p => ?_⟩
    exact congrFun (hpositions p.1) p.2
  · rintro ⟨positions, rfl⟩
    exact isRegular_regularWord positions

/-- Every binary regular word has exactly one nonzero coordinate per chunk. -/
theorem IsRegularWord.hammingNorm_eq {chunks chunkSize : ℕ}
    {x : Fin chunks × Fin chunkSize → Bool} (hx : IsRegularWord x) :
    hammingNorm x = chunks := by
  rw [hammingNorm_eq_sum_chunks]
  rw [IsRegularWord] at hx
  simp_rw [hx]
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
    IsRegularSyndromeSolution H (Cslib.Code.syndrome H (regularWord positions))
      (regularWord positions) := by
  exact ⟨isRegular_regularWord positions, rfl⟩

/-- A regular syndrome solution has the source-required total Hamming weight. -/
theorem IsRegularSyndromeSolution.hammingNorm_eq {checks chunks chunkSize : ℕ}
    {H : Matrix (Fin checks) (Fin chunks × Fin chunkSize) Bool} {y : Fin checks → Bool}
    {x : Fin chunks × Fin chunkSize → Bool} (hx : IsRegularSyndromeSolution H y x) :
    hammingNorm x = chunks :=
  hx.1.hammingNorm_eq

end Cslib.Crypto.SyndromeDecoding
