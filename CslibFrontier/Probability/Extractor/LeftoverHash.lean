/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Extractor.Basic
public import CslibFrontier.Probability.BitString.LinearHash
import CslibFrontier.Probability.MinEntropy.LeftoverHash

/-!
# Strong extractors from universal hashing

The leftover hash lemma, read as a statement about extractors: if `hash` is a two-universal family
under the uniform seed, then `ext x s = hash s x` is a strong `(k, ε)`-extractor with
`ε = √(|Output| · 2⁻ᵏ) / 2` (`IsTwoUniversal.isStrongExtractor`). If
`log₂ |Output| + 2 log₂ (1 / δ) ≤ k`, the error is at most `δ / 2`
(`IsTwoUniversal.isStrongExtractor_of_logb_le`), so universal hashing extracts all but
`2 log₂ (1 / δ)` bits of the min-entropy [Vadhan, Chapter 6][Vadhan2012],
[Håstad, Impagliazzo, Levin, Luby][HILL1999]. More generally, an `ε`-universal family gives error
`√(|Output| · (2⁻ᵏ + ε) - 1) / 2` (`IsUniversalHash.isStrongExtractor`).

A uniformly random Boolean `m × n` matrix is a two-universal family, so multiplying by it is a
strong extractor from `n`-bit sources of min-entropy at least `m + 2 log₂ (1 / δ)` to `m` bits with
error `δ / 2` and an `m n`-bit seed (`BitString.LinearHash.isStrongExtractor`).

## Main results

* `Cslib.Probability.IsTwoUniversal.isStrongExtractor`: the leftover hash lemma as a strong
  extractor.
* `Cslib.Probability.IsTwoUniversal.isStrongExtractor_of_logb_le`: its entropy-loss form.
* `Cslib.Probability.IsUniversalHash.isStrongExtractor`: the same for `ε`-universal families.
* `Cslib.BitString.LinearHash.isStrongExtractor`: Boolean matrix multiplication is a strong
  extractor.

## References

* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A Pseudorandom Generator from any One-way
  Function*][HILL1999]
-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped ENNReal

variable {Seed Input Output : Type*} [Fintype Seed] [Nonempty Seed] [Finite Input]
  [Fintype Output] [Nonempty Output]

omit [Finite Input] [Fintype Output] [Nonempty Output] in
/-- The strong-extractor experiment for a hash family is seeded hashing with the uniform seed. -/
private theorem bind_map_eq_seededHash (source : PMF Input) (hash : Seed → Input → Output) :
    (source.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, hash s x)) =
      seededHash (PMF.uniformOfFintype Seed) source hash :=
  (seededHash_eq_bind _ _ _).symm

/-- **The leftover hash lemma as a strong extractor.** A two-universal family under the uniform
seed is a strong `(k, √(|Output| · 2⁻ᵏ) / 2)`-extractor. -/
theorem IsTwoUniversal.isStrongExtractor {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) (k : ℝ) :
    IsStrongExtractor (fun x s => hash s x) k
      (Real.sqrt (Fintype.card Output * 2 ^ (-k)) / 2) := by
  intro source hsource
  have := Fintype.ofFinite Input
  have h := hhash.leftover_hash_of_isSource (isSource_of_le_minEntropy hsource 0)
  rw [uniformOfFintype_prod, NNReal.coe_zero, zero_add] at h
  rwa [bind_map_eq_seededHash]

/-- **Entropy loss of hashing.** If `log₂ |Output| + 2 log₂ (1 / δ) ≤ k`, a two-universal family
under the uniform seed is a strong `(k, δ / 2)`-extractor. -/
theorem IsTwoUniversal.isStrongExtractor_of_logb_le {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) {δ : ℝ} (hδ : 0 < δ) {k : ℝ}
    (hk : Real.logb 2 (Fintype.card Output) + 2 * Real.logb 2 δ⁻¹ ≤ k) :
    IsStrongExtractor (fun x s => hash s x) k (δ / 2) := by
  intro source hsource
  have := Fintype.ofFinite Input
  have h := hhash.leftover_hash_of_isSource_of_logb_le
    (isSource_of_le_minEntropy hsource 0) hδ hk
  rw [uniformOfFintype_prod, NNReal.coe_zero, zero_add] at h
  rwa [bind_map_eq_seededHash]

/-- **`ε`-universal hashing as a strong extractor.** An `ε`-universal family under the uniform
seed is a strong `(k, √(|Output| · (2⁻ᵏ + ε) - 1) / 2)`-extractor. For `ε = 1 / |Output|` this is
the two-universal bound `IsTwoUniversal.isStrongExtractor`. -/
theorem IsUniversalHash.isStrongExtractor {hash : Seed → Input → Output} {ε : ℝ≥0∞}
    (hhash : IsUniversalHash (PMF.uniformOfFintype Seed) hash ε) (hε : ε ≠ ⊤) (k : ℝ) :
    IsStrongExtractor (fun x s => hash s x) k
      (Real.sqrt (Fintype.card Output * (2 ^ (-k) + ε.toReal) - 1) / 2) := by
  intro source hsource
  have := Fintype.ofFinite Input
  rw [bind_map_eq_seededHash, ← uniformOfFintype_prod]
  refine (hhash.leftover_hash hε source).trans ?_
  gcongr
  exact collisionProbability_le_of_mass_le source ((le_minEntropy_iff source).mp hsource)

end Cslib.Probability

namespace Cslib.BitString.LinearHash

open Cslib.Probability

/-- **Boolean matrix multiplication is a strong extractor.** Multiplying an `n`-bit source of
min-entropy at least `m + 2 log₂ (1 / δ)` by a uniformly random Boolean `m × n` matrix gives `m`
bits within statistical distance `δ / 2` of uniform, even given the matrix. -/
theorem isStrongExtractor (n m : ℕ) {δ : ℝ} (hδ : 0 < δ) {k : ℝ}
    (hk : m + 2 * Real.logb 2 δ⁻¹ ≤ k) :
    IsStrongExtractor (fun (x : BitString n) (rows : Fin m → BitString n) => hash rows x) k
      (δ / 2) := by
  refine (isTwoUniversal n m).isStrongExtractor_of_logb_le hδ ?_
  rwa [show Fintype.card (BitString m) = 2 ^ m by simp, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

end Cslib.BitString.LinearHash
