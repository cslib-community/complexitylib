/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Extractor.Basic
public import CslibFrontier.Probability.BitString.LinearHash
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.MinEntropy.LeftoverHash
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

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

The January 8, 2007 draft parameterization uses entropy `k / δ` and collision bound
`(1 + δ) / 2^k`. It gives error `√(2δ)` for every positive `δ`, including zero-length
digests. The concatenated form places the digest before the seed [AroraBarak07],
Lemma 16.42 (printed page 308 / PDF page 324), Exercise 16.12 (319 / 335).

## Main results

* `Cslib.Probability.IsTwoUniversal.isStrongExtractor`: the leftover hash lemma as a strong
  extractor.
* `Cslib.Probability.IsTwoUniversal.isStrongExtractor_of_logb_le`: its entropy-loss form.
* `Cslib.Probability.IsUniversalHash.isStrongExtractor`: the same for `ε`-universal families.
* `Cslib.BitString.LinearHash.isStrongExtractor`: Boolean matrix multiplication is a strong
  extractor.

* `Cslib.Probability.IsUniversalHash.isStrongExtractor_of_entropy_div`: draft source parameters.
* `Cslib.Probability.IsUniversalHash.isExtractor_append_of_entropy_div`: digest-first output.

## References

* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A Pseudorandom Generator from any One-way
  Function*][HILL1999]
-/

public section

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

/-- The draft's entropy/error parameterization of the leftover hash lemma
[AroraBarak07], Lemma 16.42 (printed page 308), Exercise 16.12 (page 319).
All output lengths and positive errors are allowed; this asserts no efficiency bound. -/
theorem IsUniversalHash.isStrongExtractor_of_entropy_div
    {n k t : ℕ} {hash : BitString t → BitString n → BitString k} {δ : ℝ}
    (hδ : 0 < δ)
    (hhash : IsUniversalHash (PMF.uniformOfFintype (BitString t)) hash
      (ENNReal.ofReal ((1 + δ) / (2 : ℝ) ^ k))) :
    IsStrongExtractor (fun x s => hash s x) ((k : ℝ) / δ) (Real.sqrt (2 * δ)) := by
  by_cases hlarge : 1 / 2 ≤ δ
  · intro source _
    exact (dist_le_one _ _).trans ((Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith))
  by_cases hk : k = 0
  · subst k
    intro source _
    have heq : (source.bind fun x =>
        (PMF.uniformOfFintype (BitString t)).map fun s => (s, hash s x)) =
        PMF.uniformOfFintype (BitString t × BitString 0) := by
      rw [bind_map_eq_seededHash, seededHash_eq_uniform_of_subsingleton,
        uniformOfFintype_prod]
    rw [heq, dist_self]
    exact Real.sqrt_nonneg _
  have hpow : (2 : ℝ) ^ ((k : ℝ) - (k : ℝ) / δ) ≤ 2 * δ := by
    have hu : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 (by linarith)
    have hb := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) hu
    norm_num only [mul_one, one_add_one_eq_two] at hb
    have h_exp : (k : ℝ) - (k : ℝ) / δ ≤ 1 - δ⁻¹ := by
      have hkn : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      rw [div_eq_mul_inv]
      nlinarith
    calc
      (2 : ℝ) ^ ((k : ℝ) - (k : ℝ) / δ) ≤ 2 ^ (1 - δ⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
      _ = 2 / 2 ^ δ⁻¹ := by rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      _ ≤ 2 / (1 + δ⁻¹) := by gcongr
      _ ≤ 2 * δ := by
        apply (div_le_iff₀ (by positivity : 0 < 1 + δ⁻¹)).2
        rw [mul_add, mul_one, mul_assoc, mul_inv_cancel₀ hδ.ne']
        linarith
  have h := hhash.isStrongExtractor (by finiteness) ((k : ℝ) / δ)
  refine h.mono le_rfl ?_
  have hcard : (Fintype.card (BitString k) : ℝ) = (2 : ℝ) ^ k := by simp
  rw [hcard, ENNReal.toReal_ofReal (by positivity)]
  have hrad : (2 : ℝ) ^ k * (2 ^ (-((k : ℝ) / δ)) + (1 + δ) / 2 ^ k) - 1 =
      2 ^ ((k : ℝ) - (k : ℝ) / δ) + δ := by
    rw [mul_add, mul_div_cancel₀ _ (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num)]
    ring_nf
  rw [hrad]
  have hs := Real.sqrt_le_sqrt (show (2 : ℝ) ^ ((k : ℝ) - (k : ℝ) / δ) + δ ≤
      4 * (2 * δ) by linarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hs
  have hfour : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
    norm_num
  rw [hfour] at hs
  linarith

/-- Digest-first concatenation form of [AroraBarak07], Lemma 16.42 / Exercise 16.12.
The first `k` bits are the digest and the last `t` bits reveal the uniform independent seed.
No restriction on the seed length or running time is asserted. -/
theorem IsUniversalHash.isExtractor_append_of_entropy_div
    {n k t : ℕ} {hash : BitString t → BitString n → BitString k} {δ : ℝ}
    (hδ : 0 < δ)
    (hhash : IsUniversalHash (PMF.uniformOfFintype (BitString t)) hash
      (ENNReal.ofReal ((1 + δ) / (2 : ℝ) ^ k))) :
    IsExtractor (fun x s => Fin.append (hash s x) s) ((k : ℝ) / δ)
      (Real.sqrt (2 * δ)) := by
  intro source hsource
  let e : (BitString t × BitString k) ≃ BitString (k + t) :=
    (Equiv.prodComm _ _).trans (Fin.appendEquiv k t)
  have h := hhash.isStrongExtractor_of_entropy_div hδ source hsource
  have hm := dist_map_le
    (source.bind fun x => (PMF.uniformOfFintype (BitString t)).map fun s => (s, hash s x))
    (PMF.uniformOfFintype (BitString t × BitString k)) e
  rw [uniformOfFintype_map_equiv] at hm
  have he : (source.bind fun x =>
      (PMF.uniformOfFintype (BitString t)).map fun s => (s, hash s x)).map e =
      source.bind (fun x => (PMF.uniformOfFintype (BitString t)).map
        fun s => Fin.append (hash s x) s) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    rfl
  rw [he] at hm
  exact hm.trans h

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
  rwa [BitString.logb_card]

end Cslib.BitString.LinearHash
