/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Collision
public import Complexity.Probability.HashFamily
public import Complexity.Probability.StatisticalDistance
public import Mathlib.Algebra.BigOperators.Expect
import Complexity.Probability.PMF.Map
import Complexity.Probability.PMF.Expect

/-!
# Universal hashing and the leftover hash lemma

A hash family whose seed is independent of the source and published with the digest turns a
source with small collision probability into almost uniform bits: this is the leftover hash
lemma. It is proved once, for `ε`-universal families (`Cslib.Probability.IsUniversalHash`): the
joint law of the seed and the digest is within `√(|Output| (CP + ε) - 1) / 2` of the seed with an
independent uniform value, where `CP` is the collision probability of the source. Universal
families in the sense of Carter and Wegman have `ε = 1 / |Output|`
(`Cslib.Probability.IsTwoUniversal`), and then the bound is `√(|Output| CP) / 2`.

The statements allow any finite seed distribution satisfying the collision bound. They are
information-theoretic results; efficient sampling and evaluation require separate certificates.

## Main definitions

* `Cslib.Probability.IsTwoUniversal`: `1 / |Output|`-universal families.
* `Cslib.Probability.seededHash`: reveal the independent hash seed and its digest together.

## Main results

* `Cslib.Probability.IsDeltaUniversalHash.isTwoUniversal`: a `1 / |Output|`-Δ-universal family is
  two-universal.
* `Cslib.Probability.IsTwoUniversal.sum_ite_le`,
  `Cslib.Probability.isTwoUniversal_iff_sum_ite_le`: real-valued pairwise collision bound
  `(|Output| : ℝ)⁻¹`.
* `Cslib.Probability.isTwoUniversal_uniformOfFintype_iff`,
  `Cslib.Probability.IsTwoUniversal.expect_boole_le`: two-universality under a uniform seed as a
  uniform expectation bound.
* `Cslib.Probability.IsUniversalHash.collision_with_set_le`: isolation by a union bound.
* `Cslib.Probability.IsUniversalHash.leftover_hash_sq`,
  `Cslib.Probability.IsUniversalHash.leftover_hash`: the strong leftover hash lemma for
  `ε`-universal families.
* `Cslib.Probability.IsTwoUniversal.leftover_hash`: its form for universal families.
* `Cslib.Probability.IsTwoUniversal.leftover_hash_conditional`: extraction with side information.

## References

* [J. L. Carter, M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3, Lemma 1.
  Its collision argument generalizes from field hashing and uniform seeds to any seed
  distribution satisfying the collision bound.
* [I. Haitner, S. Vadhan, *The Many Entropies in One-Way Functions*][HaitnerVadhan2017],
  Section 2.4.1, Definition 4 and Lemma 8.

Adapted from Probability/UniversalHash.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the upstream finite-PMF distance.
-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped BigOperators ENNReal

/-- A universal hash family in the sense of Carter and Wegman [CarterWegman1979]: distinct inputs
collide with probability at most `1 / |Output|`. -/
abbrev IsTwoUniversal {Seed Input Output : Type*} [Fintype Output] (seed : PMF Seed)
    (hash : Seed → Input → Output) : Prop :=
  IsUniversalHash seed hash (Fintype.card Output : ℝ≥0∞)⁻¹

/-- A `1 / |Output|`-Δ-universal hash family is two-universal. -/
theorem IsDeltaUniversalHash.isTwoUniversal {Seed Input Output : Type*} [Fintype Output]
    [AddGroup Output] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hh : IsDeltaUniversalHash seed hash (Fintype.card Output : ℝ≥0∞)⁻¹) :
    IsTwoUniversal seed hash :=
  hh.isUniversalHash

variable {Seed Input Output : Type*} [Fintype Seed] [Finite Input] [Fintype Output]

/-- The bound `1 / |Output|` of a universal family, in real units. -/
private theorem toReal_inv_card :
    ((Fintype.card Output : ℝ≥0∞)⁻¹).toReal = (Fintype.card Output : ℝ)⁻¹ := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The bound `1 / |Output|` of a universal family is finite. -/
private theorem inv_card_ne_top [Nonempty Output] : (Fintype.card Output : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)

omit [Fintype Seed] [Finite Input] [Fintype Output] in
/-- A hash family with seeds and an input has outputs. -/
private theorem nonempty_output {seed : PMF Seed} (hash : Seed → Input → Output)
    (x : Input) : Nonempty Output :=
  ⟨hash seed.support_nonempty.some x⟩

omit [Finite Input] in
open Classical in
/-- For a universal hash family, distinct inputs collide with total seed probability at most
`(|Output| : ℝ)⁻¹`. -/
theorem IsTwoUniversal.sum_ite_le {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) {x y : Input} (hxy : x ≠ y) :
    (∑ s, if hash s x = hash s y then (seed s).toReal else 0) ≤
      (Fintype.card Output : ℝ)⁻¹ := by
  have := nonempty_output hash x (seed := seed)
  rw [← toReal_inv_card]
  exact hhash.sum_ite_toReal_le inv_card_ne_top hxy

omit [Finite Input] in
open Classical in
/-- Two-universality is equivalent to the real-valued pairwise collision bound `(|Output| : ℝ)⁻¹`
on every pair of distinct inputs. -/
theorem isTwoUniversal_iff_sum_ite_le {seed : PMF Seed} {hash : Seed → Input → Output} :
    IsTwoUniversal seed hash ↔
      ∀ x y, x ≠ y → (∑ s, if hash s x = hash s y then (seed s).toReal else 0) ≤
        (Fintype.card Output : ℝ)⁻¹ := by
  refine ⟨fun hhash x y hxy => hhash.sum_ite_le hxy, fun hhash x y hxy => ?_⟩
  have := nonempty_output hash x (seed := seed)
  have h := IsUniversalHash.of_sum_ite_toReal_le (seed := seed) (hash := hash) hhash x y hxy
  rwa [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
    ENNReal.ofReal_natCast] at h

omit [Finite Input] in
open Classical in
/-- Under the uniform seed distribution, two-universality is equivalent to bounding the uniform
expectation of the collision indicator of distinct inputs by `1 / |Output|`. -/
theorem isTwoUniversal_uniformOfFintype_iff [Nonempty Seed] {hash : Seed → Input → Output} :
    IsTwoUniversal (PMF.uniformOfFintype Seed) hash ↔
      ∀ x y, x ≠ y → (𝔼 s, if hash s x = hash s y then (1 : ℝ) else 0) ≤
        (Fintype.card Output : ℝ)⁻¹ := by
  simp only [isTwoUniversal_iff_sum_ite_le, Fintype.expect_eq_sum_div_card, Finset.sum_div,
    ite_div, one_div, zero_div, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

omit [Finite Input] in
/-- Under the uniform seed distribution, two-universality bounds the uniform expectation of the
collision indicator of distinct inputs by `1 / |Output|`. -/
theorem IsTwoUniversal.expect_boole_le [Nonempty Seed] [DecidableEq Output]
    {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) {x y : Input} (hxy : x ≠ y) :
    (𝔼 s, if hash s x = hash s y then (1 : ℝ) else 0) ≤ (Fintype.card Output : ℝ)⁻¹ := by
  convert isTwoUniversal_uniformOfFintype_iff.mp hhash x y hxy

/-- Hash a source using an independent seed and reveal both the seed and the hash value. -/
noncomputable def seededHash (seed : PMF Seed) (source : PMF Input)
    (hash : Seed → Input → Output) : PMF (Seed × Output) :=
  seed.bind (fun s => source.map (fun x => (s, hash s x)))

omit [Fintype Seed] [Finite Input] [Fintype Output] in
/-- The independent source and public seed can be sampled in either order. -/
theorem seededHash_eq_bind (seed : PMF Seed) (source : PMF Input)
    (hash : Seed → Input → Output) :
    seededHash seed source hash = source.bind (fun x => seed.map (fun s => (s, hash s x))) := by
  simpa only [seededHash, PMF.map, Function.comp_def] using
    PMF.bind_comm seed source (fun s x => PMF.pure (s, hash s x))

omit [Finite Input] in
/-- Applying a shared public hash seed cannot increase distance between source distributions. -/
theorem dist_seededHash_le [Fintype Input] (seed : PMF Seed) (p q : PMF Input)
    (hash : Seed → Input → Output) :
    dist (seededHash seed p hash) (seededHash seed q hash) ≤ dist p q := by
  rw [seededHash_eq_bind, seededHash_eq_bind]
  exact dist_bind_le p q _

omit [Fintype Seed] [Finite Input] in
/-- An empty digest is already uniform. This exact case avoids charging an extraction error
when the source has too little entropy to supply even one prefix bit. -/
theorem seededHash_eq_uniform_of_subsingleton [Subsingleton Output] [Nonempty Output]
    (seed : PMF Seed) (source : PMF Input) (hash : Seed → Input → Output) :
    seededHash seed source hash =
      seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·)) := by
  apply PMF.map_injective (f := Prod.fst)
    (fun _ _ h => Prod.ext h (Subsingleton.elim _ _))
  simp [seededHash, Function.comp_def, PMF.map, PMF.bind_const]

omit [Finite Input] [Fintype Output] in
open Classical in
/-- A hash fails to isolate a fixed input from a candidate set only if one of the other
candidates collides with it. Universality and the union bound control this probability. -/
theorem IsUniversalHash.collision_with_set_le {seed : PMF Seed} {hash : Seed → Input → Output}
    {ε : ℝ≥0∞} (hhash : IsUniversalHash seed hash ε) (hε : ε ≠ ⊤) (candidates : Finset Input)
    (x : Input) :
    (∑ s, if ∃ y ∈ candidates, y ≠ x ∧ hash s y = hash s x then (seed s).toReal else 0) ≤
      (candidates.erase x).card * ε.toReal := by
  have hpoint (s : Seed) :
      (if ∃ y ∈ candidates, y ≠ x ∧ hash s y = hash s x then (seed s).toReal else 0) ≤
        ∑ y ∈ candidates.erase x, if hash s y = hash s x then (seed s).toReal else 0 := by
    split_ifs with h
    · obtain ⟨y, hy, hyx, heq⟩ := h
      have hsum := Finset.single_le_sum (s := candidates.erase x) (a := y)
        (f := fun y => if hash s y = hash s x then (seed s).toReal else 0)
        (fun _ _ => by positivity) (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      simpa only [heq, ite_true] using hsum
    · exact Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ∑ s, ∑ y ∈ candidates.erase x,
        if hash s y = hash s x then (seed s).toReal else 0 :=
      Finset.sum_le_sum (fun s _ => hpoint s)
    _ = ∑ y ∈ candidates.erase x, ∑ s,
        if hash s y = hash s x then (seed s).toReal else 0 := Finset.sum_comm
    _ ≤ ∑ _y ∈ candidates.erase x, ε.toReal :=
      Finset.sum_le_sum (fun y hy => hhash.sum_ite_toReal_le hε (Finset.mem_erase.mp hy).1)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

omit [Finite Input] in
open Classical in
/-- A hash fails to isolate a fixed input from a candidate set only if one of the other
candidates collides with it. For a universal family this has probability at most the number of
other candidates divided by `|Output|`. -/
theorem IsTwoUniversal.collision_with_set_le {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash)
    (candidates : Finset Input) (x : Input) :
    (∑ s, if ∃ y ∈ candidates, y ≠ x ∧ hash s y = hash s x then (seed s).toReal else 0) ≤
      ((candidates.erase x).card : ℝ) / Fintype.card Output := by
  have := nonempty_output hash x (seed := seed)
  rw [div_eq_mul_inv, ← toReal_inv_card]
  exact IsUniversalHash.collision_with_set_le hhash inv_card_ne_top candidates x

omit [Fintype Output] in
/-- An `ε`-universal family bounds the average collision probability of the hashed source by
the collision probability of the source plus `ε`. -/
theorem IsUniversalHash.collisionProbability_le {seed : PMF Seed} {hash : Seed → Input → Output}
    {ε : ℝ≥0∞} (hhash : IsUniversalHash seed hash ε) (hε : ε ≠ ⊤) (source : PMF Input) :
    ∑ s, (seed s).toReal * collisionProbability (source.map (hash s)) ≤
      collisionProbability source + ε.toReal := by
  classical
  let := Fintype.ofFinite Input
  have hpair (x y : Input) :
      (∑ s, if hash s x = hash s y then (seed s).toReal else 0) ≤
        (if x = y then (1 : ℝ) else 0) + ε.toReal := by
    by_cases hxy : x = y
    · subst y
      simp only [ite_true, sum_toReal]
      exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    · simpa [hxy] using hhash.sum_ite_toReal_le hε hxy
  calc
    _ = ∑ x, ∑ y, (source x).toReal * (source y).toReal *
        (∑ s, if hash s x = hash s y then (seed s).toReal else 0) := by
      simp only [collisionProbability_map, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      simp [mul_ite, ite_mul, mul_comm]
    _ ≤ ∑ x, ∑ y, (source x).toReal * (source y).toReal *
        ((if x = y then (1 : ℝ) else 0) + ε.toReal) := by
      gcongr with x _ y _
      exact hpair x y
    _ = collisionProbability source + ε.toReal := by
      simp [mul_add, Finset.sum_add_distrib, mul_ite, ← Finset.sum_mul, ← Finset.mul_sum,
        sum_toReal, collisionProbability_eq_sum, sq]

/-- A universal family bounds the average collision probability of the hashed source by the
collision probability of the source plus `1 / |Output|`. -/
theorem IsTwoUniversal.collisionProbability_le {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input) :
    ∑ s, (seed s).toReal * collisionProbability (source.map (hash s)) ≤
      collisionProbability source + (Fintype.card Output : ℝ)⁻¹ := by
  have := nonempty_output hash source.support_nonempty.some (seed := seed)
  rw [← toReal_inv_card]
  exact IsUniversalHash.collisionProbability_le hhash inv_card_ne_top source

/-- **Leftover hash lemma** for `ε`-universal families, in squared form: the seed stays public,
and independent uniform bits replace the digest, at squared distance at most
`(|Output| (CP + ε) - 1) / 4`, where `CP` is the collision probability of the source. -/
theorem IsUniversalHash.leftover_hash_sq [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} {ε : ℝ≥0∞} (hhash : IsUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (source : PMF Input) :
    4 * dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2 ≤
      Fintype.card Output * (collisionProbability source + ε.toReal) - 1 := by
  have hsq := dist_bind_pair_sq_le seed (fun s => source.map (hash s))
    (fun _ => PMF.uniformOfFintype Output)
  have hbound : ∑ s, (seed s).toReal *
      (4 * dist (source.map (hash s)) (PMF.uniformOfFintype Output) ^ 2) ≤
      Fintype.card Output * (collisionProbability source + ε.toReal) - 1 := by
    calc
      _ ≤ ∑ s, (seed s).toReal *
          (Fintype.card Output * collisionProbability (source.map (hash s)) - 1) := by
        gcongr with s _
        exact dist_uniform_sq_le _
      _ = Fintype.card Output *
          (∑ s, (seed s).toReal * collisionProbability (source.map (hash s))) - 1 := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_toReal,
          Finset.mul_sum, mul_left_comm]
      _ ≤ _ := by
        gcongr
        exact hhash.collisionProbability_le hε source
  have hdistrib : (∑ s, (seed s).toReal *
      (4 * dist (source.map (hash s)) (PMF.uniformOfFintype Output) ^ 2)) =
      4 * ∑ s, (seed s).toReal *
        dist (source.map (hash s)) (PMF.uniformOfFintype Output) ^ 2 := by
    simp only [Finset.mul_sum, mul_left_comm]
  rw [hdistrib] at hbound
  simpa only [seededHash, PMF.map_comp, Function.comp_def] using
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 4)).trans hbound

/-- **Leftover hash lemma** for `ε`-universal families: the seed stays public, and independent
uniform bits replace the digest, with error at most `√(|Output| (CP + ε) - 1) / 2`. -/
theorem IsUniversalHash.leftover_hash [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} {ε : ℝ≥0∞} (hhash : IsUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (source : PMF Input) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      Real.sqrt (Fintype.card Output * (collisionProbability source + ε.toReal) - 1) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply Real.le_sqrt_of_sq_le
  nlinarith [hhash.leftover_hash_sq hε source]

/-- The strong leftover hash lemma for universal families, in squared form without logarithms or
square roots. -/
theorem IsTwoUniversal.leftover_hash_sq [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input) :
    4 * dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2 ≤
      Fintype.card Output * collisionProbability source := by
  have hcard : (Fintype.card Output : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := IsUniversalHash.leftover_hash_sq hhash inv_card_ne_top source
  rwa [toReal_inv_card, mul_add, mul_inv_cancel₀ hcard, add_sub_cancel_right] at h

/-- The strong leftover hash lemma: the seed stays public and independent uniform bits replace
the hash value, with error at most half the square root of output size times source collision. -/
theorem IsTwoUniversal.leftover_hash [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      Real.sqrt (Fintype.card Output * collisionProbability source) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply Real.le_sqrt_of_sq_le
  nlinarith [hhash.leftover_hash_sq source]

/-- A pointwise probability bound is sufficient for the leftover hash lemma. This is the
min-entropy form: use `mass = 2⁻ᵏ` for a source with at least `k` bits of min-entropy. -/
theorem IsTwoUniversal.leftover_hash_of_mass_le [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input)
    {mass : ℝ} (hmass : ∀ x, (source x).toReal ≤ mass) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      Real.sqrt (Fintype.card Output * mass) / 2 := by
  exact (hhash.leftover_hash source).trans (div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (collisionProbability_le_of_mass_le source hmass) (Nat.cast_nonneg _))) (by norm_num))

/-- Revealing side information costs the average collision probability of the conditional
sources. The hash seed is sampled independently of both the side information and the source. -/
theorem IsTwoUniversal.leftover_hash_conditional_sq [Nonempty Output]
    {Side : Type*} [Fintype Side] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (side : PMF Side) (source : Side → PMF Input) :
    4 * dist
        (side.bind (fun info => (seededHash seed (source info) hash).map (info, ·)))
        (side.bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ^ 2 ≤
      Fintype.card Output * ∑ info, (side info).toReal * collisionProbability (source info) := by
  calc
    _ ≤ 4 * ∑ info, (side info).toReal * dist (seededHash seed (source info) hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2 :=
      mul_le_mul_of_nonneg_left (dist_bind_pair_sq_le _ _ _) (by norm_num)
    _ = ∑ info, (side info).toReal * (4 * dist (seededHash seed (source info) hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ^ 2) := by
      simp only [Finset.mul_sum, mul_left_comm]
    _ ≤ ∑ info, (side info).toReal *
        (Fintype.card Output * collisionProbability (source info)) := by
      apply Finset.sum_le_sum
      intro info _
      exact mul_le_mul_of_nonneg_left (hhash.leftover_hash_sq _) ENNReal.toReal_nonneg
    _ = _ := by simp only [Finset.mul_sum, mul_left_comm]

/-- Conditional leftover hashing in its usual square-root form. -/
theorem IsTwoUniversal.leftover_hash_conditional [Nonempty Output]
    {Side : Type*} [Fintype Side] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (side : PMF Side) (source : Side → PMF Input) :
    dist (side.bind (fun info => (seededHash seed (source info) hash).map (info, ·)))
        (side.bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ≤
      Real.sqrt (Fintype.card Output *
        ∑ info, (side info).toReal * collisionProbability (source info)) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply Real.le_sqrt_of_sq_le
  nlinarith [hhash.leftover_hash_conditional_sq side source]

end Cslib.Probability
