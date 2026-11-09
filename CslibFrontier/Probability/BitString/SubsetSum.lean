/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.UniversalHash
public import CslibFrontier.Probability.StatisticalDistance.Product
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.Uniform
import CslibFrontier.Probability.PMF.Map

/-!
# Binary subset-sum hashing

A binary word selects a subset of independently uniform elements of a finite additive group.
Distinct words give a uniformly distributed difference, and hence collide with probability exactly
`1 / |G|`. In particular, the output group may be a finite power of `ZMod q` for any positive
modulus; no prime-modulus hypothesis is needed.

## Main definitions

* `Cslib.BitString.SubsetSum.hash`: sum the weights selected by a binary word.
* `Cslib.BitString.SubsetSum.hashRows`: hash every binary row with the same weights.

## Main results

* `Cslib.BitString.SubsetSum.uniform_hash_sub`: distinct words give a uniform difference.
* `Cslib.BitString.SubsetSum.collision_probability`: the exact collision probability.
* `Cslib.BitString.SubsetSum.isDeltaUniversalHash`, `Cslib.BitString.SubsetSum.isTwoUniversal`: the
  binary subset-sum family is `1 / |G|`-Δ-universal, hence universal.
* `Cslib.BitString.SubsetSum.dist_hashRows_le`: many independent binary rows with one public seed.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.2]
  [GentrySahaiWaters2013]

The proof reuses the finite-group uniformity lemmas in `Probability.Uniform`.
-/

@[expose] public section

namespace Cslib.BitString.SubsetSum

open Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal

variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

/-- Sum the weights at the coordinates selected by a binary word. -/
def hash (weights : ι → G) (input : ι → Bool) : G :=
  ∑ i, if input i then weights i else 0

private theorem hash_single [DecidableEq ι] (input : ι → Bool) (i : ι) (value : G) :
    hash (Pi.single i value) input = if input i then value else 0 := by
  classical
  rw [hash, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

variable [Fintype G] [DecidableEq ι]

open Classical in
/-- Distinct binary words give a uniform difference, including for composite-modulus groups. -/
theorem uniform_hash_sub (x y : ι → Bool) (hxy : x ≠ y) :
    (PMF.uniformOfFintype (ι → G)).map
      (fun weights => hash weights x - hash weights y) = PMF.uniformOfFintype G := by
  classical
  let transform : (ι → G) →+ G := {
    toFun := fun weights => hash weights x - hash weights y
    map_zero' := by simp [hash]
    map_add' := by
      intro a b
      simp only [hash, Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]
      abel }
  apply uniformOfFintype_map_addHom transform
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  intro value
  cases hx : x i <;> cases hy : y i
  · exact (hi (hx.trans hy.symm)).elim
  · exact ⟨Pi.single i (-value), by simp [transform, hash_single, hx, hy]⟩
  · exact ⟨Pi.single i value, by simp [transform, hash_single, hx, hy]⟩
  · exact (hi (hx.trans hy.symm)).elim

open Classical in
/-- The collision probability is exactly the reciprocal output-group cardinality. -/
theorem collision_probability (x y : ι → Bool) (hxy : x ≠ y) :
    (∑ weights, if hash weights x = hash weights y then
      ((PMF.uniformOfFintype (ι → G)) weights).toReal else 0) =
      (Fintype.card G : ℝ)⁻¹ := by
  have h := congrArg (fun p : PMF G => (p 0).toReal) (uniform_hash_sub (G := G) x y hxy)
  rw [map_apply_toReal] at h
  simpa only [eq_comm (a := (0 : G)), sub_eq_zero, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast] using h

/-- Uniform group weights form a `1 / |G|`-Δ-universal family on binary words: the difference
of two hashes is uniform. -/
theorem isDeltaUniversalHash :
    IsDeltaUniversalHash (PMF.uniformOfFintype (ι → G)) hash (Fintype.card G : ℝ≥0∞)⁻¹ :=
  IsDeltaUniversalHash.of_map_sub_eq_uniform fun x y hxy => uniform_hash_sub x y hxy

/-- Uniform group weights form a universal family on binary words. -/
theorem isTwoUniversal : IsTwoUniversal (PMF.uniformOfFintype (ι → G)) hash :=
  isDeltaUniversalHash.isTwoUniversal

/-- Apply the same public weights to every binary row. -/
def hashRows {κ : Type*} (weights : ι → G) (inputs : κ → ι → Bool) : κ → G :=
  fun i => hash weights (inputs i)

open Classical in
/-- Independent uniform binary rows become jointly close to uniform while their shared weights
remain public. The loss is linear in the row count; the complete row family is not assumed to be
two-universal. -/
theorem dist_hashRows_le {κ : Type*} [Fintype κ] [DecidableEq κ] :
    dist (seededHash (PMF.uniformOfFintype (ι → G))
        (PMF.uniformOfFintype (κ → ι → Bool)) hashRows)
      ((PMF.uniformOfFintype (ι → G)).bind
        (fun weights => (PMF.uniformOfFintype (κ → G)).map (weights, ·))) ≤
      Fintype.card κ * Real.sqrt (Fintype.card G / (2 : ℝ) ^ Fintype.card ι) / 2 := by
  have hrow := (isTwoUniversal (ι := ι) (G := G)).leftover_hash
    (PMF.uniformOfFintype (ι → Bool))
  have hrows := dist_bind_pair_pi_le_sum (PMF.uniformOfFintype (ι → G))
    (fun weights (_ : κ) => (PMF.uniformOfFintype (ι → Bool)).map (hash weights))
    (fun _ (_ : κ) => PMF.uniformOfFintype G)
  have real_law (weights : ι → G) :
      pi (fun _ : κ => (PMF.uniformOfFintype (ι → Bool)).map (hash weights)) =
        (PMF.uniformOfFintype (κ → ι → Bool)).map (hashRows weights) := by
    rw [pi_map, pi_uniformOfFintype]
    rfl
  simp only [real_law, pi_uniformOfFintype] at hrows
  calc
    _ ≤ ∑ _i : κ, dist (seededHash (PMF.uniformOfFintype (ι → G))
          (PMF.uniformOfFintype (ι → Bool)) hash)
        ((PMF.uniformOfFintype (ι → G)).bind
          (fun weights => (PMF.uniformOfFintype G).map (weights, ·))) := by
      simpa only [seededHash, PMF.map_comp, Function.comp_def] using hrows
    _ ≤ ∑ _i : κ, Real.sqrt (Fintype.card G / (2 : ℝ) ^ Fintype.card ι) / 2 := by
      apply Finset.sum_le_sum
      intro _ _
      simpa [collisionProbability_uniform, div_eq_mul_inv] using hrow
    _ = _ := by simp [mul_div_assoc]

end Cslib.BitString.SubsetSum
