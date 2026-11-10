/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.MildHardness
public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Reduction
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for distributional average-case complexity

Checked instances for `CslibFrontier.Computability.Complexity.Classes.AverageCase`:

* the uniform ensemble is polynomial-time computable and samplable, and its cumulative
  distribution at a concrete word;
* domination holds for bit complementation against the uniform ensemble, and fails for the
  duplication map `x ↦ x ++ x` against the uniform ensemble, for every
  length map and polynomial, so `Cslib.Complexity.DistReduction` is a genuine constraint;
* `{0^n : n ∈ K}` under the uniform ensemble is in `Avg_δ P` with `δ(n) = 2^{-n}` for an
  arbitrary, possibly undecidable, `K : Set ℕ`, the classical example that distributional classes
  with a fixed failure bound contain undecidable problems;
* a language in `P` lies in `AvgP` and `DistNP` under the uniform ensemble;
* the identity reduction, and the bridge to mild average-case hardness on a concrete function.
-/

@[expose] public section

namespace Cslib.Complexity.AverageCaseDistributionalTests

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped ENNReal

example : Ensemble.uniform.PComp := Ensemble.uniform_pComp

example : Ensemble.uniform.PSamp := Ensemble.uniform_pSamp

/-- The uniform cumulative distribution of `10` is `3/4`: the words `00`, `01`, `10`. -/
example : Ensemble.uniform.cdf [true, false] = (3 : ℕ) / (4 : ℕ) := by
  rw [Ensemble.cdf_uniform]
  rfl

/-- The numeric order on words of equal length is the lexicographic order. -/
example : [false, true, true] < [true, false, false] :=
  (BitString.binaryValue_lt_iff_lt (x := [false, true, true]) (y := [true, false, false]) rfl).mp
    (by decide)

/-- Duplication `x ↦ x ++ x` is not dominated by the uniform ensemble: its image of `U_n` puts mass
`2^{-n}` on a word of length `2n`, which has uniform probability `2^{-2n}`. -/
theorem not_dominates_dup : ¬ ∃ (m : ℕ → ℕ) (p : Polynomial ℕ), ∀ n y,
    (Ensemble.uniform.dist n).map (fun x => x ++ x) y ≤
      ((p.eval n : ℕ) : ℝ≥0∞) * Ensemble.uniform.dist (m n) y := by
  rintro ⟨m, p, h⟩
  obtain ⟨n, hn⟩ := (PolynomiallyBounded.polynomial_eval p).eventually_lt_two_pow.exists
  set x := List.replicate n false
  have hx : x.length = n := List.length_replicate
  have h1 : Ensemble.uniform.dist n x ≤
      (Ensemble.uniform.dist n).map (fun x => x ++ x) (x ++ x) :=
    Probability.PMF.le_map_apply _ _ _
  have h2 := h n (x ++ x)
  have hm : m n = (x ++ x).length := by
    by_contra hne
    have h0 : Ensemble.uniform.dist (m n) (x ++ x) = 0 := by
      rw [PMF.apply_eq_zero_iff]
      intro hmem
      exact hne (Ensemble.uniform.length_eq _ _ hmem).symm
    rw [h0, mul_zero] at h2
    have hpos : Ensemble.uniform.dist n x ≠ 0 := by
      rw [← hx, Ensemble.uniform_apply]
      simp
    exact hpos (le_antisymm (h1.trans h2) zero_le)
  have hu : Ensemble.uniform.dist n x = (2 ^ n)⁻¹ := by
    have h := Ensemble.uniform_apply x
    rw [hx] at h
    exact h
  rw [hm, Ensemble.uniform_apply] at h2
  rw [hu] at h1
  have h3 := h1.trans h2
  rw [List.length_append, hx] at h3
  have h4 := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h3
  simp only [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at h4
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [pow_add, mul_inv, ← mul_assoc] at h4
  have key : (2 : ℝ) ^ n ≤ (p.eval n : ℕ) := by
    have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt (mul_pos hpow hpow))
    calc (2 : ℝ) ^ n = (2 ^ n * 2 ^ n) * (2 ^ n)⁻¹ := by field_simp
      _ ≤ (2 ^ n * 2 ^ n) * ((p.eval n : ℕ) * (2 ^ n)⁻¹ * (2 ^ n)⁻¹) := h5
      _ = (p.eval n : ℕ) := by field_simp
  have : 2 ^ n ≤ p.eval n := by exact_mod_cast key
  omega

private theorem flip_preimage (y : List Bool) :
    (fun x : List Bool => x.map not) ⁻¹' {y} = {y.map not} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    simp [List.map_map, Function.comp_def]
  · rintro rfl
    simp [List.map_map, Function.comp_def]

/-- Complementing every bit maps the uniform ensemble to itself. -/
theorem uniform_map_flip (n : ℕ) (y : List Bool) :
    (Ensemble.uniform.dist n).map (fun x => x.map not) y = Ensemble.uniform.dist n y := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, flip_preimage,
    PMF.toOuterMeasure_apply_singleton]
  have h0 : ∀ z : List Bool, z.length ≠ n → Ensemble.uniform.dist n z = 0 := fun z hz =>
    (PMF.apply_eq_zero_iff _ _).mpr fun hmem => hz (Ensemble.uniform.length_eq _ _ hmem)
  by_cases hy : y.length = n
  · subst hy
    have h := Ensemble.uniform_apply (y.map not)
    rw [List.length_map] at h
    rw [h, Ensemble.uniform_apply]
  · rw [h0 _ (by simpa using hy), h0 _ hy]

/-- A positive instance of domination: complementing bits reduces `(L, U)` to
`({y | y.map not ∈ L}, U)` with domination factor `1`. -/
noncomputable def flipReduction (L : Set (List Bool)) :
    DistReduction ⟨L, Ensemble.uniform⟩ ⟨{y | y.map not ∈ L}, Ensemble.uniform⟩ where
  f x := x.map not
  m n := n
  p := 1
  polyTime := by polytime
  correct n x _ := by simp [List.map_map, Function.comp_def]
  dominates n y := by
    rw [uniform_map_flip, Polynomial.eval_one, Nat.cast_one, one_mul]

example (L : Set (List Bool))
    (h : (⟨{y | y.map not ∈ L}, Ensemble.uniform⟩ : DistProblem) ∈ AvgP) :
    (⟨L, Ensemble.uniform⟩ : DistProblem) ∈ AvgP :=
  (flipReduction L).mem_AvgP h

/-- `{0^n : n ∈ K}` with uniform instances, for an arbitrary `K : Set ℕ`. -/
noncomputable def zerosIn (K : Set ℕ) : DistProblem :=
  ⟨{x | x = List.replicate x.length false ∧ x.length ∈ K}, Ensemble.uniform⟩

private theorem eq_replicate_of_binaryValue_eq_zero {x : List Bool}
    (h : BitString.binaryValue x = 0) : x = List.replicate x.length false := by
  refine BitString.binaryValue_injective_of_length_eq (by simp) ?_
  rw [h, ← List.append_nil (List.replicate x.length false),
    BitString.binaryValue_replicate_false_append]
  rfl

/-- Every `zerosIn K`, even for undecidable `K`, is in `Avg_δ P` with `δ(n) = 2^{-n}`: answer "no"
unless the input is all zeros, and fail on the all-zero word. -/
theorem zerosIn_mem_AvgDeltaP (K : Set ℕ) :
    zerosIn K ∈ AvgDeltaP (fun n => (2 ^ n)⁻¹) := by
  refine ⟨fun x => if BitString.binaryValue x = 0 then none else some false, ⟨?_, ?_, ?_⟩⟩
  · polytime
  · intro n x b _ hb
    by_cases h0 : BitString.binaryValue x = 0
    · simp only [h0, ite_true, reduceCtorEq] at hb
    · simp only [h0, ite_false, Option.some.injEq] at hb
      subst hb
      simp only [zerosIn, Bool.false_eq_true, false_iff, Set.mem_ofPred_eq]
      rintro ⟨hx, -⟩
      apply h0
      rw [hx, ← List.append_nil (List.replicate _ false),
        BitString.binaryValue_replicate_false_append]
      rfl
  · intro n
    have hsub : {x | (if BitString.binaryValue x = 0 then none else some false) = none} ∩
        ((zerosIn K).ens.dist n).support ⊆ {List.replicate n false} := by
      rintro x ⟨hx, hsupp⟩
      have hlen := (zerosIn K).ens.length_eq n x hsupp
      have h0 : BitString.binaryValue x = 0 := by
        by_contra h0
        simp only [Set.mem_ofPred_eq, h0, ite_false, reduceCtorEq] at hx
      rw [Set.mem_singleton_iff, eq_replicate_of_binaryValue_eq_zero h0, hlen]
    refine (PMF.toOuterMeasure_mono _ hsub).trans ?_
    rw [PMF.toOuterMeasure_apply_singleton]
    have h := Ensemble.uniform_apply (List.replicate n false)
    rw [List.length_replicate] at h
    exact h.le

theorem zerosIn_mem_HeurDeltaP (K : Set ℕ) :
    zerosIn K ∈ HeurDeltaP (fun n => (2 ^ n)⁻¹) :=
  AvgDeltaP_subset_HeurDeltaP _ (zerosIn_mem_AvgDeltaP K)

/-- The universal language under uniform instances is in `AvgP`. -/
theorem univ_uniform_mem_AvgP : (⟨Set.univ, Ensemble.uniform⟩ : DistProblem) ∈ AvgP :=
  mem_AvgP_of_mem_P univ_mem_P

/-- The universal language under uniform instances is in `DistNP`. -/
theorem univ_uniform_mem_DistNP : (⟨Set.univ, Ensemble.uniform⟩ : DistProblem) ∈ DistNP :=
  ⟨P_subset_NP univ_mem_P, Ensemble.uniform_pComp⟩

example : (⟨Set.univ, Ensemble.uniform⟩ : DistProblem) ∈ HeurP :=
  AvgP_subset_HeurP univ_uniform_mem_AvgP

example : DistReducible (zerosIn ∅) (zerosIn ∅) := DistReducible.refl _

/-- A problem `DistNP`-hard and in `AvgP` puts all of `DistNP` in `AvgP`. -/
example (L : DistProblem) (h : DistComplete DistNP L) (hL : L ∈ AvgP) : DistNP ⊆ AvgP :=
  h.mem_AvgP_iff.mp hL

/-- The constant-`false` predicate decides a problem in `HeurP` under uniform instances, so it is
not mildly hard on average. -/
example : ¬ MildlyHardOnAverage (fun x => ((fun _ : List Bool => false) x).toNat) :=
  not_mildlyHardOnAverage_of_mem_HeurP _
    (AvgP_subset_HeurP (mem_AvgP_of_mem_P (by simpa using (empty_mem_P (enc := encBits)))))

/-- The bridge rules out infinitely-often mild hardness too. -/
example : ¬ MildlyHardOnAverageIO (fun x => ((fun _ : List Bool => false) x).toNat) :=
  not_mildlyHardOnAverageIO_of_mem_HeurP _
    (AvgP_subset_HeurP (mem_AvgP_of_mem_P (by simpa using (empty_mem_P (enc := encBits)))))

/-- Domination at every word gives support preservation, here for bit complementation. -/
example (L : Set (List Bool)) (n : ℕ) (x : List Bool)
    (hx : x ∈ (Ensemble.uniform.dist n).support) :
    x.map not ∈ (Ensemble.uniform.dist n).support :=
  (flipReduction L).mem_support hx

end Cslib.Complexity.AverageCaseDistributionalTests
