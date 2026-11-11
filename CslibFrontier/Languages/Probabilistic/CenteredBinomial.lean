/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.BitString

/-!
# Sampling centered binomial integers

The sampler subtracts the true counts of two independent blocks of `η` fair bits. Its result
is an integer, before any reduction modulo a ciphertext modulus. Every integer between `-η`
and `η`, including both endpoints, has positive probability. The law is invariant under
negation. This is the scalar centered-binomial construction of
[NIST, Section 4.2.2, Algorithm 8][NISTFIPS203], extended to every natural parameter.

The exact distribution is specified by its finite fair-bit experiment. No Gaussian equivalence
or encryption-security property is asserted. Native runtime is certified separately.

## Main definitions

* `Cslib.ProbComp.sampleCenteredBinomial`: subtract two independently sampled Boolean counts.

## Main results

* `Cslib.ProbComp.eval_sampleCenteredBinomial`: the exact two-word distribution.
* `Cslib.ProbComp.eval_sampleCenteredBinomial_eq_map`: the same law from one word of `2 * η` bits.
* `Cslib.ProbComp.mem_support_sampleCenteredBinomial_iff`: support is exactly the closed integer
  interval.
* `Cslib.ProbComp.map_neg_eval_sampleCenteredBinomial`: negation preserves the distribution.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 4.2.2,
  Algorithm 8][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.ProbComp

open Probability

/-- Subtract the true counts of two independent blocks of `η` fair bits. -/
noncomputable def sampleCenteredBinomial (η : ℕ) : ProbComp ℤ := do
  let positive ← OracleComp.countTrue η (ProbComp.uniform Bool)
  let negative ← OracleComp.countTrue η (ProbComp.uniform Bool)
  return (positive : ℤ) - negative

/-- With `η = 0` the centered binomial sampler returns `0` without sampling. -/
@[simp] theorem sampleCenteredBinomial_zero : sampleCenteredBinomial 0 = pure 0 := by
  simp [sampleCenteredBinomial, OracleComp.countTrue]

private theorem eval_replicate_uniform_bool (η : ℕ) :
    ProbComp.eval (OracleComp.replicate η (ProbComp.uniform Bool)) =
      BitString.uniformList η := by
  induction η with
  | zero => simp
  | succ η ih => simp [OracleComp.replicate_succ, BitString.uniformList_succ, ih]

/-- The exact law is the difference of the true counts of two independent uniform words. -/
theorem eval_sampleCenteredBinomial (η : ℕ) :
    ProbComp.eval (sampleCenteredBinomial η) = (do
      let positive ← BitString.uniformList η
      let negative ← BitString.uniformList η
      pure ((positive.count true : ℤ) - negative.count true)) := by
  simp only [sampleCenteredBinomial, OracleComp.countTrue, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure, eval_replicate_uniform_bool,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def]

/-- One word of exactly `2 * η` fair bits supplies the two independent counts. -/
theorem eval_sampleCenteredBinomial_eq_map (η : ℕ) :
    ProbComp.eval (sampleCenteredBinomial η) =
      (BitString.uniformList (2 * η)).map (fun bits =>
        ((bits.take η).count true : ℤ) - (bits.drop η).count true) := by
  rw [eval_sampleCenteredBinomial, two_mul]
  exact (BitString.uniformList_bind_split η η (fun positive negative =>
    PMF.pure ((positive.count true : ℤ) - negative.count true))).symm

/-- Every integer of magnitude at most `η` occurs, and no other integer does. -/
theorem mem_support_sampleCenteredBinomial_iff (η : ℕ) (z : ℤ) :
    z ∈ (ProbComp.eval (sampleCenteredBinomial η)).support ↔ z.natAbs ≤ η := by
  simp only [eval_sampleCenteredBinomial, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, BitString.mem_support_uniformList_iff,
    PMF.mem_support_pure_iff]
  constructor
  · rintro ⟨positive, hpositive, negative, hnegative, rfl⟩
    have hp := List.count_le_length (l := positive) (a := true)
    have hn := List.count_le_length (l := negative) (a := true)
    omega
  · intro hz
    by_cases hnonneg : 0 ≤ z
    · refine ⟨List.replicate z.natAbs true ++ List.replicate (η - z.natAbs) false,
        by simp only [List.length_append, List.length_replicate]; omega,
        List.replicate η false, by simp, ?_⟩
      simpa [List.count_replicate] using (Int.ofNat_natAbs_of_nonneg hnonneg).symm
    · refine ⟨List.replicate η false, by simp,
        List.replicate z.natAbs true ++ List.replicate (η - z.natAbs) false,
        by simp only [List.length_append, List.length_replicate]; omega, ?_⟩
      simpa [List.count_replicate] using Int.eq_neg_natAbs_of_nonpos (show z ≤ 0 by omega)

/-- Swapping the independent counts negates the result without changing its law. -/
theorem map_neg_eval_sampleCenteredBinomial (η : ℕ) :
    (ProbComp.eval (sampleCenteredBinomial η)).map Neg.neg =
      ProbComp.eval (sampleCenteredBinomial η) := by
  rw [eval_sampleCenteredBinomial]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
    PMF.pure_map, neg_sub]
  rw [PMF.bind_comm]

end Cslib.ProbComp
