/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Prediction
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Crypto.Negligible.Basic
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Hybrid
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# One negligible bound for a bounded family of tests

Sample a dyadic index and calibrate its test with a fresh sample from the selected reference
ensemble.
The resulting advantage is the average of the indexed squared advantages, so positive and
negative gaps cannot cancel. This supplies one negligible bound for all indices in a
polynomially bounded range, even if the chosen index is not computable.

Both ensembles must have uniform efficient samplers: calibration samples a direction and runs
the selected real-or-ideal reference experiment, followed by the challenge. The adversary is one
uniformly efficient indexed program, not a family of separate certificates. Runtime charges
include the unary index, reference sample and challenge.

## Main definitions

* `Cslib.Crypto.UniformChoice.test`: the calibrated indexed reduction.

## Main results

* `Cslib.Crypto.UniformChoice.isPPTOn_test`: strict PPT certificate for the calibrated reduction.
* `Cslib.Crypto.UniformChoice.eval_bind_test`: challenge evaluation commutes with the index.
* `Cslib.Crypto.UniformChoice.advantage_eq`: exact average of squared advantages.
* `Cslib.Crypto.UniformChoice.advantage_sq_le`: each index's squared advantage is at most
  `dyadicSize bound` times the combined test's advantage.
* `Cslib.Crypto.ComputationallyIndistinguishable.uniform_bound`: one bound for every allowed index.

## References

This uniform sampling argument supplies the parameter conversion used with
[T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Section 5.

Adapted from Crypto/Computational/UniformChoice.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal

namespace UniformChoice

/-- Sample an index and calibrate its test using a fresh real-or-ideal reference sample. -/
noncomputable def test (bound : ℕ) (real ideal : ProbComp (List Bool))
    (adversary : ℕ → List Bool → ProbComp Bool) (challenge : List Bool) : ProbComp Bool := do
  let index ← sampleDyadicIndex bound
  calibratedTest (real >>= adversary index) (ideal >>= adversary index)
    (adversary index challenge)

/-- The reduction charges sampling, reference data and both captured adversary calls. -/
@[program_certificate]
theorem isPPTOn_test {α : Type} {input : α ↪ List Bool}
    {bound : α → ℕ} {real ideal : α → ProbComp (List Bool)}
    {adversary : α → ℕ → List Bool → ProbComp Bool} {challenge : α → List Bool}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hreal : IsPPTOn input encBits real)
    (hideal : IsPPTOn input encBits ideal)
    (hadversary : IsPPTOn (encPair (encPair input encUnary) encBits) encBool
      (fun a => adversary a.1.1 a.1.2 a.2))
    (hchallenge : ComputableInPolyTime challenge input encBits) :
    IsPPTOn input encBool
      (fun a => test (bound a) (real a) (ideal a) (adversary a) (challenge a)) := by
  have hbound := hbound.tidy
  have hchallenge := hchallenge.tidy
  unfold test
  apply IsPPTOn.bind_with (left := encUnary)
  · fun_prop
  · apply isPPTOn_calibratedTest <;> ppt

/-- The challenge commutes with the independent index and calibration trial. -/
theorem eval_bind_test (bound : ℕ) (real ideal source : ProbComp (List Bool))
    (adversary : ℕ → List Bool → ProbComp Bool) :
    ProbComp.eval (source >>= test bound real ideal adversary) =
      (do
        let index ← PMF.uniformOfFintype (Fin (dyadicSize bound))
        ProbComp.eval (calibratedTest (real >>= adversary index.val)
          (ideal >>= adversary index.val) (source >>= adversary index.val))) := by
  simp only [test, ProbComp.eval_bind, eval_sampleDyadicIndex, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext index
  simp only [calibratedTest, ProbComp.eval_bind, ProbComp.eval_map, map_bind]
  rw [PMF.bind_comm]

/-- Averaging calibrated tests averages their squared advantages without sign cancellation. -/
theorem advantage_eq (bound : ℕ) (real ideal : ProbComp (List Bool))
    (adversary : ℕ → List Bool → ProbComp Bool) :
    Game.advantage (ProbComp.eval (real >>= test bound real ideal adversary))
      (ProbComp.eval (ideal >>= test bound real ideal adversary)) =
        (∑ index : Fin (dyadicSize bound),
          Game.advantage (ProbComp.eval (real >>= adversary index.val))
            (ProbComp.eval (ideal >>= adversary index.val)) ^ 2) / dyadicSize bound := by
  have hgap := fun index : Fin (dyadicSize bound) =>
    calibratedTest_gap (real >>= adversary index.val) (ideal >>= adversary index.val)
  apply NNReal.eq
  rw [Game.coe_advantage, eval_bind_test, eval_bind_test]
  simp only [PMF.monad_bind_eq_bind, Game.succProbability_uniform,
    NNReal.coe_div, NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_natCast, Game.coe_succProbability,
    Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib, hgap]
  exact abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _))

/-- A particular index is used only in this inequality; it need not be computed by the test. -/
theorem advantage_sq_le (bound : ℕ) (real ideal : ProbComp (List Bool))
    (adversary : ℕ → List Bool → ProbComp Bool) {index : ℕ} (hindex : index ≤ bound) :
    Game.advantage (ProbComp.eval (real >>= adversary index))
      (ProbComp.eval (ideal >>= adversary index)) ^ 2 ≤
      dyadicSize bound * Game.advantage (ProbComp.eval (real >>= test bound real ideal adversary))
        (ProbComp.eval (ideal >>= test bound real ideal adversary)) := by
  have hpos : (0 : ℝ≥0) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  rw [advantage_eq, mul_div_cancel₀ _ hpos.ne']
  exact Finset.single_le_sum (fun i _ => sq_nonneg
    (Game.advantage (ProbComp.eval (real >>= adversary i.val))
      (ProbComp.eval (ideal >>= adversary i.val))))
    (Finset.mem_univ (⟨index, hindex.trans_lt (lt_dyadicSize bound)⟩ : Fin (dyadicSize bound)))

end UniformChoice

/-- Efficient samplers allow one negligible bound for every polynomially bounded index of
one uniform test. Choosing the index requires no computability assumption. -/
theorem ComputationallyIndistinguishable.uniform_bound
    {real ideal : ℕ → ProbComp (List Bool)} {bound : ℕ → ℕ}
    (hsecure : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (real n)) (fun n => ProbComp.eval (ideal n)))
    (hreal : IsPPTOn encUnary encBits real)
    (hideal : IsPPTOn encUnary encBits ideal)
    (hbound : ComputableInPolyTime bound encUnary encUnary)
    (adversary : ℕ → ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun a => adversary a.1.1 a.1.2 a.2)) :
    ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n index, index ≤ bound n →
      Game.advantage (ProbComp.eval (real n >>= adversary n index))
        (ProbComp.eval (ideal n >>= adversary n index)) ≤ ε n := by
  have hbound := hbound.tidy
  let reduction := fun n => UniformChoice.test (bound n) (real n) (ideal n) (adversary n)
  have hreduce : IsPPT encBool reduction := by
    unfold reduction
    ppt
  have hnegligible : Negligible (fun n =>
      Game.advantage (ProbComp.eval (real n >>= reduction n))
        (ProbComp.eval (ideal n >>= reduction n))) := by
    simpa only [distinguishingGame, PMF.monad_bind_eq_bind,
      ProbComp.eval_bind] using hsecure reduction hreduce
  have hscaled := hnegligible.polynomiallyBounded_mul
    (dyadicSize_polynomiallyBounded.comp hbound.polynomiallyBounded)
  refine ⟨_, hscaled.sqrt, fun n index hindex => ?_⟩
  exact NNReal.le_sqrt_iff_sq_le.mpr (UniformChoice.advantage_sq_le (bound n)
    (real n) (ideal n) (adversary n) hindex)

end Cslib.Crypto
