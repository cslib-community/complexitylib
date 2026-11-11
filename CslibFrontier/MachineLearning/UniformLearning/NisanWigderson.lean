/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Circuit
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Queries
public import CslibFrontier.MachineLearning.UniformLearning.MembershipQuery

/-!
# The Nisan–Wigderson reconstruction as a membership-query learner

Let `test` distinguish the Nisan–Wigderson generator built from a design `D` and a function `f`
on `n` bits. With its random choices fixed by a trial `t`, the reconstruction guesses `f` from the
values of `f` at the at most `m 2 ^ a` queries of the trial
(`Cslib.Crypto.PRG.NisanWigderson.trialPoints`), so a learner with membership queries can run it:
`Cslib.MachineLearning.UniformLearning.nwLearner D test` queries these points on the seed `t` and
outputs the guess (`Cslib.MachineLearning.UniformLearning.eval_nwLearner`). It makes at most
`m 2 ^ a` queries (`Cslib.MachineLearning.UniformLearning.nwLearner_queriesAtMost`), and every
hypothesis it outputs has De Morgan circuit complexity at most that of the test plus
`m (2 ^ a (2 a + 3) + 1) + 1`
(`Cslib.MachineLearning.UniformLearning.complexity_eval_nwLearner_le`).

If `test` accepts outputs of the generator with probability at least `ε` more than uniform strings,
a uniformly random seed gives a hypothesis of error at most `1 / 2 - ε / (2 m)` with probability at
least `ε / (2 m)`
(`Cslib.MachineLearning.UniformLearning.div_two_mul_le_dens_uniformError_nwLearner_le`,
`Cslib.MachineLearning.UniformLearning.nwLearner_learns`). In particular, a test accepting a `δ`
fraction of all strings but no output of the generator yields a weak learner for `f` through its
negation (`Cslib.MachineLearning.UniformLearning.nwLearner_learns_of_dens`). This is one run of the
reconstruction of [Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem
2.11][CarmosinoImpagliazzoKabanetsKolokolova2016], in a library form: the test is `δ`-dense for an
arbitrary `δ` instead of `1 / 5`, and the advantage is `δ / (2 m)` instead of `1 / L`, where the
source's `L` is the output length `m`. Their repetition and selection of the best of `poly(m)` runs,
which raises the success probability, is not part of this file.

The running time of the learner is not certified: the library counts its queries and the size of
its hypotheses, not the steps needed to list the queries and build the hypothesis.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.nwLearner`: the reconstruction as a membership-query
  learner with seeds the trials.

## Main results

* `Cslib.MachineLearning.UniformLearning.eval_nwLearner`: its hypothesis is the guess of the trial.
* `Cslib.MachineLearning.UniformLearning.nwLearner_queriesAtMost`: it makes at most `m 2 ^ a`
  queries.
* `Cslib.MachineLearning.UniformLearning.complexity_eval_nwLearner_le`: its hypotheses are small
  circuits.
* `Cslib.MachineLearning.UniformLearning.div_two_mul_le_dens_uniformError_nwLearner_le`,
  `Cslib.MachineLearning.UniformLearning.nwLearner_learns`: weak learning from a distinguisher.
* `Cslib.MachineLearning.UniformLearning.nwLearner_learns_of_dens`: weak learning from a dense test
  that avoids the generator.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson
  Cslib.Probability Finset PACLearning

variable {ℓ n a m : ℕ}

/-- **The Nisan–Wigderson reconstruction as a membership-query learner.** On the seed `t`, it
queries the target at the queries of the trial `t` and outputs the guess that the reconstruction
builds from `test`. Its running time is not certified. -/
def nwLearner (D : Design ℓ n a m) (test : (Fin m → Bool) → Bool) :
    QueryLearner (Fin n) (Trial ℓ m) :=
  QueryLearner.ofNonadaptive (trialPoints D) fun g t => trialGuess D g test t

variable (D : Design ℓ n a m) (test : (Fin m → Bool) → Bool)

/-- Run on the target `f`, the learner outputs the guess of its seed. -/
theorem eval_nwLearner (f : (Fin n → Bool) → Bool) (t : Trial ℓ m) :
    (nwLearner D test t).eval f = trialGuess D f test t :=
  QueryLearner.eval_ofNonadaptive (fun _ _ _ h => trialGuess_congr D h) f t

/-- The learner makes at most `m 2 ^ a` queries. -/
theorem nwLearner_queriesAtMost : (nwLearner D test).QueriesAtMost (m * 2 ^ a) := fun t =>
  (QueryLearner.depth_ofNonadaptive_le _ _ t).trans (length_trialPoints_le D t)

/-- **Small hypotheses.** On every seed and every target, the hypothesis has De Morgan circuit
complexity at most that of the test plus `m * (2 ^ a * (2 * a + 3) + 1) + 1`. -/
theorem complexity_eval_nwLearner_le (f : (Fin n → Bool) → Bool) (t : Trial ℓ m) :
    complexity interpretation (single ((nwLearner D test t).eval f)) ≤
      complexity interpretation (single test) + m * (2 ^ a * (2 * a + 3) + 1) + 1 := by
  rw [eval_nwLearner]
  exact complexity_trialGuess_le D f test t

/-- **Weak learning from a distinguisher**, density form. Let `0 < m` and let the deterministic
test `test` accept outputs of the Nisan–Wigderson generator built from `D` and `f` with probability
at least `ε` more than uniform strings. On a uniformly random seed, the learner outputs a hypothesis
of error at most `1 / 2 - ε / (2 m)` with probability at least `ε / (2 m)`. -/
theorem div_two_mul_le_dens_uniformError_nwLearner_le (hm : 0 < m)
    (f : (Fin n → Bool) → Bool) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ε / (2 * m) ≤ (dens {t : Trial ℓ m |
      uniformError f ((nwLearner D test t).eval f) ≤ 1 / 2 - ε / (2 * m)} : ℝ) := by
  rcases lt_or_ge ε 0 with hε₀ | hε₀
  · have : ε / (2 * m) < 0 := div_neg_of_neg_of_pos hε₀ (by positivity)
    exact this.le.trans (by positivity)
  refine (div_two_mul_le_dens_goodTrials D f test hm hε₀ hε).trans ?_
  refine NNRat.cast_le.mpr (dens_le_dens fun t ht => ?_)
  rw [mem_goodTrials, trialAgreement] at ht
  simp only [mem_filter, mem_univ, true_and, eval_nwLearner, uniformError_eq_one_sub_dens]
  linarith

/-- **Weak learning from a distinguisher.** Let `0 < m` and let the deterministic test `test`
accept outputs of the Nisan–Wigderson generator built from `D` and each target `f ∈ C` with
probability at least `ε` more than uniform strings. Then with uniformly random seeds the learner
learns `C` with error `1 / 2 - ε / (2 m)` and confidence `ε / (2 m)`. This is one run of the
reconstruction of [Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem
2.11][CarmosinoImpagliazzoKabanetsKolokolova2016], with advantage `ε / (2 m)`; its running time is
not certified. -/
theorem nwLearner_learns [NeZero m] {C : ConceptClass (Fin n → Bool) Bool} {ε : ℝ}
    (hC : ∀ f ∈ C, ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    (nwLearner D test).Learns (PMF.uniformOfFintype (Trial ℓ m)) C (1 / 2 - ε / (2 * m))
      (1 - ε / (2 * m)) :=
  QueryLearner.learns_uniformOfFintype_of_le_dens fun f hf =>
    div_two_mul_le_dens_uniformError_nwLearner_le D test (NeZero.pos m) f (hC f hf)

/-- **Weak learning from a dense test that avoids the generator** [Carmosino, Impagliazzo,
Kabanets and Kolokolova, Theorem 2.11][CarmosinoImpagliazzoKabanetsKolokolova2016], one run. Let
the deterministic test `test` accept at least a `δ` fraction of all strings of `m` bits but no
output of the Nisan–Wigderson generator built from `D` and any target `f ∈ C`. Then with uniformly
random seeds the learner built from the negation of `test` learns `C` with error
`1 / 2 - δ / (2 m)` and confidence `δ / (2 m)`. The test is `δ`-dense for any `δ`, where the source
takes `δ = 1 / 5`, and the advantage is `δ / (2 m)` instead of `1 / L`, where the source's `L` is
the output length `m`; the running time of the learner is not certified. -/
theorem nwLearner_learns_of_dens [NeZero m] {C : ConceptClass (Fin n → Bool) Bool} {δ : ℝ}
    (hδ : δ ≤ dens {y | test y = true}) (havoid : ∀ f ∈ C, ∀ z, test (generator D f z) = false) :
    (nwLearner D (fun y => !test y)).Learns (PMF.uniformOfFintype (Trial ℓ m)) C
      (1 / 2 - δ / (2 * m)) (1 - δ / (2 * m)) :=
  nwLearner_learns D _ fun f hf => hδ.trans_eq
    (Generator.toReal_realExperiment_sub_toReal_idealExperiment_not _ (havoid f hf)).symm

end Cslib.MachineLearning.UniformLearning
