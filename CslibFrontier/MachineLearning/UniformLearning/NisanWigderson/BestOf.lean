/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.BestOf
public import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson

/-!
# Learning from a test that avoids the Nisan–Wigderson generator

[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 2.11, p. 10:9]
[CarmosinoImpagliazzoKabanetsKolokolova2016] turns a dense test that avoids the Nisan–Wigderson
generator of a function `f` into a membership-query learner for `f`: run the reconstruction
`poly(L)` times, estimate the agreement of each guess with `f` by sampling and membership queries,
and output the best guess. Here the reconstruction is
`Cslib.MachineLearning.UniformLearning.nwLearner`, and the repetition and selection are
`Cslib.MachineLearning.UniformLearning.QueryLearner.bestOf`.

Let `test` accept at least a `δ > 0` fraction of all strings of `m` bits but no output of the
generator built from the design `D` and any target in the class `C`. Then `k` runs of the learner
built from the negation of `test`, selected on `t` uniform points, learn `C` with error
`1 / 2 - δ / (4 m)` and confidence `1 - η` when `log (2 / η) ≤ (δ / (2 m)) k` and
`8 log (4 k / η) ≤ t (δ / (2 m))²`
(`Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns_of_dens`). The learner makes at
most `k m 2 ^ a + t` queries
(`Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_queriesAtMost`), and every hypothesis has
the De Morgan circuit bound of a single run
(`Cslib.MachineLearning.UniformLearning.complexity_eval_bestOf_nwLearner_le`).

This is Theorem 2.11 in a library form. The test is `δ`-dense for any `δ > 0`, where the source
takes advantage strictly above `1 / 5`; the error is `1 / 2 - δ / (4 m)`, where the source has
`1 / 2 - 1 / L` and its `L` is the output length `m`; and the numbers of runs and sample points are
explicit, where the source has `poly(L)`. The source's confidence parameter `α` is `η`. The
running time of the learner is not certified: the library counts its queries and the size of its
hypotheses.

## Main results

* `Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns_of_dens`: learning from a dense
  test that avoids the generator, with confidence `1 - η`.
* `Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_queriesAtMost`: the query count.
* `Cslib.MachineLearning.UniformLearning.complexity_eval_bestOf_nwLearner_le`: the hypotheses are
  small circuits.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson
  Cslib.Probability Finset PACLearning

variable {ℓ n a m k t : ℕ} (D : Design ℓ n a m) (test : (Fin m → Bool) → Bool)

/-- Best-of-`k` selection over the Nisan–Wigderson learner makes at most `k m 2 ^ a + t`
queries. -/
theorem bestOf_nwLearner_queriesAtMost [NeZero k] :
    (QueryLearner.bestOf (nwLearner D test) k t).QueriesAtMost (k * (m * 2 ^ a) + t) :=
  QueryLearner.queriesAtMost_bestOf (nwLearner_queriesAtMost D test)

/-- **Small hypotheses.** Every hypothesis of best-of-`k` selection over the Nisan–Wigderson
learner has De Morgan circuit complexity at most that of the test plus
`m * (2 ^ a * (2 * a + 3) + 1) + 1`, the bound of a single run. -/
theorem complexity_eval_bestOf_nwLearner_le [NeZero k] (f : (Fin n → Bool) → Bool)
    (ω : Fin k → Trial ℓ m) (x : Fin t → Fin n → Bool) :
    complexity interpretation (single ((QueryLearner.bestOf (nwLearner D test) k t (ω, x)).eval f))
      ≤ complexity interpretation (single test) + m * (2 ^ a * (2 * a + 3) + 1) + 1 := by
  obtain ⟨j, hj⟩ := QueryLearner.exists_eval_bestOf_eq (nwLearner D test) k t f ω x
  rw [hj]
  exact complexity_eval_nwLearner_le D test f (ω j)

/-- **Learning from a dense test that avoids the generator** [Carmosino, Impagliazzo, Kabanets and
Kolokolova, Theorem 2.11][CarmosinoImpagliazzoKabanetsKolokolova2016], in a library form. Let the
deterministic test `test` accept at least a `δ > 0` fraction of all strings of `m` bits but no
output of the Nisan–Wigderson generator built from `D` and any target `f ∈ C`. Then best-of-`k`
selection on `t` sample points over the learner built from the negation of `test` learns `C` with
error `1 / 2 - δ / (4 m)` and confidence `1 - η`, when `log (2 / η) ≤ (δ / (2 m)) k` and
`8 log (4 k / η) ≤ t (δ / (2 m))²`. The source has a `1 / 5`-dense test, error `1 / 2 - 1 / L`
with `L` the output length `m`, and `poly(L)` runs; the running time is not certified. -/
theorem bestOf_nwLearner_learns_of_dens [NeZero m] [NeZero k]
    {C : ConceptClass (Fin n → Bool) Bool} {δ η : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ dens {y | test y = true}) (havoid : ∀ f ∈ C, ∀ z, test (generator D f z) = false)
    (hη : 0 < η) (hk : Real.log (2 / η) ≤ δ / (2 * m) * k)
    (ht : 8 * Real.log (4 * k / η) ≤ t * (δ / (2 * m)) ^ 2) :
    (QueryLearner.bestOf (nwLearner D fun y => !test y) k t).Learns
      (QueryLearner.bestOfSeed (PMF.uniformOfFintype (Trial ℓ m)) k t) C
      (1 / 2 - δ / (4 * m)) η := by
  have hδ1 : δ ≤ 1 := hδ.trans (by exact_mod_cast Finset.dens_le_one)
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.2 NeZero.one_le
  refine (QueryLearner.learns_bestOf_of_weak (nwLearner_learns_of_dens D test hδ havoid)
    (by positivity) ?_ hη hk ht).mono subset_rfl (le_of_eq (by ring)) le_rfl
  rw [div_le_one (by positivity)]
  linarith

end Cslib.MachineLearning.UniformLearning
