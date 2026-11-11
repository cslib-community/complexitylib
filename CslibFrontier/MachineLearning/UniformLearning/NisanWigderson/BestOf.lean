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
# Learning from a distinguisher for the Nisan–Wigderson generator

[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 2.11, p. 10:9]
[CarmosinoImpagliazzoKabanetsKolokolova2016] turns a distinguisher for the Nisan–Wigderson
generator of a function `f` into a membership-query learner for `f`: run the reconstruction
`poly(L)` times, estimate the agreement of each guess with `f` by sampling and membership queries,
and output the best guess. Here the reconstruction is
`Cslib.MachineLearning.UniformLearning.nwLearner`, and the repetition and selection are
`Cslib.MachineLearning.UniformLearning.QueryLearner.bestOf`.

Let `test` accept outputs of the generator built from the design `D` and each target in the class
`C` with probability at least `ε > 0` more than uniform strings of `m` bits. Then `k` runs of the
learner built from `test`, selected on `t` uniform points, learn `C` with error
`1 / 2 - ε / (4 m)` and confidence `1 - η` when `ε / (2 m) ≤ 1`, `log (2 / η) ≤ (ε / (2 m)) k` and
`8 log (4 k / η) ≤ t (ε / (2 m))²`
(`Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns`). The natural-property special
case takes a test accepting at least a `δ > 0` fraction of all strings but no output of the
generator, whose negation has advantage at least `δ`
(`Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns_of_dens`). The learner makes at
most `k m 2 ^ a + t` queries
(`Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_queriesAtMost`), and every hypothesis has
the De Morgan circuit bound of a single run
(`Cslib.MachineLearning.UniformLearning.complexity_eval_bestOf_nwLearner_le`).

This is Theorem 2.11 in a library form. The distinguisher has any advantage `ε > 0`, where the
source takes advantage greater than `1 / 5`, and one test serves every target in `C`, where the
source has a single `f` (the case `C = {f}`); the error is `1 / 2 - ε / (4 m)`, where the source has
`1 / 2 - 1 / L` and its `L` is the output length `m`; and the numbers of runs and sample points are
explicit, where the source has `poly(L)`. The source's confidence parameter `α` is `η`. The
running time of the learner is not certified: the library counts its queries and the size of its
hypotheses.

## Main results

* `Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns`: learning from a distinguisher,
  with confidence `1 - η`.
* `Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns_of_dens`: the special case of a
  dense test that avoids the generator.
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

/-- **Learning from a distinguisher** [Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem
2.11][CarmosinoImpagliazzoKabanetsKolokolova2016], in a library form. Let `0 < m` and let the
deterministic test `test` accept outputs of the Nisan–Wigderson generator built from `D` and each
target `f ∈ C` with probability at least `ε > 0` more than uniform strings. Then best-of-`k`
selection on `t` sample points over the learner built from `test` learns `C` with error
`1 / 2 - ε / (4 m)` and confidence `1 - η`, when `ε / (2 m) ≤ 1`, `log (2 / η) ≤ (ε / (2 m)) k` and
`8 log (4 k / η) ≤ t (ε / (2 m))²`. The first condition holds whenever `C` is nonempty, since an
advantage is at most `1`. The source takes a distinguisher of advantage greater than `1 / 5` and
has error `1 / 2 - 1 / L`, with `L` the output length `m`, and `poly(L)` runs; the running time is
not certified. -/
theorem bestOf_nwLearner_learns [NeZero m] [NeZero k]
    {C : ConceptClass (Fin n → Bool) Bool} {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε / (2 * m) ≤ 1)
    (hC : ∀ f ∈ C, ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal)
    (hη : 0 < η) (hk : Real.log (2 / η) ≤ ε / (2 * m) * k)
    (ht : 8 * Real.log (4 * k / η) ≤ t * (ε / (2 * m)) ^ 2) :
    (QueryLearner.bestOf (nwLearner D test) k t).Learns
      (QueryLearner.bestOfSeed (PMF.uniformOfFintype (Trial ℓ m)) k t) C
      (1 / 2 - ε / (4 * m)) η := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (NeZero.pos m)
  exact (QueryLearner.learns_bestOf_of_weak (nwLearner_learns D test hC) (by positivity) hε1 hη hk
    ht).mono subset_rfl (le_of_eq (by ring)) le_rfl

/-- **Learning from a dense test that avoids the generator**, the natural-property special case of
`bestOf_nwLearner_learns`. Let the deterministic test `test` accept at least a `δ > 0` fraction of
all strings of `m` bits but no output of the Nisan–Wigderson generator built from `D` and any
target `f ∈ C`, so that its negation has advantage at least `δ`. Then best-of-`k` selection on `t`
sample points over the learner built from the negation of `test` learns `C` with error
`1 / 2 - δ / (4 m)` and confidence `1 - η`, when `log (2 / η) ≤ (δ / (2 m)) k` and
`8 log (4 k / η) ≤ t (δ / (2 m))²`. This covers only distinguishers of this one-sided form, where
Theorem 2.11 of [Carmosino, Impagliazzo, Kabanets and
Kolokolova][CarmosinoImpagliazzoKabanetsKolokolova2016] takes any distinguisher of advantage greater
than `1 / 5`; the running time is not certified. -/
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
  refine bestOf_nwLearner_learns D _ hδ0 ?_ (fun f hf => hδ.trans_eq
    (Generator.toReal_realExperiment_sub_toReal_idealExperiment_not _ (havoid f hf)).symm) hη hk ht
  rw [div_le_one (by positivity)]
  linarith

end Cslib.MachineLearning.UniformLearning
