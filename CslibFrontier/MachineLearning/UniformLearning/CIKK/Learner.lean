/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.BitPolynomial
public import CslibFrontier.MachineLearning.UniformLearning.BestOf
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Amplification
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Parameters
public import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# The CIKK learner from a dense test

The learner of Carmosino, Impagliazzo, Kabanets and Kolokolova
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2`, in a per-function black-box form.
Let `test` be a Boolean function on strings of `2 ^ ℓ` bits. Suppose it accepts at least a
`2 ^ (ℓ + 1 - g)` fraction of all strings but no output of the Nisan–Wigderson generator of the
amplified function `Amp(f) = glAmp f k`, with `k = cikkK e g` and the design
`Design.binaryPolynomial (k n + k) ℓ`. Then `cikkLearner n ℓ e g h test` learns `f` with membership
queries under the uniform distribution, with error `2^{-e}` and confidence `1 - 2^{-h}`
(`Cslib.MachineLearning.UniformLearning.learns_cikkLearner`).

The learner chains three stages:
1. the Nisan–Wigderson reconstruction built from the negated test
   (`Cslib.MachineLearning.UniformLearning.nwLearner`), a weak learner for `Amp(f)`;
2. the reconstruction of the amplification
   (`Cslib.MachineLearning.UniformLearning.ampLearner`), a learner for `f` that succeeds with
   small probability;
3. best-of selection (`Cslib.MachineLearning.UniformLearning.QueryLearner.bestOf`), which raises
   the confidence.

The parameters are those of `CslibFrontier.MachineLearning.UniformLearning.CIKK.Parameters`.

The following deviations from the source are labelled:
* **Single outer boost.** The source composes the two reconstructions, each of which boosts its own
  confidence [Carmosino, Impagliazzo, Kabanets and Kolokolova, proof of Theorem 3.2, p. 10:11].
  Here a single best-of selection over the composition replaces those boosts; the result is the
  same up to constants.
* **Density.** The test may have any density at least `2 ^ (ℓ + 1 - g)`, where the source's
  natural property has largeness `1/5`; the advantage of the Nisan–Wigderson stage is
  `δ / (2 L)` instead of `1 / L`, with `L = 2 ^ ℓ` the output length.
* **Parameters.** Error, confidence, the Nisan–Wigderson advantage and `k` are powers of two, with
  this library's constants. The deviations of `learns_ampLearner` carry over.
* **Certified resources.** The number of queries is certified
  (`Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner`), but the running time is
  not.
* **Black-box form.** The test is an arbitrary Boolean function, not a natural property.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.cikkLearner`: the learner.
* `Cslib.MachineLearning.UniformLearning.cikkSeed`: its seed distribution.

## Main results

* `Cslib.MachineLearning.UniformLearning.cikkLearner_def`: the learner unfolded into its stages.
* `Cslib.MachineLearning.UniformLearning.learns_cikkLearner`: learning from a dense test that
  rejects the generator of every amplified target.
* `Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner`,
  `Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_two_pow`: the number of queries,
  exactly and in closed form.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Finset PACLearning Cslib.Probability Cslib.Circuits.Boolean Cslib.Crypto.PRG
  Cslib.Crypto.PRG.NisanWigderson

/-- **The CIKK learner** for `p = 2`: best-of selection over `cikkRuns e g h` runs and
`cikkSamples e g h` sample points, over the reconstruction of `Amp(f) = glAmp f (cikkK e g)`
(`cikkFixed e g` fixed positions, `cikkTrials e g` trials, `cikkMasks e g` masks), over the
Nisan–Wigderson reconstruction for the design `Design.binaryPolynomial (k n + k) ℓ` built from the
negated test.

A seed consists of `cikkRuns e g h` seeds of the reconstruction of `Amp(f)`, each a
Nisan–Wigderson trial with an `AmpSeed`, and `cikkSamples e g h` sample points of `BitString n`. -/
noncomputable def cikkLearner (n ℓ e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool) :=
  QueryLearner.bestOf
    (ampLearner
      (nwLearner (Design.binaryPolynomial (cikkK e g * n + cikkK e g) ℓ) fun y => !test y)
      (cikkFixed e g) (cikkTrials e g) (cikkMasks e g))
    (cikkRuns e g h) (cikkSamples e g h)

/-- `cikkLearner` unfolded: best-of selection over the reconstruction of the amplification over
the Nisan–Wigderson reconstruction built from the negated test. -/
theorem cikkLearner_def (n ℓ e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool) :
    cikkLearner n ℓ e g h test =
      QueryLearner.bestOf
        (ampLearner
          (nwLearner (Design.binaryPolynomial (cikkK e g * n + cikkK e g) ℓ) fun y => !test y)
          (cikkFixed e g) (cikkTrials e g) (cikkMasks e g))
        (cikkRuns e g h) (cikkSamples e g h) := by
  unfold cikkLearner
  rfl

/-- The seed distribution of `cikkLearner`: `cikkRuns e g h` independent seeds of the
reconstruction of `Amp(f)`, each a uniform Nisan–Wigderson trial with an independent uniform
`AmpSeed`, and `cikkSamples e g h` independent uniform sample points. -/
noncomputable def cikkSeed (n ℓ e g h : ℕ) :=
  QueryLearner.bestOfSeed (ι := Fin n)
    (ampSeed (n := n) (PMF.uniformOfFintype (Trial ((cikkK e g * n + cikkK e g) *
        2 ^ binaryFieldDegree (cikkK e g * n + cikkK e g)) (2 ^ ℓ)))
      (cikkK e g) (cikkFixed e g) (cikkTrials e g) (cikkMasks e g))
    (cikkRuns e g h) (cikkSamples e g h)

private theorem one_div_two_pow_le_one (j : ℕ) : (1 : ℝ) / 2 ^ j ≤ 1 :=
  div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)

/-- **Learning from a dense test** [Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 5.1,
p. 10:19], for `p = 2`, in a per-function black-box form. Let the test accept at least
`2 ^ (2 ^ ℓ) 2 ^ (ℓ + 1 - g)` strings of `2 ^ ℓ` bits, and no output of the Nisan–Wigderson
generator of `glAmp f (cikkK e g)` for the design `Design.binaryPolynomial (k n + k) ℓ`, for any
`f ∈ C`. Then `cikkLearner n ℓ e g h test` learns `C` with error `2^{-e}` and confidence
`1 - 2^{-h}`. A single outer best-of selection replaces the source's per-stage boosts; this and the
other deviations are labelled in the module docstring. -/
theorem learns_cikkLearner {n ℓ : ℕ} (e g h : ℕ) {test : BitString (2 ^ ℓ) → Bool}
    {C : ConceptClass (BitString n) Bool}
    (hdense : 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ g * #{y | test y = true})
    (hrej : ∀ f ∈ C, ∀ z, test (generator (Design.binaryPolynomial (cikkK e g * n + cikkK e g) ℓ)
      (glAmp f (cikkK e g)) z) = false) :
    (cikkLearner n ℓ e g h test).Learns (cikkSeed n ℓ e g h) C (1 / 2 ^ e) (1 / 2 ^ h) := by
  -- stage 1: the Nisan–Wigderson reconstruction is a weak learner for `Amp(f)`
  have hδ : (2 : ℝ) ^ (ℓ + 1) / 2 ^ g ≤ dens {y | test y = true} := by
    rw [nnratCast_dens, div_le_div_iff₀ (by positivity) (by positivity)]
    have h' : ((2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) : ℕ) : ℝ) ≤ ((2 ^ g * #{y | test y = true} : ℕ) : ℝ) :=
      Nat.cast_le.2 hdense
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat] at h' ⊢
    linarith
  have h1 := nwLearner_learns_of_dens (Design.binaryPolynomial (cikkK e g * n + cikkK e g) ℓ)
    test (C := (glAmp · (cikkK e g)) '' C) hδ (by
      rintro _ ⟨f, hf, rfl⟩ z
      exact hrej f hf z)
  have hadv : (2 : ℝ) ^ (ℓ + 1) / 2 ^ g / (2 * ((2 ^ ℓ : ℕ) : ℝ)) = 1 / 2 ^ g := by
    push_cast
    field_simp
    ring
  rw [hadv] at h1
  -- stage 2: the reconstruction of the amplification
  have h2 := learns_ampLearner (s := cikkFixed e g) (m := cikkTrials e g) (K := cikkMasks e g)
    (ε := 1 / 2 ^ (e + 1)) h1 (one_div_two_pow_le_one g) (by positivity) (by positivity)
    (one_div_two_pow_le_one _) (cikkK_le_cikkMasks e g)
    (two_mul_cikkFixed_le_cikkK e g) (le_cikkFixed e g) (le_cikkTrials e g)
  -- stage 3: best-of selection
  have hp : (1 : ℝ) / 2 ^ g * ((1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2 / 8) ≤ 1 := by
    have hq : (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3) : ℝ) ^ 2 / 8 ≤ 1 := by
      have : (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3) : ℝ) ≤ 1 :=
        (div_le_self (by positivity) (one_le_pow₀ (by norm_num))).trans
          (one_div_two_pow_le_one g)
      have : (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3) : ℝ) ^ 2 ≤ 1 :=
        pow_le_one₀ (by positivity) this
      linarith
    calc (1 : ℝ) / 2 ^ g * ((1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2 / 8)
        ≤ 1 * 1 := mul_le_mul (one_div_two_pow_le_one g) hq (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have h3 := QueryLearner.learns_bestOf_of_success (k := cikkRuns e g h) (t := cikkSamples e g h)
    (θ := 1 / 2 ^ (e + 2)) (η := 1 / 2 ^ h) h2 hp (by positivity) (by positivity)
    (log_le_cikkRuns e g h) (log_le_cikkSamples e g h)
  refine h3.mono subset_rfl (le_of_eq ?_) le_rfl
  field_simp
  ring

/-- The learner makes at most `b (2 ^ ℓ 2 ^ (ℓ - 1) k) + t` queries, with `b = cikkRuns e g h`
runs, `t = cikkSamples e g h` sample points and `k = cikkK e g`: each run makes `2 ^ ℓ 2 ^ (ℓ - 1)`
queries to `Amp(f)`, each answered with `k` queries to `f`. -/
theorem queriesAtMost_cikkLearner (n ℓ e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool) :
    (cikkLearner n ℓ e g h test).QueriesAtMost
      (cikkRuns e g h * (2 ^ ℓ * 2 ^ (ℓ - 1) * cikkK e g) + cikkSamples e g h) :=
  QueryLearner.queriesAtMost_bestOf
    (queriesAtMost_ampLearner (nwLearner_queriesAtMost _ _) _ _ _)

/-- **Closed form of the number of queries**: at most `(h + 1) 2 ^ (2ℓ + 10g + 6e + 59)`. The
constant is this library's and is not tight. -/
theorem queriesAtMost_cikkLearner_two_pow (n ℓ e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool) :
    (cikkLearner n ℓ e g h test).QueriesAtMost ((h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 59)) := by
  refine fun ω => (queriesAtMost_cikkLearner n ℓ e g h test ω).trans ?_
  have hR := cikkRuns_le e g h
  have hK := cikkK_le_two_pow e g
  have hS := cikkSamples_le e g h
  have hℓ : 2 ^ ℓ * 2 ^ (ℓ - 1) ≤ 2 ^ (2 * ℓ) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the runs make at most half of the bound
  have h1 : cikkRuns e g h * (2 ^ ℓ * 2 ^ (ℓ - 1) * cikkK e g) ≤
      (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 58) :=
    calc cikkRuns e g h * (2 ^ ℓ * 2 ^ (ℓ - 1) * cikkK e g)
        ≤ (h + 1) * 2 ^ (9 * g + 4 * e + 43) * (2 ^ (2 * ℓ) * 2 ^ (2 * e + g + 15)) := by
          gcongr
      _ = (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 58) := by ring
  -- and so do the sample points
  have h2 : cikkSamples e g h ≤ (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 58) := by
    have hZ : 9 * g + 4 * e + 46 < 2 ^ (9 * g + 4 * e + 46) := Nat.lt_two_pow_self
    have hZ2 : 2 ≤ 2 ^ (9 * g + 4 * e + 46) := by omega
    have hmul : 9 * g + 4 * e + 2 * h + 46 ≤ (h + 1) * 2 ^ (9 * g + 4 * e + 46) := by
      have := Nat.mul_le_mul_left h hZ2
      calc 9 * g + 4 * e + 2 * h + 46
          ≤ h * 2 ^ (9 * g + 4 * e + 46) + 2 ^ (9 * g + 4 * e + 46) := by omega
        _ = (h + 1) * 2 ^ (9 * g + 4 * e + 46) := by ring
    calc cikkSamples e g h ≤ 2 ^ (2 * e + 3) * (9 * g + 4 * e + 2 * h + 46) := hS
      _ ≤ 2 ^ (2 * e + 3) * ((h + 1) * 2 ^ (9 * g + 4 * e + 46)) := by gcongr
      _ = (h + 1) * 2 ^ (9 * g + 6 * e + 49) := by ring
      _ ≤ (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 58) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc cikkRuns e g h * (2 ^ ℓ * 2 ^ (ℓ - 1) * cikkK e g) + cikkSamples e g h
      ≤ (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 58) +
          (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 58) := Nat.add_le_add h1 h2
    _ = (h + 1) * 2 ^ (2 * ℓ + 10 * g + 6 * e + 59) := by ring

end Cslib.MachineLearning.UniformLearning
