/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Crypto.Primitives.PRG.NisanWigderson
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Density
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.Finset.Sampling
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Expect
import Mathlib.Tactic.DeriveFintype

/-!
# Sampling the advice of the Nisan–Wigderson reconstruction

The reconstruction
`Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_card_nextBitGuess_eq` shows that, for a
deterministic test with advantage `ε` against the Nisan–Wigderson generator, *some* choice of a
position `i`, of the seed bits outside the `i`-th block, of a candidate bit for bit `i` and of
padding bits after position `i` gives a guess that agrees with the hard function `f` on a
`1 / 2 + ε / m` fraction of the inputs. Here these choices are sampled instead, as in the
randomized reconstruction of [Hirahara2018]: a *trial* `t` collects them, and its *agreement*
`trialAgreement D f test t` is the fraction of the inputs on which its guess is correct.
Probabilities are densities (`Finset.dens`) of sets of trials.

The agreement of a uniformly random trial is on average exactly `1 / 2 + (p₁ - p₀) / m`, where
`p₁` and `p₀` are the probabilities that the test accepts generated and uniform strings
(`Cslib.Crypto.PRG.NisanWigderson.expect_trialAgreement`): at a fixed position, the average
agreement is the probability that the predictor built from the test guesses that bit
(`Cslib.Crypto.PRG.NisanWigderson.toReal_predictionExperiment_eq_expect_trialAgreement`), and the
hybrid gaps telescope. Agreements are at most `1`, so by reverse averaging
(`Fintype.expect_sub_le_dens_filter`) a uniformly random trial has agreement at least
`1 / 2 + ε / (2 m)` with probability at least `ε / (2 m)`
(`Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials`). Among `k` independent trials
one does with probability at least `1 - (1 - ε / (2 m)) ^ k`
(`Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_exists_mem_goodTrials`), which is at least
`1 / 2` once `k ε ≥ 2 m`, for instance for `k = ⌈2 m / ε⌉`
(`Cslib.Crypto.PRG.NisanWigderson.half_le_dens_exists_mem_goodTrials`).

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.Trial`: the random choices of the reconstruction.
* `Cslib.Crypto.PRG.NisanWigderson.trialGuess`: the guess of the predictor built from a
  deterministic test, with its random choices fixed.
* `Cslib.Crypto.PRG.NisanWigderson.trialAgreement`: the fraction of inputs on which it is correct.
* `Cslib.Crypto.PRG.NisanWigderson.goodTrials`: the trials whose agreement reaches a threshold.

## Main results

* `Cslib.Crypto.PRG.Generator.toReal_realExperiment_pure`,
  `Cslib.Crypto.PRG.Generator.toReal_idealExperiment_pure`: the experiments of a deterministic
  test are densities.
* `Cslib.Crypto.PRG.NisanWigderson.toReal_predictionExperiment_eq_expect_trialAgreement`,
  `Cslib.Crypto.PRG.NisanWigderson.expect_trialAgreement`: the prediction experiments are averages
  of agreements.
* `Cslib.Crypto.PRG.NisanWigderson.half_add_div_le_expect_trialAgreement`,
  `Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_trialAgreement`: a test with advantage
  `ε` gives average agreement at least `1 / 2 + ε / m`, so some trial reaches it.
* `Cslib.Crypto.PRG.NisanWigderson.sub_div_le_dens_goodTrials`,
  `Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials`: a random trial is good with
  probability at least `ε / (2 m)`.
* `Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_exists_mem_goodTrials`,
  `Cslib.Crypto.PRG.NisanWigderson.half_le_dens_exists_mem_goodTrials`: repeated trials.

## References

* [S. Hirahara, *Non-black-box worst-case to average-case reductions within NP*][Hirahara2018]
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Cslib.Probability.PMF Finset
open scoped BigOperators ENNReal

section Deterministic

variable {Seed Output : Type*}

/-- A deterministic test accepts the output of a generator on a uniform seed with probability the
density of the seeds on which it accepts. -/
theorem Generator.toReal_realExperiment_pure [Fintype Seed] [Nonempty Seed]
    (G : Generator Seed Output) (test : Output → Bool) :
    (G.realExperiment (fun y => PMF.pure (test y)) true).toReal = dens {z | test (G z) = true} := by
  rw [Generator.realExperiment, Generator.outputDist, PMF.bind_map,
    ← toReal_uniformOfFintype_map_apply_true, ← PMF.bind_pure_comp]
  rfl

/-- A deterministic test accepts a uniform string with probability the density of the strings it
accepts. -/
theorem Generator.toReal_idealExperiment_pure [Fintype Output] [Nonempty Output]
    (test : Output → Bool) :
    (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal =
      dens {y | test y = true} := by
  rw [Generator.idealExperiment, ← toReal_uniformOfFintype_map_apply_true, ← PMF.bind_pure_comp]
  rfl

end Deterministic

namespace NisanWigderson

variable {ℓ n a m : ℕ}

/-- A *trial* of the reconstruction: its random choices. These are a position `pos`, a seed `seed`
whose bits outside the `pos`-th block are kept, a candidate bit `bit` for the bit at `pos`, and a
string `pad` whose bits after position `pos` pad the input of the test. -/
structure Trial (ℓ m : ℕ) where
  /-- The position of the predicted bit. -/
  pos : Fin m
  /-- The seed; its bits outside the `pos`-th block are kept. -/
  seed : Fin ℓ → Bool
  /-- The candidate value of the predicted bit. -/
  bit : Bool
  /-- The padding; its bits after position `pos` complete the input of the test. -/
  pad : Fin m → Bool
deriving DecidableEq, Fintype

/-- A trial is its four random choices. -/
def Trial.equivProd : Trial ℓ m ≃ Fin m × (Fin ℓ → Bool) × Bool × (Fin m → Bool) where
  toFun t := (t.pos, t.seed, t.bit, t.pad)
  invFun p :=
    let rest := p.2
    let bp := rest.2
    ⟨p.1, rest.1, bp.1, bp.2⟩

instance [NeZero m] : Nonempty (Trial ℓ m) :=
  ⟨⟨0, fun _ => false, false, fun _ => false⟩⟩

/-- The guess at the input `x` of the predictor built from the deterministic test `test`, with the
random choices `t` fixed: `nextBitGuess test t.pos t.bit t.pad` applied to the first `t.pos` bits
of the output of the generator on the seed `D.extend t.pos x t.seed`. -/
def trialGuess (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool)
    (t : Trial ℓ m) (x : Fin n → Bool) : Bool :=
  nextBitGuess test t.pos t.bit t.pad
    (Fin.take t.pos t.pos.isLt.le (generator D f (D.extend t.pos x t.seed)))

/-- The *agreement* of the trial `t`: the fraction of the inputs `x` on which its guess is `f x`. -/
def trialAgreement (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool)
    (test : (Fin m → Bool) → Bool) (t : Trial ℓ m) : ℚ≥0 :=
  dens {x | trialGuess D f test t x = f x}

/-- The *good* trials at threshold `θ`: those with agreement at least `θ`. -/
noncomputable def goodTrials (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool)
    (test : (Fin m → Bool) → Bool) (θ : ℝ) : Finset (Trial ℓ m) :=
  {t | θ ≤ (trialAgreement D f test t : ℝ)}

variable (D : Design ℓ n a m) (f : (Fin n → Bool) → Bool) (test : (Fin m → Bool) → Bool)

@[simp]
theorem mem_goodTrials {θ : ℝ} {t : Trial ℓ m} :
    t ∈ goodTrials D f test θ ↔ θ ≤ (trialAgreement D f test t : ℝ) := by
  simp [goodTrials]

/-- An agreement is at most `1`. -/
theorem trialAgreement_le_one (t : Trial ℓ m) : trialAgreement D f test t ≤ 1 :=
  dens_le_one

/-- Averaging over a uniform trial averages over its four random choices in turn. -/
private theorem expect_trial {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (g : Trial ℓ m → M) :
    𝔼 t, g t = 𝔼 i, 𝔼 w, 𝔼 r, 𝔼 u, g ⟨i, w, r, u⟩ := by
  rw [Fintype.expect_equiv Trial.equivProd g (fun p => g ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩)
    fun _ => rfl]
  simp only [Fintype.expect_prod_type]

/-- **Averaging over the random choices.** For a deterministic test, the probability that the
predictor built from it guesses bit `i` of the generator is the average agreement of the trials
at position `i`. -/
theorem toReal_predictionExperiment_eq_expect_trialAgreement (i : Fin m) :
    ((generator D f).predictionExperiment i (nextBitPredictor (fun y => PMF.pure (test y)) i)
        true).toReal =
      𝔼 w, 𝔼 r, 𝔼 u, (trialAgreement D f test ⟨i, w, r, u⟩ : ℝ) := by
  simp only [predictionExperiment_generator, hardwiredExperiment_nextBitPredictor_pure,
    monad_bind_eq_bind, toReal_uniformOfFintype_bind_apply, toReal_uniformOfFintype_map_apply_true,
    decide_eq_true_eq]
  rfl

/-- **Averaging over the random choices.** If `0 < m`, the agreement of a uniformly random trial
is on average `1 / 2 + (p₁ - p₀) / m`, where the test accepts generated strings with probability
`p₁` and uniform strings with probability `p₀`. -/
theorem expect_trialAgreement (hm : 0 < m) :
    𝔼 t : Trial ℓ m, (trialAgreement D f test t : ℝ) =
      1 / 2 + (((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
        (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) / m := by
  calc 𝔼 t : Trial ℓ m, (trialAgreement D f test t : ℝ)
      = 𝔼 i : Fin m, (1 / 2 + (generator D f).hybridGap (fun y => PMF.pure (test y)) i) := by
        rw [expect_trial]
        refine expect_congr rfl fun i _ => ?_
        rw [← toReal_predictionExperiment_eq_expect_trialAgreement,
          Generator.toReal_predictionExperiment_nextBitPredictor]
    _ = _ := by
        have hm' : (m : ℝ) ≠ 0 := by positivity
        rw [Fintype.expect_eq_sum_div_card, sum_add_distrib, Generator.sum_hybridGap, sum_const,
          card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- If `0 < m`, a deterministic test that accepts generated strings with probability at least `ε`
more than uniform ones gives an average agreement of at least `1 / 2 + ε / m`. -/
theorem half_add_div_le_expect_trialAgreement (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    1 / 2 + ε / m ≤ 𝔼 t : Trial ℓ m, (trialAgreement D f test t : ℝ) := by
  rw [expect_trialAgreement D f test hm]
  gcongr

/-- **The reconstruction**, in the vocabulary of trials: if `0 < m` and a deterministic test
accepts generated strings with probability at least `ε` more than uniform ones, some trial has
agreement at least `1 / 2 + ε / m`. -/
theorem exists_half_add_div_le_trialAgreement (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ∃ t : Trial ℓ m, 1 / 2 + ε / m ≤ (trialAgreement D f test t : ℝ) := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨t, -, ht⟩ := exists_le_of_le_expect univ_nonempty
    (half_add_div_le_expect_trialAgreement D f test hm hε)
  exact ⟨t, ht⟩

/-- **Sampling the advice**, exact form. Let `0 < m` and let a deterministic test accept generated
strings with probability at least `ε` more than uniform ones. For every `θ < 1`, a uniformly random
trial has agreement at least `θ` with probability at least `(1 / 2 + ε / m - θ) / (1 - θ)`. -/
theorem sub_div_le_dens_goodTrials (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal)
    {θ : ℝ} (hθ : θ < 1) :
    (1 / 2 + ε / m - θ) / (1 - θ) ≤ (dens (goodTrials D f test θ) : ℝ) := by
  have : NeZero m := ⟨hm.ne'⟩
  refine le_trans ?_ (Fintype.expect_sub_div_le_dens_filter
    (fun t => mod_cast trialAgreement_le_one D f test t) hθ)
  gcongr
  exact half_add_div_le_expect_trialAgreement D f test hm hε

/-- **Sampling the advice** [Hirahara2018]. Let `0 < m`, `0 ≤ ε`, and let a deterministic test
accept generated strings with probability at least `ε` more than uniform ones. A uniformly random
trial has agreement at least `1 / 2 + ε / (2 m)` with probability at least `ε / (2 m)`. -/
theorem div_two_mul_le_dens_goodTrials (hm : 0 < m) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ε / (2 * m) ≤ (dens (goodTrials D f test (1 / 2 + ε / (2 * m))) : ℝ) := by
  have : NeZero m := ⟨hm.ne'⟩
  refine le_trans ?_ (Fintype.expect_sub_le_dens_filter
    (fun t => mod_cast trialAgreement_le_one D f test t) (by positivity))
  have h := half_add_div_le_expect_trialAgreement D f test hm hε
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsplit : ε / m = ε / (2 * m) + ε / (2 * m) := by
    field_simp
    ring
  linarith

/-- **Repeated sampling.** Let `0 < m`, `0 ≤ ε`, and let a deterministic test accept generated
strings with probability at least `ε` more than uniform ones. Among `k` independent uniformly
random trials, one has agreement at least `1 / 2 + ε / (2 m)` with probability at least
`1 - (1 - ε / (2 m)) ^ k`. -/
theorem one_sub_pow_le_dens_exists_mem_goodTrials (hm : 0 < m) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) (k : ℕ) :
    1 - (1 - ε / (2 * m)) ^ k ≤ (dens {ts : Fin k → Trial ℓ m |
      ∃ j, ts j ∈ goodTrials D f test (1 / 2 + ε / (2 * m))} : ℝ) := by
  have : NeZero m := ⟨hm.ne'⟩
  have h := Fintype.one_sub_pow_le_dens_filter_exists_apply_mem (ι := Fin k)
    (div_two_mul_le_dens_goodTrials D f test hm hε₀ hε)
  rwa [Fintype.card_fin] at h

/-- **Repeated sampling** [Hirahara2018]. Let `0 < m`, `0 ≤ ε`, and let a deterministic test
accept generated strings with probability at least `ε` more than uniform ones. If `2 m ≤ k ε`,
then among `k` independent uniformly random trials one has agreement at least `1 / 2 + ε / (2 m)`
with probability at least `1 / 2`. -/
theorem half_le_dens_exists_mem_goodTrials (hm : 0 < m) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) {k : ℕ}
    (hk : 2 * m ≤ k * ε) :
    1 / 2 ≤ (dens {ts : Fin k → Trial ℓ m |
      ∃ j, ts j ∈ goodTrials D f test (1 / 2 + ε / (2 * m))} : ℝ) := by
  have : NeZero m := ⟨hm.ne'⟩
  have hm' : (0 : ℝ) < 2 * m := by positivity
  refine Fintype.half_le_dens_filter_exists_apply_mem (ι := Fin k) (by positivity)
    (div_two_mul_le_dens_goodTrials D f test hm hε₀ hε) ?_
  rw [Fintype.card_fin, ← mul_div_assoc, le_div_iff₀ hm', one_mul]
  exact hk

end NisanWigderson

end Cslib.Crypto.PRG
