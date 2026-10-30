/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Crypto.Primitives.PRG.Defs
public import Mathlib.Data.Fin.Tuple.Take
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF

/-!
# The next-bit test

A generator `G` with `m`-bit outputs is unpredictable when no predictor, shown the first `i` bits of
a generated output, guesses bit `i` with probability much better than `1 / 2`
[Boneh and Shoup, Attack Game 3.2 and Definition 3.3][BonehShoup2023]. This file proves that
unpredictability is equivalent to security in the sense of Attack Game 3.1, up to a factor of `m` in
the error. This is the next-bit theorem usually credited to Yao; the proof follows
[Boneh and Shoup, Section 3.5][BonehShoup2023] (see also
[Arora and Barak, Chapter 9][AroraBarak09]).

The proof is a hybrid argument. The `k`-th hybrid gives a test the first `k` bits of a generated
output followed by uniform bits. Running the test on the `0`-th hybrid is the ideal experiment of
Attack Game 3.1 and running it on the `m`-th is the real experiment, so the difference of the two
acceptance probabilities telescopes into the gaps between adjacent hybrids; the hybrids and the
telescoping hold for outputs over any finite alphabet. The predictor for bit
`i` built from a test pads the first `i` bits with a uniform candidate bit and uniform later bits,
runs the test, and keeps the candidate if the test accepts and flips it otherwise. By the
distinguisher/predictor lemma [Boneh and Shoup, Lemma 3.5][BonehShoup2023] it is correct with
probability exactly `1 / 2` plus the `i`-th hybrid gap.

Here the position `i` is a parameter of the prediction game, whereas the adversary of Attack Game
3.2 chooses it. A predictor that chooses its position at random wins with the average of the
fixed-position probabilities, so a bound for every fixed position also bounds it. As in the
definition of `Cslib.Crypto.PRG.Generator.Secure`, admissible tests and predictors are given by
caller-supplied predicates; the reductions between them are `Cslib.Crypto.PRG.nextBitPredictor`
and `Cslib.Crypto.PRG.predictionTest`.

## Main definitions

* `Cslib.Crypto.PRG.guessOfDistinguisher`: guess a bit with a randomized distinguisher.
* `Cslib.Crypto.PRG.Generator.hybridDist`, `Cslib.Crypto.PRG.Generator.hybridExperiment`,
  `Cslib.Crypto.PRG.Generator.hybridGap`: the hybrids between generated and uniform outputs.
* `Cslib.Crypto.PRG.Generator.predictionExperiment`,
  `Cslib.Crypto.PRG.Generator.predictionAdvantage`: Attack Game 3.2 at a fixed position.
* `Cslib.Crypto.PRG.Generator.Unpredictable`: concrete unpredictability against admissible
  predictors.
* `Cslib.Crypto.PRG.nextBitPredictor`: the predictor built from a test.
* `Cslib.Crypto.PRG.nextBitGuess`: the predictor built from a deterministic test, with its random
  choices fixed (`Cslib.Crypto.PRG.nextBitPredictor_pure`).
* `Cslib.Crypto.PRG.predictionTest`: the test built from a predictor.

## Main results

* `Cslib.Crypto.PRG.toReal_bind_guessOfDistinguisher`: the distinguisher/predictor lemma.
* `Cslib.Crypto.PRG.Generator.sum_hybridGap`, `Cslib.Crypto.PRG.Generator.exists_div_le_hybridGap`:
  the hybrid gaps telescope, so one of them is at least the average.
* `Cslib.Crypto.PRG.Generator.toReal_predictionExperiment_nextBitPredictor`: the predictor built
  from a test is correct with probability `1 / 2` plus a hybrid gap.
* `Cslib.Crypto.PRG.Generator.advantage_le_sum_predictionAdvantage`,
  `Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment`: a test with
  advantage `ε` yields a predictor for some position with success probability `1 / 2 + ε / m`.
* `Cslib.Crypto.PRG.Generator.Unpredictable.secure`: unpredictability with error `δ` implies
  security with error `m * δ`.
* `Cslib.Crypto.PRG.Generator.Secure.unpredictable`: security with error `ε` implies
  unpredictability with error `ε`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 3.5
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Cslib.Probability.PMF
open scoped NNReal ENNReal

section Guess

variable {S : Type*}

/-- Guess a bit with a randomized distinguisher `d`: draw a uniform candidate bit `r`, run `d r`,
and output `r` if it accepts and `!r` if it rejects [Boneh and Shoup, Lemma 3.5][BonehShoup2023]. -/
noncomputable def guessOfDistinguisher (d : Bool → PMF Bool) : PMF Bool := do
  let r ← uniformOfFintype Bool
  (d r).map fun a => if a then r else !r

private theorem map_decide_eq_apply_true {α : Type*} [DecidableEq α] (q : PMF α) (c : α) :
    (q.map fun a => decide (a = c)) true = q c := by
  rw [PMF.map_apply]
  simp

/-- The distinguisher/predictor lemma for a single bit, without subtraction. -/
private theorem guessOfDistinguisher_apply_add (d : Bool → PMF Bool) (b : Bool) :
    guessOfDistinguisher d b + (uniformOfFintype Bool).bind d true = d b true + 2⁻¹ := by
  have hd (r : Bool) : d r true + d r false = 1 := by
    simpa [tsum_bool] using (d r).tsum_coe
  have h2 : (2⁻¹ : ℝ≥0∞) * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  simp only [guessOfDistinguisher, monad_bind_eq_bind, PMF.bind_apply, PMF.map_apply, tsum_bool,
    uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, zero_add, add_zero]
    calc _ = 2⁻¹ * 2 * d false true + 2⁻¹ * (d true true + d true false) := by ring
      _ = _ := by rw [hd, h2, one_mul, mul_one]
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_eq_false, Bool.not_true,
      zero_add, add_zero]
    calc _ = 2⁻¹ * 2 * d true true + 2⁻¹ * (d false true + d false false) := by ring
      _ = _ := by rw [hd, h2, one_mul, mul_one]

private theorem bind_apply_add_of_forall {α β : Type*} (μ : PMF α) {f g h : α → PMF β} {b : β}
    {c : ℝ≥0∞} (hfg : ∀ x, f x b + g x b = h x b + c) :
    μ.bind f b + μ.bind g b = μ.bind h b + c := by
  simp only [PMF.bind_apply]
  rw [← tsum_add]
  simp_rw [← mul_add, hfg, mul_add]
  rw [tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- **The distinguisher/predictor lemma** [Boneh and Shoup, Lemma 3.5][BonehShoup2023]. Draw `x`
from `μ`. The guess `guessOfDistinguisher (d x)` equals `target x` with probability `1 / 2`, plus
the probability that `d x` accepts `target x`, minus the probability that `d x` accepts an
independent uniform bit. -/
theorem toReal_bind_guessOfDistinguisher (μ : PMF S) (target : S → Bool)
    (d : S → Bool → PMF Bool) :
    ((μ.bind fun x => (guessOfDistinguisher (d x)).map fun g => decide (g = target x))
        true).toReal =
      1 / 2 + ((μ.bind fun x => d x (target x)) true).toReal -
        ((μ.bind fun x => (uniformOfFintype Bool).bind (d x)) true).toReal := by
  have h := bind_apply_add_of_forall μ (b := true) (c := 2⁻¹)
    (f := fun x => (guessOfDistinguisher (d x)).map fun g => decide (g = target x))
    (g := fun x => (uniformOfFintype Bool).bind (d x)) (h := fun x => d x (target x))
    fun x => by
      simp only [map_decide_eq_apply_true]
      exact guessOfDistinguisher_apply_add (d x) (target x)
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ENNReal.toReal_add (PMF.apply_ne_top _ _) (by simp)] at h'
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
  linarith

end Guess

section Uniform

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]

/-- Overwriting one coordinate of a uniform function by an independent uniform value leaves it
uniform: `(r, z) ↦ (Function.update z i r, z i)` is an equivalence. -/
private theorem uniformOfFintype_bind_bind_update {γ : Type*} (i : ι) (f : (ι → β) → PMF γ) :
    ((uniformOfFintype β).bind fun r =>
      (uniformOfFintype (ι → β)).bind fun z => f (Function.update z i r)) =
      (uniformOfFintype (ι → β)).bind f :=
  uniformOfFintype_bind_bind_fst_equiv
    { toFun := fun p => (Function.update p.2 i p.1, p.2 i)
      invFun := fun q => (q.1 i, Function.update q.1 i q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp } f

end Uniform

section Hybrid

variable {Seed α : Type*} [Fintype Seed] [Nonempty Seed] [Fintype α] [Nonempty α] {m : ℕ}

/-- The `k`-th hybrid: the first `k` symbols of the generator's output on a uniform seed, followed
by independent uniform symbols. It is Hybrid `m - k` of
[Boneh and Shoup, Section 3.5][BonehShoup2023]. -/
noncomputable def Generator.hybridDist (G : Generator Seed (Fin m → α)) (k : ℕ) :
    PMF (Fin m → α) := do
  let y ← G.outputDist
  (uniformOfFintype (Fin m → α)).map fun z j => if (j : ℕ) < k then y j else z j

/-- The `0`-th hybrid is uniform. -/
@[simp]
theorem Generator.hybridDist_zero (G : Generator Seed (Fin m → α)) :
    G.hybridDist 0 = uniformOfFintype (Fin m → α) := by
  simp only [Generator.hybridDist, monad_bind_eq_bind, Nat.not_lt_zero, ite_false, PMF.bind_const]
  exact PMF.map_id _

/-- The `k`-th hybrid with `m ≤ k` is the output distribution of the generator. -/
theorem Generator.hybridDist_of_le (G : Generator Seed (Fin m → α)) {k : ℕ} (hk : m ≤ k) :
    G.hybridDist k = G.outputDist := by
  have h (y : Fin m → α) :
      (fun (z : Fin m → α) (j : Fin m) => if (j : ℕ) < k then y j else z j) =
        Function.const _ y := by
    funext z j
    simp [j.isLt.trans_le hk]
  simp only [Generator.hybridDist, monad_bind_eq_bind, h, PMF.map_const, PMF.bind_pure]

/-- Run a test on the `k`-th hybrid. -/
noncomputable def Generator.hybridExperiment (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) (k : ℕ) : PMF Bool :=
  (G.hybridDist k).bind adversary

/-- A test run on the `0`-th hybrid is the ideal experiment of Attack Game 3.1. -/
@[simp]
theorem Generator.hybridExperiment_zero (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) :
    G.hybridExperiment adversary 0 = idealExperiment adversary := by
  rw [Generator.hybridExperiment, Generator.hybridDist_zero, idealExperiment]

/-- A test run on the `k`-th hybrid with `m ≤ k` is the real experiment of Attack Game 3.1. -/
theorem Generator.hybridExperiment_of_le (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) {k : ℕ} (hk : m ≤ k) :
    G.hybridExperiment adversary k = G.realExperiment adversary := by
  rw [Generator.hybridExperiment, G.hybridDist_of_le hk, Generator.realExperiment]

/-- A test run on the `k`-th hybrid sees the first `k` symbols of a generated output followed by
the remaining symbols of an independent uniform string. -/
theorem Generator.hybridExperiment_eq_bind (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) (k : ℕ) :
    G.hybridExperiment adversary k = G.outputDist.bind fun y =>
      (uniformOfFintype (Fin m → α)).bind fun z =>
        adversary fun j => if (j : ℕ) < k then y j else z j := by
  simp only [Generator.hybridExperiment, Generator.hybridDist, monad_bind_eq_bind, PMF.bind_bind,
    PMF.bind_map]
  rfl

/-- The `i`-th hybrid gap of a test: the probability that it accepts the `(i + 1)`-st hybrid
minus the probability that it accepts the `i`-th, in which symbol `i` is uniform instead of
generated. -/
noncomputable def Generator.hybridGap (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) (i : Fin m) : ℝ :=
  (G.hybridExperiment adversary ((i : ℕ) + 1) true).toReal -
    (G.hybridExperiment adversary i true).toReal

/-- The hybrid gaps of a test telescope to the probability that it accepts in the real experiment
minus the probability that it accepts in the ideal experiment. -/
theorem Generator.sum_hybridGap (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) :
    ∑ i, G.hybridGap adversary i =
      (G.realExperiment adversary true).toReal - (idealExperiment adversary true).toReal := by
  rw [← G.hybridExperiment_of_le adversary le_rfl, ← G.hybridExperiment_zero adversary]
  exact (Fin.sum_univ_eq_sum_range (fun k => (G.hybridExperiment adversary (k + 1) true).toReal -
    (G.hybridExperiment adversary k true).toReal) m).trans
    (Finset.sum_range_sub (fun k => (G.hybridExperiment adversary k true).toReal) m)

/-- **The hybrid argument.** If `0 < m` and a test accepts in the real experiment with probability
at least `ε` more than in the ideal experiment, then one of its hybrid gaps is at least
`ε / m`. -/
theorem Generator.exists_div_le_hybridGap (G : Generator Seed (Fin m → α))
    (adversary : Adversary (Fin m → α)) (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ (G.realExperiment adversary true).toReal -
      (idealExperiment adversary true).toReal) :
    ∃ i, ε / m ≤ G.hybridGap adversary i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le (f := fun _ => ε / m)
    (g := G.hybridGap adversary) ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ (by positivity), G.sum_hybridGap]
      exact hε)
  exact ⟨i, hi⟩

end Hybrid

section Prediction

variable {Seed : Type*} [Fintype Seed] [Nonempty Seed] {m : ℕ}

/-- Attack Game 3.2 of [BonehShoup2023] at the fixed position `i`: the predictor receives the
first `i` bits of the generator's output on a uniform seed, and the experiment outputs `true`
exactly when the predictor's guess is bit `i`. -/
noncomputable def Generator.predictionExperiment (G : Generator Seed (Fin m → Bool))
    (i : Fin m) (predictor : Adversary (Fin i → Bool)) : PMF Bool := do
  let y ← G.outputDist
  (predictor (Fin.take i i.isLt.le y)).map fun g => decide (g = y i)

/-- The advantage of a predictor in Attack Game 3.2 of [BonehShoup2023]: the distance of its
probability of guessing bit `i` correctly from `1 / 2`. -/
noncomputable def Generator.predictionAdvantage (G : Generator Seed (Fin m → Bool))
    (i : Fin m) (predictor : Adversary (Fin i → Bool)) : ℝ :=
  |(G.predictionExperiment i predictor true).toReal - 1 / 2|

/-- Concrete unpredictability against admissible predictors
[Boneh and Shoup, Definition 3.3 with an explicit error][BonehShoup2023]: every admissible predictor
for every position has advantage at most `δ`. As for `Cslib.Crypto.PRG.Generator.Secure`, the
predicate `Admissible` is supplied by the caller; `fun _ _ => True` allows arbitrary predictors. -/
def Generator.Unpredictable (G : Generator Seed (Fin m → Bool))
    (Admissible : (i : Fin m) → Adversary (Fin i → Bool) → Prop) (δ : ℝ≥0) : Prop :=
  ∀ i predictor, Admissible i predictor → G.predictionAdvantage i predictor ≤ δ

/-- The predictor for bit `i` built from a test, following the proof of
[Boneh and Shoup, Theorem 3.6.][BonehShoup2023] Given the first `i` bits `x`, it applies
`Cslib.Crypto.PRG.guessOfDistinguisher` to the distinguisher that, on a candidate bit `r`, runs the
test on `x`, followed by `r` at position `i`, followed by uniform bits. -/
noncomputable def nextBitPredictor (adversary : Adversary (Fin m → Bool)) (i : Fin m) :
    Adversary (Fin i → Bool) := fun x =>
  guessOfDistinguisher fun r => do
    let z ← uniformOfFintype (Fin m → Bool)
    adversary fun j => if h : (j : ℕ) < i then x ⟨j, h⟩ else if j = i then r else z j

/-- The guess of the predictor built from a deterministic test, with its random choices fixed.
Given the first `i` bits `x`, it runs the test on `x`, followed by the candidate bit `r` at
position `i`, followed by the bits of `u` after position `i`, and outputs `r` if the test accepts
and `!r` otherwise. -/
def nextBitGuess (test : (Fin m → Bool) → Bool) (i : Fin m) (r : Bool) (u : Fin m → Bool)
    (x : Fin i → Bool) : Bool :=
  if test fun j => if h : (j : ℕ) < i then x ⟨j, h⟩ else if j = i then r else u j then r else !r

/-- For a deterministic test, the predictor built from it draws a uniform candidate bit `r` and a
uniform string `u` and outputs `nextBitGuess test i r u x`. -/
theorem nextBitPredictor_pure (test : (Fin m → Bool) → Bool) (i : Fin m) (x : Fin i → Bool) :
    nextBitPredictor (fun y => PMF.pure (test y)) i x =
      (do
        let r ← uniformOfFintype Bool
        (uniformOfFintype (Fin m → Bool)).map fun u => nextBitGuess test i r u x) := by
  simp only [nextBitPredictor, guessOfDistinguisher, monad_bind_eq_bind, PMF.map_bind, PMF.pure_map]
  rfl

/-- The predictor built from a test guesses bit `i` correctly with probability exactly `1 / 2`
plus the `i`-th hybrid gap of the test. -/
theorem Generator.toReal_predictionExperiment_nextBitPredictor
    (G : Generator Seed (Fin m → Bool)) (adversary : Adversary (Fin m → Bool)) (i : Fin m) :
    (G.predictionExperiment i (nextBitPredictor adversary i) true).toReal =
      1 / 2 + G.hybridGap adversary i := by
  have hpad (y z : Fin m → Bool) (r : Bool) :
      (fun j : Fin m => if h : (j : ℕ) < i then Fin.take i i.isLt.le y ⟨j, h⟩
        else if j = i then r else z j) =
        fun j : Fin m => if (j : ℕ) < i then y j else Function.update z i r j := by
    funext j
    split_ifs <;> simp_all
  have hsucc (y z : Fin m → Bool) :
      (fun j : Fin m => if (j : ℕ) < i then y j else Function.update z i (y i) j) =
        fun j : Fin m => if (j : ℕ) < i + 1 then y j else z j := by
    funext j
    rw [Function.update_apply]
    by_cases hji : j = i
    · subst hji
      simp
    · have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
      split_ifs <;> first | rfl | omega
  have h := toReal_bind_guessOfDistinguisher G.outputDist (fun y => y i)
    fun y r => (uniformOfFintype (Fin m → Bool)).bind fun z =>
      adversary fun j => if h : (j : ℕ) < i then Fin.take i i.isLt.le y ⟨j, h⟩
        else if j = i then r else z j
  refine h.trans ?_
  rw [Generator.hybridGap, G.hybridExperiment_eq_bind, G.hybridExperiment_eq_bind]
  simp only [hpad, hsucc]
  have hlast : (G.outputDist.bind fun y => (uniformOfFintype Bool).bind fun r =>
      (uniformOfFintype (Fin m → Bool)).bind fun z =>
        adversary fun j => if (j : ℕ) < i then y j else Function.update z i r j) =
      G.outputDist.bind fun y => (uniformOfFintype (Fin m → Bool)).bind fun z =>
        adversary fun j => if (j : ℕ) < i then y j else z j := by
    congr 1
    funext y
    exact uniformOfFintype_bind_bind_update i fun w =>
      adversary fun j => if (j : ℕ) < i then y j else w j
  rw [hlast]
  ring

/-- The advantage of the predictor built from a test is the absolute value of the corresponding
hybrid gap. -/
theorem Generator.predictionAdvantage_nextBitPredictor (G : Generator Seed (Fin m → Bool))
    (adversary : Adversary (Fin m → Bool)) (i : Fin m) :
    G.predictionAdvantage i (nextBitPredictor adversary i) = |G.hybridGap adversary i| := by
  rw [Generator.predictionAdvantage, G.toReal_predictionExperiment_nextBitPredictor,
    add_sub_cancel_left]

/-- The advantage of a test is at most the sum, over all positions, of the advantages of the
predictors built from it. -/
theorem Generator.advantage_le_sum_predictionAdvantage (G : Generator Seed (Fin m → Bool))
    (adversary : Adversary (Fin m → Bool)) :
    G.advantage adversary ≤ ∑ i, G.predictionAdvantage i (nextBitPredictor adversary i) := by
  rw [Generator.advantage, ← G.sum_hybridGap]
  simpa only [G.predictionAdvantage_nextBitPredictor] using Finset.abs_sum_le_sum_abs _ _

/-- If `0 < m`, then for some position the predictor built from a test has advantage at least
the advantage of the test divided by `m`. -/
theorem Generator.exists_div_le_predictionAdvantage (G : Generator Seed (Fin m → Bool))
    (adversary : Adversary (Fin m → Bool)) (hm : 0 < m) :
    ∃ i, G.advantage adversary / m ≤ G.predictionAdvantage i (nextBitPredictor adversary i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le (f := fun _ => G.advantage adversary / m)
    (g := fun i => G.predictionAdvantage i (nextBitPredictor adversary i))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ (by positivity)]
      exact G.advantage_le_sum_predictionAdvantage adversary)
  exact ⟨i, hi⟩

/-- **The next-bit theorem** in the one-sided form of [Arora and Barak, Chapter 9.][AroraBarak09] If
`0 < m` and a test accepts in the real experiment with probability at least `ε` more than in the
ideal experiment, then for some position `i` the predictor built from the test guesses bit `i`
correctly with probability at least `1 / 2 + ε / m`. -/
theorem Generator.exists_half_add_div_le_predictionExperiment
    (G : Generator Seed (Fin m → Bool)) (adversary : Adversary (Fin m → Bool)) (hm : 0 < m)
    {ε : ℝ} (hε : ε ≤ (G.realExperiment adversary true).toReal -
      (idealExperiment adversary true).toReal) :
    ∃ i, 1 / 2 + ε / m ≤
      (G.predictionExperiment i (nextBitPredictor adversary i) true).toReal := by
  obtain ⟨i, hi⟩ := G.exists_div_le_hybridGap adversary hm hε
  refine ⟨i, ?_⟩
  rw [G.toReal_predictionExperiment_nextBitPredictor]
  linarith

/-- **Unpredictability implies security** [Boneh and Shoup, Theorem 3.6][BonehShoup2023]. If every
admissible predictor has advantage at most `δ`, and the predictors built from admissible tests are
admissible, then every admissible test has advantage at most `m * δ`. -/
theorem Generator.Unpredictable.secure {G : Generator Seed (Fin m → Bool)}
    {Admissible : Adversary (Fin m → Bool) → Prop}
    {AdmissiblePredictor : (i : Fin m) → Adversary (Fin i → Bool) → Prop} {δ : ℝ≥0}
    (hG : G.Unpredictable AdmissiblePredictor δ)
    (hred : ∀ adversary, Admissible adversary →
      ∀ i, AdmissiblePredictor i (nextBitPredictor adversary i)) :
    G.Secure Admissible (m * δ) := by
  intro adversary ha
  calc G.advantage adversary
      ≤ ∑ i, G.predictionAdvantage i (nextBitPredictor adversary i) :=
        G.advantage_le_sum_predictionAdvantage adversary
    _ ≤ ∑ _i : Fin m, (δ : ℝ) := Finset.sum_le_sum fun i _ => hG i _ (hred adversary ha i)
    _ = ((m * δ : ℝ≥0) : ℝ) := by simp

/-- The test built from a predictor for bit `i`, following the proof of
[Boneh and Shoup, Theorem 3.4][BonehShoup2023]: run the predictor on the first `i` bits and accept
exactly when its guess is bit `i`. -/
noncomputable def predictionTest (i : Fin m) (predictor : Adversary (Fin i → Bool)) :
    Adversary (Fin m → Bool) := fun y =>
  (predictor (Fin.take i i.isLt.le y)).map fun g => decide (g = y i)

/-- The real experiment against the test built from a predictor is the prediction experiment. -/
@[simp]
theorem Generator.realExperiment_predictionTest (G : Generator Seed (Fin m → Bool)) (i : Fin m)
    (predictor : Adversary (Fin i → Bool)) :
    G.realExperiment (predictionTest i predictor) = G.predictionExperiment i predictor :=
  rfl

/-- On a uniform string, bit `i` is a uniform bit independent of the first `i` bits, so the test
built from a predictor accepts with probability `1 / 2`. -/
@[simp]
theorem Generator.idealExperiment_predictionTest_apply_true (i : Fin m)
    (predictor : Adversary (Fin i → Bool)) :
    idealExperiment (predictionTest i predictor) true = 2⁻¹ := by
  rw [idealExperiment, ← uniformOfFintype_bind_bind_update i, PMF.bind_comm]
  refine bind_apply_of_forall _ fun z => ?_
  have hq := (predictor (Fin.take i i.isLt.le z)).tsum_coe
  rw [tsum_bool] at hq
  simp only [predictionTest, Fin.take_update_of_ge _ _ _ _ le_rfl, Function.update_self,
    PMF.bind_apply, tsum_bool, uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    map_decide_eq_apply_true]
  rw [← mul_add, hq, mul_one]

/-- The test built from a predictor has the advantage of the predictor. -/
theorem Generator.advantage_predictionTest (G : Generator Seed (Fin m → Bool)) (i : Fin m)
    (predictor : Adversary (Fin i → Bool)) :
    G.advantage (predictionTest i predictor) = G.predictionAdvantage i predictor := by
  rw [Generator.advantage, realExperiment_predictionTest,
    idealExperiment_predictionTest_apply_true, Generator.predictionAdvantage]
  norm_num

/-- **Security implies unpredictability** [Boneh and Shoup, Theorem 3.4][BonehShoup2023]. If every
admissible test has advantage at most `ε`, and the tests built from admissible predictors are
admissible, then every admissible predictor has advantage at most `ε`. -/
theorem Generator.Secure.unpredictable {G : Generator Seed (Fin m → Bool)}
    {Admissible : Adversary (Fin m → Bool) → Prop}
    {AdmissiblePredictor : (i : Fin m) → Adversary (Fin i → Bool) → Prop} {ε : ℝ≥0}
    (hG : G.Secure Admissible ε)
    (hred : ∀ i predictor, AdmissiblePredictor i predictor →
      Admissible (predictionTest i predictor)) :
    G.Unpredictable AdmissiblePredictor ε := fun i predictor h =>
  G.advantage_predictionTest i predictor ▸ hG _ (hred i predictor h)

end Prediction

end Cslib.Crypto.PRG
