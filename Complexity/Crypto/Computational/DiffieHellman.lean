/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Crypto.Computational.DiscreteLog
public import Complexity.Crypto.Game.Statistical
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Languages.Probabilistic.Repeat
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.Bits
import Complexity.Languages.Probabilistic.Concentration
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PPT
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Computational and Decisional Diffie–Hellman assumptions

Over a `PrimeOrderGroupFamily`, the Computational Diffie–Hellman (CDH) experiment
([BonehShoup2023], Attack Game 10.5) draws a group description `d` from a setup law and two
independent uniform exponents `α, β : ZMod (F.order d)`, gives the adversary `(d, encode (α • g),
encode (β • g))`, and accepts when the adversary outputs `encode ((α * β) • g)`.

The Decisional Diffie–Hellman (DDH) experiment ([BonehShoup2023], Attack Game 10.6) compares the
real tuple `(d, encode (α • g), encode (β • g), encode ((α * β) • g))` against the ideal tuple
`(d, encode (α • g), encode (β • g), encode (γ • g))` with an independent uniform `γ`.

We prove the implications `DDH ⇒ CDH ⇒ DiscreteLog` between the assumptions, the distributional
rerandomisation lemma underlying the random self-reducibility of DDH ([BonehShoup2023],
Section 10.11, Exercises 10.8–10.9, pp. 425–426; `ddhRerandomizeLaw_real` and
`ddhRerandomizeLaw_ideal`), its word-level and game-level consequences
(`encodeDDHRerandomize`, `ddhRerandomizeGame`, `ddhRerandomizeGame_real`,
`ddhRerandomizeGame_ideal`, `advantage_ddhRerandomizeGame_eq`, `DDH.ddhRerandomizeGame`), an
original single-invocation worst-case-to-average-case DDH distinguishing reduction using
`ProbComp.sampleModNat` (`ddhSampleModExponents`, `ddhSelfReduceDistinguisher`,
`ddhWorstCaseGame`, `advantage_ddhRerandomizeGame_ddhWorstCaseGame_le`,
`advantage_ddhRealGame_le_ddhWorstCaseGame`, `ddh_of_worstCase`), and the worst-case DDH decider
of [BonehShoup2023], Section 10.11, Exercise 10.10 (p. 426; `ddhRealRefTuple`, `ddhIdealRefTuple`,
`ddhAmplifiedDecider`, `isPPTOn_ddhAmplifiedDecider`, `ddhAmplifiedDecider_error_le_pow`,
`negligible_ddhAmplifiedDecider_error`), which amplifies an average-case distinguisher with
inverse-polynomial advantage via repeated random self-reduction trials and a Chernoff/Hoeffding
tail bound (`ProbComp.countTrue_average_deviation_pow`) so that it correctly decides every input
tuple `(α • g, β • g, γ • g)` except with negligible error probability. The Diffie–Hellman
assumptions are hypotheses, not theorems.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.cdhGame`, `Cslib.Crypto.PrimeOrderGroupFamily.CDH`:
  the Computational Diffie–Hellman experiment and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlToCDHAdversary`: the reduction from discrete logarithm to
  CDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhIdealGame`, `Cslib.Crypto.PrimeOrderGroupFamily.DDH`:
  the real and ideal Decisional Diffie–Hellman experiments and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.cdhToDDHDistinguisher`: the reduction from CDH to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeDDHRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeGame`: algebraic, word-level, and game-level
  DDH rerandomisation ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.sampleExp`: approximate uniform exponent sampling modulo
  `F.order d` via `ProbComp.sampleModNat` with statistical distance at most `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhSampleModExponents`,
  `Cslib.Crypto.PrimeOrderGroupFamily.sampleModZModLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhSelfReduceDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhWorstCaseGame`: original single-invocation
  worst-case-to-average-case DDH distinguishing reduction.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealRefTuple`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhIdealRefTuple`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhAmplifiedDecider`: reference DDH / non-DDH tuples and
  the Chernoff-amplified worst-case DDH decider ([BonehShoup2023], Exercise 10.10, p. 426).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_discreteLogGame_le_cdhGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDH.discreteLog`: `CDH` implies `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_cdhGame_le_advantage_ddh_add`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.cdh`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.discreteLog`: `DDH` implies `CDH` and `DiscreteLog`
  when `1 / q` is negligible.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_ideal`: the distributional rerandomisation
  lemma for DDH tuples ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.encodeDDHRerandomize_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeDDHRerandomize_val`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeDDHRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeGame_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeGame_ideal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhRerandomizeGame_eq`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhRerandomizeGame`: word-level and game-level
  consequences of Exercises 10.8–10.9 (pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_sampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_ddhSampleModExponents`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dist_sampleModZModLaw_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_ddhSelfReduceDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhRealGame_le_ddhWorstCaseGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_worstCase`: original single-invocation
  worst-case-to-average-case DDH distinguishing reduction.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_ddhAmplifiedDecider`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhAmplifiedDecider_error_le_pow`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhAmplifiedDecider_correct_ge_one_sub_pow`,
  `Cslib.Crypto.PrimeOrderGroupFamily.negligible_ddhAmplifiedDecider_error`: worst-case DDH
  decision with negligible error from an average-case distinguisher with inverse-polynomial
  advantage ([BonehShoup2023], Exercise 10.10, p. 426).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 10.5 (Attack Games 10.5–10.6, pp. 409–410) and
  Section 10.11 (Exercises 10.7–10.10, pp. 425–426).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

variable (F : PrimeOrderGroupFamily)

/-! ### Computational Diffie–Hellman (CDH) -/

/-- The Computational Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.5): draw a
description `d` and independent uniform `α, β : ZMod (F.order d)`, give the adversary the
description and the encodings of `α • g` and `β • g`, and accept when it outputs the encoding of
`(α * β) • g`. -/
noncomputable def cdhGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let guess ← ProbComp.eval (adversary n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d)))
  return decide (guess = F.encode d ((α * β) • F.generator d))

/-- The Computational Diffie–Hellman assumption for a family and a setup law: every uniform strict
PPT adversary computes `encode ((α * β) • g)` from `(d, encode (α • g), encode (β • g))` with
negligible probability. -/
def CDH (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool),
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) encBits
      (fun input => adversary input.1 input.2) →
    Negligible fun n => Game.succProbability (F.cdhGame setup adversary n)

/-- Turn a discrete-logarithm adversary into a CDH adversary by running it on `(d, encode (α • g))`
to obtain a candidate exponent `a` and multiplying `encode (β • g)` by `a`. -/
def dlToCDHAdversary (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool))
    (n : ℕ) (input : F.Desc × List Bool × List Bool) : ProbComp (List Bool) := do
  let guess ← adversary n (input.1, input.2.1)
  return F.smul (input.1, ofBits guess, input.2.2)

/-- Whenever the discrete-logarithm adversary recovers `α`, `dlToCDHAdversary` outputs the valid
Diffie–Hellman shared element `encode ((α * β) • g)`. -/
theorem succProbability_discreteLogGame_le_cdhGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) :
    Game.succProbability (F.discreteLogGame setup adversary n) ≤
      Game.succProbability (F.cdhGame setup (F.dlToCDHAdversary adversary) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [discreteLogGame, cdhGame, dlToCDHAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun d => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun α => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
    ((ProbComp.eval (adversary n (d, F.encode d (α • F.generator d)))).bind _)]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun β => mul_le_mul_of_nonneg_left ?_ zero_le
  refine ENNReal.tsum_le_tsum fun guess => mul_le_mul_of_nonneg_left ?_ zero_le
  by_cases hα : (ofBits guess : ZMod (F.order d)) = α
  · simp only [hα, F.smul_encode, smul_smul, decide_true, le_rfl]
  · simp only [hα, decide_false, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, zero_le]

/-- The discrete-logarithm-to-CDH reduction is uniform strict PPT when the discrete-logarithm
adversary is. -/
theorem isPPTOn_dlToCDHAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => adversary input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) encBits
      (fun input => F.dlToCDHAdversary adversary input.1 input.2) := by
  have hsmul := F.computableInPolyTime_smul.tidy
  unfold dlToCDHAdversary
  refine (hA.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool =>
      (input.1, (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact ComputableTidilyInPolyTime.isPPTOn (by fun_prop)

/-- **CDH implies the discrete-logarithm assumption**. -/
theorem CDH.discreteLog {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (h : F.CDH setup) :
    F.DiscreteLog setup :=
  fun adversary hA => negligible_of_le (h _ (F.isPPTOn_dlToCDHAdversary hA))
    (F.succProbability_discreteLogGame_le_cdhGame setup adversary)

/-! ### Decisional Diffie–Hellman (DDH) -/

/-- The real Decisional Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.6): draw `d`
and independent uniform `α, β : ZMod (F.order d)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), encode ((α * β) • g))`. -/
noncomputable def ddhRealGame (setup : ℕ → PMF F.Desc)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d ((α * β) • F.generator d)))

/-- The ideal Decisional Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.6): draw `d`
and independent uniform `α, β, γ : ZMod (F.order d)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), encode (γ • g))`. -/
noncomputable def ddhIdealGame (setup : ℕ → PMF F.Desc)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d (γ • F.generator d)))

/-- The Decisional Diffie–Hellman assumption for a family and a setup law: every uniform strict PPT
distinguisher has negligible advantage between `ddhRealGame` and `ddhIdealGame`. -/
def DDH (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable (F.ddhRealGame setup) (F.ddhIdealGame setup)
    fun distinguisher =>
      IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBool (fun input => distinguisher input.1 input.2)

/-- Turn a CDH adversary into a DDH distinguisher by testing whether its candidate shared element
equals the challenge third element. -/
def cdhToDDHDistinguisher
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool))
    (n : ℕ) (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let guess ← adversary n (input.1, input.2.1, input.2.2.1)
  return decide (guess = input.2.2.2)

/-- In the real DDH game, `cdhToDDHDistinguisher` simulates the CDH game exactly. -/
@[simp] theorem ddhRealGame_cdhToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n : ℕ) :
    F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n = F.cdhGame setup adversary n := by
  simp only [ddhRealGame, cdhToDDHDistinguisher, cdhGame, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

/-- A fixed candidate word matches a uniformly chosen encoded group element with probability at
most `(F.order d)⁻¹`. -/
private theorem uniform_decide_eq_encode_le (d : F.Desc) (guess : List Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind
      (fun γ => PMF.pure (decide (guess = F.encode d (γ • F.generator d))))) true ≤
      (F.order d : ℝ≥0∞)⁻¹ := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ZMod.card, PMF.pure_apply, eq_comm (a := true),
    decide_eq_true_eq]
  have hcard :
      (Finset.univ.filter
        (fun γ : ZMod (F.order d) => guess = F.encode d (γ • F.generator d))).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr fun {γ₁ γ₂} h₁ h₂ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact F.smul_generator_injective d (F.encode_injective d (h₁.symm.trans h₂))
  calc ∑ x : ZMod (F.order d),
        (F.order d : ℝ≥0∞)⁻¹ *
          (if guess = F.encode d (x • F.generator d) then 1 else 0)
      = ((Finset.univ.filter
          (fun γ : ZMod (F.order d) =>
            guess = F.encode d (γ • F.generator d))).card : ℝ≥0∞) *
          (F.order d : ℝ≥0∞)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_boole, mul_comm]
    _ ≤ 1 * (F.order d : ℝ≥0∞)⁻¹ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) zero_le
    _ = (F.order d : ℝ≥0∞)⁻¹ := one_mul _

/-- In the ideal DDH game, `cdhToDDHDistinguisher` succeeds with probability at most `1 / m`
whenever every supported group order is at least `m`. -/
theorem ddhIdealGame_cdhToDDHDistinguisher_true_le (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n m : ℕ)
    (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) true ≤ (m : ℝ≥0∞)⁻¹ := by
  simp only [ddhIdealGame, cdhToDDHDistinguisher, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc ∑' d, setup n d * ∑' α, PMF.uniformOfFintype (ZMod (F.order d)) α *
        ∑' β, PMF.uniformOfFintype (ZMod (F.order d)) β *
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (ProbComp.eval (adversary n
              (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d)))).bind
              fun guess =>
                PMF.pure (decide (guess = F.encode d (γ • F.generator d)))) true
      ≤ ∑' d, setup n d * (m : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun d => ?_
        by_cases hd : d ∈ (setup n).support
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hord : (F.order d : ℝ≥0∞)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hm d hd))
          calc ∑' α, PMF.uniformOfFintype (ZMod (F.order d)) α *
                ∑' β, PMF.uniformOfFintype (ZMod (F.order d)) β *
                  ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                    (ProbComp.eval (adversary n
                      (d, F.encode d (α • F.generator d),
                        F.encode d (β • F.generator d)))).bind fun guess =>
                      PMF.pure (decide (guess = F.encode d (γ • F.generator d)))) true
              ≤ ∑' α, PMF.uniformOfFintype (ZMod (F.order d)) α *
                  ∑' β, PMF.uniformOfFintype (ZMod (F.order d)) β * (m : ℝ≥0∞)⁻¹ := by
                refine ENNReal.tsum_le_tsum fun α => mul_le_mul_of_nonneg_left ?_ zero_le
                refine ENNReal.tsum_le_tsum fun β => mul_le_mul_of_nonneg_left ?_ zero_le
                rw [PMF.bind_comm, PMF.bind_apply]
                calc ∑' guess, ProbComp.eval (adversary n
                        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d))) guess *
                      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                        PMF.pure (decide (guess = F.encode d (γ • F.generator d)))) true
                    ≤ ∑' guess, ProbComp.eval (adversary n
                        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d))) guess *
                      (m : ℝ≥0∞)⁻¹ := by
                      refine ENNReal.tsum_le_tsum fun guess =>
                        mul_le_mul_of_nonneg_left
                          ((F.uniform_decide_eq_encode_le d guess).trans hord) zero_le
                  _ = (m : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            _ = (m : ℝ≥0∞)⁻¹ := by
                simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        · have hd0 : setup n d = 0 := by rwa [PMF.mem_support_iff, not_not] at hd
          simp only [hd0, zero_mul, le_rfl]
    _ = (m : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Quantitative reduction from CDH to DDH**: when every supported group at parameter `n` has
order at least `m > 0`, any CDH adversary's success probability is at most the DDH distinguishing
advantage of `cdhToDDHDistinguisher` plus `1 / m`. -/
theorem succProbability_cdhGame_le_advantage_ddh_add (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.succProbability (F.cdhGame setup adversary n) ≤
      Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
        (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) + 1 / m := by
  have hideal :
      Game.succProbability (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) ≤
        1 / m := by
    have htop : (m : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hm0.ne')
    simpa only [one_div, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast] using
      ENNReal.toNNReal_mono htop
        (F.ddhIdealGame_cdhToDDHDistinguisher_true_le setup adversary n m hm)
  rw [← F.ddhRealGame_cdhToDDHDistinguisher]
  calc Game.succProbability (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
      ≤ Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
          (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) +
        Game.succProbability (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) := by
        simpa only [Game.advantage_pure_false] using
          Game.advantage_triangle
            (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
            (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n)
            (PMF.pure false)
    _ ≤ Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
          (F.ddhIdealGame setup (F.cdhToDDHDistinguisher adversary) n) + 1 / m := by
        gcongr

/-- The CDH-to-DDH reduction is uniform strict PPT when the CDH adversary is. -/
theorem isPPTOn_cdhToDDHDistinguisher
    {adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) encBits
      (fun input => adversary input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.cdhToDDHDistinguisher adversary input.1 input.2) := by
  unfold cdhToDDHDistinguisher
  refine (hA.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, (input.2.1, input.2.2.1, input.2.2.2.1))) (by fun_prop)).bind_with ?_
  have heq : ComputableTidilyInPolyTime
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × List Bool =>
        decide (p.2 = p.1.2.2.2.2))
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBits) encBool :=
    ComputableTidilyInPolyTime.decide_eq' (encB := encBits) (by fun_prop) (by fun_prop)
  exact ComputableTidilyInPolyTime.isPPTOn heq

/-- **DDH implies CDH** when every supported group at parameter `n` has order at least `m n > 0`
and `1 / m n` is negligible. -/
theorem DDH.cdh {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.CDH setup := by
  intro adversary hA
  exact negligible_of_le ((hDDH _ (F.isPPTOn_cdhToDDHDistinguisher hA)).add hinv)
    fun n => F.succProbability_cdhGame_le_advantage_ddh_add setup adversary n (m n) (hm0 n) (hm n)

/-- **DDH implies the discrete-logarithm assumption** when every supported group at parameter `n`
has order at least `m n > 0` and `1 / m n` is negligible. -/
theorem DDH.discreteLog {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.DiscreteLog setup :=
  (hDDH.cdh hm0 hm hinv).discreteLog

/-! ### Random self-reducibility of DDH -/

/-- Re-randomize a candidate DDH triple `(u, v, w)` in `F.Carrier d` using exponents
`r, s₁, s₂ : ZMod (F.order d)`. -/
def ddhRerandomize (d : F.Desc) (u v w : F.Carrier d)
    (r s₁ s₂ : ZMod (F.order d)) : F.Carrier d × F.Carrier d × F.Carrier d :=
  (r • u + s₁ • F.generator d,
    v + s₂ • F.generator d,
    r • w + (r * s₂) • u + s₁ • v + (s₁ * s₂) • F.generator d)

/-- Algebraic action of `ddhRerandomize` on multiples of the generator: a tuple error
`γ - α * β` is scaled by `r` and added to the new Diffie–Hellman product
`(r * α + s₁) * (β + s₂)`. -/
theorem ddhRerandomize_smul_generator (d : F.Desc) (α β γ r s₁ s₂ : ZMod (F.order d)) :
    F.ddhRerandomize d (α • F.generator d) (β • F.generator d) (γ • F.generator d) r s₁ s₂ =
      ((r * α + s₁) • F.generator d,
        (β + s₂) • F.generator d,
        ((r * α + s₁) * (β + s₂) + r * (γ - α * β)) • F.generator d) := by
  simp only [ddhRerandomize, smul_smul, ← add_smul]
  refine Prod.ext rfl (Prod.ext rfl (congrArg (· • F.generator d) (by ring)))

/-- The re-randomized triple distribution obtained by drawing `r, s₁, s₂ : ZMod (F.order d)`
independently and uniformly. -/
noncomputable def ddhRerandomizeLaw (d : F.Desc) (u v w : F.Carrier d) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let r ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  return F.ddhRerandomize d u v w r s₁ s₂

/-- The real DDH tuple distribution on `F.Carrier d`. -/
noncomputable def ddhRealTupleLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α • F.generator d, β • F.generator d, (α * β) • F.generator d)

/-- The ideal DDH tuple distribution on `F.Carrier d`. -/
noncomputable def ddhIdealTupleLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α • F.generator d, β • F.generator d, γ • F.generator d)

private theorem uniformOfFintype_bind_equiv {α β : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (f : α → PMF β) :
    (PMF.uniformOfFintype α).bind (fun a => f (e a)) = (PMF.uniformOfFintype α).bind f := by
  change (PMF.uniformOfFintype α).bind (f ∘ e) = (PMF.uniformOfFintype α).bind f
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- **Random self-reducibility of DDH (real case)**: re-randomizing any fixed real DDH tuple
`(α • g, β • g, (α * β) • g)` yields the exact uniform real DDH tuple distribution. -/
theorem ddhRerandomizeLaw_real (d : F.Desc) (α β : ZMod (F.order d)) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) ((α * β) • F.generator d) =
      F.ddhRealTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhRealTupleLaw, ddhRerandomize_smul_generator, sub_self, mul_zero,
    add_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d)) :=
    uniformOfFintype_bind_equiv (Equiv.addLeft β)
      (fun β' => PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  have hs₁ (r : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
          PMF.pure ((r * α + s₁) • F.generator d, (β + s₂) • F.generator d,
            ((r * α + s₁) * (β + s₂)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α' =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
          PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d)) := by
    simp_rw [hs₂]
    exact uniformOfFintype_bind_equiv (Equiv.addLeft (r * α))
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  simp_rw [hs₁, PMF.bind_const]

/-- **Random self-reducibility of DDH (ideal case)**: re-randomizing any fixed non-DDH tuple
`(α • g, β • g, γ • g)` with `γ ≠ α * β` yields the exact uniform ideal DDH tuple distribution. -/
theorem ddhRerandomizeLaw_ideal (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhIdealTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhIdealTupleLaw, ddhRerandomize_smul_generator,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (r α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d)) :=
    uniformOfFintype_bind_equiv (Equiv.addLeft β)
      (fun β' => PMF.pure (α' • F.generator d, β' • F.generator d,
        (α' * β' + r * (γ - α * β)) • F.generator d))
  have hs₁ (r : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
          PMF.pure ((r * α + s₁) • F.generator d, (β + s₂) • F.generator d,
            ((r * α + s₁) * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α' =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
          PMF.pure (α' • F.generator d, β' • F.generator d,
            (α' * β' + r * (γ - α * β)) • F.generator d)) := by
    simp_rw [hs₂]
    exact uniformOfFintype_bind_equiv (Equiv.addLeft (r * α))
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d))
  simp_rw [hs₁]
  rw [PMF.bind_comm]
  congr 1; funext α'
  rw [PMF.bind_comm]
  congr 1; funext β'
  exact uniformOfFintype_bind_equiv
    ((Equiv.mulRight₀ (γ - α * β) (sub_ne_zero.mpr hγ)).trans (Equiv.addLeft (α' * β')))
    (fun γ' => PMF.pure (α' • F.generator d, β' • F.generator d, γ' • F.generator d))

/-! ### Efficient word-level DDH random self-reduction -/

/-- Word-level DDH tuple re-randomization ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426):
given `(d, (u, v, w), r, s₁, s₂)` on encoded group elements `u, v, w : List Bool` and
natural-number exponents `r, s₁, s₂ : ℕ`, evaluate the encoded tuple corresponding to
`ddhRerandomize`. -/
def encodeDDHRerandomize
    (input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ) :
    List Bool × List Bool × List Bool :=
  let d := input.1
  let u := input.2.1.1
  let v := input.2.1.2.1
  let w := input.2.1.2.2
  let r := input.2.2.1
  let s₁ := input.2.2.2.1
  let s₂ := input.2.2.2.2
  let g := F.encode d (F.generator d)
  (F.add (d, F.smul (d, r, u), F.smul (d, s₁, g)),
    F.add (d, v, F.smul (d, s₂, g)),
    F.add (d,
      F.add (d,
        F.add (d, F.smul (d, r, w), F.smul (d, r * s₂, u)),
        F.smul (d, s₁, v)),
      F.smul (d, s₁ * s₂, g)))

/-- `encodeDDHRerandomize` evaluates `ddhRerandomize` on encoded group elements. -/
@[simp] theorem encodeDDHRerandomize_encode (d : F.Desc) (u v w : F.Carrier d) (r s₁ s₂ : ℕ) :
    F.encodeDDHRerandomize (d, (F.encode d u, F.encode d v, F.encode d w), r, s₁, s₂) =
      let t := F.ddhRerandomize d u v w
        (r : ZMod (F.order d)) (s₁ : ZMod (F.order d)) (s₂ : ZMod (F.order d))
      (F.encode d t.1, F.encode d t.2.1, F.encode d t.2.2) := by
  simp only [encodeDDHRerandomize, ddhRerandomize, F.smul_encode, F.add_encode, Nat.cast_mul]

/-- Evaluating `encodeDDHRerandomize` at `.val` of exponents in `ZMod (F.order d)` agrees with
`ddhRerandomize`. -/
theorem encodeDDHRerandomize_val (d : F.Desc) (u v w : F.Carrier d)
    (r s₁ s₂ : ZMod (F.order d)) :
    F.encodeDDHRerandomize (d, (F.encode d u, F.encode d v, F.encode d w), r.val, s₁.val, s₂.val) =
      let t := F.ddhRerandomize d u v w r s₁ s₂
      (F.encode d t.1, F.encode d t.2.1, F.encode d t.2.2) := by
  simp only [encodeDDHRerandomize_encode, ZMod.natCast_zmod_val]

/-- Word-level DDH tuple re-randomization is computable in polynomial time. -/
theorem computableInPolyTime_encodeDDHRerandomize :
    ComputableInPolyTime F.encodeDDHRerandomize
      (encPair F.encDesc
        (encPair (encPair encBits (encPair encBits encBits))
          (encPair encNat (encPair encNat encNat))))
      (encPair encBits (encPair encBits encBits)) := by
  let encIn := encPair F.encDesc
    (encPair (encPair encBits (encPair encBits encBits))
      (encPair encNat (encPair encNat encNat)))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.1)
      encIn F.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.2.1.1)
      encIn encBits := by fun_prop
  have hv : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.2.1.2.1)
      encIn encBits := by fun_prop
  have hw : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.2.1.2.2)
      encIn encBits := by fun_prop
  have hr : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.2.2.1)
      encIn encNat := by fun_prop
  have hs₁ : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.2.2.2.1)
      encIn encNat := by fun_prop
  have hs₂ : ComputableInPolyTime
      (fun input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ => input.2.2.2.2)
      encIn encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  have hru := F.computableInPolyTime_smul.comp (hd.prod (hr.prod hu))
  have hs₁g := F.computableInPolyTime_smul.comp (hd.prod (hs₁.prod hg))
  have hs₂g := F.computableInPolyTime_smul.comp (hd.prod (hs₂.prod hg))
  have hrw := F.computableInPolyTime_smul.comp (hd.prod (hr.prod hw))
  have hrs₂u := F.computableInPolyTime_smul.comp (hd.prod ((hr.binary_mul' hs₂).prod hu))
  have hs₁v := F.computableInPolyTime_smul.comp (hd.prod (hs₁.prod hv))
  have hs₁s₂g := F.computableInPolyTime_smul.comp (hd.prod ((hs₁.binary_mul' hs₂).prod hg))
  have hc₁ := F.computableInPolyTime_add.comp (hd.prod (hru.prod hs₁g))
  have hc₂ := F.computableInPolyTime_add.comp (hd.prod (hv.prod hs₂g))
  have hc₃₁ := F.computableInPolyTime_add.comp (hd.prod (hrw.prod hrs₂u))
  have hc₃₂ := F.computableInPolyTime_add.comp (hd.prod (hc₃₁.prod hs₁v))
  have hc₃ := F.computableInPolyTime_add.comp (hd.prod (hc₃₂.prod hs₁s₂g))
  exact hc₁.prod (hc₂.prod hc₃)

/-- Sample one approximate uniform exponent modulo `F.order d` using `n + |encNat (F.order d)|`
fair coins via `ProbComp.sampleModNat`, within statistical distance `1 / 2 ^ n` of exact uniform on
`ZMod (F.order d)`. -/
noncomputable def sampleExp (n : ℕ) (d : F.Desc) : ProbComp ℕ :=
  ProbComp.sampleModNat (n + (encNat (F.order d)).length) (F.order d)

/-- `sampleExp` is uniform strict PPT whenever `n` and `d` are computable in polynomial time. -/
theorem isPPTOn_sampleExp {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn encNat (fun a => F.sampleExp (n a) (d a)) := by
  have hord : ComputableInPolyTime (fun a => F.order (d a)) encIn encNat :=
    F.computableInPolyTime_order.comp hd
  have hlen : ComputableInPolyTime
      (fun a => (encNat (F.order (d a))).length) encIn encUnary :=
    (ComputableInPolyTime.encoding_length encNat).comp hord
  have hadd : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hwidth : ComputableInPolyTime
      (fun a => n a + (encNat (F.order (d a))).length) encIn encUnary :=
    hadd.comp (hn.prod hlen)
  exact isPPTOn_sampleModNat hwidth hord

/-- Replacing one `sampleExp n d` draw by an exact uniform draw on `ZMod (F.order d)`
changes `Game.advantage` by at most `1 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun s => k (s : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind k) ≤
      1 / 2 ^ n := by
  have hmap :
      ((ProbComp.eval (F.sampleExp n d)).bind fun s => k (s : ZMod (F.order d))) =
        ((ProbComp.eval (F.sampleExp n d)).map
          (Nat.cast : ℕ → ZMod (F.order d))).bind k :=
    (PMF.bind_map _ _ _).symm
  have hlt : F.order d < 2 ^ (encNat (F.order d)).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.lt_size_self (F.order d)
  have hord_le : (F.order d : ℝ) ≤ 2 ^ (encNat (F.order d)).length := by
    exact_mod_cast hlt.le
  rw [← NNReal.coe_le_coe, hmap, Game.advantage_eq_nndist, coe_nndist]
  refine (PMF.dist_bind_le _ _ k).trans ?_
  refine (ProbComp.dist_map_natCast_eval_sampleModNat_le
    (n + (encNat (F.order d)).length) (F.order d)).trans ?_
  rw [Nat.add_comm n, pow_add, ← div_div]
  have hdiv : (F.order d : ℝ) / 2 ^ (encNat (F.order d)).length ≤ 1 :=
    (div_le_one (by positivity)).mpr hord_le
  have hbound :
      (F.order d : ℝ) / 2 ^ (encNat (F.order d)).length / 2 ^ n ≤ 1 / 2 ^ n :=
    div_le_div_of_nonneg_right hdiv (by positivity)
  simpa using hbound

/-- Sample three independent nearly-uniform exponents modulo `F.order d` at statistical distance
at most `1 / 2 ^ n` each using `ProbComp.sampleModNat ((F.order d).size + n) (F.order d)`
(original). -/
noncomputable def ddhSampleModExponents (n : ℕ) (d : F.Desc) : ProbComp (ℕ × ℕ × ℕ) := do
  let r ← ProbComp.sampleModNat ((F.order d).size + n) (F.order d)
  let s₁ ← ProbComp.sampleModNat ((F.order d).size + n) (F.order d)
  let s₂ ← ProbComp.sampleModNat ((F.order d).size + n) (F.order d)
  return (r, s₁, s₂)

/-- `ddhSampleModExponents` is uniform strict PPT (original). -/
theorem isPPTOn_ddhSampleModExponents :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encNat (encPair encNat encNat))
      (fun input => F.ddhSampleModExponents input.1 input.2) := by
  let encIn := encPair encUnary F.encDesc
  have hn : ComputableInPolyTime (fun input : ℕ × F.Desc => input.1) encIn encUnary := by
    fun_prop
  have hd : ComputableInPolyTime (fun input : ℕ × F.Desc => input.2) encIn F.encDesc := by
    fun_prop
  have horder : ComputableInPolyTime (fun input : ℕ × F.Desc => F.order input.2) encIn encNat :=
    F.computableInPolyTime_order.comp hd
  have hsize : ComputableInPolyTime
      (fun input : ℕ × F.Desc => (F.order input.2).size) encIn encUnary :=
    ComputableInPolyTime.binary_size.comp horder
  have hsize_tidy := hsize.tidy
  have hn_tidy := hn.tidy
  have hbits : ComputableInPolyTime
      (fun input : ℕ × F.Desc => (F.order input.2).size + input.1) encIn encUnary :=
    ComputableInPolyTime.of_tidy (by fun_prop)
  have hsample : IsPPTOn encIn encNat
      (fun input : ℕ × F.Desc =>
        ProbComp.sampleModNat ((F.order input.2).size + input.1) (F.order input.2)) :=
    isPPTOn_sampleModNat hbits horder
  unfold ddhSampleModExponents
  refine hsample.bind_with ?_
  refine (hsample.preprocess (prepare := Prod.fst) (by fun_prop)).bind_with ?_
  refine (hsample.preprocess
    (prepare := fun p : ((ℕ × F.Desc) × ℕ) × ℕ => p.1.1) (by fun_prop)).bind_with ?_
  exact ComputableInPolyTime.isPPTOn (by fun_prop)

/-- Distribution of a single modular exponent sampled via `ProbComp.sampleModNat` at parameter `n`
and group description `d`, projected to `ZMod (F.order d)` (original). -/
noncomputable def sampleModZModLaw (n : ℕ) (d : F.Desc) : PMF (ZMod (F.order d)) :=
  (ProbComp.eval (ProbComp.sampleModNat ((F.order d).size + n) (F.order d))).map Nat.cast

/-- Each modular exponent sampled by `ProbComp.sampleModNat ((F.order d).size + n) (F.order d)`
is within statistical distance `1 / 2 ^ n` of `PMF.uniformOfFintype (ZMod (F.order d))`
(original). -/
theorem dist_sampleModZModLaw_le (n : ℕ) (d : F.Desc) :
    dist (PMF.uniformOfFintype (ZMod (F.order d))) (F.sampleModZModLaw n d) ≤ 1 / 2 ^ n := by
  have : NeZero (F.order d) := ⟨(F.prime_order d).ne_zero⟩
  rw [dist_comm]
  refine (ProbComp.dist_map_natCast_eval_sampleModNat_le
    ((F.order d).size + n) (F.order d)).trans ?_
  have hlt : (F.order d : ℝ) ≤ 2 ^ (F.order d).size := by
    exact_mod_cast (Nat.lt_size_self (F.order d)).le
  have hpos : (0 : ℝ) < 2 ^ (F.order d).size := by positivity
  calc
    (F.order d : ℝ) / 2 ^ ((F.order d).size + n)
      ≤ 2 ^ (F.order d).size / (2 ^ (F.order d).size * 2 ^ n) := by
        rw [pow_add]
        gcongr
    _ = 1 / 2 ^ n := by
        rw [div_mul_eq_div_div, div_self hpos.ne']

/-- The single-invocation DDH random self-reduction distinguisher (original): given a DDH
distinguisher `distinguisher`, re-randomize an input tuple `(d, u, v, w)` by sampling
`(r, s₁, s₂) ← F.ddhSampleModExponents n d`, computing
`(u', v', w') = F.encodeDDHRerandomize (d, (u, v, w), r, s₁, s₂)`, and running `distinguisher` on
`(d, u', v', w')`. -/
noncomputable def ddhSelfReduceDistinguisher
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let exps ← F.ddhSampleModExponents n input.1
  distinguisher n (input.1, F.encodeDDHRerandomize (input.1, input.2, exps))

/-- `ddhSelfReduceDistinguisher` is uniform strict PPT whenever `distinguisher` is (original). -/
theorem isPPTOn_ddhSelfReduceDistinguisher
    {distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool}
    (hD : IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => distinguisher input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.ddhSelfReduceDistinguisher distinguisher input.1 input.2) := by
  have hsample := F.isPPTOn_ddhSampleModExponents
  have hrerand := F.computableInPolyTime_encodeDDHRerandomize
  unfold ddhSelfReduceDistinguisher
  refine (hsample.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, input.2.1)) (by fun_prop)).bind_with ?_
  exact hD.preprocess
    (prepare := fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ =>
      (p.1.1, p.1.2.1, F.encodeDDHRerandomize (p.1.2.1, p.1.2.2, p.2)))
    (by fun_prop)

/-- Game-level DDH tuple re-randomization experiment ([BonehShoup2023], Exercises 10.8–10.9,
pp. 425–426): draw `d ← setup n` and independent uniform `r, s₁, s₂ : ZMod (F.order d)`,
re-randomize the encoded tuple `tuple d` using `encodeDDHRerandomize`, and run `distinguisher`. -/
noncomputable def ddhRerandomizeGame (setup : ℕ → PMF F.Desc)
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let r ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encodeDDHRerandomize
      (d, (F.encode d (tuple d).1, F.encode d (tuple d).2.1, F.encode d (tuple d).2.2),
        r.val, s₁.val, s₂.val)))

/-- Re-randomizing any family of real DDH tuples `(α d • g, β d • g, (α d * β d) • g)` with
`encodeDDHRerandomize` produces the exact average-case `ddhRealGame`
([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426). -/
@[simp] theorem ddhRerandomizeGame_real (setup : ℕ → PMF F.Desc)
    (α β : ∀ d : F.Desc, ZMod (F.order d))
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    F.ddhRerandomizeGame setup
      (fun d => (α d • F.generator d, β d • F.generator d, (α d * β d) • F.generator d))
      distinguisher n = F.ddhRealGame setup distinguisher n := by
  simp only [ddhRerandomizeGame, ddhRealGame, encodeDDHRerandomize_val, PMF.monad_bind_eq_bind]
  congr 1; funext d
  have hlaw := congrArg
    (fun p : PMF (F.Carrier d × F.Carrier d × F.Carrier d) =>
      p.bind fun t =>
        ProbComp.eval (distinguisher n (d, F.encode d t.1, F.encode d t.2.1, F.encode d t.2.2)))
    (F.ddhRerandomizeLaw_real d (α d) (β d))
  simpa only [ddhRerandomizeLaw, ddhRealTupleLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind] using hlaw

/-- Re-randomizing any family of non-DDH tuples `(α d • g, β d • g, γ d • g)` with
`γ d ≠ α d * β d` on the support of `setup n` using `encodeDDHRerandomize` produces the exact
average-case `ddhIdealGame` ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426). -/
theorem ddhRerandomizeGame_ideal (setup : ℕ → PMF F.Desc)
    (α β γ : ∀ d : F.Desc, ZMod (F.order d))
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hγ : ∀ d ∈ (setup n).support, γ d ≠ α d * β d) :
    F.ddhRerandomizeGame setup
      (fun d => (α d • F.generator d, β d • F.generator d, γ d • F.generator d))
      distinguisher n = F.ddhIdealGame setup distinguisher n := by
  simp only [ddhRerandomizeGame, ddhIdealGame, encodeDDHRerandomize_val, PMF.monad_bind_eq_bind]
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun d => ?_
  by_cases hd : d ∈ (setup n).support
  · congr 1
    have hlaw := congrArg
      (fun p : PMF (F.Carrier d × F.Carrier d × F.Carrier d) =>
        (p.bind fun t =>
          ProbComp.eval
            (distinguisher n (d, F.encode d t.1, F.encode d t.2.1, F.encode d t.2.2))) b)
      (F.ddhRerandomizeLaw_ideal d (hγ d hd))
    simpa only [ddhRerandomizeLaw, ddhIdealTupleLaw, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind] using hlaw
  · have hd0 : setup n d = 0 := by rwa [PMF.mem_support_iff, not_not] at hd
    simp only [hd0, zero_mul]

/-- **DDH rerandomization advantage identity** ([BonehShoup2023], Exercises 10.8–10.9,
pp. 425–426): for any real DDH tuple family `(α d, β d)` and any non-DDH tuple family
`(α' d, β' d, γ' d)` with `γ' d ≠ α' d * β' d` on the support of `setup n`, the distinguishing
advantage after `encodeDDHRerandomize` equals the average-case DDH advantage. -/
theorem advantage_ddhRerandomizeGame_eq (setup : ℕ → PMF F.Desc)
    (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d))
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hγ' : ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d) :
    Game.advantage
      (F.ddhRerandomizeGame setup
        (fun d => (α d • F.generator d, β d • F.generator d, (α d * β d) • F.generator d))
        distinguisher n)
      (F.ddhRerandomizeGame setup
        (fun d => (α' d • F.generator d, β' d • F.generator d, γ' d • F.generator d))
        distinguisher n) =
      Game.advantage (F.ddhRealGame setup distinguisher n)
        (F.ddhIdealGame setup distinguisher n) := by
  rw [F.ddhRerandomizeGame_real, F.ddhRerandomizeGame_ideal setup α' β' γ' distinguisher n hγ']

/-- **DDH rerandomization indistinguishability** ([BonehShoup2023], Exercises 10.8–10.9,
pp. 425–426): under the average-case `DDH` assumption, no uniform strict PPT distinguisher can
distinguish the exact re-randomization of any real DDH tuple family from the exact re-randomization
of any non-DDH tuple family. -/
theorem DDH.ddhRerandomizeGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d))
    (hγ' : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d) :
    Game.Indistinguishable
      (F.ddhRerandomizeGame setup
        (fun d => (α d • F.generator d, β d • F.generator d, (α d * β d) • F.generator d)))
      (F.ddhRerandomizeGame setup
        (fun d => (α' d • F.generator d, β' d • F.generator d, γ' d • F.generator d)))
      fun distinguisher =>
        IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
          encBool (fun input => distinguisher input.1 input.2) := by
  intro distinguisher hD
  refine negligible_of_eventually_le (hDDH distinguisher hD) (hγ'.mono fun n hn => ?_)
  exact (F.advantage_ddhRerandomizeGame_eq setup α β α' β' γ' distinguisher n hn).le

/-- The worst-case DDH experiment on a fixed tuple family `tuple` (original): draw `d ← setup n`
and give the encoded tuple `(d, encode (tuple d).1, encode (tuple d).2.1, encode (tuple d).2.2)`
directly to `distinguisher`. -/
noncomputable def ddhWorstCaseGame (setup : ℕ → PMF F.Desc)
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  ProbComp.eval (distinguisher n
    (d, F.encode d (tuple d).1, F.encode d (tuple d).2.1, F.encode d (tuple d).2.2))

private noncomputable def ddhRerandomizeStep
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) (d : F.Desc) (r s₁ s₂ : ZMod (F.order d)) : Game :=
  let t := F.ddhRerandomize d (tuple d).1 (tuple d).2.1 (tuple d).2.2 r s₁ s₂
  ProbComp.eval (distinguisher n (d, F.encode d t.1, F.encode d t.2.1, F.encode d t.2.2))

private theorem ddhRerandomizeGame_eq_bind_step (setup : ℕ → PMF F.Desc)
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    F.ddhRerandomizeGame setup tuple distinguisher n =
      (setup n).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun r =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
              F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂ := by
  simp only [ddhRerandomizeGame, ddhRerandomizeStep, encodeDDHRerandomize_val,
    PMF.monad_bind_eq_bind]

private theorem ddhWorstCaseGame_ddhSelfReduceDistinguisher_eq_bind_step (setup : ℕ → PMF F.Desc)
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    F.ddhWorstCaseGame setup tuple (F.ddhSelfReduceDistinguisher distinguisher) n =
      (setup n).bind fun d =>
        (F.sampleModZModLaw n d).bind fun r =>
          (F.sampleModZModLaw n d).bind fun s₁ =>
            (F.sampleModZModLaw n d).bind fun s₂ =>
              F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂ := by
  simp only [ddhWorstCaseGame, ddhSelfReduceDistinguisher, ddhSampleModExponents, sampleModZModLaw,
    ddhRerandomizeStep, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def, encodeDDHRerandomize_encode]

/-- Combining `PMF.dist_bind_le` (different first-stage distributions on a finite type) with
`Game.advantage_bind_le` (different kernels) bounds the Boolean advantage of two bound games by
the first-stage statistical distance plus a uniform kernel advantage bound. -/
private theorem advantage_bind_le_dist_add {α : Type*} [Fintype α] (p q : PMF α)
    (f g : α → Game) {ε δ : ℝ} (hpq : dist p q ≤ ε)
    (hfg : ∀ a, (Game.advantage (f a) (g a) : ℝ) ≤ δ) :
    (Game.advantage (p.bind f) (q.bind g) : ℝ) ≤ ε + δ := by
  have htri : (Game.advantage (p.bind f) (q.bind g) : ℝ) ≤
      (Game.advantage (p.bind f) (q.bind f) : ℝ) +
      (Game.advantage (q.bind f) (q.bind g) : ℝ) := by
    exact_mod_cast Game.advantage_triangle (p.bind f) (q.bind f) (q.bind g)
  have h1 : (Game.advantage (p.bind f) (q.bind f) : ℝ) ≤ ε := by
    rw [Game.advantage_eq_nndist, coe_nndist]
    exact (PMF.dist_bind_le p q f).trans hpq
  have h2 : (Game.advantage (q.bind f) (q.bind g) : ℝ) ≤ δ :=
    Game.advantage_bind_le q f g hfg
  exact htri.trans (add_le_add h1 h2)

/-- **Statistical distance bound for `ddhSelfReduceDistinguisher`** (original): replacing the three
exact uniform `ZMod (F.order d)` exponents in `ddhRerandomizeGame` with
`ddhSampleModExponents n d` changes the game output distribution by at most `3 / 2 ^ n`. -/
theorem advantage_ddhRerandomizeGame_ddhWorstCaseGame_le (setup : ℕ → PMF F.Desc)
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    Game.advantage (F.ddhRerandomizeGame setup tuple distinguisher n)
      (F.ddhWorstCaseGame setup tuple (F.ddhSelfReduceDistinguisher distinguisher) n) ≤
      3 / 2 ^ n := by
  apply NNReal.coe_le_coe.mp
  rw [F.ddhRerandomizeGame_eq_bind_step, F.ddhWorstCaseGame_ddhSelfReduceDistinguisher_eq_bind_step]
  have hd (d : F.Desc) :
      (Game.advantage
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun r =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
              F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂)
        ((F.sampleModZModLaw n d).bind fun r =>
          (F.sampleModZModLaw n d).bind fun s₁ =>
            (F.sampleModZModLaw n d).bind fun s₂ =>
              F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂) : ℝ) ≤
        (3 / 2 ^ n : ℝ) := by
    have hstep := F.dist_sampleModZModLaw_le n d
    have hs₂ (r s₁ : ZMod (F.order d)) :
        (Game.advantage
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
            F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂)
          ((F.sampleModZModLaw n d).bind fun s₂ =>
            F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂) : ℝ) ≤
          1 / 2 ^ n + 0 :=
      advantage_bind_le_dist_add _ _ _ _ hstep fun s₂ => by
        simp only [Game.advantage_self, NNReal.coe_zero, le_rfl]
    have hs₁ (r : ZMod (F.order d)) :
        (Game.advantage
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
              F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂)
          ((F.sampleModZModLaw n d).bind fun s₁ =>
            (F.sampleModZModLaw n d).bind fun s₂ =>
              F.ddhRerandomizeStep tuple distinguisher n d r s₁ s₂) : ℝ) ≤
          1 / 2 ^ n + (1 / 2 ^ n + 0) :=
      advantage_bind_le_dist_add _ _ _ _ hstep fun s₁ => hs₂ r s₁
    have hr := advantage_bind_le_dist_add _ _ _ _ hstep hs₁
    exact hr.trans_eq (by ring)
  have hsetup := Game.advantage_bind_le (setup n) _ _ hd
  simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow] using hsetup

/-- **Quantitative single-invocation worst-case-to-average-case DDH reduction** (original): the
average-case DDH advantage of `distinguisher` is at most the worst-case DDH advantage of
`ddhSelfReduceDistinguisher distinguisher` plus `6 / 2 ^ n`. -/
theorem advantage_ddhRealGame_le_ddhWorstCaseGame (setup : ℕ → PMF F.Desc)
    (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d))
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hγ' : ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d) :
    let tuple₀ := fun d => (α d • F.generator d, β d • F.generator d, (α d * β d) • F.generator d)
    let tuple₁ := fun d => (α' d • F.generator d, β' d • F.generator d, γ' d • F.generator d)
    Game.advantage (F.ddhRealGame setup distinguisher n)
      (F.ddhIdealGame setup distinguisher n) ≤
      Game.advantage
        (F.ddhWorstCaseGame setup tuple₀
          (F.ddhSelfReduceDistinguisher distinguisher) n)
        (F.ddhWorstCaseGame setup tuple₁
          (F.ddhSelfReduceDistinguisher distinguisher) n) +
      6 / 2 ^ n := by
  intro tuple₀ tuple₁
  rw [← F.advantage_ddhRerandomizeGame_eq setup α β α' β' γ' distinguisher n hγ']
  have h1 := Game.advantage_triangle
    (F.ddhRerandomizeGame setup tuple₀ distinguisher n)
    (F.ddhWorstCaseGame setup tuple₀ (F.ddhSelfReduceDistinguisher distinguisher) n)
    (F.ddhRerandomizeGame setup tuple₁ distinguisher n)
  have h2 := Game.advantage_triangle
    (F.ddhWorstCaseGame setup tuple₀ (F.ddhSelfReduceDistinguisher distinguisher) n)
    (F.ddhWorstCaseGame setup tuple₁ (F.ddhSelfReduceDistinguisher distinguisher) n)
    (F.ddhRerandomizeGame setup tuple₁ distinguisher n)
  have h0 := F.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le setup tuple₀ distinguisher n
  have h3 :
      Game.advantage
        (F.ddhWorstCaseGame setup tuple₁ (F.ddhSelfReduceDistinguisher distinguisher) n)
        (F.ddhRerandomizeGame setup tuple₁ distinguisher n) ≤ 3 / 2 ^ n := by
    rw [Game.advantage_comm]
    exact F.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le setup tuple₁ distinguisher n
  calc
    Game.advantage (F.ddhRerandomizeGame setup tuple₀ distinguisher n)
        (F.ddhRerandomizeGame setup tuple₁ distinguisher n)
      ≤ Game.advantage (F.ddhRerandomizeGame setup tuple₀ distinguisher n)
          (F.ddhWorstCaseGame setup tuple₀ (F.ddhSelfReduceDistinguisher distinguisher) n) +
        (Game.advantage
          (F.ddhWorstCaseGame setup tuple₀ (F.ddhSelfReduceDistinguisher distinguisher) n)
          (F.ddhWorstCaseGame setup tuple₁ (F.ddhSelfReduceDistinguisher distinguisher) n) +
        Game.advantage
          (F.ddhWorstCaseGame setup tuple₁ (F.ddhSelfReduceDistinguisher distinguisher) n)
          (F.ddhRerandomizeGame setup tuple₁ distinguisher n)) :=
      h1.trans (add_le_add le_rfl h2)
    _ ≤ 3 / 2 ^ n +
        (Game.advantage
          (F.ddhWorstCaseGame setup tuple₀ (F.ddhSelfReduceDistinguisher distinguisher) n)
          (F.ddhWorstCaseGame setup tuple₁ (F.ddhSelfReduceDistinguisher distinguisher) n) +
        3 / 2 ^ n) :=
      add_le_add h0 (add_le_add le_rfl h3)
    _ = Game.advantage
          (F.ddhWorstCaseGame setup tuple₀ (F.ddhSelfReduceDistinguisher distinguisher) n)
          (F.ddhWorstCaseGame setup tuple₁ (F.ddhSelfReduceDistinguisher distinguisher) n) +
        6 / 2 ^ n := by
      ring

/-- **Average-case DDH from worst-case DDH via `ddhSelfReduceDistinguisher`** (original): if a
worst-case real DDH tuple family is indistinguishable from a worst-case non-DDH tuple family for
all uniform strict PPT distinguishers, then `F.DDH setup` holds. -/
theorem ddh_of_worstCase {setup : ℕ → PMF F.Desc}
    (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d))
    (hγ' : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d)
    (hworst : Game.Indistinguishable
      (F.ddhWorstCaseGame setup
        (fun d => (α d • F.generator d, β d • F.generator d, (α d * β d) • F.generator d)))
      (F.ddhWorstCaseGame setup
        (fun d => (α' d • F.generator d, β' d • F.generator d, γ' d • F.generator d)))
      fun distinguisher =>
        IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
          encBool (fun input => distinguisher input.1 input.2)) :
    F.DDH setup := by
  intro distinguisher hD
  have hgeom : Negligible fun n => (6 / 2 ^ n : ℝ≥0) := by
    refine negligible_of_le
      ((negligible_geometric (ratio := 2⁻¹) (by norm_num)).polynomiallyBounded_mul
        (p := fun _ => 6) (by fun_prop))
      fun n => ?_
    exact le_of_eq (by simp only [Nat.cast_ofNat, div_eq_mul_inv, inv_pow])
  refine negligible_of_eventually_le
    ((hworst (F.ddhSelfReduceDistinguisher distinguisher)
      (F.isPPTOn_ddhSelfReduceDistinguisher hD)).add hgeom)
    (hγ'.mono fun n hn =>
      F.advantage_ddhRealGame_le_ddhWorstCaseGame setup α β α' β' γ' distinguisher n hn)

/-! ### Worst-case DDH decider via Chernoff amplification ([BonehShoup2023], Exercise 10.10) -/

/-- Canonical encoded real DDH tuple `(0 • g, 0 • g, (0 * 0) • g)` for group description `d`,
computed in polynomial time via `F.smul (d, 0, F.encode d (F.generator d))`
([BonehShoup2023], Section 10.11, Exercise 10.10, p. 426). -/
def ddhRealRefTuple (d : F.Desc) : List Bool × List Bool × List Bool :=
  let g := F.encode d (F.generator d)
  let z := F.smul (d, 0, g)
  (z, z, z)

/-- Canonical encoded non-DDH tuple `(0 • g, 0 • g, 1 • g)` for group description `d`
(since `1 ≠ 0 * 0` in `ZMod (F.order d)` for prime `F.order d`;
[BonehShoup2023], Section 10.11, Exercise 10.10, p. 426). -/
def ddhIdealRefTuple (d : F.Desc) : List Bool × List Bool × List Bool :=
  let g := F.encode d (F.generator d)
  let z := F.smul (d, 0, g)
  (z, z, g)

/-- `ddhRealRefTuple` equals the encoded tuple `((0 : ZMod q) • g, (0 : ZMod q) • g,
((0 : ZMod q) * 0) • g)`. -/
@[simp] theorem ddhRealRefTuple_eq_encode (d : F.Desc) :
    F.ddhRealRefTuple d =
      (F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d (((0 : ZMod (F.order d)) * 0) • F.generator d)) := by
  simp [ddhRealRefTuple, F.smul_encode]

/-- `ddhIdealRefTuple` equals the encoded tuple `((0 : ZMod q) • g, (0 : ZMod q) • g,
(1 : ZMod q) • g)`. -/
@[simp] theorem ddhIdealRefTuple_eq_encode (d : F.Desc) :
    F.ddhIdealRefTuple d =
      (F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d ((1 : ZMod (F.order d)) • F.generator d)) := by
  simp [ddhIdealRefTuple, F.smul_encode]

/-- `ddhRealRefTuple` is computable in polynomial time. -/
theorem computableInPolyTime_ddhRealRefTuple :
    ComputableInPolyTime F.ddhRealRefTuple F.encDesc
      (encPair encBits (encPair encBits encBits)) := by
  have hg := F.computableInPolyTime_generator
  have hzero : ComputableInPolyTime (fun _ : F.Desc => (0 : ℕ)) F.encDesc encNat := by fun_prop
  have hz := F.computableInPolyTime_smul.comp
    (ComputableInPolyTime.id'.prod (hzero.prod hg))
  exact hz.prod (hz.prod hz)

/-- `ddhIdealRefTuple` is computable in polynomial time. -/
theorem computableInPolyTime_ddhIdealRefTuple :
    ComputableInPolyTime F.ddhIdealRefTuple F.encDesc
      (encPair encBits (encPair encBits encBits)) := by
  have hg := F.computableInPolyTime_generator
  have hzero : ComputableInPolyTime (fun _ : F.Desc => (0 : ℕ)) F.encDesc encNat := by fun_prop
  have hz := F.computableInPolyTime_smul.comp
    (ComputableInPolyTime.id'.prod (hzero.prod hg))
  exact hz.prod (hz.prod hg)

/-- On a deterministic group setup `fun _ => PMF.pure d`, `ddhWorstCaseGame` evaluates
`distinguisher` directly on `(d, encode (tuple d))`. -/
@[simp] theorem ddhWorstCaseGame_pure (d : F.Desc)
    (tuple : ∀ d : F.Desc, F.Carrier d × F.Carrier d × F.Carrier d)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    F.ddhWorstCaseGame (fun _ => PMF.pure d) tuple distinguisher n =
      ProbComp.eval (distinguisher n
        (d, F.encode d (tuple d).1, F.encode d (tuple d).2.1, F.encode d (tuple d).2.2)) := by
  simp [ddhWorstCaseGame]

/-- **Single-trial real DDH proximity**: on any fixed group `d` and any real DDH triple
`(α • g, β • g, (α * β) • g)`, the acceptance probability of `ddhSelfReduceDistinguisher` differs
from the average-case `ddhRealGame (fun _ => PMF.pure d)` acceptance probability by at most
`3 / 2 ^ n`. -/
theorem advantage_ddhRealGame_pure_ddhSelfReduceDistinguisher_le (d : F.Desc)
    (α β : ZMod (F.order d))
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    Game.advantage (F.ddhRealGame (fun _ => PMF.pure d) distinguisher n)
      (ProbComp.eval (F.ddhSelfReduceDistinguisher distinguisher n
        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
          F.encode d ((α * β) • F.generator d)))) ≤ 3 / 2 ^ n := by
  have h := F.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le (fun _ => PMF.pure d)
    (fun d' => ((α.val : ZMod (F.order d')) • F.generator d',
      (β.val : ZMod (F.order d')) • F.generator d',
      ((α.val : ZMod (F.order d')) * (β.val : ZMod (F.order d'))) • F.generator d'))
    distinguisher n
  simpa only [ddhRerandomizeGame_real, ddhWorstCaseGame_pure, ZMod.natCast_zmod_val] using h

/-- **Single-trial non-DDH proximity**: on any fixed group `d` and any non-DDH triple
`(α • g, β • g, γ • g)` with `γ ≠ α * β`, the acceptance probability of
`ddhSelfReduceDistinguisher` differs from the average-case `ddhIdealGame (fun _ => PMF.pure d)`
acceptance probability by at most `3 / 2 ^ n`. -/
theorem advantage_ddhIdealGame_pure_ddhSelfReduceDistinguisher_le (d : F.Desc)
    {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    Game.advantage (F.ddhIdealGame (fun _ => PMF.pure d) distinguisher n)
      (ProbComp.eval (F.ddhSelfReduceDistinguisher distinguisher n
        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
          F.encode d (γ • F.generator d)))) ≤ 3 / 2 ^ n := by
  classical
  let α' : ∀ d' : F.Desc, ZMod (F.order d') := fun d' =>
    if h : d' = d then h ▸ α else 0
  let β' : ∀ d' : F.Desc, ZMod (F.order d') := fun d' =>
    if h : d' = d then h ▸ β else 0
  let γ' : ∀ d' : F.Desc, ZMod (F.order d') := fun d' =>
    if h : d' = d then h ▸ γ else 1
  have hγ' : ∀ d' ∈ (PMF.pure d).support, γ' d' ≠ α' d' * β' d' := by
    intro d' hd'
    have hd_eq : d' = d := by simpa using hd'
    subst hd_eq
    simpa [α', β', γ'] using hγ
  have h := F.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le (fun _ => PMF.pure d)
    (fun d' => (α' d' • F.generator d', β' d' • F.generator d', γ' d' • F.generator d'))
    distinguisher n
  rw [F.ddhRerandomizeGame_ideal (fun _ => PMF.pure d) α' β' γ' distinguisher n hγ'] at h
  simpa only [ddhWorstCaseGame_pure, α', β', γ', ↓reduceDIte] using h

/-- **Chernoff-amplified worst-case DDH decider** ([BonehShoup2023], Section 10.11, Exercise 10.10,
p. 426): given an average-case DDH distinguisher `distinguisher` and an inverse-advantage bound
`invEps : ℕ → ℕ`, perform `N = (n + 3) * (7 * invEps n) ^ 2` independent trials of
`ddhSelfReduceDistinguisher` on the input tuple `(d, u, v, w)`, on the reference DH tuple
`ddhRealRefTuple d`, and on the reference non-DH tuple `ddhIdealRefTuple d`, and accept iff the
empirical count `cIn` is at least as close to `cReal` as to `cIdeal`. -/
noncomputable def ddhAmplifiedDecider
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (invEps : ℕ → ℕ) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let d := input.1
  let N := (n + 3) * (7 * invEps n) ^ 2
  let cIn ← OracleComp.countTrue N
    (F.ddhSelfReduceDistinguisher distinguisher n (d, input.2))
  let cReal ← OracleComp.countTrue N
    (F.ddhSelfReduceDistinguisher distinguisher n (d, F.ddhRealRefTuple d))
  let cIdeal ← OracleComp.countTrue N
    (F.ddhSelfReduceDistinguisher distinguisher n (d, F.ddhIdealRefTuple d))
  return decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cIdeal) + (cIdeal - cIn))

/-- `ddhAmplifiedDecider` is uniform strict PPT whenever `distinguisher` is uniform strict PPT and
`invEps` is computable in polynomial time in unary ([BonehShoup2023], Exercise 10.10, p. 426). -/
theorem isPPTOn_ddhAmplifiedDecider
    {distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool}
    (hD : IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => distinguisher input.1 input.2))
    {invEps : ℕ → ℕ} (hinvEps : ComputableInPolyTime invEps encUnary encUnary) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.ddhAmplifiedDecider distinguisher invEps input.1 input.2) := by
  have hself := F.isPPTOn_ddhSelfReduceDistinguisher hD
  have hN_unary : ComputableInPolyTime
      (fun n : ℕ => (n + 3) * (7 * invEps n) ^ 2) encUnary encUnary := by
    have hinv_t := hinvEps.tidy
    exact ComputableInPolyTime.of_tidy (by fun_prop)
  have hN : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        (input.1 + 3) * (7 * invEps input.1) ^ 2)
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encUnary :=
    hN_unary.comp (ComputableInPolyTime.fst _ _)
  have hd : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool => input.2.1)
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      F.encDesc :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
  have hcIn : IsPPTOn
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))) encUnary
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        OracleComp.countTrue ((input.1 + 3) * (7 * invEps input.1) ^ 2)
          (F.ddhSelfReduceDistinguisher distinguisher input.1 (input.2.1, input.2.2))) :=
    hself.countTrue hN
  have hrealTrial : IsPPTOn
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))) encBool
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        F.ddhSelfReduceDistinguisher distinguisher input.1
          (input.2.1, F.ddhRealRefTuple input.2.1)) :=
    hself.preprocess
      (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        (input.1, input.2.1, F.ddhRealRefTuple input.2.1))
      ((ComputableInPolyTime.fst _ _).prod
        (hd.prod (F.computableInPolyTime_ddhRealRefTuple.comp hd)))
  have hcReal : IsPPTOn
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))) encUnary
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        OracleComp.countTrue ((input.1 + 3) * (7 * invEps input.1) ^ 2)
          (F.ddhSelfReduceDistinguisher distinguisher input.1
            (input.2.1, F.ddhRealRefTuple input.2.1))) :=
    hrealTrial.countTrue hN
  have hidealTrial : IsPPTOn
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))) encBool
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        F.ddhSelfReduceDistinguisher distinguisher input.1
          (input.2.1, F.ddhIdealRefTuple input.2.1)) :=
    hself.preprocess
      (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        (input.1, input.2.1, F.ddhIdealRefTuple input.2.1))
      ((ComputableInPolyTime.fst _ _).prod
        (hd.prod (F.computableInPolyTime_ddhIdealRefTuple.comp hd)))
  have hcIdeal : IsPPTOn
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))) encUnary
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        OracleComp.countTrue ((input.1 + 3) * (7 * invEps input.1) ^ 2)
          (F.ddhSelfReduceDistinguisher distinguisher input.1
            (input.2.1, F.ddhIdealRefTuple input.2.1))) :=
    hidealTrial.countTrue hN
  have hcmp : ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ =>
        decide ((q.1 - q.2.1) + (q.2.1 - q.1) ≤ (q.1 - q.2.2) + (q.2.2 - q.1)))
      (encPair encUnary (encPair encUnary encUnary)) encBool :=
    ComputableInPolyTime.of_tidy (by polytime)
  have hproj : ComputableInPolyTime
      (fun p : (((ℕ × F.Desc × List Bool × List Bool × List Bool) × ℕ) × ℕ) × ℕ =>
        (p.1.1.2, p.1.2, p.2))
      (encPair
        (encPair
          (encPair
            (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
            encUnary)
          encUnary)
        encUnary)
      (encPair encUnary (encPair encUnary encUnary)) :=
    ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))).prod
      (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  unfold ddhAmplifiedDecider
  refine hcIn.bind_with ?_
  refine (hcReal.preprocess (prepare := Prod.fst) (ComputableInPolyTime.fst _ _)).bind_with ?_
  refine (hcIdeal.preprocess
    (prepare := fun p : ((ℕ × F.Desc × List Bool × List Bool × List Bool) × ℕ) × ℕ => p.1.1)
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))).bind_with ?_
  exact (hcmp.comp hproj).isPPTOn

private theorem cast_sub_add_sub_eq_abs (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · have hR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hR),
      neg_sub]
  · have hR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hR)]

private theorem abs_succProbability_sub_le_of_advantage_le {g₁ g₂ : Game} {ε : ℝ}
    (h : (Game.advantage g₁ g₂ : ℝ) ≤ ε) :
    |(g₁ true).toReal - (g₂ true).toReal| ≤ ε := by
  simpa only [Game.coe_advantage, Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] using h

/-- **Quantitative worst-case DDH decision bound** ([BonehShoup2023], Section 10.11, Exercise 10.10,
p. 426): if `distinguisher n` has average-case DDH advantage at least `1 / invEps n` on group `d`
and the modular-sampling bias satisfies `3 / 2 ^ n ≤ 1 / (12 * invEps n)`, then for *every*
triple `(α • g, β • g, γ • g)` over `d`, `ddhAmplifiedDecider` outputs an answer different from
`decide (γ = α * β)` with probability at most `(1 / 2) ^ n`. -/
theorem ddhAmplifiedDecider_error_le_pow
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (invEps : ℕ → ℕ) (n : ℕ) (d : F.Desc) (α β γ : ZMod (F.order d))
    (hpos : 0 < invEps n)
    (hadv : 1 / (invEps n : ℝ) ≤
      Game.advantage (F.ddhRealGame (fun _ => PMF.pure d) distinguisher n)
        (F.ddhIdealGame (fun _ => PMF.pure d) distinguisher n))
    (hmod : 3 / (2 ^ n : ℝ) ≤ 1 / (12 * (invEps n : ℝ))) :
    ((ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n
      (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
        F.encode d (γ • F.generator d)))).toOuterMeasure
      {b | b ≠ decide (γ = α * β)}).toReal ≤ (1 / 2 : ℝ) ^ n := by
  have : Fact (Nat.Prime (F.order d)) := ⟨F.prime_order d⟩
  let N := (n + 3) * (7 * invEps n) ^ 2
  have h7pos : 0 < 7 * invEps n := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by positivity : 0 < N)
  let tIn := F.ddhSelfReduceDistinguisher distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d (γ • F.generator d))
  let tReal := F.ddhSelfReduceDistinguisher distinguisher n (d, F.ddhRealRefTuple d)
  let tIdeal := F.ddhSelfReduceDistinguisher distinguisher n (d, F.ddhIdealRefTuple d)
  let pReal := (F.ddhRealGame (fun _ => PMF.pure d) distinguisher n true).toReal
  let pIdeal := (F.ddhIdealGame (fun _ => PMF.pure d) distinguisher n true).toReal
  let ε : ℝ := 1 / (invEps n : ℝ)
  have h12eq : 1 / (12 * (invEps n : ℝ)) = ε / 12 := by dsimp [ε]; ring
  have h7eq' : 1 / ((7 * invEps n : ℕ) : ℝ) = ε / 7 := by dsimp [ε]; push_cast; ring
  have hadv' : ε ≤ |pReal - pIdeal| := by
    simpa only [Game.coe_advantage, Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
      pReal, pIdeal, ε] using hadv
  have hmod' : 3 / (2 ^ n : ℝ) ≤ ε / 12 := h12eq ▸ hmod
  have hRealRef : |(ProbComp.eval tReal true).toReal - pReal| ≤ ε / 12 := by
    rw [abs_sub_comm]
    refine (abs_succProbability_sub_le_of_advantage_le ?_).trans hmod'
    simpa only [tReal, ddhRealRefTuple_eq_encode, NNReal.coe_div, NNReal.coe_ofNat,
      NNReal.coe_pow] using
      NNReal.coe_le_coe.mpr
        (F.advantage_ddhRealGame_pure_ddhSelfReduceDistinguisher_le d 0 0 distinguisher n)
  have hIdealRef : |(ProbComp.eval tIdeal true).toReal - pIdeal| ≤ ε / 12 := by
    rw [abs_sub_comm]
    refine (abs_succProbability_sub_le_of_advantage_le ?_).trans hmod'
    have h10 : (1 : ZMod (F.order d)) ≠ 0 * 0 := by simp
    simpa only [tIdeal, ddhIdealRefTuple_eq_encode, NNReal.coe_div, NNReal.coe_ofNat,
      NNReal.coe_pow] using
      NNReal.coe_le_coe.mpr
        (F.advantage_ddhIdealGame_pure_ddhSelfReduceDistinguisher_le d h10 distinguisher n)
  let good (t : ProbComp Bool) : Set ℕ :=
    {c | |(c : ℝ) / N - (ProbComp.eval t true).toReal| < 1 / (7 * invEps n : ℕ)}
  have hconc (t : ProbComp Bool) :
      (((ProbComp.eval (OracleComp.countTrue N t)).toOuterMeasure (good t)ᶜ).toReal) ≤
        (1 / 2 : ℝ) ^ (n + 2) := by
    simpa only [good, N, Set.compl_ofPred, not_lt, show n + 3 = (n + 2) + 1 by omega] using
      ProbComp.countTrue_average_deviation_pow (n + 2) (7 * invEps n) h7pos t
  have hdet {cIn cReal cIdeal : ℕ} (hcIn : cIn ∈ good tIn) (hcReal : cReal ∈ good tReal)
      (hcIdeal : cIdeal ∈ good tIdeal) :
      decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cIdeal) + (cIdeal - cIn)) =
        decide (γ = α * β) := by
    have hcIn' : |(cIn : ℝ) / N - (ProbComp.eval tIn true).toReal| < ε / 7 := by
      simpa only [good, Set.mem_ofPred_eq, h7eq'] using hcIn
    have hcReal' : |(cReal : ℝ) / N - (ProbComp.eval tReal true).toReal| < ε / 7 := by
      simpa only [good, Set.mem_ofPred_eq, h7eq'] using hcReal
    have hcIdeal' : |(cIdeal : ℝ) / N - (ProbComp.eval tIdeal true).toReal| < ε / 7 := by
      simpa only [good, Set.mem_ofPred_eq, h7eq'] using hcIdeal
    have hcmp_iff :
        ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cIdeal) + (cIdeal - cIn)) ↔
          |(cIn : ℝ) / N - (cReal : ℝ) / N| ≤ |(cIn : ℝ) / N - (cIdeal : ℝ) / N| := by
      rw [← @Nat.cast_le ℝ, cast_sub_add_sub_eq_abs, cast_sub_add_sub_eq_abs,
        ← div_le_div_iff_of_pos_right hNpos, ← abs_of_pos hNpos, ← abs_div, ← abs_div,
        abs_of_pos hNpos, sub_div, sub_div]
    by_cases hγ : γ = α * β
    · have hInRef : |(ProbComp.eval tIn true).toReal - pReal| ≤ ε / 12 := by
        subst hγ
        rw [abs_sub_comm]
        refine (abs_succProbability_sub_le_of_advantage_le ?_).trans hmod'
        simpa only [tIn, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow] using
          NNReal.coe_le_coe.mpr
            (F.advantage_ddhRealGame_pure_ddhSelfReduceDistinguisher_le d α β distinguisher n)
      rw [abs_le] at hRealRef hIdealRef hInRef
      rw [abs_lt] at hcIn' hcReal' hcIdeal'
      have hdReal : |(cIn : ℝ) / N - (cReal : ℝ) / N| ≤ ε / 2 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have hdIdeal : ε / 2 ≤ |(cIn : ℝ) / N - (cIdeal : ℝ) / N| := by
        rcases le_abs.mp hadv' with hgap | hgap
        · exact (by linarith : ε / 2 ≤ (cIn : ℝ) / N - (cIdeal : ℝ) / N).trans (le_abs_self _)
        · exact (by linarith : ε / 2 ≤ -((cIn : ℝ) / N - (cIdeal : ℝ) / N)).trans (neg_le_abs _)
      simp [hγ, hcmp_iff.mpr (hdReal.trans hdIdeal)]
    · have hInRef : |(ProbComp.eval tIn true).toReal - pIdeal| ≤ ε / 12 := by
        rw [abs_sub_comm]
        refine (abs_succProbability_sub_le_of_advantage_le ?_).trans hmod'
        simpa only [tIn, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow] using
          NNReal.coe_le_coe.mpr
            (F.advantage_ddhIdealGame_pure_ddhSelfReduceDistinguisher_le d hγ distinguisher n)
      rw [abs_le] at hRealRef hIdealRef hInRef
      rw [abs_lt] at hcIn' hcReal' hcIdeal'
      have hdIdeal : |(cIn : ℝ) / N - (cIdeal : ℝ) / N| < ε / 2 :=
        abs_lt.mpr ⟨by linarith, by linarith⟩
      have hdReal : ε / 2 < |(cIn : ℝ) / N - (cReal : ℝ) / N| := by
        rcases le_abs.mp hadv' with hgap | hgap
        · exact (by linarith : ε / 2 < -((cIn : ℝ) / N - (cReal : ℝ) / N)).trans_le (neg_le_abs _)
        · exact (by linarith : ε / 2 < (cIn : ℝ) / N - (cReal : ℝ) / N).trans_le (le_abs_self _)
      simp [hγ, hcmp_iff.not.mpr (not_le.mpr (hdIdeal.trans hdReal))]
  simp only [ddhAmplifiedDecider, ProbComp.eval_bind, ProbComp.eval_pure]
  have hstep1 := PMF.toOuterMeasure_bind_failure_toReal_le
    (ProbComp.eval (OracleComp.countTrue N tIn))
    (fun cIn => (ProbComp.eval (OracleComp.countTrue N tReal)).bind fun cReal =>
      (ProbComp.eval (OracleComp.countTrue N tIdeal)).bind fun cIdeal =>
        PMF.pure (decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cIdeal) + (cIdeal - cIn))))
    (good tIn) {b | b ≠ decide (γ = α * β)}
    (error := (1 / 2 : ℝ) ^ (n + 2) + (1 / 2 : ℝ) ^ (n + 2)) (by positivity)
    fun cIn _ hcIn => by
      refine (PMF.toOuterMeasure_bind_failure_toReal_le
        (ProbComp.eval (OracleComp.countTrue N tReal))
        (fun cReal => (ProbComp.eval (OracleComp.countTrue N tIdeal)).bind fun cIdeal =>
          PMF.pure (decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cIdeal) + (cIdeal - cIn))))
        (good tReal) {b | b ≠ decide (γ = α * β)}
        (error := (1 / 2 : ℝ) ^ (n + 2)) (by positivity)
        fun cReal _ hcReal => ?_).trans (by linarith [hconc tReal])
      refine (PMF.toOuterMeasure_bind_failure_toReal_le
        (ProbComp.eval (OracleComp.countTrue N tIdeal))
        (fun cIdeal =>
          PMF.pure (decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cIdeal) + (cIdeal - cIn))))
        (good tIdeal) {b | b ≠ decide (γ = α * β)}
        (error := 0) le_rfl
        fun cIdeal _ hcIdeal => ?_).trans (by linarith [hconc tIdeal])
      rw [hdet hcIn hcReal hcIdeal, PMF.toOuterMeasure_pure_apply]
      simp
  have hInConc := hconc tIn
  have hpow0 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
  rw [pow_add, pow_two] at hstep1 hInConc
  linarith

/-- **Directional correctness of `ddhAmplifiedDecider`** ([BonehShoup2023], Section 10.11,
Exercise 10.10, p. 426): under the hypotheses of `ddhAmplifiedDecider_error_le_pow`, on every
triple `(α • g, β • g, γ • g)` over `d`, `ddhAmplifiedDecider` outputs the correct decision
`decide (γ = α * β)` with probability at least `1 - (1 / 2) ^ n`. -/
theorem ddhAmplifiedDecider_correct_ge_one_sub_pow
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (invEps : ℕ → ℕ) (n : ℕ) (d : F.Desc) (α β γ : ZMod (F.order d))
    (hpos : 0 < invEps n)
    (hadv : 1 / (invEps n : ℝ) ≤
      Game.advantage (F.ddhRealGame (fun _ => PMF.pure d) distinguisher n)
        (F.ddhIdealGame (fun _ => PMF.pure d) distinguisher n))
    (hmod : 3 / (2 ^ n : ℝ) ≤ 1 / (12 * (invEps n : ℝ))) :
    1 - (1 / 2 : ℝ) ^ n ≤
      (ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n
        (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
          F.encode d (γ • F.generator d))) (decide (γ = α * β))).toReal := by
  let p := ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d (γ • F.generator d)))
  have herr := F.ddhAmplifiedDecider_error_le_pow distinguisher invEps n d α β γ hpos hadv hmod
  have hsum := PMF.sum_toReal p
  rw [Fintype.sum_bool] at hsum
  have hne : (p.toOuterMeasure {b | b ≠ decide (γ = α * β)}).toReal =
      1 - (p (decide (γ = α * β))).toReal := by
    rw [PMF.toOuterMeasure_apply_toReal, Fintype.sum_bool]
    cases hdec : decide (γ = α * β) <;> simp <;> linarith
  linarith [herr, hne]

/-- **Boneh–Shoup Exercise 10.10 (Worst-case DDH decider with negligible error, p. 426)**:
if `invEps` is computable in polynomial time in unary and `distinguisher` has average-case DDH
advantage at least `1 / invEps n` on `d n` eventually, then for *every* worst-case sequence of
input tuples `(d n, α n, β n, γ n)`, `ddhAmplifiedDecider` decides whether `γ n = α n * β n` with
negligible error probability. -/
theorem negligible_ddhAmplifiedDecider_error
    {distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool}
    {invEps : ℕ → ℕ} (hinvEps : ComputableInPolyTime invEps encUnary encUnary)
    (d : ℕ → F.Desc) (α β γ : ∀ n, ZMod (F.order (d n)))
    (hpos : ∀ᶠ n in Filter.atTop, 0 < invEps n)
    (hadv : ∀ᶠ n in Filter.atTop, 1 / (invEps n : ℝ) ≤
      Game.advantage (F.ddhRealGame (fun _ => PMF.pure (d n)) distinguisher n)
        (F.ddhIdealGame (fun _ => PMF.pure (d n)) distinguisher n)) :
    Negligible fun n =>
      ((ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n
        (d n, F.encode (d n) (α n • F.generator (d n)),
          F.encode (d n) (β n • F.generator (d n)),
          F.encode (d n) (γ n • F.generator (d n))))).toOuterMeasure
        {b | b ≠ decide (γ n = α n * β n)}).toNNReal := by
  have hgeom : Negligible fun n => ((2⁻¹ : ℝ≥0) ^ n) :=
    negligible_geometric (ratio := 2⁻¹) (by norm_num)
  have hpoly : PolynomiallyBounded fun n => 36 * invEps n + 1 := by
    obtain ⟨c, k, hck⟩ := hinvEps.tidy.polyBounded_length.exists_le
    refine PolynomiallyBounded.of_forall_le (36 * c + 1) k fun n => ?_
    have hn := hck n
    simp only [encUnary_apply, List.length_replicate] at hn
    have hpow : 1 ≤ (n + 1) ^ k := Nat.one_le_pow k (n + 1) (Nat.succ_pos n)
    nlinarith
  have hmod_ev : ∀ᶠ n in Filter.atTop, 3 / (2 ^ n : ℝ) ≤ 1 / (12 * (invEps n : ℝ)) := by
    filter_upwards [hpos, hgeom.eventually_le_inv_polynomial hpoly (fun _ => Nat.succ_pos _)]
      with n hn hlt
    have hinv_pos : (0 : ℝ) < invEps n := by exact_mod_cast hn
    have hlt' : (1 : ℝ) / 2 ^ n ≤ 1 / (36 * (invEps n : ℝ) + 1) := by
      simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat, inv_pow, one_div,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlt
    have hle1 : (1 : ℝ) / (36 * (invEps n : ℝ) + 1) ≤ 1 / (36 * (invEps n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hle2 := hlt'.trans hle1
    have h36 : (1 : ℝ) / (36 * (invEps n : ℝ)) = (1 / 3) * (1 / (12 * (invEps n : ℝ))) := by ring
    have h3pow : (3 : ℝ) / 2 ^ n = 3 * ((1 : ℝ) / 2 ^ n) := by ring
    rw [h36] at hle2
    rw [h3pow]
    linarith
  refine negligible_of_eventually_le hgeom ?_
  filter_upwards [hpos, hadv, hmod_ev] with n hn hadv_n hmod_n
  have herr := F.ddhAmplifiedDecider_error_le_pow distinguisher invEps n (d n)
    (α n) (β n) (γ n) hn hadv_n hmod_n
  rw [← NNReal.coe_le_coe]
  simpa only [ENNReal.coe_toNNReal_eq_toReal, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat,
    one_div] using herr

end Cslib.Crypto.PrimeOrderGroupFamily
