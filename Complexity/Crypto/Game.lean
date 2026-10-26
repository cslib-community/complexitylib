/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: submitted #1069 @1d14c55a10cfe3fe4463cffa61a7f02f0d56f502

public import Complexity.Crypto.Negligible
public import Cslib.Probability.PMF

/-!
# Security of Boolean experiments

A `Game` is the distribution of the Boolean output of a security experiment, independent of the
language used to write the experiment. A game has a success probability, and two games have a
distinguishing advantage: the absolute difference of their success probabilities, as in
[BonehShoup2023], Section 3.1. The convention where the advantage of a single game is its
success probability is comparison with certain failure, and the convention measuring bias away
from a fair coin is `guessingAdvantage`.

Families of games indexed by a natural-number security parameter are indistinguishable for a
class of adversaries when every admissible adversary has negligible advantage. Adversaries are
whole objects, which may themselves be families of tests, and the game at each parameter is
obtained from the adversary. Finite cryptographic primitives instantiate these definitions
directly, and computational definitions over infinite sample spaces can reuse them.

## Main definitions

* `Cslib.Crypto.Game`: Boolean experiment distributions with nonnegative success and advantage.
* `Cslib.Crypto.Game.Indistinguishable`: negligible advantage for each admissible adversary.

## Main results

* `Cslib.Crypto.Game.Indistinguishable.of_reduction`: preserve admissibility and transfer security
  with a polynomial loss and negligible error.
* `Cslib.Crypto.Game.advantage_le_of_apply_le`, `Cslib.Crypto.Game.advantage_bind_le`: bound
  real-valued distinguishing advantage from mutual acceptance-probability bounds or across a common
  first-stage distribution.
* `Cslib.Crypto.Game.advantage_bind_uniformOfFintype_of_ne_le`: exceptional-point loss under a
  uniform finite first-stage choice, extracted from the reviewed support in PR #1103.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.1.

Copied from cslib PR #1069 at `1d14c55a10cfe3fe4463cffa61a7f02f0d56f502`.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped ENNReal NNReal

/-- The distribution of the Boolean output of a security experiment. -/
abbrev Game := PMF Bool

namespace Game

/-- The probability that an experiment succeeds, that is, outputs `true`. -/
abbrev succProbability (game : Game) : ℝ≥0 := (game true).toNNReal

/-- The probability that an experiment fails, that is, outputs `false`. -/
abbrev failProbability (game : Game) : ℝ≥0 := (game false).toNNReal

/-- Success probability is at most one. -/
theorem succProbability_le_one (game : Game) : succProbability game ≤ 1 := by
  simpa using ENNReal.toNNReal_mono ENNReal.one_ne_top (PMF.coe_le_one game true)

/-- An experiment either succeeds or fails. -/
theorem succProbability_add_failProbability (game : Game) :
    succProbability game + failProbability game = 1 := by
  rw [succProbability, failProbability,
    ← ENNReal.toNNReal_add (game.apply_ne_top _) (game.apply_ne_top _), add_comm, ← tsum_bool,
    game.tsum_coe, ENNReal.toNNReal_one]

/-- Failure probability is the complement of success probability. -/
theorem failProbability_eq (game : Game) : failProbability game = 1 - succProbability game :=
  eq_tsub_of_add_eq (by rw [add_comm, succProbability_add_failProbability])

/-- Complementing a game's answer exchanges success and failure. -/
@[simp] theorem succProbability_not (game : Game) :
    succProbability (game.map Bool.not) = failProbability game := by
  simp [succProbability, failProbability]

/-- The distinguishing advantage between two games is the absolute difference of their success
probabilities. -/
abbrev advantage (game1 game2 : Game) : ℝ≥0 :=
  nndist game1.succProbability game2.succProbability

/-- As a real number, the advantage is the absolute difference of the success probabilities. -/
theorem coe_advantage (game1 game2 : Game) :
    (advantage game1 game2 : ℝ) = |(succProbability game1 : ℝ) - succProbability game2| := by
  rw [advantage, coe_nndist, NNReal.dist_eq]

/-- Distinguishing advantage is at most one. -/
theorem advantage_le_one (game1 game2 : Game) : advantage game1 game2 ≤ 1 := by
  rw [advantage, NNReal.nndist_eq]
  exact max_le (tsub_le_iff_right.mpr (le_add_right (succProbability_le_one _)))
    (tsub_le_iff_right.mpr (le_add_right (succProbability_le_one _)))

/-- Equal games have zero advantage. -/
theorem advantage_self (game : Game) : advantage game game = 0 := nndist_self _

/-- Swapping the games preserves advantage. -/
theorem advantage_comm (game1 game2 : Game) : advantage game1 game2 = advantage game2 game1 :=
  nndist_comm _ _

/-- Complementing both answers preserves advantage. -/
@[simp] theorem advantage_not (game1 game2 : Game) :
    advantage (game1.map Bool.not) (game2.map Bool.not) = advantage game1 game2 := by
  apply NNReal.eq
  rw [coe_advantage, coe_advantage, succProbability_not, succProbability_not, failProbability_eq,
    failProbability_eq, NNReal.coe_sub (succProbability_le_one _),
    NNReal.coe_sub (succProbability_le_one _), sub_sub_sub_cancel_left, abs_sub_comm]

/-- The elementary game-hopping inequality. -/
theorem advantage_triangle (first middle last : Game) :
    advantage first last ≤ advantage first middle + advantage middle last := nndist_triangle _ _ _

/-- Comparing with certain failure measures the probability of success. -/
@[simp] theorem advantage_pure_false (game : Game) :
    advantage game (PMF.pure false) = succProbability game := by
  simp [advantage, succProbability]

open Probability in
/-- The advantage of a game over a fair coin, measuring its prediction bias. -/
noncomputable abbrev guessingAdvantage (game : Game) : ℝ≥0 :=
  advantage game (PMF.uniformOfFintype Bool)

open Probability in
/-- As a real number, the guessing advantage is the distance of the success probability from
one half. -/
theorem coe_guessingAdvantage (game : Game) :
    (guessingAdvantage game : ℝ) = |(succProbability game : ℝ) - 1 / 2| := by
  rw [guessingAdvantage, coe_advantage]
  simp [succProbability, ENNReal.toNNReal_ofNat]

/-- Two families of games are indistinguishable for a class of adversaries when each admissible
adversary has negligible advantage. The admissibility predicate applies to the whole adversary
before the security parameter is supplied, so it can constrain the adversary across all
parameters at once. -/
def Indistinguishable {Adversary : Type*} (game1 game2 : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) : Prop :=
  ∀ adversary, Admissible adversary →
    Negligible (fun n => advantage (game1 adversary n) (game2 adversary n))

/-- A common concrete bound on the advantage of all admissible adversaries at each parameter. -/
def IndistinguishableWithError {Adversary : Type*} (game1 game2 : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) (ε : ℕ → ℝ≥0) : Prop :=
  ∀ adversary, Admissible adversary →
    ∀ n, advantage (game1 adversary n) (game2 adversary n) ≤ ε n

/-- Restricting admissibility preserves a concrete bound. -/
theorem IndistinguishableWithError.of_admissible {Adversary : Type*}
    {game1 game2 : Adversary → ℕ → Game} {Admissible Restricted : Adversary → Prop}
    {ε : ℕ → ℝ≥0} (h : IndistinguishableWithError game1 game2 Admissible ε)
    (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    IndistinguishableWithError game1 game2 Restricted ε :=
  fun adversary ha => h adversary (hsub adversary ha)

/-- Restricting admissibility preserves indistinguishability. -/
theorem Indistinguishable.of_admissible {Adversary : Type*} {game1 game2 : Adversary → ℕ → Game}
    {Admissible Restricted : Adversary → Prop} (h : Indistinguishable game1 game2 Admissible)
    (hsub : ∀ adversary, Restricted adversary → Admissible adversary) :
    Indistinguishable game1 game2 Restricted := fun adversary ha => h adversary (hsub adversary ha)

/-- Enlarging an error budget preserves its guarantee. -/
theorem IndistinguishableWithError.mono {Adversary : Type*} {game1 game2 : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε δ : ℕ → ℝ≥0}
    (h : IndistinguishableWithError game1 game2 Admissible ε) (hle : ∀ n, ε n ≤ δ n) :
    IndistinguishableWithError game1 game2 Admissible δ :=
  fun adversary ha n => (h adversary ha n).trans (hle n)

/-- A family of games is indistinguishable from itself. -/
theorem Indistinguishable.refl {Adversary : Type*} (game : Adversary → ℕ → Game)
    (Admissible : Adversary → Prop) : Indistinguishable game game Admissible :=
  fun _ _ => by simp

/-- Swapping the games preserves a concrete bound. -/
theorem IndistinguishableWithError.symm {Adversary : Type*} {game1 game2 : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : IndistinguishableWithError game1 game2 Admissible ε) :
    IndistinguishableWithError game2 game1 Admissible ε :=
  fun adversary ha n => (advantage_comm _ _).trans_le (h adversary ha n)

/-- Swapping the games preserves indistinguishability. -/
theorem Indistinguishable.symm {Adversary : Type*} {game1 game2 : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} (h : Indistinguishable game1 game2 Admissible) :
    Indistinguishable game2 game1 Admissible :=
  fun adversary ha => (h adversary ha).congr fun _ => advantage_comm _ _

/-- Concrete bounds add across a game hop. -/
theorem IndistinguishableWithError.trans {Adversary : Type*}
    {first middle last : Adversary → ℕ → Game} {Admissible : Adversary → Prop} {ε δ : ℕ → ℝ≥0}
    (hfirst : IndistinguishableWithError first middle Admissible ε)
    (hlast : IndistinguishableWithError middle last Admissible δ) :
    IndistinguishableWithError first last Admissible (fun n => ε n + δ n) :=
  fun adversary ha n =>
    (advantage_triangle _ _ _).trans (add_le_add (hfirst adversary ha n) (hlast adversary ha n))

/-- Indistinguishability composes through an intermediate family of games. -/
theorem Indistinguishable.trans {Adversary : Type*} {first middle last : Adversary → ℕ → Game}
    {Admissible : Adversary → Prop} (hfirst : Indistinguishable first middle Admissible)
    (hlast : Indistinguishable middle last Admissible) :
    Indistinguishable first last Admissible := fun adversary ha =>
  negligible_of_le ((hfirst adversary ha).add (hlast adversary ha))
    fun _ => advantage_triangle _ _ _

/-- A negligible common error bound implies indistinguishability. -/
theorem IndistinguishableWithError.indistinguishable {Adversary : Type*}
    {game1 game2 : Adversary → ℕ → Game} {Admissible : Adversary → Prop} {ε : ℕ → ℝ≥0}
    (h : IndistinguishableWithError game1 game2 Admissible ε) (hε : Negligible ε) :
    Indistinguishable game1 game2 Admissible :=
  fun adversary ha => negligible_of_le hε (h adversary ha)

/-- A reduction turns each target adversary into a source adversary. It transfers
indistinguishability from the source games to the target games when it preserves admissibility
and bounds the target advantage by the source advantage up to a polynomial loss and a negligible
error. The loss and the error may depend on the target adversary, while the reduction maps whole
adversaries and does not depend on the security parameter. -/
theorem Indistinguishable.of_reduction {SourceAdversary TargetAdversary : Type*}
    {source1 source2 : SourceAdversary → ℕ → Game} {target1 target2 : TargetAdversary → ℕ → Game}
    {SourceAdmissible : SourceAdversary → Prop} {TargetAdmissible : TargetAdversary → Prop}
    (h : Indistinguishable source1 source2 SourceAdmissible)
    (reduce : TargetAdversary → SourceAdversary)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary →
      ∃ (loss : ℕ → ℕ) (error : ℕ → ℝ≥0), PolynomiallyBounded loss ∧ Negligible error ∧ ∀ n,
        advantage (target1 adversary n) (target2 adversary n) ≤
          loss n * advantage (source1 (reduce adversary) n) (source2 (reduce adversary) n) +
            error n) :
    Indistinguishable target1 target2 TargetAdmissible := by
  intro adversary ha
  obtain ⟨loss, error, hloss, herror, hbound⟩ := hbound adversary ha
  have hsource := h _ (hadmissible adversary ha)
  exact negligible_of_le (by fun_prop (disch := assumption)) hbound

-- upstream: candidate

/-- As a real number, the success probability is the real-valued probability of `true`. -/
@[simp] theorem coe_succProbability (game : Game) :
    (succProbability game : ℝ) = (game true).toReal := rfl

open scoped ENNReal in
/-- Mutual upper bounds on the two acceptance probabilities bound the real-valued advantage. -/
theorem advantage_le_of_apply_le {game1 game2 : Game} {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (h1 : game1 true ≤ game2 true + B) (h2 : game2 true ≤ game1 true + B) :
    (advantage game1 game2 : ℝ) ≤ B.toReal := by
  rw [coe_advantage, coe_succProbability, coe_succProbability]
  have ht1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hB⟩) h1
  have ht2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hB⟩) h2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hB] at ht1 ht2
  exact abs_sub_le_iff.mpr ⟨sub_le_iff_le_add'.mpr ht1, sub_le_iff_le_add'.mpr ht2⟩

open scoped ENNReal in
/-- Averaging two families of games over a common first stage preserves any uniform real-valued
advantage bound. -/
theorem advantage_bind_le {α : Type*} (d : PMF α) (game1 game2 : α → Game) {ε : ℝ}
    (h : ∀ a, (advantage (game1 a) (game2 a) : ℝ) ≤ ε) :
    (advantage (d.bind game1) (d.bind game2) : ℝ) ≤ ε := by
  have hε0 : 0 ≤ ε := by
    obtain ⟨a, -⟩ := d.support_nonempty
    exact (NNReal.coe_nonneg _).trans (h a)
  have h1 (a : α) : game1 a true ≤ game2 a true + ENNReal.ofReal ε := by
    have ha := h a
    rw [coe_advantage, coe_succProbability, coe_succProbability] at ha
    have hle : (game1 a true).toReal ≤ (game2 a true).toReal + ε :=
      sub_le_iff_le_add'.mp (abs_sub_le_iff.mp ha).1
    have hof := ENNReal.ofReal_le_ofReal hle
    rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg hε0,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)] at hof
  have h2 (a : α) : game2 a true ≤ game1 a true + ENNReal.ofReal ε := by
    have ha := h a
    rw [coe_advantage, coe_succProbability, coe_succProbability] at ha
    have hle : (game2 a true).toReal ≤ (game1 a true).toReal + ε :=
      sub_le_iff_le_add'.mp (abs_sub_le_iff.mp ha).2
    have hof := ENNReal.ofReal_le_ofReal hle
    rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg hε0,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)] at hof
  have hsum1 : (d.bind game1) true ≤ (d.bind game2) true + ENNReal.ofReal ε := by
    rw [PMF.bind_apply, PMF.bind_apply]
    calc ∑' a, d a * game1 a true
        ≤ ∑' a, d a * (game2 a true + ENNReal.ofReal ε) :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h1 a) zero_le
      _ = (∑' a, d a * game2 a true) + ENNReal.ofReal ε := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, d.tsum_coe, one_mul]
  have hsum2 : (d.bind game2) true ≤ (d.bind game1) true + ENNReal.ofReal ε := by
    rw [PMF.bind_apply, PMF.bind_apply]
    calc ∑' a, d a * game2 a true
        ≤ ∑' a, d a * (game1 a true + ENNReal.ofReal ε) :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h2 a) zero_le
      _ = (∑' a, d a * game1 a true) + ENNReal.ofReal ε := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, d.tsum_coe, one_mul]
  have hadv := advantage_le_of_apply_le ENNReal.ofReal_ne_top hsum1 hsum2
  rwa [ENNReal.toReal_ofReal hε0] at hadv


open Probability in
/-- If a family of games `g : α → Game` agrees with `p : Game` on every `a ≠ a₀`, then averaging
`g` over `PMF.uniformOfFintype α` is within `(Fintype.card α)⁻¹` of `p`. -/
theorem advantage_bind_uniformOfFintype_of_ne_le {α : Type*} [Fintype α] [Nonempty α]
    (a₀ : α) (g : α → Game) (p : Game) (hne : ∀ a, a ≠ a₀ → g a = p) :
    Game.advantage ((PMF.uniformOfFintype α).bind g) p ≤ (Fintype.card α : ℝ≥0)⁻¹ := by
  classical
  have hsingle :
      ((PMF.uniformOfFintype α).bind fun a => PMF.pure (decide (a = a₀))) true =
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [PMF.bind_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply, PMF.pure_apply, eq_comm (a := true)]
  have hle₁ :
      ((PMF.uniformOfFintype α).bind g) true ≤ p true + (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [← PMF.bind_const (PMF.uniformOfFintype α) p, ← hsingle, PMF.bind_apply, PMF.bind_apply,
      PMF.bind_apply, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    by_cases ha : a = a₀
    · simp only [ha, decide_true, PMF.pure_apply, ↓reduceIte]
      exact (PMF.coe_le_one _ _).trans le_add_self
    · simp [hne a ha, ha]
  have hle₂ :
      p true ≤ ((PMF.uniformOfFintype α).bind g) true + (Fintype.card α : ℝ≥0∞)⁻¹ := by
    nth_rw 1 [← PMF.bind_const (PMF.uniformOfFintype α) p]
    rw [← hsingle, PMF.bind_apply, PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    by_cases ha : a = a₀
    · simp only [ha, decide_true, PMF.pure_apply, ↓reduceIte]
      exact (PMF.coe_le_one _ _).trans le_add_self
    · simp [hne a ha, ha]
  have hinv_ne_top : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hadv := Game.advantage_le_of_apply_le hinv_ne_top hle₁ hle₂
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, ← NNReal.coe_natCast, ← NNReal.coe_inv] at hadv
  exact NNReal.coe_le_coe.mp hadv

end Game
end Cslib.Crypto
