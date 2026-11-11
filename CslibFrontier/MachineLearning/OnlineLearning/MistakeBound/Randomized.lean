/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Hedge
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Randomized online learners and Hedge over deterministic experts

Outside the realizable case, no deterministic learner can compete with the best concept of even a
two-element class (`exists_mistakes_eq_length_of_const_mem` in `MistakeBound.Agnostic`), so the
learner randomizes. A randomized learner `RandomizedLearner α` maps the labelled history and the
current instance to the law `PMF Bool` of its prediction. The adversary is *oblivious*: it fixes
the labelled sequence `S` in advance, as in [BenDavidPalShalevShwartz2009, §6].
`expectedMistakes A S` is the sum over the rounds of `S` of the probability that the prediction is
wrong. By linearity of expectation this is the expected number of mistakes of any learner whose
round-`t` prediction, given the history, has the law `A (S.take t) S[t].1`. The learner's own
earlier coin flips need not be modelled, since against an oblivious adversary only these marginal
laws matter. A deterministic learner is the special case `OnlineLearner.toRandomized`
(`expectedMistakes_toRandomized`).

`hedgeLearner η E` runs Hedge [FreundSchapire1997] with learning rate `η` over a finite family of
deterministic learners `E : ι → OnlineLearner α`, with the 0-1 mistake indicators as losses. In
each round it draws an expert from the distribution `Experts.prob (Experts.hedgeFactor η)` of the
experts-setting core `OnlineLearning.MultiplicativeUpdate` and predicts as that expert does. The
losses of earlier rounds are recomputed from the history, so the learner is a genuine online
learner. `expectedMistakes_hedgeLearner` identifies its expected mistakes with Hedge's expected
loss, and `expectedMistakes_hedgeLearner_le` transfers the tuned regret bound
`Experts.hedge_regret_le_sqrt`: on every sequence of at most `T` rounds, with `log N ≤ T` for `N`
experts, the expected mistakes exceed those of every expert by at most `2 √(T log N)`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.RandomizedLearner`: randomized online
  learners.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.expectedMistakes`: the expected number of
  mistakes on a fixed labelled sequence.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.hedgeLearner`: Hedge over deterministic
  experts.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.expectedMistakes_toRandomized`: deterministic
  learners have `expectedMistakes = mistakes`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.expectedMistakes_hedgeLearner_le`: the regret
  of Hedge against every expert is at most `2 √(T log N)`.

## References

* [S. Ben-David, D. Pál, S. Shalev-Shwartz, *Agnostic online
  learning*][BenDavidPalShalevShwartz2009]
* [Y. Freund, R. E. Schapire, *A decision-theoretic generalization of on-line learning and an
  application to boosting*][FreundSchapire1997]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open Finset

variable {α : Type*}

/-! ### Randomized learners -/

/-- A randomized online learner: after the labelled history `h`, the law of its prediction on the
instance `x`. -/
abbrev RandomizedLearner (α : Type*) := List (α × Bool) → α → PMF Bool

/-- The expected number of mistakes of the randomized learner `A` on the labelled sequence `S`,
fixed in advance: the sum over the rounds of the probability of predicting the wrong label. -/
noncomputable def expectedMistakes (A : RandomizedLearner α) (S : List (α × Bool)) : ℝ :=
  ∑ t : Fin S.length, (A (S.take t) S[t].1 (!S[t].2)).toReal

/-- A deterministic learner as a randomized learner. -/
noncomputable def OnlineLearner.toRandomized (A : OnlineLearner α) : RandomizedLearner α :=
  fun h x => PMF.pure (A h x)

theorem expectedMistakes_toRandomized (A : OnlineLearner α) (S : List (α × Bool)) :
    expectedMistakes A.toRandomized S = mistakes A S := by
  rw [expectedMistakes, mistakes_eq_card, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [OnlineLearner.toRandomized, PMF.pure_apply]
  cases A (S.take t) S[t].1 <;> cases S[t].2 <;> simp

/-! ### Hedge over deterministic experts -/

variable {ι : Type*}

/-- The 0-1 loss of the expert `E i` in round `t` of `S`, and `0` after the end of `S`. -/
noncomputable def expertLoss (E : ι → OnlineLearner α) (S : List (α × Bool)) (t : ℕ) (i : ι) :
    ℝ :=
  if h : t < S.length then (if E i (S.take t) S[t].1 = S[t].2 then 0 else 1) else 0

/-- The loss of round `s` depends only on the first `t > s` rounds. -/
theorem expertLoss_take {E : ι → OnlineLearner α} {S : List (α × Bool)} {t s : ℕ} (hs : s < t) :
    expertLoss E (S.take t) s = expertLoss E S s := by
  funext i
  simp only [expertLoss, List.length_take, List.take_take, List.getElem_take]
  by_cases h : s < S.length
  · rw [dite_eq_left (lt_min hs h), dite_eq_left h, min_eq_left hs.le]
  · rw [dite_eq_right (fun h' => h (lt_of_lt_of_le h' (min_le_right _ _))), dite_eq_right h]

/-- The mistakes of an expert are the sum of its losses. -/
theorem mistakes_eq_sum_expertLoss (E : ι → OnlineLearner α) (S : List (α × Bool)) (i : ι) :
    (mistakes (E i) S : ℝ) = ∑ t ∈ range S.length, expertLoss E S t i := by
  rw [mistakes_eq_card, Finset.card_filter, Finset.sum_range]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [expertLoss, dite_eq_left t.2]
  split_ifs <;> simp_all

variable [Fintype ι]

private theorem hedgeFactor_pos (η x : ℝ) : 0 < Experts.hedgeFactor η x := by
  rw [Experts.hedgeFactor_apply]
  exact Real.exp_pos _

theorem sum_ofReal_prob_hedgeFactor [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i, ENNReal.ofReal (Experts.prob (Experts.hedgeFactor η) ℓ t i) = 1 := by
  have hpos : ∀ s < t, ∀ i, 0 < Experts.hedgeFactor η (ℓ s i) := fun _ _ _ => hedgeFactor_pos _ _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Experts.prob_nonneg hpos i),
    Experts.sum_prob hpos, ENNReal.ofReal_one]

/-- **Hedge over deterministic experts** with learning rate `η`: after the history `h`, draw the
expert `i` with Hedge's probability for the 0-1 losses of the experts on `h`, and predict as `E i`
does. -/
noncomputable def hedgeLearner [Nonempty ι] (η : ℝ) (E : ι → OnlineLearner α) :
    RandomizedLearner α := fun h x =>
  (PMF.ofFintype (fun i => ENNReal.ofReal
      (Experts.prob (Experts.hedgeFactor η) (expertLoss E h) h.length i))
    (sum_ofReal_prob_hedgeFactor η _ _)).map fun i => E i h x

/-- The probability that Hedge predicts `b` is the total weight of the experts that predict `b`. -/
theorem toReal_hedgeLearner_apply [Nonempty ι] (η : ℝ) (E : ι → OnlineLearner α)
    (h : List (α × Bool)) (x : α) (b : Bool) :
    (hedgeLearner η E h x b).toReal =
      ∑ i, if E i h x = b then Experts.prob (Experts.hedgeFactor η) (expertLoss E h) h.length i
        else 0 := by
  have hpos : ∀ s < h.length, ∀ i, 0 < Experts.hedgeFactor η (expertLoss E h s i) :=
    fun _ _ _ => hedgeFactor_pos _ _
  rw [hedgeLearner, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hb : E i h x = b
    · rw [ite_eq_left hb.symm, ite_eq_left hb, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (Experts.prob_nonneg hpos i)]
    · rw [ite_eq_right (Ne.symm hb), ite_eq_right hb, ENNReal.toReal_zero]
  · intro i _
    split <;> simp

/-- The expected mistakes of Hedge are its expected loss in the experts setting. -/
theorem expectedMistakes_hedgeLearner [Nonempty ι] (η : ℝ) (E : ι → OnlineLearner α)
    (S : List (α × Bool)) :
    expectedMistakes (hedgeLearner η E) S =
      ∑ t ∈ range S.length, ∑ i, Experts.prob (Experts.hedgeFactor η) (expertLoss E S) t i *
        expertLoss E S t i := by
  rw [expectedMistakes, Finset.sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [toReal_hedgeLearner_apply]
  have hlen : (S.take t).length = t := List.length_take_of_le t.2.le
  rw [hlen, Experts.prob_congr (fun s hs => expertLoss_take (S := S) hs)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [expertLoss, dite_eq_left t.2]
  cases E i (S.take t) S[t].1 <;> cases S[t].2 <;> simp

/-- **Regret of Hedge over deterministic experts.** For `N` experts and a horizon `T` with
`log N ≤ T`, on every labelled sequence of at most `T` rounds, Hedge with learning rate
`√(log N / T)` makes at most `mistakes (E i) S + 2 √(T log N)` expected mistakes, for every expert
`i`. -/
theorem expectedMistakes_hedgeLearner_le [Nonempty ι] (E : ι → OnlineLearner α) {T : ℕ}
    (hT : Real.log (Fintype.card ι) ≤ T) (S : List (α × Bool)) (hS : S.length ≤ T) (i : ι) :
    expectedMistakes (hedgeLearner (√(Real.log (Fintype.card ι) / T)) E) S ≤
      mistakes (E i) S + 2 * √(T * Real.log (Fintype.card ι)) := by
  have hpad : ∀ f : ℕ → ℝ, (∀ t, S.length ≤ t → f t = 0) →
      ∑ t ∈ range S.length, f t = ∑ t ∈ range T, f t := fun f hf =>
    Finset.sum_subset (Finset.range_subset_range.mpr hS) fun t _ ht =>
      hf t (by simpa using ht)
  have hzero : ∀ t, S.length ≤ t → ∀ j, expertLoss E S t j = 0 := fun t ht j => by
    simp [expertLoss, not_lt.mpr ht]
  rw [expectedMistakes_hedgeLearner, mistakes_eq_sum_expertLoss,
    hpad _ fun t ht => by simp [hzero t ht], hpad _ fun t ht => hzero t ht i]
  have hloss : ∀ s < T, ∀ j, |expertLoss E S s j| ≤ 1 := fun s _ j => by
    unfold expertLoss
    split_ifs <;> simp
  rcases Nat.lt_or_eq_of_le (Fintype.card_pos (α := ι)) with h2 | h1
  · exact Experts.hedge_regret_le_sqrt (by omega) hT hloss i
  · -- A single expert: Hedge follows it.
    have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp h1.symm.le
    have hp : ∀ η t j, Experts.prob (Experts.hedgeFactor η) (expertLoss E S) t j = 1 :=
      fun η t j => by
      have := Experts.sum_prob (ι := ι) (φ := Experts.hedgeFactor η) (ℓ := expertLoss E S)
        (t := t) fun _ _ _ => hedgeFactor_pos _ _
      rwa [Fintype.sum_subsingleton _ j] at this
    have hlog : Real.log (Fintype.card ι) = 0 := by
      rw [← h1, Nat.cast_one, Real.log_one]
    rw [hlog, mul_zero, Real.sqrt_zero, mul_zero, add_zero]
    exact le_of_eq (Finset.sum_congr rfl fun t _ => by
      rw [Fintype.sum_subsingleton _ i, hp, one_mul])

end Cslib.MachineLearning.OnlineLearning.MistakeBound
