/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
import Complexity.Probability.PMF.Event

/-!
# Two-prover one-round games

A *two-prover one-round game* [Holenstein, Definition 1][Holenstein2009] draws a pair of questions
`(x, y)` from a distribution on `X × Y`, sends `x` to Alice and `y` to Bob, and accepts their
answers `a` and `b` according to a predicate `Q x y a b`. Its *value* is the largest winning
probability of a pair of deterministic strategies `X → A` and `Y → B`
(`Cslib.PCP.TwoProverGame.value`). Shared randomness does not help
(`winProb_shared_le_value`) [Holenstein, (3)][Holenstein2009]. The `n`-fold *parallel repetition*
asks `n` independent pairs of questions at once and accepts when every coordinate is accepted
(`Cslib.PCP.TwoProverGame.pow`) [Holenstein, Definition 2][Holenstein2009]. Answering each
coordinate independently with an optimal strategy shows `value G ^ n ≤ value (G.pow n)`
(`pow_value_le_value_pow`); the parallel repetition theorem bounds `value (G.pow n)` from above.

## Main definitions

* `Cslib.PCP.TwoProverGame`: a two-prover one-round game.
* `Cslib.PCP.TwoProverGame.winProb`, `Cslib.PCP.TwoProverGame.value`: winning probability and value.
* `Cslib.PCP.TwoProverGame.pow`: parallel repetition.

## Main results

* `Cslib.PCP.TwoProverGame.winProb_le_value`, `Cslib.PCP.TwoProverGame.exists_winProb_eq_value`:
  the value is attained by a deterministic strategy.
* `Cslib.PCP.TwoProverGame.winProb_shared_le_value`: shared randomness does not help.
* `Cslib.PCP.TwoProverGame.pow_value_le_value_pow`: `value G ^ n ≤ value (G.pow n)`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.PCP

/-- A **two-prover one-round game** [Holenstein, Definition 1][Holenstein2009]: questions drawn
from `questions`, answers accepted by `accepts`. -/
structure TwoProverGame (X Y A B : Type*) where
  /-- The distribution of the pair of questions. -/
  questions : PMF (X × Y)
  /-- The acceptance predicate on questions and answers. -/
  accepts : X → Y → A → B → Prop

namespace TwoProverGame

variable {X Y A B : Type*} (G : TwoProverGame X Y A B)

/-- The probability that the deterministic strategies `ha` and `hb` win. -/
noncomputable def winProb (ha : X → A) (hb : Y → B) : ℝ :=
  (G.questions.toOuterMeasure {q | G.accepts q.1 q.2 (ha q.1) (hb q.2)}).toReal

/-- The **value** of a game: the largest winning probability of deterministic strategies. -/
noncomputable def value : ℝ := ⨆ (ha : X → A) (hb : Y → B), G.winProb ha hb

theorem winProb_nonneg (ha : X → A) (hb : Y → B) : 0 ≤ G.winProb ha hb := ENNReal.toReal_nonneg

theorem winProb_le_one (ha : X → A) (hb : Y → B) : G.winProb ha hb ≤ 1 := by
  simpa [winProb] using
    ENNReal.toReal_mono ENNReal.one_ne_top (Cslib.Probability.PMF.toOuterMeasure_le_one _ _)

section Finite

variable [Finite X] [Finite Y] [Finite A] [Finite B]

omit [Finite X] [Finite A] in
private theorem bddAbove_range_winProb (ha : X → A) : BddAbove (Set.range (G.winProb ha)) :=
  (Set.finite_range _).bddAbove

omit [Finite Y] [Finite B] in
private theorem bddAbove_range_iSup :
    BddAbove (Set.range fun ha : X → A => ⨆ hb : Y → B, G.winProb ha hb) :=
  (Set.finite_range _).bddAbove

theorem winProb_le_value (ha : X → A) (hb : Y → B) : G.winProb ha hb ≤ G.value :=
  (le_ciSup (G.bddAbove_range_winProb ha) hb).trans (le_ciSup G.bddAbove_range_iSup ha)

theorem exists_winProb_eq_value [Nonempty A] [Nonempty B] :
    ∃ (ha : X → A) (hb : Y → B), G.winProb ha hb = G.value := by
  obtain ⟨ha, hha⟩ := exists_eq_ciSup_of_finite (f := fun ha : X → A => ⨆ hb, G.winProb ha hb)
  obtain ⟨hb, hhb⟩ := exists_eq_ciSup_of_finite (f := G.winProb ha)
  exact ⟨ha, hb, hhb.trans hha⟩

theorem value_nonneg [Nonempty A] [Nonempty B] : 0 ≤ G.value := by
  obtain ⟨ha, hb, h⟩ := G.exists_winProb_eq_value
  exact h ▸ G.winProb_nonneg ha hb

theorem value_le_one [Nonempty A] [Nonempty B] : G.value ≤ 1 := by
  obtain ⟨ha, hb, h⟩ := G.exists_winProb_eq_value
  exact h ▸ G.winProb_le_one ha hb

/-- **Shared randomness does not help** [Holenstein, (3)][Holenstein2009]: strategies that read a
common random string `r` drawn from `ρ` win with probability at most the value. -/
theorem winProb_shared_le_value [Nonempty A] [Nonempty B] {R : Type*} (ρ : PMF R)
    (ha : X → R → A) (hb : Y → R → B) :
    ((ρ.bind fun r => G.questions.map fun q => (q, ha q.1 r, hb q.2 r)).toOuterMeasure
        {z | G.accepts z.1.1 z.1.2 z.2.1 z.2.2}).toReal ≤ G.value := by
  refine ENNReal.toReal_le_of_le_ofReal G.value_nonneg ?_
  rw [PMF.toOuterMeasure_bind_apply]
  have hr : ∀ r, (G.questions.map fun q => (q, ha q.1 r, hb q.2 r)).toOuterMeasure
      {z | G.accepts z.1.1 z.1.2 z.2.1 z.2.2} ≤ ENNReal.ofReal G.value := by
    intro r
    rw [PMF.toOuterMeasure_map_apply,
      ← ENNReal.ofReal_toReal (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (G.winProb_le_value (fun x => ha x r) (fun y => hb y r))
  calc ∑' r, ρ r * (G.questions.map fun q => (q, ha q.1 r, hb q.2 r)).toOuterMeasure
        {z | G.accepts z.1.1 z.1.2 z.2.1 z.2.2}
      ≤ ∑' r, ρ r * ENNReal.ofReal G.value := tsum_le_tsum fun r => by gcongr; exact hr r
    _ = ENNReal.ofReal G.value := by rw [ENNReal.tsum_mul_right, ρ.tsum_coe, one_mul]

end Finite

/-! ### Parallel repetition -/

/-- The probability that every coordinate of an independent tuple lies in its own event is the
product of the probabilities. -/
theorem _root_.Cslib.Probability.PMF.toOuterMeasure_pi_forall {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Finite (α i)] (p : ∀ i, PMF (α i)) (E : ∀ i, Set (α i)) :
    (Probability.PMF.pi p).toOuterMeasure {u | ∀ i, u i ∈ E i} =
      ∏ i, (p i).toOuterMeasure (E i) := by
  classical
  have := fun i => Fintype.ofFinite (α i)
  simp only [PMF.toOuterMeasure_apply, tsum_fintype, Set.indicator_apply, Set.mem_ofPred_eq,
    Probability.PMF.pi_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : ∀ i, u i ∈ E i
  · rw [ite_eq_left hu]
    exact Finset.prod_congr rfl fun i _ => (ite_eq_left (hu i)).symm
  · rw [ite_eq_right hu]
    push Not at hu
    obtain ⟨i, hi⟩ := hu
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

/-- The **`n`-fold parallel repetition** [Holenstein, Definition 2][Holenstein2009]: `n`
independent pairs of questions, accepted when every coordinate is accepted. -/
noncomputable def pow [Finite X] [Finite Y] (n : ℕ) :
    TwoProverGame (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questions := (Probability.PMF.pi fun _ : Fin n => G.questions).map
    fun q => (fun i => (q i).1, fun i => (q i).2)
  accepts x y a b := ∀ i, G.accepts (x i) (y i) (a i) (b i)

/-- Answering each coordinate independently wins with the product of the probabilities. -/
theorem winProb_pow [Finite X] [Finite Y] (n : ℕ) (ha : X → A) (hb : Y → B) :
    (G.pow n).winProb (fun x i => ha (x i)) (fun y i => hb (y i)) = G.winProb ha hb ^ n := by
  rw [winProb, winProb, pow, PMF.toOuterMeasure_map_apply]
  have := Cslib.Probability.PMF.toOuterMeasure_pi_forall (fun _ : Fin n => G.questions)
    fun _ => {q | G.accepts q.1 q.2 (ha q.1) (hb q.2)}
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [← ENNReal.toReal_pow, ← this]
  rfl

/-- Answering each coordinate independently with an optimal strategy shows that parallel
repetition cannot lower the value below `value G ^ n`. -/
theorem pow_value_le_value_pow [Finite X] [Finite Y] [Finite A] [Finite B] [Nonempty A]
    [Nonempty B] (n : ℕ) : G.value ^ n ≤ (G.pow n).value := by
  obtain ⟨ha, hb, h⟩ := G.exists_winProb_eq_value
  rw [← h, ← G.winProb_pow n ha hb]
  exact (G.pow n).winProb_le_value _ _

end TwoProverGame

end Cslib.PCP
