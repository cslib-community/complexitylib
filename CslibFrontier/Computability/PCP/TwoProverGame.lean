/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.CorrelatedSampling.Embeddability
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product.Event
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.StatisticalDistance.Event

/-!
# Two-prover one-round games

A *two-prover one-round game* [Holenstein, Definition 2.2][Holenstein2009] draws a pair of questions
`(x, y)` from a distribution on `X × Y`, sends `x` to Alice and `y` to Bob, and accepts their
answers `a` and `b` according to a predicate `Q x y a b`. Its *value* is the largest winning
probability of a pair of deterministic strategies `X → A` and `Y → B`
(`Cslib.PCP.TwoProverGame.value`). Shared randomness does not help
(`winProb_shared_le_value`) [Holenstein, (2.5)][Holenstein2009]. The `n`-fold *parallel repetition*
asks `n` independent pairs of questions at once and accepts when every coordinate is accepted
(`Cslib.PCP.TwoProverGame.pow`) [Holenstein, Definition 2.3][Holenstein2009]. Answering each
coordinate independently with an optimal strategy shows `value G ^ n ≤ value (G.pow n)`
(`pow_value_le_value_pow`); the parallel repetition theorem bounds `value (G.pow n)` from above
(`value_pow_le`, in `CslibFrontier/Computability/PCP/ParallelRepetition.lean`).

For a pair of strategies of the repetition, `winsOn` is the event that every coordinate in a set
`C` is won [Holenstein, Definition 2.4][Holenstein2009] and `winProbOn` its probability. If the
questions of `G` embed with error `ε` in the law of `((x_j, y_j), (x, y))`, for questions `(x, y)`
of the repetition conditioned on winning `C`, then Alice and Bob can play `G` by running the
embedding and answering at coordinate `j`. So coordinate `j` is won given `C` with probability at
most `v(G) + ε` (`winProbOn_insert_le`). This is the step of
[Holenstein, proof of Lemma 6.5][Holenstein2009] that extracts a strategy.

## Main definitions

* `Cslib.PCP.TwoProverGame`: a two-prover one-round game.
* `Cslib.PCP.TwoProverGame.winProb`, `Cslib.PCP.TwoProverGame.value`: winning probability and value.
* `Cslib.PCP.TwoProverGame.pow`: parallel repetition.
* `Cslib.PCP.TwoProverGame.winsOn`, `Cslib.PCP.TwoProverGame.winProbOn`: winning a set of
  coordinates of the repetition, and its probability.

## Main results

* `Cslib.PCP.TwoProverGame.winProb_le_value`, `Cslib.PCP.TwoProverGame.exists_winProb_eq_value`:
  the value is attained by a deterministic strategy.
* `Cslib.PCP.TwoProverGame.winProb_shared_le_value`: shared randomness does not help.
* `Cslib.PCP.TwoProverGame.pow_value_le_value_pow`: `value G ^ n ≤ value (G.pow n)`.
* `Cslib.PCP.TwoProverGame.toOuterMeasure_accepts_le_value_add`: an embedding of the questions
  gives a strategy.
* `Cslib.PCP.TwoProverGame.winProbOn_insert_le`: strategy extraction for the repetition,
  `Pr[W_C ∧ W_j] ≤ Pr[W_C] (v(G) + ε)`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.PCP

/-- A **two-prover one-round game** [Holenstein, Definition 2.2][Holenstein2009]: questions drawn
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

theorem winProb_le_one (ha : X → A) (hb : Y → B) : G.winProb ha hb ≤ 1 :=
  Cslib.Probability.PMF.toOuterMeasure_toReal_le_one _ _

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

/-- **Shared randomness does not help** [Holenstein, (2.5)][Holenstein2009]: strategies that read a
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

/-- The **`n`-fold parallel repetition** [Holenstein, Definition 2.3][Holenstein2009]: `n`
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

/-! ### Winning a set of coordinates -/

section Coordinates

variable {n : ℕ} (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B)

/-- The event `⋀_{i ∈ C} W_i` [Holenstein, Definition 2.4][Holenstein2009] that the strategies `ha`
and `hb` of the `n`-fold repetition win every coordinate in `C`. -/
def winsOn (C : Finset (Fin n)) : Set ((Fin n → X) × (Fin n → Y)) :=
  {(x, y) : (Fin n → X) × (Fin n → Y) | ∀ i ∈ C, G.accepts (x i) (y i) (ha x i) (hb y i)}

/-- Every question wins the empty set of coordinates. -/
@[simp] theorem winsOn_empty : G.winsOn ha hb ∅ = Set.univ := by
  ext ⟨x, y⟩
  simp [winsOn]

/-- Winning `C ∪ D` is winning `C` and winning `D`. -/
theorem winsOn_union (C D : Finset (Fin n)) :
    G.winsOn ha hb (C ∪ D) = G.winsOn ha hb C ∩ G.winsOn ha hb D := by
  ext ⟨x, y⟩
  simp only [winsOn, Finset.mem_union, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩,
    fun h i hi => hi.elim (h.1 i) (h.2 i)⟩

/-- Winning more coordinates is a smaller event. -/
theorem winsOn_anti : Antitone (G.winsOn ha hb) :=
  fun _ _ hCD _ hw i hi => hw i (hCD hi)

/-- Winning every coordinate is winning the repeated game. -/
theorem winsOn_univ [Finite X] [Finite Y] :
    G.winsOn ha hb Finset.univ =
      {(x, y) : (Fin n → X) × (Fin n → Y) | (G.pow n).accepts x y (ha x) (hb y)} := by
  ext ⟨x, y⟩
  simp [winsOn, pow]

variable [Finite X] [Finite Y]

/-- The probability `Pr[⋀_{i ∈ C} W_i]` that the strategies `ha` and `hb` of the `n`-fold
repetition win every coordinate in `C`. -/
noncomputable def winProbOn (C : Finset (Fin n)) : ℝ :=
  ((G.pow n).questions.toOuterMeasure (G.winsOn ha hb C)).toReal

/-- The empty set of coordinates is won with probability one. -/
@[simp] theorem winProbOn_empty : G.winProbOn ha hb ∅ = 1 := by
  rw [winProbOn, winsOn_empty,
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _), ENNReal.toReal_one]

/-- Winning every coordinate has the winning probability of the repeated game. -/
theorem winProbOn_univ : G.winProbOn ha hb Finset.univ = (G.pow n).winProb ha hb := by
  rw [winProbOn, winsOn_univ, winProb]

/-- Winning probabilities are nonnegative. -/
theorem winProbOn_nonneg (C : Finset (Fin n)) : 0 ≤ G.winProbOn ha hb C := ENNReal.toReal_nonneg

/-- Winning more coordinates is less likely. -/
theorem winProbOn_anti : Antitone (G.winProbOn ha hb) := fun _ _ hCD =>
  Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ (G.winsOn_anti ha hb hCD)

end Coordinates

/-! ### Strategies from embeddings -/

section Embedding

open Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

variable [Fintype X] [Fintype Y] [Finite A] [Finite B] [Nonempty A] [Nonempty B]

/-- **A strategy from an embedding** [Holenstein, proof of Lemma 6.5][Holenstein2009]. Suppose the
questions of `G` embed with error `ε` in a law `L` of `((x, y), (s, t))`, and `α` and `β` turn the
outputs into answers. Then the answers `α s` and `β t` are accepted with probability at most
`v(G) + ε` under `L`: Alice and Bob can run the embedding on their questions and answer `α s` and
`β t`, and shared randomness does not help. -/
theorem toOuterMeasure_accepts_le_value_add {S T : Type*} [Fintype S] [Fintype T]
    {L : PMF ((X × Y) × (S × T))} {ε : ℝ} (hL : IsEmbeddable G.questions L ε) (α : S → A)
    (β : T → B) :
    (L.toOuterMeasure {((x, y), (s, t)) : (X × Y) × (S × T) | G.accepts x y (α s) (β t)}).toReal ≤
      G.value + ε := by
  obtain ⟨R, ρ, fA, fB, hd⟩ := hL
  set E := {((x, y), (s, t)) : (X × Y) × (S × T) | G.accepts x y (α s) (β t)}
  set M := G.questions.bind fun xy => ρ.map fun r => (xy, (fA xy.1 r, fB xy.2 r))
  -- Under the embedding, the answers are those of a strategy with shared randomness.
  have hM : M.map (fun w => (w.1, α w.2.1, β w.2.2)) =
      ρ.bind fun r => G.questions.map fun q => (q, α (fA q.1 r), β (fB q.2 r)) := by
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    simp only [← PMF.bind_pure_comp, Function.comp_def]
    exact PMF.bind_comm _ _ _
  have hshared : (M.toOuterMeasure E).toReal ≤ G.value := by
    have h := G.winProb_shared_le_value ρ (fun x r => α (fA x r)) (fun y r => β (fB y r))
    rwa [← hM, PMF.toOuterMeasure_map_apply] at h
  have habs := Cslib.Probability.PMF.abs_toOuterMeasure_toReal_sub_le_dist L M E
  rw [dist_comm] at habs
  linarith [le_abs_self ((L.toOuterMeasure E).toReal - (M.toOuterMeasure E).toReal)]

/-- **Strategy extraction** [Holenstein, proof of Lemma 6.5][Holenstein2009], multiplied out so
that it never divides by `Pr[W_C]`. Condition the questions `(x, y)` of the `n`-fold repetition on
winning every coordinate in `C`. If the questions of `G` embed with error `ε` in the conditioned
law of `((x j, y j), (x, y))`, then coordinate `j` is won given `W_C` with probability at most
`v(G) + ε`: `Pr[W_C ∧ W_j] ≤ Pr[W_C] (v(G) + ε)`. -/
theorem winProbOn_insert_le {n : ℕ} (ha : (Fin n → X) → Fin n → A)
    (hb : (Fin n → Y) → Fin n → B) (C : Finset (Fin n)) (j : Fin n)
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) {ε : ℝ}
    (hε : IsEmbeddable G.questions
      (((G.pow n).questions.filter (G.winsOn ha hb C) hC).map fun (x, y) => ((x j, y j), (x, y)))
      ε) :
    G.winProbOn ha hb (insert j C) ≤ G.winProbOn ha hb C * (G.value + ε) := by
  have hext := G.toOuterMeasure_accepts_le_value_add hε (fun x => ha x j) (fun y => hb y j)
  rw [PMF.toOuterMeasure_map_apply] at hext
  have hpre : ((fun (x, y) => ((x j, y j), (x, y))) ⁻¹'
      {((x, y), (s, t)) : (X × Y) × ((Fin n → X) × (Fin n → Y)) |
        G.accepts x y (ha s j) (hb t j)}) = G.winsOn ha hb {j} := by
    ext ⟨x, y⟩
    simp [winsOn]
  rw [hpre] at hext
  rw [winProbOn, winProbOn, Finset.insert_eq, winsOn_union, Set.inter_comm,
    ← Cslib.Probability.PMF.toOuterMeasure_filter_mul_eq_inter _ _ _ hC, ENNReal.toReal_mul,
    mul_comm]
  exact mul_le_mul_of_nonneg_left hext ENNReal.toReal_nonneg

end Embedding

end TwoProverGame

end Cslib.PCP
