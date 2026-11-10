/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.StatisticalQuery.Basic
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import CslibFrontier.MachineLearning.StatisticalQuery.LowerBound
import CslibFrontier.Probability.PMF
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.TFAE

/-!
# The statistical query dimension characterizes weak learning

The statistical query dimension `sqDim D C` of a concept class `C` under a distribution `D` is the
largest `d` such that `C` contains `d` concepts whose pairwise correlations under `D` have absolute
value at most `1 / d` [Reyzin, Definition 11][Reyzin2020]. [BlumEtAl1994, Definition 2] uses the
threshold `1 / d ^ 3` instead; its dimension `d₃` and this one `d₁` satisfy
`d₃ ≤ d₁ < (d₃ + 1) ^ 3`, so polynomial boundedness does not depend on the normalization. The
one-sided variant `sqDimOneSided D C` bounds the correlations only from above,
`corr D f g ≤ 1 / d`. This is the hypothesis that Szörényi's argument for the lower bound of
[Reyzin, Theorem 12][Reyzin2020] uses. It is at least `sqDim D C` (`sqDim_le_sqDimOneSided`) and at
most `18 (sqDim D C + 1) ^ 3` (`sqDimOneSided_le`), so the two notions are polynomially related.
The dimension controls weak learning from statistical queries [BlumEtAl1994, §5]:

* **Lower bound.** A learner using `q` queries of tolerance `τ` whose hypotheses have correlation
  at least `τ` with the target (`1 - 2 ε ≥ τ`) has `sqDimOneSided D C · τ ^ 2 ≤ 2 q + 2`
  (`LearnsStateless.sqDimOneSided_mul_sq_le`), hence `sqDim D C · τ ^ 2 ≤ 2 q + 2`
  (`LearnsStateless.sqDim_mul_sq_le`), from the bound of
  `CslibFrontier/MachineLearning/StatisticalQuery/LowerBound.lean`. This is one weaker than the
  count `d τ ^ 2 ≤ 2 q + 1` of [Reyzin, Theorem 12][Reyzin2020]: a hypothesis with error `ε > 0`
  may correlate with one more concept of the family.
* **Upper bound.** For `d = sqDim D C` there is a learner making at most `d` queries, each a
  correlational query `E_D [g (x) · y]` (in `±1` values) for a concept `g ∈ C`, that learns `C`
  under `D` with tolerance `τ` and error `1/2 - 1/(2 (d + 1)) + τ`, for every `τ`
  (`exists_learns_sqDim`). This is [Reyzin, Observation 23][Reyzin2020], the analogue of
  [BlumEtAl1994, Theorem 13] for the threshold `1 / d`.
* **Characterization.** For a sequence of classes `C n` under distributions `D n`, `sqDim (D n)
  (C n)` is polynomially bounded if and only if `sqDimOneSided (D n) (C n)` is, if and only if
  `C n` is weakly learnable from polynomially many statistical queries of inverse-polynomial
  tolerance with inverse-polynomial advantage over `1/2`, if and only if this holds with
  correlational queries (`tfae_polynomiallyBounded_sqDim`).

The upper bound uses a family `G ⊆ C` of maximum size whose pairwise correlations have absolute
value at most `1 / (d + 1)`. It has at most `d` members, since otherwise `d + 1` of them would
witness `sqDim D C ≥ d + 1`, and every `c ∈ C` has correlation of absolute value more than
`1 / (d + 1)` with some member of `G`, since otherwise `G ∪ {c}` would be a larger such family
(`exists_cover_sqDim`). The learner `corrLearner` asks for the correlation of the target with each
member of `G`, takes the member `g` whose answer has the largest absolute value, and returns `g` if
that answer is nonnegative and the negation of `g` otherwise. Its hypothesis has correlation more
than `1 / (d + 1) - 2 τ` with the target; it need not lie in `C`. Reyzin's sketch of
Observation 23 takes the family that realizes the dimension, at threshold `1 / d`; we choose the
family at threshold `1 / (d + 1)`, which gives the correlation bound the argument needs.

All learners here are deterministic and the bounds count queries only, not running time. The
domain `X` is finite and the distribution `D` is fixed and known to the learner.

## Main definitions

* `Cslib.MachineLearning.StatisticalQuery.sqDim`: the statistical query dimension.
* `Cslib.MachineLearning.StatisticalQuery.sqDimOneSided`: its one-sided variant.
* `Cslib.MachineLearning.StatisticalQuery.corrQuery`: the correlational query of a concept.
* `Cslib.MachineLearning.StatisticalQuery.askCorr`: ask one correlational query.
* `Cslib.MachineLearning.StatisticalQuery.corrHypothesis`: the concept, or its negation, with the
  answer of largest absolute value.
* `Cslib.MachineLearning.StatisticalQuery.corrLearner`: ask the correlations with a list of
  concepts and return the best one or its negation.

## Main results

* `Cslib.MachineLearning.StatisticalQuery.exists_finset_card_eq_sqDim`,
  `Cslib.MachineLearning.StatisticalQuery.le_sqDim`,
  `Cslib.MachineLearning.StatisticalQuery.sqDim_le_ncard`: the dimension is attained and bounded
  by the size of the class.
* `Cslib.MachineLearning.StatisticalQuery.exists_cover_sqDim`: at most `sqDim D C` concepts of `C`
  cover `C` with correlations of absolute value more than `1 / (sqDim D C + 1)`.
* `Cslib.MachineLearning.StatisticalQuery.isQueryBounded_corrLearner`,
  `Cslib.MachineLearning.StatisticalQuery.queriesSatisfy_corrLearner`,
  `Cslib.MachineLearning.StatisticalQuery.learns_corrLearner`: the correlational learner makes one
  correlational query per concept and learns a covered class.
* `Cslib.MachineLearning.StatisticalQuery.exists_learns_sqDim`: the weak learner from the
  statistical query dimension.
* `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.sqDimOneSided_mul_sq_le`,
  `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.sqDim_mul_sq_le`: the lower bounds.
* `Cslib.MachineLearning.StatisticalQuery.sqDim_le_sqDimOneSided`,
  `Cslib.MachineLearning.StatisticalQuery.sqDimOneSided_le`: the two dimensions are polynomially
  related.
* `Cslib.MachineLearning.StatisticalQuery.tfae_polynomiallyBounded_sqDim`: the characterization of
  weak learning.

## References

* [A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour, S. Rudich, *Weakly learning DNF and
  characterizing statistical query learning using Fourier analysis*][BlumEtAl1994]
* [L. Reyzin, *Statistical queries and statistical algorithms: foundations and
  applications*][Reyzin2020]
-/

public section

namespace Cslib.MachineLearning.StatisticalQuery

open Finset

variable {X : Type} [Fintype X]

/-! ### The statistical query dimension -/

/-- The **statistical query dimension** of `C` under `D`: the largest `d` such that `C` contains
`d` distinct concepts whose pairwise correlations under `D` have absolute value at most `1 / d`
[Reyzin, Definition 11][Reyzin2020], for a fixed distribution.

[BlumEtAl1994, Definition 2] uses the threshold `1 / d ^ 3` instead. Its dimension `d₃` and this
one `d₁` satisfy `d₃ ≤ d₁ < (d₃ + 1) ^ 3`. A `d₃`-family is a `d₁`-family, since
`1 / d ^ 3 ≤ 1 / d`. Any `k = d₃ + 1` members of a `d₁`-family with `d₁ ≥ k ^ 3` would have
pairwise correlations of absolute value at most `1 / k ^ 3`. So polynomial boundedness does not
depend on the normalization; this elementary relation is not formalized. The one-sided variant
`sqDimOneSided` is at least this dimension and at most `18 (sqDim D C + 1) ^ 3`
(`sqDim_le_sqDimOneSided`, `sqDimOneSided_le`). -/
noncomputable def sqDim (D : PMF X) (C : PACLearning.ConceptClass X Bool) : ℕ :=
  sSup {d | ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = d ∧
    (F : Set (X → Bool)).Pairwise fun f g => |corr D f g| ≤ 1 / d}

private theorem bddAbove_sqDim_set (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    BddAbove {d | ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = d ∧
      (F : Set (X → Bool)).Pairwise fun f g => |corr D f g| ≤ 1 / d} := by
  classical
  refine ⟨Fintype.card (X → Bool), ?_⟩
  rintro d ⟨F, -, rfl, -⟩
  exact Finset.card_le_univ F

private theorem nonempty_sqDim_set (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    {d | ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = d ∧
      (F : Set (X → Bool)).Pairwise fun f g => |corr D f g| ≤ 1 / d}.Nonempty :=
  ⟨0, ∅, by simp⟩

/-- A family of `d` concepts of `C` with pairwise correlations of absolute value at most `1 / d`
shows `d ≤ sqDim D C`. -/
theorem le_sqDim {D : PMF X} {C : PACLearning.ConceptClass X Bool} {F : Finset (X → Bool)}
    (hFC : (F : Set (X → Bool)) ⊆ C)
    (hF : (F : Set (X → Bool)).Pairwise fun f g => |corr D f g| ≤ 1 / F.card) :
    F.card ≤ sqDim D C :=
  le_csSup (bddAbove_sqDim_set D C) ⟨F, hFC, rfl, hF⟩

/-- The statistical query dimension is attained: `C` contains `sqDim D C` concepts with pairwise
correlations of absolute value at most `1 / sqDim D C`. -/
theorem exists_finset_card_eq_sqDim (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = sqDim D C ∧
      (F : Set (X → Bool)).Pairwise fun f g => |corr D f g| ≤ 1 / sqDim D C :=
  Nat.sSup_mem (nonempty_sqDim_set D C) (bddAbove_sqDim_set D C)

/-- The statistical query dimension is at most the number of concepts. -/
theorem sqDim_le_ncard (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    sqDim D C ≤ C.ncard := by
  obtain ⟨F, hFC, hF, -⟩ := exists_finset_card_eq_sqDim D C
  rw [← hF, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hFC (Set.toFinite C)

/-- The empty class has statistical query dimension `0`. -/
@[simp] theorem sqDim_empty (D : PMF X) : sqDim D (∅ : PACLearning.ConceptClass X Bool) = 0 :=
  Nat.le_zero.1 ((sqDim_le_ncard D ∅).trans_eq (Set.ncard_empty _))

/-- A larger class has a larger statistical query dimension. -/
theorem sqDim_mono (D : PMF X) {C C' : PACLearning.ConceptClass X Bool} (h : C ⊆ C') :
    sqDim D C ≤ sqDim D C' := by
  obtain ⟨F, hFC, hF, hpair⟩ := exists_finset_card_eq_sqDim D C
  rw [← hF] at hpair ⊢
  exact le_sqDim (hFC.trans h) hpair

/-- A nonempty class has statistical query dimension at least `1`. -/
theorem one_le_sqDim {D : PMF X} {C : PACLearning.ConceptClass X Bool} (hC : C.Nonempty) :
    1 ≤ sqDim D C := by
  obtain ⟨c, hc⟩ := hC
  have h := le_sqDim (D := D) (F := {c}) (by simpa using hc) (by simp)
  rwa [card_singleton] at h

/-! ### The one-sided variant -/

/-- The **one-sided statistical query dimension** of `C` under `D`: the largest `d` such that `C`
contains `d` distinct concepts whose pairwise correlations under `D` are at most `1 / d`. This
variant of [Reyzin, Definition 11][Reyzin2020] drops the absolute value. Szörényi's argument for the
lower bound of [Reyzin, Theorem 12][Reyzin2020] uses only this upper bound on the correlations, so
the lower bound holds for it (`LearnsStateless.sqDimOneSided_mul_sq_le`). It is at least
`sqDim D C` (`sqDim_le_sqDimOneSided`) and at most `18 (sqDim D C + 1) ^ 3`
(`sqDimOneSided_le`). -/
noncomputable def sqDimOneSided (D : PMF X) (C : PACLearning.ConceptClass X Bool) : ℕ :=
  sSup {d | ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = d ∧
    (F : Set (X → Bool)).Pairwise fun f g => corr D f g ≤ 1 / d}

private theorem bddAbove_sqDimOneSided_set (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    BddAbove {d | ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = d ∧
      (F : Set (X → Bool)).Pairwise fun f g => corr D f g ≤ 1 / d} := by
  classical
  refine ⟨Fintype.card (X → Bool), ?_⟩
  rintro d ⟨F, -, rfl, -⟩
  exact Finset.card_le_univ F

private theorem nonempty_sqDimOneSided_set (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    {d | ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = d ∧
      (F : Set (X → Bool)).Pairwise fun f g => corr D f g ≤ 1 / d}.Nonempty :=
  ⟨0, ∅, by simp⟩

/-- A family of `d` concepts of `C` with pairwise correlations at most `1 / d` shows
`d ≤ sqDimOneSided D C`. -/
theorem le_sqDimOneSided {D : PMF X} {C : PACLearning.ConceptClass X Bool}
    {F : Finset (X → Bool)} (hFC : (F : Set (X → Bool)) ⊆ C)
    (hF : (F : Set (X → Bool)).Pairwise fun f g => corr D f g ≤ 1 / F.card) :
    F.card ≤ sqDimOneSided D C :=
  le_csSup (bddAbove_sqDimOneSided_set D C) ⟨F, hFC, rfl, hF⟩

/-- The one-sided statistical query dimension is attained. -/
theorem exists_finset_card_eq_sqDimOneSided (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    ∃ F : Finset (X → Bool), (F : Set (X → Bool)) ⊆ C ∧ F.card = sqDimOneSided D C ∧
      (F : Set (X → Bool)).Pairwise fun f g => corr D f g ≤ 1 / sqDimOneSided D C :=
  Nat.sSup_mem (nonempty_sqDimOneSided_set D C) (bddAbove_sqDimOneSided_set D C)

/-- The one-sided statistical query dimension is at most the number of concepts. -/
theorem sqDimOneSided_le_ncard (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    sqDimOneSided D C ≤ C.ncard := by
  obtain ⟨F, hFC, hF, -⟩ := exists_finset_card_eq_sqDimOneSided D C
  rw [← hF, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hFC (Set.toFinite C)

/-- The statistical query dimension is at most the one-sided one. -/
theorem sqDim_le_sqDimOneSided (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    sqDim D C ≤ sqDimOneSided D C := by
  obtain ⟨F, hFC, hF, hpair⟩ := exists_finset_card_eq_sqDim D C
  rw [← hF] at hpair ⊢
  exact le_sqDimOneSided hFC (hpair.mono' fun _ _ h => (le_abs_self _).trans h)

/-! ### Covering a class by almost uncorrelated concepts -/

/-- At most `sqDim D C` concepts of `C` cover `C`: every concept of `C` has correlation of absolute
value more than `1 / (sqDim D C + 1)` with one of them. They form a family of maximum size whose
pairwise correlations have absolute value at most `1 / (sqDim D C + 1)`. -/
theorem exists_cover_sqDim (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    ∃ G : Finset (X → Bool), (G : Set (X → Bool)) ⊆ C ∧ G.card ≤ sqDim D C ∧
      ∀ c ∈ C, ∃ g ∈ G, 1 / ((sqDim D C : ℝ) + 1) < |corr D c g| := by
  classical
  set d := sqDim D C with hd
  set γ : ℝ := 1 / ((d : ℝ) + 1) with hγ
  -- The good families: subsets of `C` with pairwise correlations of absolute value at most `γ`.
  set S : Finset (Finset (X → Bool)) := univ.filter fun F : Finset (X → Bool) =>
    (F : Set (X → Bool)) ⊆ C ∧ (F : Set (X → Bool)).Pairwise fun f g => |corr D f g| ≤ γ with hS
  have hS0 : (∅ : Finset (X → Bool)) ∈ S := by simp [hS]
  obtain ⟨G, hGS, hGmax⟩ := S.exists_max_image Finset.card ⟨∅, hS0⟩
  obtain ⟨hGC, hGpair⟩ := (mem_filter.1 hGS).2
  -- A good family has at most `d` members.
  have hcard : G.card ≤ d := by
    by_contra hlt
    push Not at hlt
    obtain ⟨F, hFG, hF⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ G.card by omega)
    have hle := le_sqDim (D := D) (C := C) (F := F) ((coe_subset.2 hFG).trans hGC) (by
      rw [hF, Nat.cast_add, Nat.cast_one]
      exact hGpair.mono (coe_subset.2 hFG))
    omega
  refine ⟨G, hGC, hcard, fun c hc => ?_⟩
  by_cases hcG : c ∈ G
  · refine ⟨c, hcG, ?_⟩
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast one_le_sqDim (D := D) ⟨c, hc⟩
    rw [corr_self, abs_one, hγ, div_lt_one (by positivity)]
    linarith
  -- Otherwise adding `c` gives a larger family, which is not good.
  by_contra hnot
  push Not at hnot
  have hins : insert c G ∈ S := by
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · rw [coe_insert]
      exact Set.insert_subset hc hGC
    · rw [coe_insert]
      refine hGpair.insert fun g hg _ => ⟨hnot g hg, ?_⟩
      rw [corr_comm]
      exact hnot g hg
  have := hGmax _ hins
  rw [card_insert_of_notMem hcG] at this
  omega

/-! ### The correlational learner -/

/-- The correlational query of the concept `g`: the product of the `±1` values of `g (x)` and of
the label. Its expectation is the correlation of the target with `g`
(`expect_corrQuery`). -/
noncomputable def corrQuery (g : X → Bool) : Query X where
  toFun x y := BitString.signVal (g x) * BitString.signVal y
  abs_le_one' x y := by
    rw [abs_mul, BitString.abs_signVal, BitString.abs_signVal, one_mul]

/-- The expectation of the correlational query of `g` is the correlation of the target with
`g`. -/
theorem expect_corrQuery (D : PMF X) (c g : X → Bool) : expect D c (corrQuery g) = corr D c g := by
  simp only [expect, corr, corrQuery, mul_comm (BitString.signVal (g _))]

/-- Ask for the correlation of the target with `g`, and return `g` with the answer. -/
noncomputable def askCorr (g : X → Bool) : OracleComp (spec X) ((X → Bool) × ℝ) :=
  (g, ·) <$> OracleComp.query (spec := spec X) (corrQuery g)

/-- The hypothesis chosen from the answered concepts: a concept `g` whose answer `a` has the
largest absolute value, if `a ≥ 0`, and the negation of `g` otherwise (the constant `false` if
there are no answers). -/
noncomputable def corrHypothesis (answers : List ((X → Bool) × ℝ)) : X → Bool :=
  match answers.argmax fun p => |p.2| with
  | none => fun _ => false
  | some m => if 0 ≤ m.2 then m.1 else fun x => !m.1 x

/-- Ask for the correlation of the target with each concept of `gs` and return a concept whose
answer has the largest absolute value, or its negation if that answer is negative. -/
noncomputable def corrLearner (gs : List (X → Bool)) : OracleComp (spec X) (X → Bool) := do
  let answers ← gs.mapM askCorr
  pure (corrHypothesis answers)

omit [Fintype X] in
/-- The correlational learner makes one query for each concept of the list. -/
theorem isQueryBounded_corrLearner (gs : List (X → Bool)) :
    (corrLearner gs).IsQueryBounded gs.length := by
  have h := (OracleComp.IsCostBounded.mapM (cost := fun _ => 1) (n := 1) (inputs := gs)
    (program := askCorr) fun g _ => (OracleComp.isCostBounded_map_iff _ _ _).2 (.query _)).bind
    fun answers => .pure (corrHypothesis answers) 0
  rw [mul_one, add_zero] at h
  exact h

omit [Fintype X] in
/-- Every query of the correlational learner is the correlational query of a concept of the
list. -/
theorem queriesSatisfy_corrLearner (gs : List (X → Bool)) :
    OracleComp.QueriesSatisfy (fun φ => ∃ g ∈ gs, φ = corrQuery g) (corrLearner gs) :=
  (OracleComp.QueriesSatisfy.mapM fun g hg =>
    (OracleComp.queriesSatisfy_map_iff _ _).2 (.query ⟨g, hg, rfl⟩)).bind
    fun _ => .pure _

omit [Fintype X] in
/-- The answers collected by the correlational learner: each is a valid answer for its concept,
and every concept of the list is answered. -/
private theorem forall₂_askCorr {possible : Query X → Set ℝ} {gs : List (X → Bool)}
    {answers : List ((X → Bool) × ℝ)}
    (h : List.Forall₂ (fun g p => p ∈ OracleComp.supportWith possible (askCorr g)) gs answers) :
    (∀ p ∈ answers, p.2 ∈ possible (corrQuery p.1)) ∧ ∀ g ∈ gs, ∃ a, (g, a) ∈ answers := by
  induction h with
  | nil => exact ⟨fun _ hp => absurd hp List.not_mem_nil, fun _ hg => absurd hg List.not_mem_nil⟩
  | @cons g p gs answers hp _ ih =>
    rw [askCorr, OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_query] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    refine ⟨fun p' hp' => ?_, fun g' hg' => ?_⟩
    · rcases List.mem_cons.1 hp' with rfl | hp'
      · exact ha
      · exact ih.1 p' hp'
    · rcases List.mem_cons.1 hg' with rfl | hg'
      · exact ⟨a, List.mem_cons_self⟩
      · obtain ⟨a', ha'⟩ := ih.2 g' hg'
        exact ⟨a', List.mem_cons_of_mem _ ha'⟩

/-- **The correlational learner learns a covered class.** If every concept `c ∈ C` has
correlation of absolute value more than `γ` with some concept of `gs`, then `corrLearner gs` learns
`C` under `D` with tolerance `τ` and error `(1 - γ) / 2 + τ`. -/
theorem learns_corrLearner {D : PMF X} {C : PACLearning.ConceptClass X Bool}
    {gs : List (X → Bool)} {γ : ℝ} (hcover : ∀ c ∈ C, ∃ g ∈ gs, γ < |corr D c g|) (τ : ℝ) :
    Learns (corrLearner gs) D C τ ((1 - γ) / 2 + τ) := by
  intro c hc h hh
  obtain ⟨g₀, hg₀, hγ⟩ := hcover c hc
  rw [corrLearner, OracleComp.mem_supportWith_bind_iff] at hh
  obtain ⟨answers, hanswers, hh⟩ := hh
  rw [OracleComp.eq_of_mem_supportWith_pure hh]
  rw [OracleComp.mem_supportWith_mapM_iff] at hanswers
  -- Each answer is `(g, a)` with `a` within `τ` of the correlation with `g`, and every concept of
  -- the list is answered.
  obtain ⟨hvalid, hcovered⟩ := forall₂_askCorr hanswers
  obtain ⟨a₀, ha₀⟩ := hcovered g₀ hg₀
  rw [corrHypothesis]
  cases hm : answers.argmax fun p => |p.2| with
  | none =>
    rw [List.argmax_eq_none] at hm
    rw [hm] at ha₀
    exact absurd ha₀ List.not_mem_nil
  | some m =>
    -- The chosen answer has the largest absolute value, so it exceeds `γ - τ` in absolute value.
    have hle : |a₀| ≤ |m.2| :=
      List.le_of_mem_argmax (f := fun p : (X → Bool) × ℝ => |p.2|) ha₀ hm
    have hm_valid : |m.2 - expect D c (corrQuery m.1)| ≤ τ := hvalid m (List.argmax_mem hm)
    have h₀_valid : |a₀ - expect D c (corrQuery g₀)| ≤ τ := hvalid _ ha₀
    rw [expect_corrQuery] at hm_valid h₀_valid
    have h₀ : |corr D c g₀| - |a₀| ≤ τ := by
      have := abs_sub_abs_le_abs_sub (corr D c g₀) a₀
      rw [abs_sub_comm] at this
      linarith
    dsimp only
    split_ifs with hsign
    · -- A nonnegative answer: the concept itself has correlation more than `γ - 2 τ`.
      rw [abs_of_nonneg hsign] at hle
      have hcorr := corr_eq_one_sub_two_mul_disagreement D c m.1
      linarith [(abs_le.1 hm_valid).2]
    · -- A negative answer: the negation has correlation more than `γ - 2 τ`.
      push Not at hsign
      rw [abs_of_neg hsign] at hle
      have hcorr := corr_eq_one_sub_two_mul_disagreement D c fun x => !m.1 x
      rw [corr_not_right] at hcorr
      linarith [(abs_le.1 hm_valid).1]

/-! ### The weak learner and the lower bound -/

/-- **Weak learning from the statistical query dimension** [Reyzin, Observation 23][Reyzin2020],
the analogue of [BlumEtAl1994, Theorem 13] for the threshold `1 / d`. For
`d = sqDim D C` there is a learner making at most `d` queries, each the correlational query of a
concept of `C`, that learns `C` under `D` with tolerance `τ` and error `1/2 - 1/(2 (d + 1)) + τ`,
for every `τ`. Its hypotheses are concepts of `C` or their negations. -/
theorem exists_learns_sqDim (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    ∃ A : Algorithm X, A.IsQueryBounded (sqDim D C) ∧
      OracleComp.QueriesSatisfy (fun φ => ∃ g ∈ C, φ = corrQuery g) A ∧
      ∀ τ : ℝ, Learns A D C τ (1 / 2 - 1 / (2 * ((sqDim D C : ℝ) + 1)) + τ) := by
  classical
  obtain ⟨G, hGC, hcard, hcover⟩ := exists_cover_sqDim D C
  refine ⟨corrLearner G.toList, ?_, ?_, fun τ => ?_⟩
  · exact (isQueryBounded_corrLearner _).mono (by rw [length_toList]; exact hcard)
  · refine (queriesSatisfy_corrLearner _).mono fun φ ⟨g, hg, hφ⟩ => ⟨g, hGC (mem_toList.1 hg), hφ⟩
  · have h := learns_corrLearner (D := D) (C := C) (gs := G.toList)
      (fun c hc => by
        obtain ⟨g, hg, hlt⟩ := hcover c hc
        exact ⟨g, mem_toList.2 hg, hlt⟩) τ
    have e : (1 - 1 / ((sqDim D C : ℝ) + 1)) / 2 = 1 / 2 - 1 / (2 * ((sqDim D C : ℝ) + 1)) := by
      field_simp
    rwa [e] at h

/-- **The statistical query dimension lower bound**, one-sided form [Reyzin, Theorem 12][Reyzin2020]
(a quantitative form of [BlumEtAl1994, Theorem 12]). A learner learning `C` under `D` from at most
`q` queries of tolerance `τ ≥ 0` with error `ε ≥ 0`, where `1 - 2 ε ≥ τ`, has
`sqDimOneSided D C · τ ^ 2 ≤ 2 q + 2`. This is
one weaker than Reyzin's count `d τ ^ 2 ≤ 2 q + 1`, because a hypothesis with error `ε > 0` may
correlate with one more concept of the family; for exact learning see
`LearnsStateless.card_mul_sq_sub_one_le_two_mul`. -/
theorem LearnsStateless.sqDimOneSided_mul_sq_le {D : PMF X}
    {C : PACLearning.ConceptClass X Bool} {A : Algorithm X} {τ ε : ℝ}
    (hA : LearnsStateless A D C τ ε) {q : ℕ} (hq : A.IsQueryBounded q) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hετ : τ ≤ 1 - 2 * ε) :
    sqDimOneSided D C * τ ^ 2 ≤ 2 * q + 2 := by
  obtain ⟨F, hFC, hF, hpair⟩ := exists_finset_card_eq_sqDimOneSided D C
  have h := hA.card_mul_sq_sub_one_le_two_mul_add_one (κ := F) hq (f := Subtype.val)
    (fun f => hFC f.2) (fun f g hfg => by
      rw [Fintype.card_coe, hF]
      exact hpair f.2 g.2 (Subtype.coe_ne_coe.2 hfg)) hτ hε hετ
  rw [Fintype.card_coe, hF] at h
  linarith

/-- **The statistical query dimension lower bound** (a quantitative form of
[BlumEtAl1994, Theorem 12]): a learner learning
`C` under `D` from at most `q` queries of tolerance `τ ≥ 0` with error `ε ≥ 0`, where
`1 - 2 ε ≥ τ`, has `sqDim D C · τ ^ 2 ≤ 2 q + 2`
(`LearnsStateless.sqDimOneSided_mul_sq_le` and `sqDim_le_sqDimOneSided`). -/
theorem LearnsStateless.sqDim_mul_sq_le {D : PMF X} {C : PACLearning.ConceptClass X Bool}
    {A : Algorithm X} {τ ε : ℝ} (hA : LearnsStateless A D C τ ε) {q : ℕ}
    (hq : A.IsQueryBounded q) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hετ : τ ≤ 1 - 2 * ε) :
    sqDim D C * τ ^ 2 ≤ 2 * q + 2 := by
  have h := hA.sqDimOneSided_mul_sq_le hq hτ hε hετ
  have hle : (sqDim D C : ℝ) ≤ sqDimOneSided D C := by exact_mod_cast sqDim_le_sqDimOneSided D C
  nlinarith [sq_nonneg τ]

/-- **The one-sided statistical query dimension is polynomial in the statistical query
dimension**: `sqDimOneSided D C ≤ 18 (sqDim D C + 1) ^ 3`. The weak learner of
`exists_learns_sqDim` with tolerance `τ = 1 / (3 (d + 1))` has accuracy `τ`, so the one-sided lower
bound `LearnsStateless.sqDimOneSided_mul_sq_le` applies with `d` queries. -/
theorem sqDimOneSided_le (D : PMF X) (C : PACLearning.ConceptClass X Bool) :
    sqDimOneSided D C ≤ 18 * (sqDim D C + 1) ^ 3 := by
  suffices h : (sqDimOneSided D C : ℝ) ≤ 18 * ((sqDim D C : ℝ) + 1) ^ 3 by exact_mod_cast h
  obtain ⟨A, hq, -, hA⟩ := exists_learns_sqDim D C
  set d : ℝ := (sqDim D C : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hd1 : 0 < d + 1 := by linarith
  have h := (hA (1 / (3 * (d + 1)))).learnsStateless.sqDimOneSided_mul_sq_le hq (by positivity)
    (by
      have : 1 / (2 * (d + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have : 0 ≤ 1 / (3 * (d + 1)) := by positivity
      linarith)
    (by
      field_simp
      ring_nf
      nlinarith)
  rw [← hd] at h
  have e : (sqDimOneSided D C : ℝ) =
      sqDimOneSided D C * (1 / (3 * (d + 1))) ^ 2 * (9 * (d + 1) ^ 2) := by
    field_simp
    ring
  rw [e]
  calc (sqDimOneSided D C : ℝ) * (1 / (3 * (d + 1))) ^ 2 * (9 * (d + 1) ^ 2)
      ≤ (2 * d + 2) * (9 * (d + 1) ^ 2) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 18 * (d + 1) ^ 3 := by ring

/-! ### The characterization of weak learning -/

/-- **The statistical query dimension characterizes weak learning** [BlumEtAl1994, §5]
(see [Reyzin, Theorem 12 and Observation 23][Reyzin2020]). For concept classes `C n` on finite
domains `X n` under distributions `D n`, the following are equivalent:

1. the statistical query dimension `sqDim (D n) (C n)` is polynomially bounded in `n`;
2. the one-sided dimension `sqDimOneSided (D n) (C n)` is polynomially bounded in `n`;
3. there are polynomially bounded `q` and `p` and learners for each `n` making at most `q n`
   queries, each the correlational query of a concept of `C n`, that learn `C n` under `D n` with
   tolerance `1 / (p n + 1)` and error `1/2 - 1 / (p n + 1)`, against adaptive answers;
4. the same with arbitrary statistical queries, against fixed answer functions only.

So weak learnability with polynomially many queries, inverse-polynomial tolerance and
inverse-polynomial advantage does not depend on the choice between statistical and correlational
queries, or between adaptive and fixed answers, and polynomial boundedness of the dimension does
not depend on whether correlations are bounded in absolute value. -/
theorem tfae_polynomiallyBounded_sqDim {X : ℕ → Type} [∀ n, Fintype (X n)] (D : ∀ n, PMF (X n))
    (C : ∀ n, PACLearning.ConceptClass (X n) Bool) :
    List.TFAE
      [PolynomiallyBounded fun n => sqDim (D n) (C n),
       PolynomiallyBounded fun n => sqDimOneSided (D n) (C n),
       ∃ q p : ℕ → ℕ, PolynomiallyBounded q ∧ PolynomiallyBounded p ∧ ∀ n,
         ∃ A : Algorithm (X n), A.IsQueryBounded (q n) ∧
           OracleComp.QueriesSatisfy (fun φ => ∃ g ∈ C n, φ = corrQuery g) A ∧
           Learns A (D n) (C n) (1 / ((p n : ℝ) + 1)) (1 / 2 - 1 / ((p n : ℝ) + 1)),
       ∃ q p : ℕ → ℕ, PolynomiallyBounded q ∧ PolynomiallyBounded p ∧ ∀ n,
         ∃ A : Algorithm (X n), A.IsQueryBounded (q n) ∧
           LearnsStateless A (D n) (C n) (1 / ((p n : ℝ) + 1)) (1 / 2 - 1 / ((p n : ℝ) + 1))] := by
  tfae_have 1 → 3 := by
    intro hdim
    refine ⟨fun n => sqDim (D n) (C n), fun n => 4 * sqDim (D n) (C n) + 3, hdim,
      (PolynomiallyBounded.const 4).mul hdim |>.add (PolynomiallyBounded.const 3), fun n => ?_⟩
    obtain ⟨A, hq, hcorr, hA⟩ := exists_learns_sqDim (D n) (C n)
    refine ⟨A, hq, hcorr, ?_⟩
    have h := hA (1 / ((4 * sqDim (D n) (C n) + 3 : ℕ) + 1 : ℝ))
    have e : (1 / 2 - 1 / (2 * ((sqDim (D n) (C n) : ℝ) + 1)) +
        1 / ((4 * sqDim (D n) (C n) + 3 : ℕ) + 1 : ℝ)) =
        1 / 2 - 1 / ((4 * sqDim (D n) (C n) + 3 : ℕ) + 1 : ℝ) := by
      push_cast
      field_simp
      ring
    rwa [e] at h
  tfae_have 3 → 4 := by
    rintro ⟨q, p, hq, hp, h⟩
    refine ⟨q, p, hq, hp, fun n => ?_⟩
    obtain ⟨A, hAq, -, hA⟩ := h n
    exact ⟨A, hAq, hA.learnsStateless⟩
  tfae_have 4 → 2 := by
    rintro ⟨q, p, hq, hp, h⟩
    refine (((PolynomiallyBounded.const 2).mul hq |>.add (PolynomiallyBounded.const 2)).mul
      ((hp.add (PolynomiallyBounded.const 1)).pow 2)).mono_of_le fun n => ?_
    obtain ⟨A, hAq, hA⟩ := h n
    set P : ℝ := (p n : ℝ) + 1 with hP
    have hP1 : 1 ≤ P := by
      rw [hP]
      linarith [(Nat.cast_nonneg (p n) : (0 : ℝ) ≤ p n)]
    -- Raise a negative error bound to `0`, which only weakens the guarantee.
    have hA' : LearnsStateless A (D n) (C n) (1 / P) (max (1 / 2 - 1 / P) 0) :=
      fun c hc answer hanswer => (hA c hc answer hanswer).trans (le_max_left _ _)
    have hτ : (0 : ℝ) ≤ 1 / P := by positivity
    have hετ : 1 / P ≤ 1 - 2 * max (1 / 2 - 1 / P) 0 := by
      have h1P : 1 / P ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hP1
      rcases le_total (1 / 2 - 1 / P) 0 with hle | hle
      · rw [max_eq_right hle]
        linarith
      · rw [max_eq_left hle]
        linarith
    have hbound := hA'.sqDimOneSided_mul_sq_le hAq hτ (le_max_right _ _) hετ
    have hPpos : 0 < P := by linarith
    have hreal : (sqDimOneSided (D n) (C n) : ℝ) ≤ (2 * q n + 2) * P ^ 2 := by
      have e : (sqDimOneSided (D n) (C n) : ℝ) =
          sqDimOneSided (D n) (C n) * (1 / P) ^ 2 * P ^ 2 := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hbound (by positivity)
    rw [hP] at hreal
    exact_mod_cast hreal
  tfae_have 2 → 1 := fun h => h.mono_of_le fun n => sqDim_le_sqDimOneSided (D n) (C n)
  tfae_finish

end Cslib.MachineLearning.StatisticalQuery
