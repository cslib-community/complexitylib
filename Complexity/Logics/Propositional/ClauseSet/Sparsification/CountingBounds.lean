/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParameters
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingPathBounds
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingSearch

/-!
# Depth and Leaf-Count Bounds for Counting Sparsification

We connect the actual counting-path insertion and petal-step bounds of `CountingPathBounds`
(Appendix A.2, Lemma A.3 on p. 46 and the path budgets of Appendix A.3 on p. 46 of
[OpenAI2026ETH]) to the prefix words of a `CountingBranchingRule`, and combine a leaf-only
petal-step injection (a library adaptation of §A.3's depth-and-B-positions node encoding on p. 46)
with the geometric binomial-tail bound `Cslib.sum_choose_le_two_pow_div_add_one` and the
first-success threshold base `countingThresholdBase` of `CountingParameters` (pp. 46–47) to bound
the number of leaf words of any counting-sparsification tree.

For a `CountingBranchingRule (fun r => M ^ r) V σ` starting from a state `s` whose clause set
`R.toClauseSet s` is `Reduced`, nontautological, of width at most `k`, and supported on a finite
variable set `declared` of size `N = declared.card`:
* every node word `w` has length at most `countingDepthCoeff k M * N`, where
  `countingDepthCoeff k M = 4 * ∑ r < k - 1, (3 * M) ^ r`;
* every node word `w` has `M * #{i < w.length | w[i] = true} ≤ countingBChoiceCoeff k * N`, where
  `countingBChoiceCoeff k = 4 * ∑ r < k - 1, 3 ^ r`;
* as a library adaptation of §A.3's `(Cn + 1) * ∑ choose` node bound (p. 46), leafhood rules out
  trailing-`false` ambiguity so two leaf words with `true` steps at the same positions are equal
  (`CountingBranchingRule.IsLeafWord.eq_of_getD_eq`); any finset `W` of leaf words therefore
  injects into the subsets of `range (countingDepthCoeff k M * N)` of cardinality at most
  `countingBChoiceCoeff k * N / M` without a separate depth factor, giving the pure binomial-sum
  leaf bound `W.card ≤ ∑ j ≤ countingBChoiceCoeff k * N / M, (countingDepthCoeff k M * N).choose j`
  (`CountingBranchingRule.card_le_of_isLeafWord`);
* under the integer parameter budget `countingBChoiceCoeff k ≤ M` and
  `B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k M * M) ≤ M` (for `2 ≤ k`, with
  `1 ≤ B`), and in particular unconditionally at `M = countingThresholdBase k B`,
  `W.card ≤ 2 ^ (N / B + 1)` (`CountingBranchingRule.card_le_two_pow_of_isLeafWord`,
  `CountingBranchingRule.card_le_two_pow_thresholdBase`).

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.IsLeafWord.eq_of_getD_eq`: two
  leaf words with `true` steps at the same positions are equal.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.IsNodeWord.length_le`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.IsLeafWord.length_le`: linear depth
  bound along node and leaf words.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.IsNodeWord.mul_card_le`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.IsLeafWord.mul_card_le`: `M`-scaled
  petal-step budget along node and leaf words.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.card_le_of_isLeafWord`:
  binomial-sum bound on any finset of leaf words.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.card_le_two_pow_of_isLeafWord`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.card_le_two_pow_thresholdBase`:
  exponential bound `2 ^ (declared.card / B + 1)` on any finset of leaf words under the integer
  parameter budget and at `countingThresholdBase k B`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.2 (Lemma A.3, p. 46) and
  Appendix A.3 (pp. 46–47)][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

theorem countingDepthCoeff_eq_zero {k : ℕ} (hk : k ≤ 1) (M : ℕ) :
    countingDepthCoeff k M = 0 := by
  have hk0 : k - 1 = 0 := by omega
  simp [countingDepthCoeff, hk0]

theorem countingBChoiceCoeff_eq_zero {k : ℕ} (hk : k ≤ 1) :
    countingBChoiceCoeff k = 0 := by
  have hk0 : k - 1 = 0 := by omega
  simp [countingBChoiceCoeff, hk0]

/-! ### Prefix paths and leaf-count bounds for a counting branching rule -/

namespace CountingBranchingRule

variable {θ : ℕ → ℕ} {σ : Type*} (R : CountingBranchingRule θ V σ)

private theorem walk_append (s : σ) (u v : List Bool) :
    R.walk s (u ++ v) = R.walk (R.walk s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => exact ih (R.next s a)

private theorem walk_take_succ (s : σ) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    R.walk s (w.take (i + 1)) = R.next (R.walk s (w.take i)) (w.getD i false) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, walk_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rfl

variable {R}

private theorem IsNodeWord.not_sparse_take {s : σ} {w : List Bool} (h : R.IsNodeWord s w) :
    ∀ i < w.length, ¬ Sparse θ (R.toClauseSet (R.walk s (w.take i))) := by
  induction w generalizing s with
  | nil => intro i hi; simp at hi
  | cons b w ih =>
    intro i hi
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [List.take_succ_cons, walk]
      exact ih h.2 i (by simpa using hi)

/-- **Leaf words are determined by their petal steps.** Two leaf words with `true` steps at the
same positions are equal. -/
theorem IsLeafWord.eq_of_getD_eq {s : σ} {w w' : List Bool} (hw : R.IsLeafWord s w)
    (hw' : R.IsLeafWord s w') (h : ∀ i, w.getD i false = w'.getD i false) : w = w' := by
  induction w generalizing s w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons b' w' => exact absurd hw hw'.1
  | cons b w ih =>
    cases w' with
    | nil => exact absurd hw' hw.1
    | cons b' w' =>
      have hb : b = b' := by simpa using h 0
      subst hb
      rw [ih hw.2 hw'.2 fun i => by simpa using h (i + 1)]

/-- Every node word `w` of a counting branching rule induces a sequence of valid choices
`(c i, H i)` along its prefixes `w.take i`. -/
theorem exists_choice_seq_of_isNodeWord (s : σ) {w : List Bool} (hw : R.IsNodeWord s w) :
    ∃ (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)),
      (∀ i < w.length,
        R.toClauseSet (R.walk s (w.take (i + 1))) =
          countingChild (R.toClauseSet (R.walk s (w.take i))) (c i) (H i) (w.getD i false)) ∧
      (∀ i < w.length, Choice θ (R.toClauseSet (R.walk s (w.take i))) (c i) (H i)) := by
  classical
  have hns := hw.not_sparse_take
  have hch (i : ℕ) (hi : i < w.length) := R.exists_choice_next _ (hns i hi)
  let c (i : ℕ) : ℕ := if hi : i < w.length then (hch i hi).choose else 0
  let H (i : ℕ) : Finset (Literal V) :=
    if hi : i < w.length then (hch i hi).choose_spec.choose else ∅
  have hspec (i : ℕ) (hi : i < w.length) :
      Choice θ (R.toClauseSet (R.walk s (w.take i))) (c i) (H i) ∧
        ∀ b, R.toClauseSet (R.next (R.walk s (w.take i)) b) =
          countingChild (R.toClauseSet (R.walk s (w.take i))) (c i) (H i) b := by
    simp only [c, H, dite_eq_left hi]
    exact (hch i hi).choose_spec.choose_spec
  refine ⟨c, H, fun i hi => ?_, fun i hi => (hspec i hi).1⟩
  rw [walk_take_succ R s w hi]
  exact (hspec i hi).2 _

section PathBounds

variable {M k : ℕ} (hM : 2 ≤ M)
  {R : CountingBranchingRule (fun r => M ^ r) V σ} {s : σ}
  (hred : Reduced (R.toClauseSet s))
  (hnt : ∀ C ∈ R.toClauseSet s, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
  (hk : ∀ C ∈ R.toClauseSet s, C.card ≤ k)
  (declared : Finset V)
  (hsupport : ∀ C ∈ R.toClauseSet s, ∀ l ∈ C, l.1 ∈ declared)
include hM hred hnt hk hsupport

/-- **Node words are short.** From a reduced, nontautological clause set of width `≤ k` over
`declared`, every node word has length at most `countingDepthCoeff k M * declared.card`. -/
theorem IsNodeWord.length_le {w : List Bool} (hw : R.IsNodeWord s w) :
    w.length ≤ countingDepthCoeff k M * declared.card := by
  obtain ⟨c, H, hstep, hchoice⟩ := exists_choice_seq_of_isNodeWord s hw
  exact counting_length_le hM w.length (fun i => R.toClauseSet (R.walk s (w.take i)))
    c H (fun i => w.getD i false) hstep hchoice hred hnt hk declared hsupport

/-- **Node words have few petal steps.** From a reduced, nontautological clause set of width `≤ k`
over `declared`, every node word satisfies
`M * #{i < w.length | w.getD i false = true} ≤ countingBChoiceCoeff k * declared.card`. -/
theorem IsNodeWord.mul_card_le {w : List Bool} (hw : R.IsNodeWord s w) :
    M * ((range w.length).filter fun i => w.getD i false = true).card ≤
      countingBChoiceCoeff k * declared.card := by
  obtain ⟨c, H, hstep, hchoice⟩ := exists_choice_seq_of_isNodeWord s hw
  exact mul_card_counting_B_le hM w.length (fun i => R.toClauseSet (R.walk s (w.take i)))
    c H (fun i => w.getD i false) hstep hchoice hred hnt hk declared hsupport

/-- **Leaf words are short.** From a reduced, nontautological clause set of width `≤ k` over
`declared`, every leaf word has length at most `countingDepthCoeff k M * declared.card`. -/
theorem IsLeafWord.length_le {w : List Bool} (hw : R.IsLeafWord s w) :
    w.length ≤ countingDepthCoeff k M * declared.card :=
  hw.isNodeWord.length_le hM hred hnt hk declared hsupport

/-- **Leaf words have few petal steps.** From a reduced, nontautological clause set of width `≤ k`
over `declared`, every leaf word satisfies
`M * #{i < w.length | w.getD i false = true} ≤ countingBChoiceCoeff k * declared.card`. -/
theorem IsLeafWord.mul_card_le {w : List Bool} (hw : R.IsLeafWord s w) :
    M * ((range w.length).filter fun i => w.getD i false = true).card ≤
      countingBChoiceCoeff k * declared.card :=
  hw.isNodeWord.mul_card_le hM hred hnt hk declared hsupport

/-- **Binomial-sum leaf-word bound.** From a reduced, nontautological clause set of width `≤ k` over
`declared`, any finset `W` of leaf words has cardinality at most
`∑_{j ≤ countingBChoiceCoeff k * declared.card / M}
  (countingDepthCoeff k M * declared.card).choose j`. -/
theorem card_le_of_isLeafWord (W : Finset (List Bool)) (hW : ∀ w ∈ W, R.IsLeafWord s w) :
    W.card ≤ ∑ j ∈ range (countingBChoiceCoeff k * declared.card / M + 1),
      (countingDepthCoeff k M * declared.card).choose j := by
  classical
  set Λ := countingDepthCoeff k M * declared.card
  set ρ := countingBChoiceCoeff k * declared.card / M
  let pos (w : List Bool) : Finset ℕ := (range Λ).filter fun i => w.getD i false = true
  have hpos : ∀ w ∈ W, pos w ∈ (range Λ).powerset.filter (·.card ≤ ρ) := by
    intro w hw
    have hlen := (hW w hw).length_le hM hred hnt hk declared hsupport
    refine mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), ?_⟩
    refine (Nat.le_div_iff_mul_le (by omega)).mpr ((Nat.mul_comm _ _).trans_le
      ((Nat.mul_le_mul_left M (card_le_card fun i hi => ?_)).trans
        ((hW w hw).mul_card_le hM hred hnt hk declared hsupport)))
    obtain ⟨-, hi⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hi⟩
    by_contra hge
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.false_ne_true hi
  have hinj : Set.InjOn pos W := by
    intro w hw w' hw' h
    refine (hW w hw).eq_of_getD_eq (hW w' hw') fun i => ?_
    by_cases hi : i < Λ
    · have := congrArg (i ∈ ·) h
      simp only [pos, mem_filter, mem_range, hi, true_and, eq_iff_iff] at this
      cases hwi : w.getD i false <;> cases hw'i : w'.getD i false <;> simp_all
    · have hl := (hW w hw).length_le hM hred hnt hk declared hsupport
      have hl' := (hW w' hw').length_le hM hred hnt hk declared hsupport
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  calc W.card = (W.image pos).card := (card_image_of_injOn hinj).symm
    _ ≤ ((range Λ).powerset.filter (·.card ≤ ρ)).card :=
        card_le_card fun t ht => by
          obtain ⟨w, hw, rfl⟩ := mem_image.mp ht
          exact hpos w hw
    _ ≤ ((range (ρ + 1)).biUnion fun j => (range Λ).powersetCard j).card := by
        refine card_le_card fun t ht => ?_
        obtain ⟨htΛ, htρ⟩ := mem_filter.mp ht
        exact mem_biUnion.mpr ⟨t.card, mem_range.mpr (by omega),
          mem_powersetCard.mpr ⟨mem_powerset.mp htΛ, rfl⟩⟩
    _ ≤ ∑ j ∈ range (ρ + 1), ((range Λ).powersetCard j).card := card_biUnion_le
    _ = ∑ j ∈ range (ρ + 1), Λ.choose j := by
        refine sum_congr rfl fun j _ => ?_
        rw [card_powersetCard, card_range]

/-- **Exponential leaf-word bound.** Under the integer parameter budget `countingBChoiceCoeff k ≤ M`
and `B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k M * M) ≤ M` (for `2 ≤ k`,
with `1 ≤ B`), any finset `W` of leaf words has cardinality at most `2 ^ (declared.card / B + 1)`.
-/
theorem card_le_two_pow_of_isLeafWord {B : ℕ} (hB : 1 ≤ B)
    (hbudget : 2 ≤ k → countingBChoiceCoeff k ≤ M ∧
      B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k M * M) ≤ M)
    (W : Finset (List Bool)) (hW : ∀ w ∈ W, R.IsLeafWord s w) :
    W.card ≤ 2 ^ (declared.card / B + 1) := by
  refine (card_le_of_isLeafWord hM hred hnt hk declared hsupport W hW).trans ?_
  by_cases hk2 : 2 ≤ k
  · obtain ⟨hΓM, hbud⟩ := hbudget hk2
    exact Cslib.sum_choose_le_two_pow_div_add_one
      (four_le_countingDepthCoeff hk2) (four_le_countingBChoiceCoeff hk2)
      hΓM hB hbud declared.card
  · have hk1 : k ≤ 1 := by omega
    rw [countingDepthCoeff_eq_zero hk1 M, countingBChoiceCoeff_eq_zero hk1]
    simp only [zero_mul, Nat.zero_div, zero_add, range_one, sum_singleton, Nat.choose_zero_right]
    exact Nat.one_le_two_pow

end PathBounds

/-- **Unconditional exponential leaf-word bound at `countingThresholdBase k B`.**
For any `1 ≤ B` and any counting branching rule `R` at `M = countingThresholdBase k B`, any finset
`W` of leaf words from a reduced, nontautological clause set of width `≤ k` over `declared` has
cardinality at most `2 ^ (declared.card / B + 1)`. -/
theorem card_le_two_pow_thresholdBase {k B : ℕ} (hB : 1 ≤ B)
    {R : CountingBranchingRule (fun r => (countingThresholdBase k B) ^ r) V σ} {s : σ}
    (hred : Reduced (R.toClauseSet s))
    (hnt : ∀ C ∈ R.toClauseSet s, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (hk : ∀ C ∈ R.toClauseSet s, C.card ≤ k)
    (declared : Finset V)
    (hsupport : ∀ C ∈ R.toClauseSet s, ∀ l ∈ C, l.1 ∈ declared)
    (W : Finset (List Bool)) (hW : ∀ w ∈ W, R.IsLeafWord s w) :
    W.card ≤ 2 ^ (declared.card / B + 1) :=
  card_le_two_pow_of_isLeafWord (two_le_countingThresholdBase k B) hred hnt hk declared hsupport hB
    (fun hk2 => countingThresholdBase_spec hk2 hB) W hW

end CountingBranchingRule

end Cslib.Logic.PL.ClauseSet.Sparsification
