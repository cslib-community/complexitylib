/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingInsertions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Depth and B-choice budgets for actual counting paths

Appendix A.3 [OpenAI2026ETH], printed p.46, obtains depth `C * n` and at most `Γ * n / M`
B-choices from actual insertion events, where `C = 4 * ∑ r < k - 1, (3 * M) ^ r` and
`Γ = 4 * ∑ r < k - 1, 3 ^ r`. Here the B-budget is stated as `M * #B ≤ Γ * n`, without division.

Every step inserts a genuinely new heart or petal of width between one and `k - 1`; every B-step
of petal width `j` inserts at least `M ^ j` such clauses. Summing these lower bounds against the
cumulative insertion bounds proves both budgets. There is no replacement by distinct-clause counts
and no assumed path-length bound. The empty sums at `k ≤ 1` force zero steps. No ambient finite
variable type or positivity of the declared-variable count is needed.

The input is the existing Nat-indexed actual counting path. Tree/search clients can obtain it from
successive word prefixes and their branching rule's choice witnesses. Node/leaf-word counting,
effective parameter selection and native resource bounds remain separate consumer obligations.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.card_le_counting_node`: root width is preserved.
* `Cslib.Logic.PL.ClauseSet.Sparsification.counting_new_nonempty`: every step inserts a new clause.
* `Cslib.Logic.PL.ClauseSet.Sparsification.counting_length_le_sum_insertions`: depth lower charge.
* `Cslib.Logic.PL.ClauseSet.Sparsification.mul_card_counting_petalSteps_le`: B-step lower charge.
* `Cslib.Logic.PL.ClauseSet.Sparsification.counting_length_le`: the `C * n` depth bound.
* `Cslib.Logic.PL.ClauseSet.Sparsification.mul_card_counting_B_le`: the `Γ * n` weighted B-budget.
* `Cslib.Logic.PL.ClauseSet.Sparsification.counting_path_budgets_of_card_le`: declared-budget form.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.3][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- All clauses along an actual heavy-heart counting path retain the root width bound.
The payload-width theorem includes the additional negated-heart units. -/
theorem card_le_counting_node {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) {t : ℕ} (ht : t ≤ N) : ∀ C ∈ ψ t, C.card ≤ k := by
  induction t with
  | zero => exact hk
  | succ t ih =>
    have hprev := ih (by omega)
    obtain ⟨D, hD⟩ := (hheavy t (by omega)).flower_nonempty hθ
    have hck : c t ≤ k := (mem_flower.mp hD).2.1 ▸ hprev D (flower_subset _ _ _ hD)
    intro C hC
    rw [hstep t (by omega), countingChild_eq_reduce_union] at hC
    rcases mem_union.mp (reduce_subset _ hC) with hC | hC
    · exact hprev C hC
    · exact (card_lt_of_mem_countingIntro (hheavy t (by omega)) hC).le.trans hck

/-- Every selected width is at most the root width bound. -/
theorem counting_selected_width_le {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) {m : ℕ} (hm : m < N) : c m ≤ k := by
  obtain ⟨C, hC⟩ := (hheavy m hm).flower_nonempty hθ
  exact (mem_flower.mp hC).2.1 ▸
    card_le_counting_node hθ N ψ c H b hstep hheavy hk hm.le C (flower_subset _ _ _ hC)

/-- Every heart/petal is genuinely new, including width-one petals. This excludes the current
node and root using reducedness and root-subclause witnesses, without nontautology. -/
theorem intro_subset_counting_new {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    {m : ℕ} (hm : m < N) :
    intro (ψ m) (c m) (H m) (b m) ⊆
      countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0) := by
  have hredm : Reduced (ψ m) := by
    cases m with
    | zero => exact hred
    | succ m =>
      rw [hstep m (by omega), countingChild_eq_reduce_union]
      exact reduced_reduce _
  intro C hC
  have hCI : C ∈ countingIntro (ψ m) (c m) (H m) (b m) := by
    cases hb : b m with
    | false => simpa only [hb, intro, countingIntro] using hC
    | true =>
      rw [countingIntro]
      exact mem_union_left _ (by simpa only [hb, intro] using hC)
  refine mem_sdiff.mpr ⟨hCI, ?_⟩
  intro hCold
  rcases mem_union.mp hCold with hCold | hCold
  · exact notMem_of_mem_intro hθ hredm (hheavy m hm) hC hCold
  · obtain ⟨D, hD, hDC⟩ := exists_mem_counting_node_subset N ψ c H b hstep hm.le hCold
    obtain ⟨E, hE, hCE⟩ := exists_flower_ssuperset hθ (hheavy m hm) hC
    exact hredm E (flower_subset _ _ _ hE) D hD
      (Finset.ssubset_of_subset_of_ssubset hDC hCE)

/-- Every legal counting step has at least one insertion absent from current and root.
The witness is a heart or petal, so already-present B-negated units do not affect this fact. -/
theorem counting_new_nonempty {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    {m : ℕ} (hm : m < N) :
    (countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)).Nonempty :=
  (intro_nonempty hθ (hheavy m hm) (b m)).mono
    (intro_subset_counting_new hθ N ψ c H b hstep hheavy hred hm)

/-- Every actual payload width lies in `[1,k)`, where `k` bounds the root widths. -/
theorem card_mem_Ico_of_mem_countingIntro {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) {m : ℕ} (hm : m < N) {C : Finset (Literal V)}
    (hC : C ∈ countingIntro (ψ m) (c m) (H m) (b m)) : C.card ∈ Ico 1 k := by
  have hpos := card_pos.mpr
    (countingIntro_nonempty (hheavy m hm).1 (hheavy m hm).2.1 hC)
  exact mem_Ico.mpr ⟨hpos, (card_lt_of_mem_countingIntro (hheavy m hm) hC).trans_le
    (counting_selected_width_le hθ N ψ c H b hstep hheavy hk hm)⟩

/-- Charging each step to its nonempty insertion batch bounds path length by the sum of
width-indexed event counts. No deduplication across steps or terminal-sparsity premise is used. -/
theorem counting_length_le_sum_insertions {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0)) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) : N ≤ ∑ j ∈ Ico 1 k, countingInsertionCount N ψ c H b j := by
  let I (m : ℕ) := countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)
  calc
    N = ∑ _m ∈ range N, 1 := by simp
    _ ≤ ∑ m ∈ range N, (I m).card := by
      refine sum_le_sum fun m hm => ?_
      exact card_pos.mpr (counting_new_nonempty hθ N ψ c H b hstep hheavy hred (mem_range.mp hm))
    _ = ∑ m ∈ range N, ∑ j ∈ Ico 1 k, ((I m).filter (·.card = j)).card := by
      refine sum_congr rfl fun m hm => card_eq_sum_card_fiberwise fun C hC => ?_
      exact card_mem_Ico_of_mem_countingIntro hθ N ψ c H b hstep hheavy hk
        (mem_range.mp hm) (mem_sdiff.mp hC).1
    _ = ∑ j ∈ Ico 1 k, countingInsertionCount N ψ c H b j := by
      rw [sum_comm]
      rfl

/-- A B-step of petal width `j` inserts at least `θ j` new width-`j` clauses. Summing these
per-step contributions gives a lower bound on actual cumulative insertion events, including `j=1`.
-/
theorem mul_card_counting_petalSteps_le {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0)) (j : ℕ) :
    θ j * ((range N).filter fun m => b m = true ∧ c m - (H m).card = j).card ≤
      countingInsertionCount N ψ c H b j := by
  let S := (range N).filter fun m => b m = true ∧ c m - (H m).card = j
  let I (m : ℕ) := (countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)).filter
    fun C => C.card = j
  calc
    _ = ∑ _m ∈ S, θ j := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ m ∈ S, (I m).card := by
      refine sum_le_sum fun m hm => ?_
      obtain ⟨hmN, hb, hj⟩ := mem_filter.mp hm
      have hm' := mem_range.mp hmN
      have hnew := intro_subset_counting_new hθ N ψ c H b hstep hheavy hred hm'
      have hsub : petals (ψ m) (c m) (H m) ⊆ I m := by
        intro C hC
        refine mem_filter.mpr ⟨hnew ?_, (card_of_mem_petals hC).trans hj⟩
        simpa only [hb, intro] using hC
      calc
        θ j ≤ (flower (ψ m) (c m) (H m)).card := hj ▸ (hheavy m hm').2.2
        _ = (petals (ψ m) (c m) (H m)).card := (card_petals _ _ _).symm
        _ ≤ (I m).card := card_le_card hsub
    _ ≤ ∑ m ∈ range N, (I m).card := sum_le_sum_of_subset (filter_subset _ _)
    _ = countingInsertionCount N ψ c H b j := rfl

/-- Actual counting paths have depth at most `C * declared.card`, with the source's
`C = 4 * ∑ r < k - 1, (3 * M) ^ r`. At `k ≤ 1` the empty sum forces zero steps. -/
theorem counting_length_le {M : ℕ} (hM : 2 ≤ M)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun r => M ^ r) (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) :
    N ≤ (4 * ∑ r ∈ range (k - 1), (3 * M) ^ r) * declared.card := by
  have hθ : ∀ r, 1 ≤ M ^ r := fun r => Nat.one_le_pow r M (by omega)
  calc
    N ≤ ∑ j ∈ Ico 1 k, countingInsertionCount N ψ c H b j :=
      counting_length_le_sum_insertions hθ N ψ c H b hstep (fun i hi => (hchoice i hi).1) hred hk
    _ ≤ ∑ j ∈ Ico 1 k, 4 * (3 * M) ^ (j - 1) * declared.card := by
      refine sum_le_sum fun j hj => ?_
      exact countingInsertionCount_le_pow hM N ψ c H b hstep hchoice hred hnt declared hsupport
        (mem_Ico.mp hj).1
    _ = _ := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, mul_sum, sum_mul, mul_assoc]

/-- At each fixed petal width, the B-step budget keeps one factor of `M` after canceling a
positive power of `M`. There is no division by the number of declared variables. -/
theorem mul_card_counting_petalSteps_le_pow {M : ℕ} (hM : 2 ≤ M)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun r => M ^ r) (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (declared : Finset V) (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared)
    {j : ℕ} (hj : 1 ≤ j) :
    M * ((range N).filter fun m => b m = true ∧ c m - (H m).card = j).card ≤
      4 * 3 ^ (j - 1) * declared.card := by
  have hθ : ∀ r, 1 ≤ M ^ r := fun r => Nat.one_le_pow r M (by omega)
  have hcharge := mul_card_counting_petalSteps_le hθ N ψ c H b hstep
    (fun i hi => (hchoice i hi).1) hred j
  have hbound := countingInsertionCount_le_pow hM N ψ c H b hstep hchoice hred hnt
    declared hsupport hj
  have hpow : M ^ j = M ^ (j - 1) * M := by
    rw [← pow_succ]
    congr 1
    omega
  apply Nat.le_of_mul_le_mul_left (c := M ^ (j - 1)) _ (pow_pos (by omega : 0 < M) _)
  calc
    _ = M ^ j * ((range N).filter fun m => b m = true ∧ c m - (H m).card = j).card := by
      rw [hpow, mul_assoc]
    _ ≤ countingInsertionCount N ψ c H b j := hcharge
    _ ≤ 4 * (3 * M) ^ (j - 1) * declared.card := hbound
    _ = _ := by rw [mul_pow]; ring

/-- The source's weighted B-choice budget: `M * #B ≤ Γ * declared.card`, where
`Γ = 4 * ∑ r < k - 1, 3 ^ r`. This includes `k ≤ 1` and zero declared variables. -/
theorem mul_card_counting_B_le {M : ℕ} (hM : 2 ≤ M)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun r => M ^ r) (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) :
    M * ((range N).filter fun m => b m = true).card ≤
      (4 * ∑ r ∈ range (k - 1), 3 ^ r) * declared.card := by
  have hθ : ∀ r, 1 ≤ M ^ r := fun r => Nat.one_le_pow r M (by omega)
  have hmaps : ∀ m ∈ (range N).filter (fun m => b m = true), c m - (H m).card ∈ Ico 1 k := by
    intro m hm
    have hm' := mem_range.mp (mem_filter.mp hm).1
    have hheavy := (hchoice m hm').1
    have hck := counting_selected_width_le hθ N ψ c H b hstep
      (fun i hi => (hchoice i hi).1) hk hm'
    apply mem_Ico.mpr
    have := hheavy.1
    have := hheavy.2.1
    omega
  have hfiber : ((range N).filter (fun m => b m = true)).card =
      ∑ j ∈ Ico 1 k, ((range N).filter fun m => b m = true ∧ c m - (H m).card = j).card := by
    rw [card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl fun j hj => ?_
    congr 1
    ext m
    simp only [mem_filter]
    tauto
  rw [hfiber, mul_sum]
  calc
    _ ≤ ∑ j ∈ Ico 1 k, 4 * 3 ^ (j - 1) * declared.card := by
      refine sum_le_sum fun j hj => ?_
      exact mul_card_counting_petalSteps_le_pow hM N ψ c H b hstep hchoice hred hnt
        declared hsupport (mem_Ico.mp hj).1
    _ = _ := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, mul_sum, sum_mul, mul_assoc]

/-- Both actual path budgets hold for any declared-variable budget above the finite support's
cardinality, including zero. The B-budget retains the source's exact coefficient `Γ`. -/
theorem counting_path_budgets_of_card_le {M : ℕ} (hM : 2 ≤ M)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun r => M ^ r) (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) {k : ℕ}
    (hk : ∀ C ∈ ψ 0, C.card ≤ k) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) {n : ℕ} (hn : declared.card ≤ n) :
    N ≤ (4 * ∑ r ∈ range (k - 1), (3 * M) ^ r) * n ∧
      M * ((range N).filter fun m => b m = true).card ≤
        (4 * ∑ r ∈ range (k - 1), 3 ^ r) * n :=
  ⟨(counting_length_le hM N ψ c H b hstep hchoice hred hnt hk declared hsupport).trans
      (Nat.mul_le_mul_left _ hn),
    (mul_card_counting_B_le hM N ψ c H b hstep hchoice hred hnt hk declared hsupport).trans
      (Nat.mul_le_mul_left _ hn)⟩

end Cslib.Logic.PL.ClauseSet.Sparsification
