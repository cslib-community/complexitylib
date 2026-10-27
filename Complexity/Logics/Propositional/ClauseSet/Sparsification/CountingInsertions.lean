/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingSurvival
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Cumulative counting-sparsification insertions

Appendix A.2, Lemma A.3 and equation (A.3) [OpenAI2026ETH] bound actual insertion events along
every path prefix. `countingInsertionCount` sums the new payload at each step, excluding clauses
already in the current node or the root. It does not deduplicate events across steps or discard
insertions whose clauses are later deleted.

For widths at least two, immediate survival gives the exact balance between cumulative insertions,
present marked clauses and cumulative deletions. Summing the marked-occurrence bound over the two
literals per declared variable bounds present clauses. Summing the one-step deletion charge then
gives (A.3). Units are handled by the existing unit-event budget, including B-negated-heart units.
No tree, potential, search algorithm, depth, leaf-count or native-resource result is asserted.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.countingInsertionCount`: cumulative insertion events.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.countingInsertionCount_eq_present_add_deleted`:
  exact higher-width event balance.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingInsertionCount_one_le`: unit-event budget.
* `Cslib.Logic.PL.ClauseSet.Sparsification.card_counting_marked_le`: present-clause bound.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingInsertionCount_le_rec`: recurrence (A.3).
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingInsertionCount_le_pow`: Lemma A.3's closed bound.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.2, Lemma A.3][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of width-`j` insertion events in the first `N` steps. Each summand excludes both
the current node and the initial root; a later deletion does not erase the earlier event. -/
def countingInsertionCount (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal V)) (b : ℕ → Bool) (j : ℕ) : ℕ :=
  ∑ m ∈ range N, ((countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)).filter
    fun C => C.card = j).card

/-- The empty path prefix has no insertion events, regardless of its root. -/
@[simp]
theorem countingInsertionCount_zero (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal V)) (b : ℕ → Bool) (j : ℕ) :
    countingInsertionCount 0 ψ c H b j = 0 := by simp [countingInsertionCount]

/-- Along actual heavy-heart counting steps, every literal remains on a declared root variable.
This does not require a finite ambient variable type, reducedness or nontautology. -/
theorem support_counting_node {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) {t : ℕ} (ht : t ≤ N) :
    ∀ C ∈ ψ t, ∀ l ∈ C, l.1 ∈ declared := by
  induction t with
  | zero => exact hsupport
  | succ t ih =>
    have hprev := ih (by omega)
    obtain ⟨D, hD⟩ := (hheavy t (by omega)).flower_nonempty hθ
    have hH : ∀ l ∈ H t, l.1 ∈ declared :=
      fun l hl => hprev D (flower_subset _ _ _ hD) l ((mem_flower.mp hD).2.2 hl)
    rw [hstep t (by omega)]
    exact support_countingChild (ψ t) (c t) (H t) declared hprev hH (b t)

/-- Unit events, including the negated-heart units, have total at most two per declared variable.
The root-excluding count is bounded by the existing current-excluding unit-event API. -/
theorem countingInsertionCount_one_le {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (declared : Finset V) (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) :
    countingInsertionCount N ψ c H b 1 ≤ 2 * declared.card := by
  refine le_trans ?_ (sum_countingUnitInsertions_le hθ N ψ c H b hstep hheavy
    hred declared hsupport)
  unfold countingInsertionCount
  refine sum_le_sum fun m hm => card_le_card fun C hC => ?_
  obtain ⟨hCI, hC1⟩ := mem_filter.mp hC
  obtain ⟨hCI, hCold⟩ := mem_sdiff.mp hCI
  exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hCI, fun h => hCold (mem_union_left _ h)⟩, hC1⟩

/-- At any counting node, the present marked width-`j ≥ 2` clauses number at most
`4 * declared.card * θ (j - 1)`. Both `Choice` priorities are used by the occurrence supplier. -/
theorem card_counting_marked_le {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i)) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) {t j : ℕ} (ht : t ≤ N)
    (hj : 2 ≤ j) :
    ((ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j).card ≤
      4 * declared.card * θ (j - 1) := by
  let literals := declared ×ˢ (univ : Finset Bool)
  have hs := support_counting_node hθ N ψ c H b hstep (fun i hi => (hchoice i hi).1)
    declared hsupport ht
  have hcover : (ψ t).filter (fun C => C ∉ ψ 0 ∧ C.card = j) ⊆
      literals.biUnion fun l => (ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ {l} ⊆ C := by
    intro C hC
    obtain ⟨hCψ, hCroot, hCj⟩ := mem_filter.mp hC
    obtain ⟨l, hl⟩ : C.Nonempty := card_pos.mp (by omega)
    exact mem_biUnion.mpr ⟨l, mem_product.mpr ⟨hs C hCψ l hl, mem_univ _⟩,
      mem_filter.mpr ⟨hCψ, hCroot, hCj, singleton_subset_iff.mpr hl⟩⟩
  calc
    _ ≤ (literals.biUnion fun l =>
        (ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ {l} ⊆ C).card := card_le_card hcover
    _ ≤ ∑ l ∈ literals,
        ((ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ {l} ⊆ C).card := card_biUnion_le
    _ ≤ ∑ _l ∈ literals, 2 * θ (j - 1) := by
      refine sum_le_sum fun l hl => ?_
      have hbound := card_counting_newContaining_lt hθ N ψ c H b hstep hchoice (j := j) ht
        (S := {l}) (by simp) (by simp only [card_singleton]; omega)
      simpa only [card_singleton] using hbound.le
    _ = 4 * declared.card * θ (j - 1) := by
      simp only [sum_const, smul_eq_mul, literals, card_product, card_univ, Fintype.card_bool]
      ring

/-- For widths at least two, insertion events telescope exactly into currently present marked
clauses plus deletion events. Events are counted at their steps, without a no-reinsertion premise.
Immediate survival and root exclusion are derived from the actual counting path. -/
theorem countingInsertionCount_eq_present_add_deleted {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) {j : ℕ} (hj : 2 ≤ j) :
    countingInsertionCount N ψ c H b j =
      ((ψ N).filter fun C => C ∉ ψ 0 ∧ C.card = j).card +
      ∑ m ∈ range N, ((ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ C ∉ ψ (m + 1)).card := by
  let S (m : ℕ) := (ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j
  let I (m : ℕ) := (countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)).filter
    fun C => C.card = j
  let D (m : ℕ) := (ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ C ∉ ψ (m + 1)
  have hinc (m : ℕ) (hm : m < N) : (I m).card + (S m).card =
      (D m).card + (S (m + 1)).card := by
    have hsurv := countingIntro_filter_eq_node_sdiff hθ N ψ c H b hstep hheavy hred hnt hm hj
    have hI : I m = S (m + 1) \ S m := by
      ext C
      have hsurvC := congrArg (C ∈ ·) hsurv
      simp only [mem_filter, mem_sdiff, mem_union] at hsurvC
      simp only [I, S, mem_filter, mem_sdiff, mem_union]
      tauto
    have hD : D m = S m \ S (m + 1) := by
      ext C
      simp only [D, S, mem_filter, mem_sdiff]
      tauto
    rw [hI, hD, card_sdiff_add_card, card_sdiff_add_card, union_comm]
  suffices ∀ n, n ≤ N → (∑ m ∈ range n, (I m).card) =
      (S n).card + ∑ m ∈ range n, (D m).card from this N le_rfl
  intro n
  induction n with
  | zero =>
    have hS0 : S 0 = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro C hC h
      exact h.1 hC
    simp [hS0]
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hstep := hinc n (by omega)
    rw [sum_range_succ, sum_range_succ]
    omega

/-- Summing the actual one-step deletion charges gives the deletion term of (A.3).
This part requires both `Choice` priorities and reducedness, but not nontautology. -/
theorem sum_counting_deleted_marked_le {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0)) (j : ℕ) :
    (∑ m ∈ range N, ((ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ C ∉ ψ (m + 1)).card) ≤
      2 * ∑ i ∈ Ico 1 j, θ (j - i) * countingInsertionCount N ψ c H b i := by
  calc
    _ ≤ ∑ m ∈ range N, ∑ i ∈ Ico 1 j, 2 * θ (j - i) *
        ((countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)).filter
          fun C => C.card = i).card := by
      refine sum_le_sum fun m hm => ?_
      exact card_counting_deleted_marked_le hθ N ψ c H b hstep hchoice hred (mem_range.mp hm) j
    _ = 2 * ∑ i ∈ Ico 1 j, θ (j - i) * countingInsertionCount N ψ c H b i := by
      rw [sum_comm]
      simp only [countingInsertionCount, mul_sum, mul_assoc]

/-- Equation (A.3) for actual cumulative insertion events along any legal counting-path prefix.
The hypotheses assert actual steps, choices and root invariants; neither the balance nor its
target bounds are assumptions. Units have the sharper bound `countingInsertionCount_one_le`.
-/
theorem countingInsertionCount_le_rec {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (declared : Finset V) (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared)
    {j : ℕ} (hj : 2 ≤ j) :
    countingInsertionCount N ψ c H b j ≤ 4 * declared.card * θ (j - 1) +
      2 * ∑ i ∈ Ico 1 j, θ (j - i) * countingInsertionCount N ψ c H b i := by
  rw [countingInsertionCount_eq_present_add_deleted hθ N ψ c H b hstep
    (fun i hi => (hchoice i hi).1) hred hnt hj]
  exact add_le_add (card_counting_marked_le hθ N ψ c H b hstep hchoice declared hsupport le_rfl hj)
    (sum_counting_deleted_marked_le hθ N ψ c H b hstep hchoice hred j)

/-- Lemma A.3: for thresholds `θ r = M ^ r`, every path prefix has at most
`4 * (3 * M) ^ (j - 1) * declared.card` width-`j` insertion events. This holds for all `j ≥ 1`,
in particular the manuscript's range `1 ≤ j < k` for width-`k` roots. The proof does not divide
by the declared-variable count, so it includes zero variables and zero-length prefixes. -/
theorem countingInsertionCount_le_pow {M : ℕ} (hM : 2 ≤ M)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun r => M ^ r) (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (declared : Finset V) (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared)
    {j : ℕ} (hj : 1 ≤ j) :
    countingInsertionCount N ψ c H b j ≤ 4 * (3 * M) ^ (j - 1) * declared.card := by
  have hθ : ∀ r, 1 ≤ M ^ r := fun r => Nat.one_le_pow r M (by omega)
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj1 : j = 1
    · subst j
      have hunit := countingInsertionCount_one_le hθ N ψ c H b hstep
        (fun i hi => (hchoice i hi).1) hred declared hsupport
      simp only [Nat.sub_self, pow_zero, mul_one]
      omega
    have hj2 : 2 ≤ j := by omega
    have hrec := countingInsertionCount_le_rec hθ N ψ c H b hstep hchoice hred hnt
      declared hsupport hj2
    have hterm (i : ℕ) (hi : i ∈ Ico 1 j) :
        M ^ (j - i) * countingInsertionCount N ψ c H b i ≤
          (4 * declared.card * M ^ (j - 1)) * 3 ^ (i - 1) := by
      obtain ⟨hi1, hij⟩ := mem_Ico.mp hi
      have hpow : M ^ (j - i) * M ^ (i - 1) = M ^ (j - 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ ≤ M ^ (j - i) * (4 * (3 * M) ^ (i - 1) * declared.card) :=
          Nat.mul_le_mul_left _ (ih i hij hi1)
        _ = (4 * declared.card * (M ^ (j - i) * M ^ (i - 1))) * 3 ^ (i - 1) := by
          rw [mul_pow]
          ring
        _ = _ := by rw [hpow]
    have hgeom : 1 + 2 * (∑ i ∈ Ico 1 j, (3 : ℕ) ^ (i - 1)) = 3 ^ (j - 1) := by
      rw [sum_Ico_eq_sum_range]
      simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.reduceAdd, mul_comm, add_comm]
        using geom_sum_mul_add (2 : ℕ) (j - 1)
    calc
      _ ≤ 4 * declared.card * M ^ (j - 1) +
          2 * ∑ i ∈ Ico 1 j, M ^ (j - i) * countingInsertionCount N ψ c H b i := hrec
      _ ≤ 4 * declared.card * M ^ (j - 1) +
          2 * ∑ i ∈ Ico 1 j, (4 * declared.card * M ^ (j - 1)) * 3 ^ (i - 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 (sum_le_sum hterm)) _
      _ = (4 * declared.card * M ^ (j - 1)) *
          (1 + 2 * ∑ i ∈ Ico 1 j, 3 ^ (i - 1)) := by
        rw [← mul_sum]
        ring
      _ = (4 * declared.card * M ^ (j - 1)) * 3 ^ (j - 1) := by rw [hgeom]
      _ = _ := by rw [mul_pow]; ring

/-- The closed insertion bound also holds for any declared-variable budget above the finite
support's cardinality. No inhabitance or positivity of that budget is required. -/
theorem countingInsertionCount_le_pow_of_card_le {M : ℕ} (hM : 2 ≤ M)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun r => M ^ r) (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (declared : Finset V) (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared)
    {n : ℕ} (hn : declared.card ≤ n) {j : ℕ} (hj : 1 ≤ j) :
    countingInsertionCount N ψ c H b j ≤ 4 * (3 * M) ^ (j - 1) * n :=
  (countingInsertionCount_le_pow hM N ψ c H b hstep hchoice hred hnt declared hsupport hj).trans
    (Nat.mul_le_mul_left _ hn)

end Cslib.Logic.PL.ClauseSet.Sparsification
