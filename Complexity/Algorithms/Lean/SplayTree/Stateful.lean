/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.SearchTree.Stateful
public import Complexity.Algorithms.Lean.SplayTree.AccessLemma

/-!
# Self-Adjusting Stateful Ordered-Set Realization by Splay Trees

This module realizes the shared `Cslib.OrderedSet.spec α` interface (`contains`, `insert`, `erase`,
`minimum`, `successor`) using annotation-free bottom-up splay trees ([SleatorTarjan1985b],
Section 3, pp. 660–665), reusing the shared `Cslib.Algorithms.Lean.SearchTree.Rep` representation
relation (`Ordered t ∧ elements t = s`) and `SearchTree.rep_empty` directly on `BinaryTree α`.

## Self-adjustment and amortized vs. worst-case guarantees

Unlike `Cslib.Algorithms.Lean.AVLTree.realization`, splay trees store no balance metadata and
restructure the concrete `BinaryTree α` even during read queries (`contains`, `minimum`,
`successor`). The `Cslib.Stateful.Realization` framework accommodates this directly: read queries
leave the abstract `Finset α` state unchanged while transitioning `t` to a newly splayed tree `t'`
satisfying `SearchTree.Rep s t'`.

Because a single operation on an unbalanced initial tree can perform up to `s.card - 1` rotations,
no logarithmic per-operation worst-case `Cslib.Stateful.Bound` holds on arbitrary trees. Instead,
by telescoping `unitPotential` across any adaptive client execution (`Executes Exec`), this module
proves a single-tree `OrderedSet.spec α` dictionary specialization/analogue of Sleator and Tarjan's
**Balance Theorem with Updates** ([SleatorTarjan1985b], Section 3, Theorem 6, p. 665; whereas
Theorem 6 treats multi-tree sequences of `access`, `insert`, `delete`, `join`, and `split`, here we
instantiate single-tree `contains`, `insert`, `erase`, `minimum`, and `successor` and count exact
edge rotations, with unit-weight `split`/`join` bounds proved in `AccessLemma.lean`):
* In `ℝ` (`executes_amortized_real_le`), any adaptive client execution from `SearchTree.Rep s t`
  satisfies `(total id ns : ℝ) + unitPotential t' - unitPotential t ≤ realHistoryCost s history`,
  where each step charges `7 log₂(|s_j| + 1) + 3`.
* In `ℕ` (`executes_total_le_of_empty`, `run_correct_empty`), starting from `.nil`
  (`SearchTree.rep_empty`), total rotations satisfy
  `total id ns ≤ (spec α).totalCost amortizedCharge ∅ history` with
  `amortizedCharge s _ = 7 * Nat.log 2 (s.card + 1) + 10`, matching the discrete `Spec.totalCost`
  idiom of `SearchTree` and `AVLTree`.

## Cost model and limitations

Native traces record exact binary-tree edge rotations per operation (`0` on empty trees or root
hits). On non-empty trees, downward path visits satisfy `visits = rotations + 1`. Ancestor-stack
allocation, node allocation, key-comparison implementation, and pure client continuations are not
charged as RAM or Turing-machine instructions.

## Main definitions

* `StepResult`, `step`, `Exec`: self-adjusting single-operation execution and native trace relation.
* `realization`: `Cslib.Stateful.Realization` of `Cslib.OrderedSet.spec α` reusing
  `Cslib.Algorithms.Lean.SearchTree.Rep`.
* `realOpCharge`, `realHistoryCost`, `amortizedCharge`: continuous (`Real.logb 2`) and discrete
  (`Nat.log 2`) per-operation amortized rotation budgets.
* `ClientRun`, `run`: executable adaptive client runner with named output fields.

## Main results

* `exec_unitPotential_amortized_le`: uniform unit-weight single-step rotation bound across all five
  `OrderedSet.Op α` operations (combining the unit-weight specialization of [SleatorTarjan1985b],
  Section 3, Lemma 2, pp. 663–664 for `contains`, `insert`, and `erase` with the Access-Lemma
  companion bounds for `minimum` and `successor`).
* `executes_amortized_real_le`, `executes_rotations_le_realHistoryCost_of_empty`: real-valued
  telescoping amortized bounds across arbitrary adaptive `OrderedSet.spec` clients (single-tree
  dictionary analogue of [SleatorTarjan1985b], Section 3, Theorem 6, p. 665).
* `executes_total_le`, `executes_total_le_of_empty`, `run_correct`, `run_correct_empty`: discrete
  `Spec.totalCost` rotation bounds and full semantic + amortized correctness for `run`.

## References

* [SleatorTarjan1985b] Daniel Dominic Sleator and Robert Endre Tarjan,
  *Self-Adjusting Binary Search Trees*, Journal of the ACM 32(3), Section 3, pp. 660–665, 1985.
-/

public section

namespace Cslib.Algorithms.Lean.SplayTree

open Cslib.Stateful Cslib.OrderedSet
open Cslib.Algorithms.Lean.SearchTree (elements Ordered Rep rep_empty)

variable {α : Type} [LinearOrder α]

/-- Output of a single self-adjusting `OrderedSet.Op α` step on a `BinaryTree α`. -/
structure StepResult (α : Type) [LinearOrder α] (o : Op α) where
  /-- Restructured splay tree after the operation. -/
  tree : BinaryTree α
  /-- Operation result of type `(OrderedSet.spec α).Result o`. -/
  answer : (spec α).Result o
  /-- Exact number of binary-tree edge rotations executed. -/
  rotations : ℕ

/-- Execute one `OrderedSet.Op α` on a splay tree, splaying on queries as well as updates. -/
@[expose] def step (t : BinaryTree α) (o : Op α) : StepResult α o :=
  match o with
  | .contains x =>
      let res := contains x t
      ⟨res.tree, res.answer, res.rotations⟩
  | .insert x =>
      let res := insert x t
      ⟨res.tree, (), res.rotations⟩
  | .erase x =>
      let res := erase x t
      ⟨res.tree, (), res.rotations⟩
  | .minimum =>
      let res := minimum t
      ⟨res.tree, res.answer, res.rotations⟩
  | .successor x =>
      let res := successor x t
      ⟨res.tree, res.answer, res.rotations⟩

/-- Native execution relation for `OrderedSet.spec α` over self-adjusting `BinaryTree α`,
recording exact rotation counts. -/
@[expose] def Exec : Execution (spec α) (BinaryTree α) ℕ :=
  fun t o a t' n => step t o = ⟨t', a, n⟩

/-- Self-adjusting semantic realization of `OrderedSet.spec α` by `BinaryTree α`, reusing
`Cslib.Algorithms.Lean.SearchTree.Rep`. -/
@[expose] def realization : Realization (spec α) (Exec (α := α)) where
  rep := Rep
  total {_ t} o _ _ :=
    match h : step t o with
    | ⟨t', a, n⟩ => ⟨a, t', n, h⟩
  correct {s t o a t' n} hr _ he := by
    obtain ⟨ht, rfl⟩ := hr
    cases o with
    | contains x =>
      cases he
      refine ⟨?_, ordered_contains ht x, elements_contains x t⟩
      rw [Bool.eq_iff_iff, contains_answer_eq_true ht x, decide_eq_true_eq]
    | insert x =>
      cases he
      exact ⟨rfl, ordered_insert ht x, elements_insert x t⟩
    | erase x =>
      cases he
      exact ⟨rfl, ordered_erase ht x, elements_erase ht x⟩
    | minimum =>
      cases he
      exact ⟨(minimum_spec ht).eq_least, ordered_minimum ht, elements_minimum t⟩
    | successor x =>
      cases he
      exact ⟨(successor_spec ht x).eq_least, ordered_successor ht x, elements_successor x t⟩

@[simp] theorem realization_rep : (realization (α := α)).rep = Rep := rfl

/-! ### Amortized Rotation Bounds Across Adaptive Clients -/

/-- Continuous per-operation amortized rotation charge `7 log₂(|s| + 1) + 3`. -/
@[expose] noncomputable def realOpCharge (s : Finset α) (_ : Op α) : ℝ :=
  7 * Real.logb 2 ((s.card : ℝ) + 1) + 3

/-- Sum of `realOpCharge` along an abstract `OrderedSet.spec α` operation history. -/
@[expose] noncomputable def realHistoryCost (s : Finset α) : List (Op α) → ℝ
  | [] => 0
  | o :: os => realOpCharge s o + realHistoryCost ((spec α).step s o).1 os

@[simp] theorem realHistoryCost_nil (s : Finset α) : realHistoryCost s [] = 0 := rfl

@[simp] theorem realHistoryCost_cons (s : Finset α) (o : Op α) (os : List (Op α)) :
    realHistoryCost s (o :: os) = realOpCharge s o + realHistoryCost ((spec α).step s o).1 os :=
  rfl

/-- Discrete `ℕ`-valued per-operation amortized rotation budget
`7 * Nat.log 2 (s.card + 1) + 10`, upper-bounding `realOpCharge s o` via `⌊log₂(n + 1)⌋ + 1`. -/
@[expose] def amortizedCharge (s : Finset α) (_ : Op α) : ℕ :=
  7 * Nat.log 2 (s.card + 1) + 10

private theorem logb_two_add_one_le_nat_log (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 1) ≤ (Nat.log 2 (n + 1) : ℝ) + 1 := by
  have hlt : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (n + 1)
  have hle : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (Nat.log 2 (n + 1) + 1) := by
    exact_mod_cast hlt.le
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hle
  rw [Real.logb_pow, Real.logb_self_eq_one (b := 2) (by norm_num)] at hlog
  push_cast at hlog
  linarith

omit [LinearOrder α] in
theorem realOpCharge_le_amortizedCharge (s : Finset α) (o : Op α) :
    realOpCharge s o ≤ (amortizedCharge s o : ℝ) := by
  have h := logb_two_add_one_le_nat_log s.card
  simp only [realOpCharge, amortizedCharge, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem realHistoryCost_le_totalCost (s : Finset α) (os : List (Op α)) :
    realHistoryCost s os ≤ ((spec α).totalCost amortizedCharge s os : ℝ) := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih =>
    simp only [realHistoryCost_cons, Spec.totalCost_cons, Nat.cast_add]
    linarith [realOpCharge_le_amortizedCharge s o, ih ((spec α).step s o).1]

/-- Uniform unit-weight amortized rotation bound across all five `OrderedSet.Op α` operations,
combining the unit-weight specialization of [SleatorTarjan1985b], Section 3, Lemma 2, pp. 663–664
for `contains`, `insert`, and `erase` with the companion Access-Lemma bounds for `minimum` and
`successor`. -/
theorem exec_unitPotential_amortized_le {s : Finset α} {t t' : BinaryTree α} {o : Op α}
    {a : (spec α).Result o} {n : ℕ} (hr : Rep s t) (he : Exec t o a t' n) :
    (n : ℝ) + unitPotential t' - unitPotential t ≤ realOpCharge s o := by
  obtain ⟨ht, rfl⟩ := hr
  have hL : 0 ≤ Real.logb 2 (((elements t).card : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (elements t).card := Nat.cast_nonneg _
    exact Real.logb_nonneg (by norm_num) (by linarith)
  simp only [realOpCharge]
  cases o with
  | contains x =>
    cases he
    linarith [contains_unitPotential_amortized_le ht x]
  | insert x =>
    cases he
    linarith [insert_unitPotential_amortized_le ht x]
  | erase x =>
    cases he
    linarith [erase_unitPotential_amortized_le ht x]
  | minimum =>
    cases he
    linarith [minimum_unitPotential_amortized_le ht]
  | successor x =>
    cases he
    linarith [successor_unitPotential_amortized_le ht x]

/-- Single-tree `OrderedSet.spec α` dictionary analogue of the **Balance Theorem with Updates**
([SleatorTarjan1985b], Section 3, Theorem 6, p. 665; real-valued telescoping form): for any
adaptive client `p` executed from `SearchTree.Rep s t`, the total rotation count plus potential
change is bounded by `realHistoryCost` along the induced abstract history. -/
theorem executes_amortized_real_le {β : Type} {p : (spec α).Client β}
    {s : Finset α} {t t' : BinaryTree α} {a : β} {ns : List ℕ}
    (hr : Rep s t) (he : Executes Exec p t a t' ns) :
    let (_, _, history) := (spec α).runClient s p
    (total id ns : ℝ) + unitPotential t' - unitPotential t ≤
      realHistoryCost s history := by
  induction he generalizing s with
  | pure a t =>
    simp
  | call hstep hrest ih =>
    obtain ⟨ha, hr'⟩ := realization.correct hr trivial hstep
    have hop := exec_unitPotential_amortized_le hr hstep
    subst ha
    have htail := ih hr'
    simp only [total_cons, id_eq, Spec.runClient_liftBind, realHistoryCost_cons, Nat.cast_add]
      at htail ⊢
    linarith

/-- Starting from `.nil` (`SearchTree.rep_empty`), the real-valued total rotation count of any
adaptive `OrderedSet.spec α` client `p` is bounded by `realHistoryCost` along its abstract history
(single-tree dictionary analogue of [SleatorTarjan1985b], Section 3, Theorem 6, p. 665). -/
theorem executes_rotations_le_realHistoryCost_of_empty {β : Type} {p : (spec α).Client β}
    {t' : BinaryTree α} {a : β} {ns : List ℕ}
    (he : Executes Exec p .nil a t' ns) :
    let (_, _, history) := (spec α).runClient ∅ p
    (total id ns : ℝ) ≤ realHistoryCost ∅ history := by
  have htel := executes_amortized_real_le rep_empty he
  have hpot := unitPotential_nonneg t'
  simp only [unitPotential_nil] at htel
  linarith

/-- Discrete `ℕ`-valued total rotation bound from an arbitrary initial tree `SearchTree.Rep s t`,
charging `amortizedCharge` per operation plus the initial potential allowance
`s.card * (Nat.log 2 (s.card + 1) + 1)`. -/
theorem executes_total_le {β : Type} {p : (spec α).Client β}
    {s : Finset α} {t t' : BinaryTree α} {a : β} {ns : List ℕ}
    (hr : Rep s t) (he : Executes Exec p t a t' ns) :
    let (_, _, history) := (spec α).runClient s p
    total id ns ≤
      (spec α).totalCost amortizedCharge s history +
        s.card * (Nat.log 2 (s.card + 1) + 1) := by
  have htel := executes_amortized_real_le hr he
  have hhist :=
    realHistoryCost_le_totalCost s (let (_, _, history) := (spec α).runClient s p; history)
  dsimp only at htel hhist ⊢
  have hpot_end := unitPotential_nonneg t'
  have hpot_init : unitPotential t ≤ (s.card : ℝ) * ((Nat.log 2 (s.card + 1) : ℝ) + 1) := by
    obtain ⟨ht, helem⟩ := hr
    have h1 := unitPotential_le_card_mul_logb ht
    rw [helem] at h1
    have h2 := logb_two_add_one_le_nat_log s.card
    have hcard_nn : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    nlinarith
  refine Nat.cast_le (α := ℝ).mp ?_
  push_cast
  linarith

/-- Single-tree `OrderedSet.spec α` dictionary analogue of the **Balance Theorem with Updates**
([SleatorTarjan1985b], Section 3, Theorem 6, p. 665; `ℕ`-valued `Spec.totalCost` form): starting
from `.nil`, any adaptive client `p` executes at most
`(spec α).totalCost amortizedCharge ∅ history` total rotations. -/
theorem executes_total_le_of_empty {β : Type} {p : (spec α).Client β}
    {t' : BinaryTree α} {a : β} {ns : List ℕ}
    (he : Executes Exec p .nil a t' ns) :
    let (_, _, history) := (spec α).runClient ∅ p
    total id ns ≤ (spec α).totalCost amortizedCharge ∅ history := by
  simpa using executes_total_le rep_empty he

/-! ### Executable Adaptive Client Runner -/

/-- Named output record of executing an adaptive `(OrderedSet.spec α).Client β` on a splay tree. -/
structure ClientRun (α β : Type) where
  /-- Final client return value. -/
  value : β
  /-- Final self-adjusted splay tree. -/
  tree : BinaryTree α
  /-- Per-operation rotation counts in execution order. -/
  rotations : List ℕ
  deriving DecidableEq, Repr

/-- Execute an adaptive `OrderedSet` client concretely on a splay tree, recording exact rotation
counts per operation. -/
@[expose] def run {β : Type} (t : BinaryTree α) : (spec α).Client β → ClientRun α β
  | .pure a => ⟨a, t, []⟩
  | .liftBind o k =>
      let sres := step t o
      let cres := run sres.tree (k sres.answer)
      ⟨cres.value, cres.tree, sres.rotations :: cres.rotations⟩

/-- The concrete runner produces a valid `Executes Exec` derivation. -/
theorem run_exec {β : Type} (p : (spec α).Client β) (t : BinaryTree α) :
    Executes Exec p t (run t p).value (run t p).tree (run t p).rotations := by
  induction p generalizing t with
  | pure a => exact .pure a t
  | liftBind o k ih =>
    simp only [run]
    exact .call rfl (ih (step t o).answer (step t o).tree)

/-- Running the concrete splay-tree interpreter from `SearchTree.Rep s t` agrees with abstract
`Finset α` semantics, preserves `SearchTree.Rep`, and satisfies the amortized logarithmic rotation
bound. -/
theorem run_correct {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : BinaryTree α} (hr : Rep s t) :
    let (value, finalState, history) := (spec α).runClient s p
    (run t p).value = value ∧
      Rep finalState (run t p).tree ∧
      total id (run t p).rotations ≤
        (spec α).totalCost amortizedCharge s history +
          s.card * (Nat.log 2 (s.card + 1) + 1) := by
  have hexec := run_exec p t
  have htot := executes_total_le hr hexec
  dsimp only at htot ⊢
  have hc :=
    realization.correct_client hr ((spec α).validHistory_of_forall_valid (fun _ _ => trivial) s _)
      hexec
  exact ⟨hc.1, hc.2, htot⟩

/-- Running an adaptive `OrderedSet` client starting from `.nil` agrees with `Finset α` semantics,
preserves `SearchTree.Rep`, and satisfies `total id (run .nil p).rotations ≤ totalCost
amortizedCharge` with zero initial potential overhead. -/
theorem run_correct_empty {β : Type} (p : (spec α).Client β) :
    let (value, finalState, history) := (spec α).runClient ∅ p
    (run .nil p).value = value ∧
      Rep finalState (run .nil p).tree ∧
      total id (run .nil p).rotations ≤
        (spec α).totalCost amortizedCharge ∅ history := by
  have h := run_correct p rep_empty
  simpa using h

end Cslib.Algorithms.Lean.SplayTree
