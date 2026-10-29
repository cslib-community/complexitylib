/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

public import Complexity.Foundations.Data.List.Counting
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTree

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification

namespace ComplexityTests.SparsificationCountingTree

private theorem count_eq_card {V : Type*} [DecidableEq V]
    (ψ : ClauseSet V) (s : Finset V) :
    ψ.toCNF.modelCountOn s = (Finset.univ.filter fun σ : s → Bool =>
      ψ.Sat (fun v => if h : v ∈ s then σ ⟨v, h⟩ else false)).card := by
  unfold CNF.modelCountOn
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ClauseSet.eval_toCNF_eq_true_iff]

private theorem one_le_two_pow : ∀ j, 1 ≤ j → 1 ≤ 2 ^ j :=
  fun _ _ => Nat.one_le_two_pow

/-! ### 1. Sharpness of `2 ≤ (flower ψ c H).card` for potential decrease -/

-- A single width-2 clause (`z = 1`, `c = 2`, `|H| = 1`) has potential `4`, and its petal-plus-unit
-- child `{{(1, true)}, {(0, false)}}` also has potential `2 + 2 = 4`: `z ≥ 2` cannot be dropped.
private def singleFlower : ClauseSet (Fin 2) :=
  {{(0, true), (1, true)}}

example : potential singleFlower = 4 := by decide

example : (flower singleFlower 2 {(0, true)}).card = 1 := by decide

example : potential (countingChild singleFlower 2 {(0, true)} true) = 4 := by decide

-- With two clauses (`z = 2`), both branches strictly drop below potential `8` (`2 < 8`, `6 < 8`).
private def twoFlower : ClauseSet (Fin 3) :=
  {{(0, true), (1, true)}, {(0, true), (2, true)}}

example : potential twoFlower = 8 := by decide

example : potential (countingChild twoFlower 2 {(0, true)} false) = 2 := by decide

example : potential (countingChild twoFlower 2 {(0, true)} true) = 6 := by decide

/-! ### 2. Multi-step recursion (`depth = 2`, `3` sparse leaves) under `θ j = 2 ^ j` -/

-- At the root:
--   `C₁ = {(0, true), (1, true), (2, true)}`, `C₂ = {(0, true), (1, true), (3, true)}` (width 3),
--   `E₁ = {(1, true), (4, true)}` (width 2).
-- Step 1 uniquely selects `(3, {(0, true), (1, true)})`.
-- Its `false` (heart) child `{{(0, true), (1, true)}, {(1, true), (4, true)}}` creates a new
-- width-2 flower around `{(1, true)}` and branches a second time into `leaf₀₀` and `leaf₀₁`, while
-- its `true` (petal + negated-heart-units) child `leaf₁` is already `(2 ^ ·)`-sparse.
private def multiRoot : ClauseSet (Fin 5) :=
  {{(0, true), (1, true), (2, true)},
   {(0, true), (1, true), (3, true)},
   {(1, true), (4, true)}}

private def child₀ : ClauseSet (Fin 5) :=
  {{(0, true), (1, true)}, {(1, true), (4, true)}}

private def leaf₀₀ : ClauseSet (Fin 5) :=
  {{(1, true)}}

private def leaf₀₁ : ClauseSet (Fin 5) :=
  {{(1, false)}, {(0, true)}, {(4, true)}}

private def leaf₁ : ClauseSet (Fin 5) :=
  {{(0, false)}, {(1, false)}, {(2, true)}, {(3, true)}, {(1, true), (4, true)}}

-- Potentials strictly decrease along every branch: `20 → 8 → 2`, `20 → 8 → 6`, and `20 → 12`.
example : potential multiRoot = 20 ∧ potential child₀ = 8 ∧
    potential leaf₀₀ = 2 ∧ potential leaf₀₁ = 6 ∧ potential leaf₁ = 12 := by
  decide

private theorem child₀_eq :
    countingChild multiRoot 3 {(0, true), (1, true)} false = child₀ := by decide

private theorem leaf₁_eq :
    countingChild multiRoot 3 {(0, true), (1, true)} true = leaf₁ := by decide

private theorem leaf₀₀_eq :
    countingChild child₀ 2 {(1, true)} false = leaf₀₀ := by decide

private theorem leaf₀₁_eq :
    countingChild child₀ 2 {(1, true)} true = leaf₀₁ := by decide

private theorem sparse_leaf₀₀ : Sparse (2 ^ ·) leaf₀₀ :=
  (sparse_iff_forall_mem_powerset one_le_two_pow leaf₀₀).mpr (by unfold Heavy; decide)

private theorem sparse_leaf₀₁ : Sparse (2 ^ ·) leaf₀₁ :=
  (sparse_iff_forall_mem_powerset one_le_two_pow leaf₀₁).mpr (by unfold Heavy; decide)

private theorem sparse_leaf₁ : Sparse (2 ^ ·) leaf₁ :=
  (sparse_iff_forall_mem_powerset one_le_two_pow leaf₁).mpr (by unfold Heavy; decide)

private theorem countingLeaves_multiRoot :
    countingLeaves (2 ^ ·) multiRoot = [leaf₀₀, leaf₀₁, leaf₁] := by
  have hstep1 : countingLeaves (2 ^ ·) multiRoot =
      countingLeaves (2 ^ ·) child₀ ++ countingLeaves (2 ^ ·) leaf₁ := by
    rw [countingLeaves_of_mem_powerset_unique one_le_two_pow (c := 3)
      (H := {(0, true), (1, true)})
      (by unfold Heavy; decide) (by decide) (by unfold Heavy; decide) (by unfold Heavy; decide),
      child₀_eq, leaf₁_eq]
  have hstep2 : countingLeaves (2 ^ ·) child₀ =
      countingLeaves (2 ^ ·) leaf₀₀ ++ countingLeaves (2 ^ ·) leaf₀₁ := by
    rw [countingLeaves_of_mem_powerset_unique one_le_two_pow (c := 2)
      (H := {(1, true)})
      (by unfold Heavy; decide) (by decide) (by unfold Heavy; decide) (by unfold Heavy; decide),
      leaf₀₀_eq, leaf₀₁_eq]
  rw [hstep1, hstep2, countingLeaves_of_sparse sparse_leaf₀₀,
    countingLeaves_of_sparse sparse_leaf₀₁, countingLeaves_of_sparse sparse_leaf₁]
  rfl

-- Individual leaf counts are `16`, `4`, and `1`, summing to `21 = multiRoot`'s model count.
example : leaf₀₀.toCNF.modelCountOn Finset.univ = 16 := by rw [count_eq_card]; decide

example : leaf₀₁.toCNF.modelCountOn Finset.univ = 4 := by rw [count_eq_card]; decide

example : leaf₁.toCNF.modelCountOn Finset.univ = 1 := by rw [count_eq_card]; decide

example : multiRoot.toCNF.modelCountOn Finset.univ = 21 := by rw [count_eq_card]; decide

example : ((countingLeaves (2 ^ ·) multiRoot).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 21 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

-- Concrete assignment check: the all-true assignment satisfies `leaf₀₀` and neither `leaf₀₁` nor
-- `leaf₁`, while `witnessAssign` (`x₀ = x₁ = false`, others `true`) satisfies `leaf₁` alone.
private def witnessAssign : Fin 5 → Bool
  | 0 => false
  | 1 => false
  | _ => true

example : (countingLeaves (2 ^ ·) multiRoot).countP
    (fun L => decide (L.Sat (fun _ => true))) = 1 := by
  rw [countingLeaves_multiRoot]
  decide

example : leaf₁.Sat witnessAssign ∧
    ¬ leaf₀₀.Sat witnessAssign ∧
    ¬ leaf₀₁.Sat witnessAssign := by
  decide

/-! ### 3. Unused declared variables and support preservation -/

-- Embedding `multiRoot` into `Fin 6` leaves variable `5` unused: every leaf stays supported on
-- `{0, 1, 2, 3, 4}`, while `modelCountOn Finset.univ` doubles from `21` to `42`.
private def multiRootSix : ClauseSet (Fin 6) :=
  {{(0, true), (1, true), (2, true)},
   {(0, true), (1, true), (3, true)},
   {(1, true), (4, true)}}

example : ∀ L ∈ countingLeaves (2 ^ ·) multiRootSix,
    Reduced L ∧
      ∀ C ∈ L, C.card ≤ 3 ∧ (5, true) ∉ C ∧ (5, false) ∉ C := by
  intro L hL
  have hsup := support_of_mem_countingLeaves (declared := ({0, 1, 2, 3, 4} : Finset (Fin 6)))
    (by decide) hL
  have hcard := card_le_of_mem_countingLeaves (k := 3) (by decide) hL
  refine ⟨reduced_of_mem_countingLeaves (by unfold Reduced; decide) hL, fun C hC => ?_⟩
  refine ⟨hcard C hC, fun h5t => ?_, fun h5f => ?_⟩
  · have := hsup C hC (5, true) h5t
    revert this; decide
  · have := hsup C hC (5, false) h5f
    revert this; decide

example : ((countingLeaves (2 ^ ·) multiRootSix).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 42 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

/-! ### 4. Empty formula, unit clauses, contradictory formulas, and `CNF` round-trip -/

-- Empty clause set on 3 declared variables has 1 leaf `∅` with `2^3 = 8` models; on `Empty`, `1`.
example : countingLeaves (2 ^ ·) (∅ : ClauseSet (Fin 3)) = [∅] :=
  countingLeaves_of_sparse
    ((sparse_iff_forall_mem_powerset one_le_two_pow ∅).mpr (by unfold Heavy; decide))

example : ((countingLeaves (2 ^ ·) (∅ : ClauseSet (Fin 3))).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 8 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

theorem empty_leaves_count :
    ((countingLeaves (2 ^ ·) (∅ : ClauseSet Empty)).map
      fun L => L.toCNF.modelCountOn ∅).sum = 1 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

-- Pure unit clauses are already sparse and retain their exact count (`2` models on `Fin 3`).
private def unitClauseSet : ClauseSet (Fin 3) :=
  {{(0, true)}, {(1, false)}}

example : countingLeaves (2 ^ ·) unitClauseSet = [unitClauseSet] :=
  countingLeaves_of_sparse
    ((sparse_iff_forall_mem_powerset one_le_two_pow unitClauseSet).mpr (by unfold Heavy; decide))

example : ((countingLeaves (2 ^ ·) unitClauseSet).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 2 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

-- Contradictory clause set containing the empty clause `{∅}`: 1 leaf, `0` models.
example : countingLeaves (2 ^ ·) ({∅} : ClauseSet (Fin 2)) = [{∅}] :=
  countingLeaves_of_sparse
    ((sparse_iff_forall_mem_powerset one_le_two_pow {∅}).mpr (by unfold Heavy; decide))

example : ((countingLeaves (2 ^ ·) ({∅} : ClauseSet (Fin 2))).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 0 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

-- Contradictory unit pair `{x₀} ∧ {¬x₀}` combined with a heavy width-2 flower: `countingLeaves`
-- still branches cleanly into 2 sparse leaves, both with `0` models (`0 + 0 = 0`).
private def unsatHeavy : ClauseSet (Fin 4) :=
  {{(0, true)}, {(0, false)}, {(1, true), (2, true)}, {(1, true), (3, true)}}

example : (countingLeaves (2 ^ ·) unsatHeavy).length = 2 := by
  have hstep : countingLeaves (2 ^ ·) unsatHeavy =
      countingLeaves (2 ^ ·) (countingChild unsatHeavy 2 {(1, true)} false) ++
        countingLeaves (2 ^ ·) (countingChild unsatHeavy 2 {(1, true)} true) :=
    countingLeaves_of_mem_powerset_unique one_le_two_pow (c := 2) (H := {(1, true)})
      (by unfold Heavy; decide) (by decide) (by unfold Heavy; decide) (by unfold Heavy; decide)
  have hs0 : Sparse (2 ^ ·) (countingChild unsatHeavy 2 {(1, true)} false) :=
    (sparse_iff_forall_mem_powerset one_le_two_pow _).mpr (by unfold Heavy; decide)
  have hs1 : Sparse (2 ^ ·) (countingChild unsatHeavy 2 {(1, true)} true) :=
    (sparse_iff_forall_mem_powerset one_le_two_pow _).mpr (by unfold Heavy; decide)
  rw [hstep, countingLeaves_of_sparse hs0, countingLeaves_of_sparse hs1]
  rfl

example : ((countingLeaves (2 ^ ·) unsatHeavy).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 0 := by
  rw [sum_modelCountOn_countingLeaves, count_eq_card]
  decide

-- `CNF` formula with duplicate and subsumed clauses: both `toClauseSet` and `reduce ∘ toClauseSet`
-- conserve `CNF.modelCountOn Finset.univ = 21`.
private def multiCNF : CNF (Fin 5) :=
  [[(0, true), (1, true), (2, true)],
   [(0, true), (1, true), (2, true)],
   [(0, true), (1, true), (3, true)],
   [(1, true), (4, true)],
   [(1, true), (2, false), (4, true)]]

example : ((countingLeaves (2 ^ ·) multiCNF.toClauseSet).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 21 := by
  rw [sum_modelCountOn_countingLeaves_toClauseSet]
  unfold CNF.modelCountOn
  decide

example : ((countingLeaves (2 ^ ·) (reduce multiCNF.toClauseSet)).map
    fun L => L.toCNF.modelCountOn Finset.univ).sum = 21 := by
  rw [sum_modelCountOn_countingLeaves_reduce_toClauseSet]
  unfold CNF.modelCountOn
  decide

/-! ### 5. Unique-index and unique-member extraction from `List.countP = 1` -/

-- Even when non-matching elements repeat (`3` appears twice), `countP = 1` yields both the unique
-- index `1` and the unique matching list member `4`.
example :
    (∃ i : Fin [3, 4, 3, 5].length, ([3, 4, 3, 5][i] == 4) = true ∧ i = ⟨1, by decide⟩) ∧
      ∃ a, (a ∈ [3, 4, 3, 5] ∧ (a == 4) = true) ∧ a = 4 := by
  obtain ⟨i, hi, huniq_i⟩ :=
    List.existsUnique_fin_of_countP_eq_one (l := [3, 4, 3, 5]) (p := (· == 4)) (by decide)
  obtain ⟨a, ha, huniq_a⟩ :=
    List.existsUnique_mem_of_countP_eq_one (l := [3, 4, 3, 5]) (p := (· == 4)) (by decide)
  exact ⟨⟨i, hi, (huniq_i ⟨1, by decide⟩ rfl).symm⟩,
    ⟨a, ha, (huniq_a 4 ⟨by decide, rfl⟩).symm⟩⟩

-- Singleton list at index `0`.
example : ∃! i : Fin [true].length, [true][i] = true :=
  List.existsUnique_fin_of_countP_eq_one (l := [true]) (p := id) (by decide)

-- End-to-end unique-leaf wrappers on `multiRoot` and `witnessAssign`.
example : ∃! i : Fin (countingLeaves (2 ^ ·) multiRoot).length,
    ((countingLeaves (2 ^ ·) multiRoot)[i]).Sat witnessAssign :=
  (sat_iff_existsUnique_fin_countingLeaves (2 ^ ·) multiRoot witnessAssign).mp (by decide)

example : ∃! L, L ∈ countingLeaves (2 ^ ·) multiRoot ∧ L.Sat witnessAssign :=
  (sat_iff_existsUnique_mem_countingLeaves (2 ^ ·) multiRoot witnessAssign).mp (by decide)

end ComplexityTests.SparsificationCountingTree
