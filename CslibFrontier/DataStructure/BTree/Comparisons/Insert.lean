/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import CslibFrontier.DataStructure.BTree.Insert

/-!
# Comparison costs of B-tree insertion

`insertQ` instantiates `insertM` at `FreeM (LEQuery α)` with the query interface `LEQuery.ask`
and `visit := pure ()`, 
in the comparison-query model of `Cslib.DataStructure.BTree.Comparisons.Query`.

Insertion queries the order of keys to find the correct subtree during the downward search.
The splits on the way back up and the new root grown on overflow make zero comparisons,
because they only rebuild nodes using keys already compared and sorted.
At each node, scanning its `rest` contributes at most `rest.length + 1` comparisons:
one per passed triple, with a possible second comparison at the stopping separator.

## Main definitions

* `insertQ`: the instrumented insertion.

## Main results

* `eval_insertQ`: the value of `insertQ` under `orderOracle` is `insert`.
* `countQueries_insertQ_le`: insertion into a subtree makes at most `2 * t * tr.height` 
* comparisons under any oracle.
* `countQueries_insertQ_le_log`: insertion into a well-formed tree 
* makes logarithmically many comparisons.
* `insertQ_upperBound`: the exact `UpperBound` packaging for `insertQ`.

## References

* [BayerMcCreight1972]
* [CLRS2009]
* [Mundler2021]
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BTree

variable {α β : Type} {t : ℕ} {k : α} {v : β} {tr : BTree α β}

/-- Counted B-tree insert operation. -/
def insertQ (t : ℕ) (k : α) (v : β) (tr : BTree α β) :
    FreeM (LEQuery α) (BTree α β) :=
  insertM t LEQuery.ask (pure ()) k v tr

/-- `insertQ` is `insertM` with `LEQuery.ask` and `pure ()`. -/
theorem insertQ_def :
    insertQ t k v tr = insertM t LEQuery.ask (pure ()) k v tr := by unfold insertQ; rfl

/-- Counted B-tree node insert or split operation. -/
private def insertOrSplitQ (t : ℕ) (k : α) (v : β) (tr : BTree α β) :
    FreeM (LEQuery α) (InsertResult α β) :=
  insertOrSplitM t LEQuery.ask (pure ()) k v tr

/-- Counted B-tree node remainder insert operation. -/
private def insertRestQ (t : ℕ) (k : α) (v : β) (rest : List (Triple α β)) :
    FreeM (LEQuery α) (Option (List (Triple α β))) :=
  insertRestM t LEQuery.ask (pure ()) k v rest

/-- Under the order's oracle, `insertQ` evaluates to the pure insertion `insert`. -/
@[simp] theorem eval_insertQ [LinearOrder α] :
    (insertQ t k v tr).eval orderOracle = insert t k v tr := by
  simpa [insert_def, insertQ] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_insertM t LEQuery.ask (pure ()) k v tr)

@[simp] private theorem eval_insertOrSplitQ [LinearOrder α] :
    (insertOrSplitQ t k v tr).eval orderOracle = (insertOrSplitM t leI (pure ()) k v tr).run := by
  simpa [insertOrSplitQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_insertOrSplitM t LEQuery.ask (pure ()) k v tr)

@[simp] private theorem eval_insertRestQ [LinearOrder α] {rest : List (Triple α β)} :
    (insertRestQ t k v rest).eval orderOracle = (insertRestM t leI (pure ()) k v rest).run := by
  simpa [insertRestQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_insertRestM t LEQuery.ask (pure ()) k v rest)

private theorem countQueries_insertRestQ_le_of_ret_none (oracle :
    {ι :
    Type} → LEQuery α ι → ι) (rest :
    List (Triple α β))
    (h_ret : (insertRestQ t k v rest).eval oracle = none) :
    (insertRestQ t k v rest).countQueries oracle ≤ rest.length + 1 := by
  induction rest with
  | nil =>
    simp [insertRestQ, insertRestM]
  | cons head tail ih =>
    obtain ⟨k', v', c⟩ := head
    by_cases hk : oracle (LEQuery.le k k') = true
    · by_cases hk' : oracle (LEQuery.le k' k) = true
      · simp [insertRestQ, insertRestM, hk, hk'] at h_ret
      · simp [insertRestQ, insertRestM, hk, hk']
    · simp only [
      insertRestQ,
      insertRestM,
      bind_pure_comp,
      FreeM.eval_bind,
      FreeM.eval_lift,
      hk,
      Bool.false_eq_true,
      ↓reduceIte] at h_ret
      cases h_eval : FreeM.eval (fun {ι} => oracle) (insertRestM t LEQuery.ask (pure ()) k v tail)
      <;> simp [h_eval, FreeM.eval_map] at h_ret

private theorem countQueries_insertRestQ_le (oracle :
    {ι :
    Type} → LEQuery α ι → ι) (rest :
    List (Triple α β)) (B :
    ℕ)
    (h_cost : ∀ c ∈ rest.map Triple.child, (insertOrSplitQ t k v c).countQueries oracle ≤ B) :
    (insertRestQ t k v rest).countQueries oracle ≤ rest.length + 1 + B := by
  induction rest with
  | nil =>
    simp [insertRestQ, insertRestM]
  | cons head tail ih =>
    obtain ⟨k', v', c⟩ := head
    by_cases hk : oracle (LEQuery.le k k') = true
    · by_cases hk' : oracle (LEQuery.le k' k) = true
      · simp [insertRestQ, insertRestM, hk, hk']; omega
      · simp [insertRestQ, insertRestM, hk, hk']; omega
    · simp only [
      insertRestQ,
      insertRestM,
      bind_pure_comp,
      FreeM.countQueries_bind,
      FreeM.countQueries_lift,
      ↓FreeM.countQueries_ite,
      FreeM.eval_lift,
      hk,
      Bool.false_eq_true,
      ↓reduceIte,
      List.length_cons]
      cases h_eval : (insertRestM t LEQuery.ask (pure ()) k v tail).eval oracle <;> simp only [
        FreeM.countQueries_map,
        FreeM.countQueries_pure]
      · have hc : (insertOrSplitQ t k v c).countQueries oracle ≤ B := by apply h_cost; simp
        have h_none := countQueries_insertRestQ_le_of_ret_none 
          oracle tail (by simpa [insertRestQ] using h_eval)
        simp only [insertRestQ, insertOrSplitQ] at hc h_none ⊢
        omega
      · have h_tail := ih (fun c hc => h_cost c (by simp [hc]))
        simp only [insertRestQ] at h_tail ⊢
        omega





@[simp] private theorem countQueries_insertOrSplitQ_leaf (oracle : {ι : Type} → LEQuery α ι → ι) :
    (insertOrSplitQ t k v (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [insertOrSplitQ, insertOrSplitM]

private theorem countQueries_insertOrSplitQ_node_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (first : BTree α β) (rest : List (Triple α β)) (B : ℕ)
    (h_cost : ∀ c ∈ (node first rest).children,
        (insertOrSplitQ t k v c).countQueries oracle ≤ B) :
    (insertOrSplitQ t k v (.node first rest)).countQueries oracle ≤ rest.length + 1 + B := by
  simp only [insertOrSplitQ, insertOrSplitM, bind_pure_comp, pure_bind, FreeM.countQueries_bind]
  cases h_eval : (insertRestM t LEQuery.ask (pure ()) k v rest).eval oracle <;> simp only [
    FreeM.countQueries_map,
    FreeM.countQueries_pure]
  · have h_first : (insertOrSplitQ t k v first).countQueries oracle ≤ B := by apply h_cost; simp
    have h_none := countQueries_insertRestQ_le_of_ret_none 
      oracle rest (by simpa [insertRestQ] using h_eval)
    simp only [insertRestQ, insertOrSplitQ] at h_first h_none ⊢
    omega
  · have h_rest : ∀ c ∈ rest.map Triple.child,
        (insertOrSplitQ t k v c).countQueries oracle ≤ B := by
      intro c hc
      apply h_cost
      simp [hc]
    have h_some := countQueries_insertRestQ_le oracle rest B h_rest
    simp only [insertRestQ] at h_some ⊢
    omega

private theorem countQueries_insertOrSplitQ_le [LinearOrder α]
    (oracle : {ι : Type} → LEQuery α ι → ι) (h : IsWF t tr) :
    (insertOrSplitQ t k v tr).countQueries oracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan (by have := h.two_le; omega) (countQueries_insertOrSplitQ_leaf oracle)
    (fun first rest _ hB => countQueries_insertOrSplitQ_node_le oracle first rest _ hB)
    h.rootKeys_le h.occupied_of_mem_children

/-- Insertion into the empty tree makes zero comparisons. -/
@[simp] theorem countQueries_insertQ_leaf (oracle : {ι : Type} → LEQuery α ι → ι) :
    (insertQ t k v (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [insertQ, insertM, insertOrSplitM]

/-- Insertion makes at most `2 * t * height` comparisons. -/
theorem countQueries_insertQ_le [LinearOrder α]
    (oracle : {ι : Type} → LEQuery α ι → ι) (h : IsWF t tr) :
    (insertQ t k v tr).countQueries oracle ≤ 2 * t * tr.height := by
  simp only [insertQ, insertM, FreeM.countQueries_bind, FreeM.countQueries_pure,
      add_zero]
  exact countQueries_insertOrSplitQ_le oracle h


/-- Insertion into a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_insertQ_le_log [LinearOrder α]
    (oracle : {ι : Type} → LEQuery α ι → ι) (h : IsWF t tr) :
    (insertQ t k v tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_insertQ_le oracle h).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- `UpperBound` packaging for `insertQ`. -/
theorem insertQ_upperBound [LinearOrder α] (v : β) :
    UpperBound (fun p : WFInput α β t => insertQ t p.val.2 v p.val.1)
      (fun p => p.val.1.height) (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_insertQ_le oracle p.property

end Cslib.DataStructure.BTree
