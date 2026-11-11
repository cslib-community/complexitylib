/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import CslibFrontier.DataStructure.BTree.Insert

/-!
# Comparison costs of B-tree insertion
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BTree

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α} {v : β} {tr : BTree α β}

def insertQ (t : ℕ) (k : α) (v : β) (tr : BTree α β) :
    FreeM (LEQuery α) (BTree α β) :=
  insertM t LEQuery.ask (pure ()) k v tr

def insertOrSplitQ (t : ℕ) (k : α) (v : β) (tr : BTree α β) :
    FreeM (LEQuery α) (InsertResult α β) :=
  insertOrSplitM t LEQuery.ask (pure ()) k v tr

def insertRestQ (t : ℕ) (k : α) (v : β) (rest : List (Triple α β)) :
    FreeM (LEQuery α) (Option (List (Triple α β))) :=
  insertRestM t LEQuery.ask (pure ()) k v rest

@[simp] theorem eval_insertQ : (insertQ t k v tr).eval orderOracle = insert t k v tr := by
  simpa [insert_def, insertQ] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_insertM t LEQuery.ask (pure ()) k v tr)

@[simp] theorem eval_insertOrSplitQ :
    (insertOrSplitQ t k v tr).eval orderOracle = (insertOrSplitM t leI (pure ()) k v tr).run := by
  simpa [insertOrSplitQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_insertOrSplitM t LEQuery.ask (pure ()) k v tr)

@[simp] theorem eval_insertRestQ {rest : List (Triple α β)} :
    (insertRestQ t k v rest).eval orderOracle = (insertRestM t leI (pure ()) k v rest).run := by
  simpa [insertRestQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_insertRestM t LEQuery.ask (pure ()) k v rest)

theorem countQueries_insertRestQ_le_of_ret_none (rest : List (Triple α β))
    (h_ret : (insertRestQ t k v rest).eval orderOracle = none) :
    (insertRestQ t k v rest).countQueries orderOracle ≤ rest.length + 1 := by
  induction rest with
  | nil =>
    simp [insertRestQ, insertRestM]
  | cons head tail ih =>
    obtain ⟨k', v', c⟩ := head
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k
      · simp [insertRestQ, insertRestM, hk, hk'] at h_ret
      · simp [insertRestQ, insertRestM, hk, hk']
    · simp [insertRestQ, insertRestM, hk] at h_ret
      cases h_eval : FreeM.eval (fun {ι} => orderOracle)
        (insertRestM t LEQuery.ask (pure ()) k v tail)
      · simp [h_eval, FreeM.eval_map] at h_ret
      · simp [h_eval] at h_ret

theorem countQueries_insertRestQ_le (rest : List (Triple α β)) (B : ℕ)
    (h_cost : ∀ c ∈ rest.map Triple.child, (insertOrSplitQ t k v c).countQueries orderOracle ≤ B) :
    (insertRestQ t k v rest).countQueries orderOracle ≤ rest.length + 1 + B := by
  induction rest with
  | nil =>
    simp [insertRestQ, insertRestM]
  | cons head tail ih =>
    obtain ⟨k', v', c⟩ := head
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k
      · simp [insertRestQ, insertRestM, hk, hk']; omega
      · simp [insertRestQ, insertRestM, hk, hk']; omega
    · simp [insertRestQ, insertRestM, hk]
      cases h_eval : (insertRestM t LEQuery.ask (pure ()) k v tail).eval orderOracle <;>
        simp [FreeM.countQueries_map]
      · have hc : (insertOrSplitQ t k v c).countQueries orderOracle ≤ B := by apply h_cost; simp
        have h_none := countQueries_insertRestQ_le_of_ret_none tail
          (by simpa [insertRestQ] using h_eval)
        simp only [insertRestQ, insertOrSplitQ] at hc h_none ⊢
        omega
      · have h_tail := ih (fun c hc => h_cost c (by simp [hc]))
        simp only [insertRestQ] at h_tail ⊢
        omega





@[simp] theorem countQueries_insertOrSplitQ_leaf :
    (insertOrSplitQ t k v (.leaf : BTree α β)).countQueries orderOracle = 0 := by
  simp [insertOrSplitQ, insertOrSplitM]

theorem countQueries_insertOrSplitQ_node_le (first : BTree α β) (rest : List (Triple α β)) (B : ℕ)
    (h_cost : ∀ c ∈ (node first rest).children,
        (insertOrSplitQ t k v c).countQueries orderOracle ≤ B) :
    (insertOrSplitQ t k v (.node first rest)).countQueries orderOracle ≤ rest.length + 1 + B := by
  simp [insertOrSplitQ, insertOrSplitM, FreeM.countQueries_bind]
  cases h_eval : (insertRestM t LEQuery.ask (pure ()) k v rest).eval orderOracle <;>
    simp [FreeM.countQueries_map]
  · have h_first : (insertOrSplitQ t k v first).countQueries orderOracle ≤ B := by
      apply h_cost; simp
    have h_none := countQueries_insertRestQ_le_of_ret_none rest
      (by simpa [insertRestQ] using h_eval)
    simp only [insertRestQ, insertOrSplitQ] at h_first h_none ⊢
    omega
  · have h_rest : ∀ c ∈ rest.map Triple.child,
        (insertOrSplitQ t k v c).countQueries orderOracle ≤ B := by
      intro c hc
      apply h_cost
      simp [hc]
    have h_some := countQueries_insertRestQ_le rest B h_rest
    simp only [insertRestQ] at h_some ⊢
    omega

theorem countQueries_insertOrSplitQ_le (h : IsWF t tr) :
    (insertOrSplitQ t k v tr).countQueries orderOracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan (by have := h.two_le; omega) (countQueries_insertOrSplitQ_leaf)
    (fun first rest _ hB => countQueries_insertOrSplitQ_node_le first rest _ hB)
    h.rootKeys_le h.occupied_of_mem_children

theorem countQueries_insertQ_le (h : IsWF t tr) :
    (insertQ t k v tr).countQueries orderOracle ≤ 2 * t * tr.height := by
  simp only [insertQ, insertM, FreeM.countQueries_bind, FreeM.countQueries_pure,
      add_zero]
  exact countQueries_insertOrSplitQ_le h

end Cslib.DataStructure.BTree
