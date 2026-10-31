/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD

/-!
# Indexed multiplicity under list membership filtering

These statements count positions, so repeated equal lists still contribute separately.
They are generalized from the canonical incidence-path occupancy proofs.

## Main results

* `List.two_le_filter_contains_iff`.
* `List.exists_other_index_of_two_le_filter_contains`.
* `List.toFinset_filter_not_mem`: filtering `C` by non-membership in `H` takes the set difference
  `C.toFinset \ H.toFinset`.
* `List.countP_le_sum_map`: if `1 ≤ f x` whenever `p x = true` on `l`, then
  `l.countP p ≤ (l.map f).sum`.
* `List.any_id_le_of_forall₂`, `List.all_id_le_of_forall₂`: `List.any id` and `List.all id` are
  monotone with respect to `List.Forall₂ (· ≤ ·)`.
-/

@[expose] public section

namespace List

/-- At least two memberships correspond to distinct indices, even for repeated equal lists. -/
theorem two_le_filter_contains_iff {α : Type*} [DecidableEq α]
    (rs : List (List α)) (p : α) :
    2 ≤ (rs.filter fun r => r.contains p).length ↔
      ∃ (i j : ℕ) (hi : i < rs.length) (hj : j < rs.length),
        i ≠ j ∧ p ∈ rs[i] ∧ p ∈ rs[j] := by
  constructor
  · intro hlen
    induction rs with
    | nil => simp at hlen
    | cons r rs ih =>
      by_cases hp : p ∈ r
      · have hne : (rs.filter fun r => r.contains p) ≠ [] := by
          intro h
          have hf : ((r :: rs).filter fun r => r.contains p) = [r] := by
            have hpred : r.contains p = true := by simpa using hp
            simp only [List.filter_cons, hpred, ↓reduceIte, h]
          rw [hf] at hlen
          simp at hlen
        cases hf : rs.filter (fun r => r.contains p) with
        | nil => exact False.elim (hne hf)
        | cons t ts =>
          have ht : t ∈ rs.filter (fun r => r.contains p) := by rw [hf]; simp
          obtain ⟨htmem, htp⟩ := List.mem_filter.mp ht
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp htmem
          exact ⟨0, j + 1, by simp, by simpa using hj, by omega, hp, by simpa using htp⟩
      · have hf : ((r :: rs).filter fun r => r.contains p) = rs.filter (fun r => r.contains p) := by
          simp [hp]
        rw [hf] at hlen
        obtain ⟨i, j, hi, hj, hij, hpi, hpj⟩ := ih hlen
        exact ⟨i + 1, j + 1, by simpa using hi, by simpa using hj, by omega, hpi, hpj⟩
  · rintro ⟨i, j, hi, hj, hij, hpi, hpj⟩
    induction rs generalizing i j with
    | nil => simp at hi
    | cons r rs ih =>
      cases i with
      | zero =>
        cases j with
        | zero => exact False.elim (hij rfl)
        | succ j =>
          have hj' : j < rs.length := by simpa using hj
          have hm : rs[j] ∈ rs.filter (fun r => r.contains p) :=
            List.mem_filter.mpr ⟨List.getElem_mem (by simpa using hj),
              List.contains_iff_mem.mpr hpj⟩
          obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp hm
          have hphead : p ∈ r := hpi
          simp only [List.filter_cons, List.contains_iff_mem.mpr hphead,
            ite_true, List.length_cons]
          omega
      | succ i =>
        cases j with
        | zero =>
          have hi' : i < rs.length := by simpa using hi
          have hm : rs[i] ∈ rs.filter (fun r => r.contains p) :=
            List.mem_filter.mpr ⟨List.getElem_mem (by simpa using hi),
              List.contains_iff_mem.mpr hpi⟩
          obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp hm
          have hphead : p ∈ r := hpj
          simp only [List.filter_cons, List.contains_iff_mem.mpr hphead,
            ite_true, List.length_cons]
          omega
        | succ j =>
          have ht := ih i j (by simpa using hi) (by simpa using hj) (by omega) hpi hpj
          rw [List.filter_cons]
          split_ifs
          · simp only [List.length_cons]
            omega
          · exact ht

/-- Two filtered memberships give an index different from any given natural number. -/
theorem exists_other_index_of_two_le_filter_contains {α : Type*} [DecidableEq α]
    (rs : List (List α)) (p : α) (i : ℕ)
    (hcount : 2 ≤ (rs.filter fun r => r.contains p).length) :
    ∃ j, ∃ hj : j < rs.length, j ≠ i ∧ p ∈ rs[j] := by
  obtain ⟨j, k, hj, hk, hjk, hpj, hpk⟩ := (two_le_filter_contains_iff rs p).1 hcount
  by_cases hji : j = i
  · exact ⟨k, hk, by omega, hpk⟩
  · exact ⟨j, hj, hji, hpj⟩

/-- Filtering `C` by non-membership in `H` takes the set difference `C.toFinset \ H.toFinset`. -/
theorem toFinset_filter_not_mem {α : Type*} [DecidableEq α] (C H : List α) :
    (C.filter fun l => !H.any (· == l)).toFinset = C.toFinset \ H.toFinset := by
  ext l
  rw [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff, List.mem_toFinset, List.mem_toFinset]
  refine and_congr_right fun _ => ?_
  rw [Bool.not_eq_true', List.any_eq_false]
  exact ⟨fun h hl => h l hl (beq_self_eq_true l), fun h l' hl' heq => h (beq_iff_eq.mp heq ▸ hl')⟩

/-- If `1 ≤ f x` whenever `p x = true` on `l`, then `l.countP p ≤ (l.map f).sum`. -/
theorem countP_le_sum_map {α : Type*} {p : α → Bool} {f : α → ℕ} {l : List α}
    (h : ∀ x ∈ l, p x = true → 1 ≤ f x) : l.countP p ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons]
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hp : p a = true
    · have := h a List.mem_cons_self hp
      simp only [hp, ite_true]
      omega
    · simp only [hp, Bool.false_eq_true, ite_false]
      omega

/-- `List.any id` is monotone with respect to `List.Forall₂ (· ≤ ·)`. -/
theorem any_id_le_of_forall₂ {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) :
    u.any id ≤ v.any id := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih =>
    simp only [List.any_cons, id]
    exact max_le_max hab ih

/-- `List.all id` is monotone with respect to `List.Forall₂ (· ≤ ·)`. -/
theorem all_id_le_of_forall₂ {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) :
    u.all id ≤ v.all id := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih =>
    simp only [List.all_cons, id]
    exact min_le_min hab ih

end List
