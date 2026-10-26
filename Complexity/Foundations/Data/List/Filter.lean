/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Data.List.GetD

/-!
# Indexed multiplicity under list membership filtering

These statements count positions, so repeated equal lists still contribute separately.
They are generalized from the canonical incidence-path occupancy proofs.

## Main results

* `List.two_le_filter_contains_iff`.
* `List.exists_other_index_of_two_le_filter_contains`.
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

end List
