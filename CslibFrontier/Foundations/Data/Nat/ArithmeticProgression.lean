/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

/-!
# Counting terms of a natural-number arithmetic progression up to a deadline

Given a start `d`, step `p`, and deadline `T`, `Cslib.arithmeticProgressionCount d p T` counts the
natural numbers `t ≤ T` of the form `d + k * p` (`Cslib.arithmeticProgressionCount_spec`), with
`p = 0` representing a singleton at `d`.

## Main definitions

* `Cslib.arithmeticProgressionCount`: count of progression terms `d + k * p` in `{0, …, T}`.

## Main results

* `Cslib.arithmeticProgressionCount_spec`: `Set.ncard {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * p}` equals
  `arithmeticProgressionCount d p T`.
-/

@[expose] public section

namespace Cslib

/-- Number of progression terms `d + k * p` in `{0, ..., T}`, with `p = 0` denoting a singleton
visit at `d`. -/
def arithmeticProgressionCount (d p T : ℕ) : ℕ :=
  if T < d then 0 else if p = 0 then 1 else (T - d) / p + 1

/-- `arithmeticProgressionCount d p T` counts the times `t ≤ T` of the form `d + k * p`. -/
theorem arithmeticProgressionCount_spec (d p T : ℕ) :
    Set.ncard {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * p} =
      arithmeticProgressionCount d p T := by
  classical
  have hset : {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * p} =
      ↑((Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      Nat.lt_succ_iff]
  rw [hset, Set.ncard_coe_finset]
  unfold arithmeticProgressionCount
  split_ifs with hT hp
  · have he : (Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht, k, rfl⟩ := Finset.mem_filter.mp ht
      have hlt := Finset.mem_range.mp ht
      lia
    rw [he, Finset.card_empty]
  · have he : (Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p) = {d} := by
      ext t
      simp only [hp, Nat.mul_zero, Nat.add_zero, exists_const, Finset.mem_filter,
        Finset.mem_range, Finset.mem_singleton]
      lia
    rw [he, Finset.card_singleton]
  · have hpos : 0 < p := by lia
    have he : (Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p) =
        (Finset.range ((T - d) / p + 1)).image (fun k => d + k * p) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨ht, k, rfl⟩
        refine ⟨k, ?_, rfl⟩
        have hh : k ≤ (T - d) / p := (Nat.le_div_iff_mul_le hpos).mpr (by lia)
        lia
      · rintro ⟨k, hk, rfl⟩
        have hh : k * p ≤ T - d :=
          (Nat.le_div_iff_mul_le hpos).mp (show k ≤ (T - d) / p by lia)
        exact ⟨by lia, k, rfl⟩
    rw [he, Finset.card_image_of_injective _ (show Function.Injective
      (fun k : ℕ => d + k * p) from by intro a b hab; nlinarith), Finset.card_range]

end Cslib
