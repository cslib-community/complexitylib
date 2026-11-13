/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Foundations.Data.List.IdxOfInjective

/-! Ordinary-import reuse with repeated elements and a map injective only on used names. -/

namespace CslibFrontierTests.IdxOfInjective

private def rename (n : ℕ) : ℕ := if n = 7 then 11 else 10

private theorem usedInjection : Set.InjOn rename {v | v ∈ ([2, 7, 2] : List ℕ)} := by
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp [rename]

example : (([2, 7, 2] : List ℕ).map rename).idxOf (rename 7) = 1 :=
  List.idxOf_map_injOn _ _ usedInjection (by simp)

example : rename 0 = rename 2 := by decide

-- Membership remains a real hypothesis: outside the list, first-occurrence indices can differ.
example : (([2, 7, 2] : List ℕ).map rename).idxOf (rename 0) ≠
    ([2, 7, 2] : List ℕ).idxOf 0 := by decide

end CslibFrontierTests.IdxOfInjective
