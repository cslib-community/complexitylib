/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Relation.Acyclic

/-!
# Acyclic relations: tests

Topological numberings of an acyclic relation on a finite set, including the bound by the number
of elements, a relation with a cycle that has none, and simple cycles inside closed walks.
-/

namespace ComplexityTests.RelationAcyclic

open Relation

/-- The successor relation on `{0, 1, 2}`: a path, hence acyclic. -/
private def step (a b : ℕ) : Prop := a < 2 ∧ b = a + 1

/-- The relation `0 → 1 → 2 → 0`: a cycle. -/
private def rot (a b : ℕ) : Prop := a < 3 ∧ b = (a + 1) % 3

private theorem step_support (a b : ℕ) (h : step a b) : a ∈ ({0, 1, 2} : Finset ℕ) ∧
    b ∈ ({0, 1, 2} : Finset ℕ) := by
  obtain ⟨ha, rfl⟩ := h
  have : a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl <;> decide

-- The path has a numbering below its three elements.
example : ∃ f : ℕ → ℕ, (∀ a ∈ ({0, 1, 2} : Finset ℕ), f a < 3) ∧ ∀ a b, step a b → f a < f b := by
  simpa using exists_rank_of_forall_not_transGen _ step_support
    (not_transGen_of_rank (f := id) fun a b h => by rw [h.2]; exact Nat.lt_succ_self a)

-- Through the equivalence, the identity numbering certifies acyclicity.
example : ∀ a, ¬TransGen step a a :=
  (forall_not_transGen_iff_exists_rank _ step_support).2
    ⟨id, fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> decide,
      fun a b h => by rw [h.2]; exact Nat.lt_succ_self a⟩

-- The cycle `0 → 1 → 2 → 0` is a simple cycle, so no numbering increases along `rot`.
example : ¬∃ f : ℕ → ℕ, ∀ a b, rot a b → f a < f b := by
  rintro ⟨f, hf⟩
  have hc : (([0, 1, 2] : List ℕ) : Cycle ℕ).Chain rot := by
    rw [Cycle.chain_coe_cons]
    simp [rot]
  exact forall_not_transGen_iff.1 (not_transGen_of_rank hf) _ (by simp) (by simp) hc

-- A closed walk around the cycle twice contains a simple cycle among its elements.
example : ∃ c : List ℕ, c ≠ [] ∧ c.Nodup ∧ c ⊆ [0, 1, 2, 0, 1, 2] ∧ (c : Cycle ℕ).Chain rot := by
  refine exists_nodup_of_cycle_chain (by simp) ?_
  rw [Cycle.chain_coe_cons]
  simp [rot]

-- Closed walks are the transitive closure relating an element to itself.
example : TransGen rot 1 1 :=
  transGen_of_cycle_chain (c := [0, 1, 2]) (by rw [Cycle.chain_coe_cons]; simp [rot]) (by simp)

end ComplexityTests.RelationAcyclic
