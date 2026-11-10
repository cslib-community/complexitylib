/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Init.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Basic

/-!
# A discrete intermediate value theorem

A sequence of natural numbers that grows by at most one per step takes every value between its
value at the start and any of its later values (`Nat.exists_eq_of_forall_le_add_one`). Compare
`SimpleGraph.Walk.mem_support_hasse_of_ge_of_le`, the same fact for walks in the Hasse diagram of
a linear order.

Similarly, if changing one coordinate of a function on a finite domain raises a natural-valued
measure by at most `B`, and the measure starts at most `t` and ends above `t`, then it takes some
intermediate value in `(t, t + B]` (`Nat.exists_lt_le_add_of_update_le`).

## Main results

* `Nat.exists_eq_of_forall_le_add_one`: the discrete intermediate value theorem for sequences.
* `Nat.exists_lt_le_add_of_update_le`: discrete intermediate values under coordinate updates.
-/

@[expose] public section

namespace Nat

/-- **A discrete intermediate value theorem.** A sequence of natural numbers that grows by at
most one per step up to time `T` takes, by time `T`, every value between `a 0` and `a T`. -/
theorem exists_eq_of_forall_le_add_one {a : ℕ → ℕ} {k T : ℕ} (h0 : a 0 ≤ k) (hT : k ≤ a T)
    (hstep : ∀ t < T, a (t + 1) ≤ a t + 1) : ∃ t ≤ T, a t = k := by
  induction T with
  | zero => exact ⟨0, Nat.le_refl 0, Nat.le_antisymm h0 hT⟩
  | succ T ih =>
    by_cases h : k ≤ a T
    · obtain ⟨t, ht, hat⟩ := ih h fun t ht => hstep t (by omega)
      exact ⟨t, by omega, hat⟩
    · exact ⟨T + 1, Nat.le_refl _, by have := hstep T (by omega); omega⟩

/-- **Discrete intermediate values under coordinate updates.** If changing one coordinate raises
a measure by at most `B`, and the measure is at most `t` at `u` and above `t` at `v`, then it
lies in `(t, t + B]` somewhere. -/
theorem exists_lt_le_add_of_update_le {ι α : Type*} [Finite ι] [DecidableEq ι]
    (μ : (ι → α) → ℕ) {B t : ℕ} (hμ : ∀ w i a, μ (Function.update w i a) ≤ μ w + B)
    {u v : ι → α} (hu : μ u ≤ t) (hv : t < μ v) : ∃ w, t < μ w ∧ μ w ≤ t + B := by
  have := Fintype.ofFinite ι
  let w : Finset ι → ι → α := fun S i => if i ∈ S then v i else u i
  suffices h : ∀ S : Finset ι, μ (w S) ≤ t ∨ ∃ w, t < μ w ∧ μ w ≤ t + B by
    refine (h Finset.univ).resolve_left fun hle => ?_
    have : w Finset.univ = v := funext fun i => by simp [w]
    exact absurd (this ▸ hle) (not_le.2 hv)
  intro S
  induction S using Finset.induction_on with
  | empty => exact Or.inl (by simpa [w] using hu)
  | @insert i S hi ih =>
    have e : w (insert i S) = Function.update (w S) i (v i) := funext fun j => by
      by_cases hj : j = i
      · subst hj
        simp [w]
      · simp [w, hj]
    rcases ih with hle | found
    · by_cases hnext : μ (w (insert i S)) ≤ t
      · exact Or.inl hnext
      · refine Or.inr ⟨_, not_le.1 hnext, ?_⟩
        rw [e]
        exact (hμ _ _ _).trans (Nat.add_le_add_right hle B)
    · exact Or.inr found

end Nat
