/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Layouts from scores

Sorting the vertices by a score, with ties broken by a fixed numbering, gives a layout every
initial segment of which is a *threshold set* of the score: some `m` is at least every score
inside it and at most every score outside it (`Cslib.Circuits.Frontier.Layout.exists_threshold`).
Which window of a grid `a, a + δ, ..., a + M δ` a threshold falls in is decided by
`Cslib.Circuits.Frontier.exists_grid_index`. Both turn estimates at the grid thresholds into
bounds on every frontier of the layouts by Gaussian scores.

## Main results

* `Cslib.Circuits.Frontier.Layout.exists_threshold`: the layout by a score.
* `Cslib.Circuits.Frontier.exists_grid_index`: the grid window of a threshold.
* `Cslib.Circuits.Frontier.Multigraph.width_le_of_ncard_frontier_le`: bounding the width by a
  real bound on the frontiers.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

namespace Layout

variable {V : Type*}

/-- **Sorting by a score.** Listing the vertices in increasing order of a score, with ties broken
by a fixed numbering, gives a layout whose initial segments are threshold sets: for `t < |V|`,
some `m` is at least the score of every vertex among the first `t` and at most the score of every
other vertex. -/
theorem exists_threshold [Finite V] {α : Type*} [LinearOrder α] (score : V → α) :
    ∃ π : Layout V, ∀ t < Nat.card V, ∃ m : α, (∀ v ∈ π.initial t, score v ≤ m) ∧
      ∀ v ∉ π.initial t, m ≤ score v := by
  let f : V → α ×ₗ Fin (Nat.card V) := fun v => toLex (score v, Finite.equivFin V v)
  have hf : f.Injective := fun v w h =>
    (Finite.equivFin V).injective (congrArg (fun x => (ofLex x).2) h)
  obtain ⟨π, hπ⟩ := exists_lt_iff hf
  refine ⟨π, fun t ht => ⟨score (π.symm ⟨t, ht⟩), fun v hv => ?_, fun v hv => ?_⟩⟩
  · rw [π.initial_eq_of_lt_iff hπ ht] at hv
    exact Prod.Lex.monotone_fst (f v) _ (le_of_lt hv)
  · rw [π.initial_eq_of_lt_iff hπ ht] at hv
    exact Prod.Lex.monotone_fst _ (f v) (not_lt.mp hv)

end Layout

/-- **Grid windows.** A real number in `[a, a + M δ)` lies in one of the `M` windows
`[a + i δ, a + (i + 1) δ)`. -/
theorem exists_grid_index {a δ m : ℝ} (hδ : 0 < δ) {M : ℕ} (hlo : a ≤ m)
    (hhi : m < a + M * δ) : ∃ i < M, a + i * δ ≤ m ∧ m < a + (i + 1) * δ := by
  have hdiv : 0 ≤ (m - a) / δ := div_nonneg (by linarith) hδ.le
  have ht : a + ⌊(m - a) / δ⌋₊ * δ ≤ m := by
    have := (le_div_iff₀ hδ).mp (Nat.floor_le hdiv)
    linarith
  have ht' : m < a + (⌊(m - a) / δ⌋₊ + 1) * δ := by
    have := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((m - a) / δ))
    linarith
  refine ⟨⌊(m - a) / δ⌋₊, ?_, ht, ht'⟩
  by_contra! h
  have : (M : ℝ) * δ ≤ ⌊(m - a) / δ⌋₊ * δ := by gcongr
  linarith

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E) (π : Layout V)

/-- A nonnegative real bound on the frontiers before the last vertex bounds the width. -/
theorem width_le_of_ncard_frontier_le [Finite E] {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t < Nat.card V, ((G.frontier π t).ncard : ℝ) ≤ B) : (G.width π : ℝ) ≤ B := by
  have hcut (t : ℕ) : (G.frontier π t).ncard ≤ ⌊B⌋₊ := by
    refine Nat.le_floor ?_
    rcases lt_or_ge t (Nat.card V) with ht | ht
    · exact h t ht
    · rw [G.frontier_of_card_le π ht, ncard_empty, Nat.cast_zero]
      exact hB
  exact (Nat.cast_le.mpr ((G.width_le_iff π).2 hcut)).trans (Nat.floor_le hB)

end Multigraph

end Cslib.Circuits.Frontier
