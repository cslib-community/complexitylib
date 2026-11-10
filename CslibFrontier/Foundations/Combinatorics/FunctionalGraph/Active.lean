/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.Checkpoints
public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.Cycle

/-!
# Checkpoints charged to long trajectories

Fix `L > 0`. The *active* states are those of transient depth at least `L` and the periodic
states on cycles of length at least `L` (`activeVertices`). Packing checkpoints only inside the
active set gives at most `|active| / L` of them, and still every orbit repeats among its first
`4 L` states or reaches a checkpoint within `4 L` steps (`exists_active_checkpoints`). The
active set need not be invariant: a short transient is skipped within `2 L` steps, and a short
cycle repeats.

The state type may live in any universe; it is finite.

## Main definitions

* `Cslib.FunctionalGraph.activeVertices`: deep transient states and states of long cycles.

## Main results

* `Cslib.FunctionalGraph.exists_active_checkpoints`: checkpoints charged to the active set.

## References

* Adapted from lean/Proofs/ActiveCheckpoints.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u
variable {α : Type u} [Fintype α] (f : α → α)

open scoped Classical in
/-- The states of transient depth at least `L` and the periodic states on cycles of length at
least `L`. -/
noncomputable def activeVertices (L : ℕ) : Finset α :=
  Finset.univ.filter fun x => L ≤ transientDepth f x ∨
    x ∈ periodicPts f ∧ L ≤ cycleLength f x

/-- A state is active exactly when its transient depth is at least `L` or it is periodic with
cycle length at least `L`. -/
@[simp] theorem mem_activeVertices (L : ℕ) (x : α) :
    x ∈ activeVertices f L ↔
      L ≤ transientDepth f x ∨ x ∈ periodicPts f ∧ L ≤ cycleLength f x := by
  classical
  simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Active checkpoints.** For `L > 0` there are at most `|active| / L` checkpoints, all
active, such that every orbit repeats a state among its first `4 L` or reaches a checkpoint in
fewer than `4 L` steps. -/
theorem exists_active_checkpoints (L : ℕ) (hL : 0 < L) :
    ∃ H : Finset α, H ⊆ activeVertices f L ∧ H.card * L ≤ (activeVertices f L).card ∧
      ∀ x, Repeats f x (4 * L) ∨ ∃ d < 4 * L, f^[d] x ∈ H := by
  obtain ⟨H, hH, hc, hcover⟩ := exists_checkpoints_on f (activeVertices f L) hL
  refine ⟨H, hH, hc, fun x => ?_⟩
  by_cases hd : 2 * L ≤ transientDepth f x
  · have hprefix (i : Fin L) : f^[i.val] x ∈ activeVertices f L := by
      refine (mem_activeVertices f L _).mpr (Or.inl ?_)
      rw [transientDepth_iterate]
      omega
    rcases hcover x hprefix with ⟨i, j, hij, hj, he⟩ | ⟨d, hd, hm⟩
    · exact Or.inl ⟨i, j, hij, by omega, he⟩
    · exact Or.inr ⟨d, by omega, hm⟩
  · by_cases hl : cycleLength f x < L
    · refine Or.inl ⟨transientDepth f x, transientDepth f x + cycleLength f x,
        by have := cycleLength_pos f x; omega, by omega, ?_⟩
      have hp : f^[cycleLength f x] (f^[transientDepth f x] x) = _ := isPeriodicPt_cycleLength f x
      simpa only [← iterate_add_apply, Nat.add_comm] using hp.symm
    · set y := f^[transientDepth f x] x
      have hprefix (i : Fin L) : f^[i.val] y ∈ activeVertices f L := by
        refine (mem_activeVertices f L _).mpr (Or.inr ⟨?_, ?_⟩)
        · rw [← iterate_add_apply, iterate_mem_periodicPts_iff]
          omega
        · rw [cycleLength_iterate, cycleLength_iterate]
          omega
      rcases hcover y hprefix with ⟨i, j, hij, hj, he⟩ | ⟨d, ht, hm⟩
      · refine Or.inl ⟨i + transientDepth f x, j + transientDepth f x, by omega, by omega, ?_⟩
        simpa only [iterate_add_apply] using he
      · refine Or.inr ⟨d + transientDepth f x, by omega, ?_⟩
        simpa only [iterate_add_apply] using hm

end Cslib.FunctionalGraph
