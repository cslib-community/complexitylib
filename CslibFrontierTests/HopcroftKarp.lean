/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp
import Mathlib.Data.Nat.Sqrt

/-!
# Hopcroft–Karp Tests

Kernel-checked examples (without `native_decide`) for
`CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath` and
`CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp`:

1. **Two-phase trap:** on the path `u₁ — v₀ — u₀ — v₁` the first phase greedily matches
   `(u₀, v₀)`, and the length-3 augmenting path `u₁ v₀ u₀ v₁` needs a second phase. Both the dense
   and the sparse solver return the perfect matching `{(0, 1), (1, 0)}` and a cover of size `2`
   after `2 = 2⌊√2⌋` phases, so the phase bound `IsPhaseRun.le_two_mul_sqrt` is attained.
2. **Non-vacuity of the phase structures:** an explicit two-phase `IsPhaseRun` for the trap
   graph, with positive and negative `IsMaximalLayeredAugmentation` instances.
3. **Further instances:** a `4 × 4` upper-triangular graph (one phase, perfect matching), an
   unbalanced `5 × 3` graph (matching and cover of size `2`), positive and negative
   `decidePerfectMatchingHKM` instances, `BipAdjValid` witnesses, and agreement with the
   Edmonds–Karp solver `bipartiteMatchingM`.
-/

public section

namespace CslibFrontierTests.HopcroftKarp

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow

/-! ### 1. Two-phase trap -/

theorem sqrt_two : 1 = Nat.sqrt 2 := Nat.eq_sqrt.mpr ⟨by decide, by decide⟩

/-- The path `u₁ — v₀ — u₀ — v₁` on `Fin 2 × Fin 2`. -/
def trapGraph : Fin 2 × Fin 2 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | _ => false

/-- Exact adjacency lists of `trapGraph`. -/
def trapAdj : Fin 2 → List (Fin 2)
  | ⟨0, _⟩ => [0, 1]
  | ⟨1, _⟩ => [0]

theorem trapAdj_valid : BipAdjValid trapGraph trapAdj := by
  unfold BipAdjValid
  decide

example : ¬ BipAdjValid trapGraph (fun _ => []) := by
  unfold BipAdjValid
  decide

example : bipAdjSteps trapAdj = 3 := by decide

example : (hopcroftKarpDenseM trapGraph).ret.matching = {(0, 1), (1, 0)} := by decide

example : (hopcroftKarpDenseM trapGraph).ret.cover.size = 2 := by decide

example : (hopcroftKarpDenseM trapGraph).ret.phases = 2 := by decide

example : (hopcroftKarpM trapGraph trapAdj).ret.matching = {(0, 1), (1, 0)} := by decide

example : (hopcroftKarpM trapGraph trapAdj).ret.phases = 2 := by decide

/-- The charged cost of the dense run, within the proved bound `3 * 37 + 8 = 119`. -/
example : (hopcroftKarpDenseM trapGraph).time = 65 := by decide

example : (hopcroftKarpDenseM trapGraph).time ≤ 119 := by
  have h := hopcroftKarpDenseM_time_le trapGraph
  rw [Nat.min_self, ← sqrt_two] at h
  omega

/-- The phase bound `2⌊√ν⌋` is attained by the trap graph. -/
example : (hopcroftKarpDenseM trapGraph).ret.phases =
    2 * Nat.sqrt (hopcroftKarpDenseM trapGraph).ret.matching.card := by
  rw [show (hopcroftKarpDenseM trapGraph).ret.matching.card = 2 by decide, ← sqrt_two]
  decide

example :
    IsMaxMatching trapGraph (hopcroftKarpM trapGraph trapAdj).ret.matching ∧
      IsMinVertexCover trapGraph (hopcroftKarpM trapGraph trapAdj).ret.cover := by
  obtain ⟨hmax, hmin, _⟩ := hopcroftKarpM_correct trapAdj_valid
  exact ⟨hmax, hmin⟩

/-! ### 2. Non-vacuity of the phase structures -/

/-- First phase: `{(0, 0)}` is a maximal layered augmentation of the empty matching. -/
theorem trap_phase₁ : IsMaximalLayeredAugmentation trapGraph ∅ {(0, 0)} 0 := by
  refine ⟨by decide, fun u v h => absurd h (Finset.notMem_empty _), fun u v h => ?_,
    fun r hr p hp => ?_⟩
  · rw [Finset.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, isLayer_zero.mpr (by decide), .inl ⟨by decide, rfl⟩⟩
  · have hr1 : r = 1 := by
      clear hp
      revert hr
      revert r
      decide
    subst hr1
    cases hp with
    | @last _ v _ hG _ hU =>
      revert hG hU
      revert v
      decide
    | cons _ _ hM _ _ => exact absurd hM (Finset.notMem_empty _)

/-- The empty edge set is not a maximal layered augmentation: `[(0, 0)]` is still available. -/
example : ¬ IsMaximalLayeredAugmentation trapGraph ∅ ∅ 0 := fun h =>
  h.maximal 0 (by decide) [(0, 0)]
    (.last (isLayer_zero.mpr (by decide)) rfl (by decide) (by decide))

/-- Second phase: after `{(0, 0)}`, the path `u₁ v₀ u₀ v₁` is a maximal layered augmentation with
`k = 1`. -/
theorem trap_phase₂ : IsMaximalLayeredAugmentation trapGraph {(0, 0)} {(1, 0), (0, 1)} 1 := by
  refine ⟨by decide, by decide, fun u v h => ?_, fun r hr => ?_⟩
  · have hl0 : IsLayer trapGraph {(0, 0)} 0 1 := by
      unfold IsLayer
      decide
    have hl1 : IsLayer trapGraph {(0, 0)} 1 0 := isLayer_zero.mpr (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, hl1, .inr ⟨0, by decide, hl0⟩⟩
    · exact ⟨1, hl0, .inl ⟨by decide, rfl⟩⟩
  · exfalso
    revert hr
    revert r
    decide

/-- The two phases form an `IsPhaseRun` of length `2` from the empty matching. -/
theorem trap_phaseRun : IsPhaseRun trapGraph ∅ 2 := by
  refine .step (k := 0) (t := 0) (fun j hj => absurd hj (Nat.not_lt_zero j)) (by decide)
    (by decide) trap_phase₁ ?_
  have h₁ : augment ∅ ({(0, 0)} : Finset (Fin 2 × Fin 2)) = {(0, 0)} := by decide
  rw [h₁]
  refine .step (k := 1) (t := 1) (fun j hj => ?_) (by decide) (by decide) trap_phase₂ .done
  obtain rfl : j = 0 := by omega
  decide

/-! ### 3. Further instances -/

/-- Upper-triangular `4 × 4` graph: `(u, v)` is an edge iff `u ≤ v`. -/
def triGraph : Fin 4 × Fin 4 → Bool := fun e => decide (e.1.val ≤ e.2.val)

example : (hopcroftKarpDenseM triGraph).ret.matching.card = 4 := by decide

example : (hopcroftKarpDenseM triGraph).ret.phases = 1 := by decide

/-- Unbalanced `5 × 3` graph: every left vertex sees `v₀`, and `u₄` sees every right vertex. -/
def starGraph : Fin 5 × Fin 3 → Bool := fun e => decide (e.2.val = 0 ∨ e.1.val = 4)

example : (hopcroftKarpDenseM starGraph).ret.matching.card = 2 := by decide

example : (hopcroftKarpDenseM starGraph).ret.cover.size = 2 := by decide

example : (hopcroftKarpDenseM starGraph).ret.matching.card =
    (bipartiteMatchingM starGraph).ret.matching.card :=
  card_hopcroftKarpM_matching (bipAdjValid_denseBipAdj starGraph)

/-- `3 × 3` bipartite graph with a unique perfect matching `(0, 1), (1, 2), (2, 0)`. -/
def perfGraph : Fin 3 × Fin 3 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨2, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

/-- `3 × 3` bipartite graph violating Hall's condition (`{1, 2}` only neighbors `{0}`). -/
def noPerfGraph : Fin 3 × Fin 3 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

theorem perfGraph_hasPerfectMatching :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching perfGraph :=
  (decidePerfectMatchingHKM_eq_true_iff (bipAdjValid_denseBipAdj perfGraph)).mp (by decide)

theorem noPerfGraph_not_hasPerfectMatching :
    ¬ Cslib.Circuits.BipartiteMatching.HasPerfectMatching noPerfGraph := by
  rw [← decidePerfectMatchingHKM_eq_true_iff (bipAdjValid_denseBipAdj noPerfGraph)]
  decide

end CslibFrontierTests.HopcroftKarp
