/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.IterativeCompression.OddCycleTransversal

/-!
# Odd cycle transversal by iterative compression: tests

* The minimum vertex separator (`Cslib.Algorithms.Lean.MaxFlow.minSeparatorM`) on a path and on a
  four-cycle, with a forbidden vertex.
* Theorem-level facts, by `decide` on colourings and the correctness theorem `octM_isSome_iff`:
  the triangle and the five-cycle need exactly one deleted vertex, `K₄` needs exactly two, and
  the four-cycle is bipartite (`∅` suffices).
* Compiled runs of `octM` (`#guard`) on the same graphs, checking that each output is an odd cycle
  transversal of the right size with a colouring proper off it.
-/

namespace ComplexityTests.OddCycleTransversal

open SimpleGraph Cslib.Algorithms.Lean.IterativeCompression Cslib.Algorithms.Lean.MaxFlow

set_option linter.hashCommand false

/-- The cycle on `Fin n`: `v` is adjacent to `v + 1 mod n`. -/
private def cyc (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel fun u v => (u.1 + 1) % n = v.1

private instance (n : ℕ) : DecidableRel (cyc n).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u.1 + 1) % n = v.1 ∨ (v.1 + 1) % n = u.1)))

/-- The path `0 - 1 - 2`. -/
private def path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun u v => u.1 + 1 = v.1

private instance : DecidableRel path3.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)))

/-- Boolean form of "`c` is proper off `S`", for compiled checks. -/
private def properOff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Vector Bool n)
    (S : List (Fin n)) : Bool :=
  decide (∀ u v : Fin n, G.Adj u v → u ∉ S → v ∉ S → vget c u ≠ vget c v)

/-- The output of `octM G k` is a solution: at most `k` vertices, no repetitions, and a colouring
proper off it (checked by `properOff`). -/
private def checkOct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Bool :=
  match (octM G k).ret with
  | some (S, c) => decide (S.length ≤ k) && decide S.Nodup && properOff G c S
  | none => false

/-! ### Minimum vertex separators -/

-- In the path `0 - 1 - 2`, one vertex separates `0` from `2`. A separator may contain terminals:
-- the cut nearest to the source returns `{0}`.
#guard (minSeparatorM path3 #v[false, false, false] #v[true, false, false]
  #v[false, false, true]).ret.sep == [0]

-- In the four-cycle `0 - 1 - 2 - 3 - 0`, separating `{0, 1}` from `{2, 3}` needs two vertices
-- (the edges `0 - 3` and `1 - 2`).
#guard (minSeparatorM (cyc 4) #v[false, false, false, false] #v[true, true, false, false]
  #v[false, false, true, true]).ret.sep.length == 2

-- With `1` forbidden as a separator vertex but blocking walks (in `Z`), one more vertex suffices.
#guard (minSeparatorM (cyc 4) #v[false, true, false, false] #v[true, true, false, false]
  #v[false, false, true, true]).ret.sep.length == 1

-- If `Z` already separates, the separator is empty.
#guard (minSeparatorM (cyc 4) #v[true, true, false, false] #v[true, true, false, false]
  #v[false, false, true, true]).ret.sep == []

/-! ### Theorem-level facts -/

/-- Two of any three vertices share a colour. -/
private theorem pigeon (c : Fin 3 → Bool) : ∃ u v : Fin 3, u ≠ v ∧ c u = c v := by
  revert c
  decide

/-- The triangle is not bipartite. -/
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsOddCycleTransversal ∅ := by
  rw [isOddCycleTransversal_iff_exists_bool]
  rintro ⟨c, hc⟩
  obtain ⟨u, v, huv, h⟩ := pigeon c
  exact hc huv (Set.notMem_empty u) (Set.notMem_empty v) h

/-- Deleting one vertex of the triangle leaves an edge. -/
example : (⊤ : SimpleGraph (Fin 3)).IsOddCycleTransversal {0} := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v = 1), fun u v huv hu hv => ?_⟩
  simp only [Set.mem_singleton_iff] at hu hv
  revert u v
  decide

/-- The five-cycle is not bipartite: a proper colouring would alternate along an odd cycle. -/
private theorem cyc5_not_bipartite :
    ∀ c : Fin 5 → Bool, ∃ u v : Fin 5, (cyc 5).Adj u v ∧ c u = c v := by
  decide

/-- The five-cycle with vertex `0` deleted is a path. -/
private theorem cyc5_oct : (cyc 5).IsOddCycleTransversal ({0} : Finset (Fin 5)) := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v.1 % 2 = 1), fun u v huv hu hv => ?_⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  revert u v
  decide

/-- The four-cycle is bipartite. -/
private theorem cyc4_oct : (cyc 4).IsOddCycleTransversal ((∅ : Finset (Fin 4)) : Set (Fin 4)) := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v.1 % 2 = 1), fun u v huv _ _ => ?_⟩
  revert u v
  decide

example : (cyc 4).IsBipartite := by
  have := cyc4_oct
  rwa [Finset.coe_empty, isOddCycleTransversal_empty_iff] at this

/-- Any three of the four vertices of `K₄`, avoiding one deleted vertex, contain two of the same
colour. -/
private theorem k4_pigeon :
    ∀ a : Fin 4, ∀ c : Fin 4 → Bool, ∃ u v : Fin 4, u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ c u = c v := by
  decide

/-- `K₄` has no odd cycle transversal of at most one vertex. -/
private theorem k4_no_small_oct (T : Finset (Fin 4)) (hT : T.card ≤ 1) :
    ¬ (⊤ : SimpleGraph (Fin 4)).IsOddCycleTransversal T := by
  obtain ⟨a, ha⟩ : ∃ a, T ⊆ {a} := by
    rcases Finset.card_le_one_iff_subset_singleton.mp hT with ⟨a, ha⟩
    exact ⟨a, ha⟩
  rw [isOddCycleTransversal_iff_exists_bool]
  rintro ⟨c, hc⟩
  obtain ⟨u, v, huv, hua, hva, h⟩ := k4_pigeon a c
  exact hc huv (fun hu => hua (Finset.mem_singleton.mp (ha hu)))
    (fun hv => hva (Finset.mem_singleton.mp (ha hv))) h

/-- Deleting two vertices of `K₄` leaves an edge. -/
private theorem k4_oct :
    (⊤ : SimpleGraph (Fin 4)).IsOddCycleTransversal ({0, 1} : Finset (Fin 4)) := by
  rw [isOddCycleTransversal_iff_exists_bool]
  refine ⟨fun v => decide (v = 2), fun u v huv hu hv => ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hu hv
  revert u v
  decide

/-- `octM` on `K₄`: no solution with one vertex, a solution with two. -/
example : (octM (⊤ : SimpleGraph (Fin 4)) 1).ret = none ∧
    (octM (⊤ : SimpleGraph (Fin 4)) 2).ret.isSome := by
  refine ⟨Option.not_isSome_iff_eq_none.mp fun h => ?_,
    octM_isSome_iff.mpr ⟨_, k4_oct, by decide⟩⟩
  obtain ⟨T, hT, hk⟩ := octM_isSome_iff.mp h
  exact k4_no_small_oct T hk hT

/-- `octM` on the five-cycle: no solution with no vertex, a solution with one. -/
example : (octM (cyc 5) 0).ret = none ∧ (octM (cyc 5) 1).ret.isSome := by
  refine ⟨Option.not_isSome_iff_eq_none.mp fun h => ?_,
    octM_isSome_iff.mpr ⟨_, cyc5_oct, by decide⟩⟩
  obtain ⟨T, hT, hk⟩ := octM_isSome_iff.mp h
  obtain rfl := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
  rw [isOddCycleTransversal_iff_exists_bool] at hT
  obtain ⟨c, hc⟩ := hT
  obtain ⟨u, v, huv, h⟩ := cyc5_not_bipartite c
  exact hc huv (by simp) (by simp) h

/-- `octM` on the four-cycle with `k = 0` succeeds. -/
example : (octM (cyc 4) 0).ret.isSome :=
  octM_isSome_iff.mpr ⟨∅, cyc4_oct, le_rfl⟩

/-- The running-time bound, instantiated. -/
example : (octM (⊤ : SimpleGraph (Fin 4)) 2).time ≤ 312 * 3 ^ 2 * 5 ^ 6 :=
  time_octM_le 2

/-! ### Compiled runs -/

-- The triangle: one vertex.
#guard (octM (⊤ : SimpleGraph (Fin 3)) 0).ret.isNone
#guard checkOct (⊤ : SimpleGraph (Fin 3)) 1

-- The five-cycle: one vertex. With `k = 3` the output need not be minimum (here it has three
-- vertices): `octM` decides "at most `k`".
#guard (octM (cyc 5) 0).ret.isNone
#guard checkOct (cyc 5) 1
#guard checkOct (cyc 5) 3

-- `K₄`: two vertices.
#guard (octM (⊤ : SimpleGraph (Fin 4)) 1).ret.isNone
#guard checkOct (⊤ : SimpleGraph (Fin 4)) 2

-- The four-cycle and the path are bipartite: no vertex.
#guard checkOct (cyc 4) 0
#guard checkOct path3 0

-- Two disjoint triangles in `Fin 6` need two vertices.
private def twoTriangles : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v => u.1 / 3 = v.1 / 3

private instance : DecidableRel twoTriangles.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u.1 / 3 = v.1 / 3 ∨ v.1 / 3 = u.1 / 3)))

#guard (octM twoTriangles 1).ret.isNone
#guard checkOct twoTriangles 2

-- The seven-cycle: one vertex.
#guard (octM (cyc 7) 0).ret.isNone
#guard checkOct (cyc 7) 1

end ComplexityTests.OddCycleTransversal
