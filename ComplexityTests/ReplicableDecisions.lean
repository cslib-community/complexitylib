/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Probability.ReplicableDecisions.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

/-!
# Finite graph-selector regression examples

Actual line graphs of odd and even class distance exercise the full graph wrapper.
The one-edge and two-edge cases have no neighborhood-correct law; disconnected forced
classes and an empty forced class have zero profiles. No native decision procedure is used.
-/

set_option linter.privateModule false

open scoped ENNReal
open Cslib.ReplicableDecisions

namespace ComplexityTests.ReplicableDecisions

private abbrev lineGraph (n : ℕ) := SimpleGraph.pathGraph (n + 1)

private def lineProblem (n : ℕ) (hn : 0 < n) : Problem (Fin (n + 1)) where
  graph := lineGraph n
  forcedZero := {0}
  forcedOne := {⟨n, Nat.lt_succ_self n⟩}
  disjoint := by
    rw [Set.disjoint_left]
    intro v hz ho
    simp only [Set.mem_singleton_iff] at hz ho
    have heq := congrArg Fin.val (hz.symm.trans ho)
    simp only [Fin.val_zero] at heq
    omega

private theorem coordinate_le_length {n : ℕ} {a b : Fin (n + 1)}
    (p : (lineGraph n).Walk a b) : b.val ≤ a.val + p.length := by
  induction p with
  | nil => omega
  | @cons a c b hac q ih =>
    have hac' : a.val + 1 = c.val ∨ c.val + 1 = a.val := SimpleGraph.pathGraph_adj.mp hac
    simp only [SimpleGraph.Walk.length_cons]
    rcases hac' with hac' | hac' <;> omega

private theorem line_distance {n : ℕ} (hn : 0 < n)
    (p : (lineGraph n).Walk 0 ⟨n, Nat.lt_succ_self n⟩) (hp : p.length = n) :
    (lineProblem n hn).classDistance = n := by
  have hle : (lineGraph n).edist 0 ⟨n, Nat.lt_succ_self n⟩ ≤ n := by
    simpa only [hp] using p.edist_le
  obtain ⟨d, hd, hdn⟩ := ENat.le_natCast_iff.mp hle
  obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hd
  have hbound := coordinate_le_length q
  simp only [Fin.val_zero, hq, zero_add] at hbound
  have heq : (lineGraph n).edist 0 ⟨n, Nat.lt_succ_self n⟩ = n := by
    rw [hd]
    exact_mod_cast (show d = n by omega)
  simpa [lineProblem, Problem.classDistance, Problem.distanceFrom] using heq

private theorem line_edge (n : ℕ) (a b : Fin (n + 1)) (h : a.val + 1 = b.val) :
    (lineGraph n).Adj a b := SimpleGraph.pathGraph_adj.mpr (Or.inl h)

private theorem distance_three : (lineProblem 3 (by decide)).classDistance = 3 :=
  line_distance (by decide)
    (.cons (line_edge 3 0 1 rfl) (.cons (line_edge 3 1 2 rfl)
      (.cons (line_edge 3 2 3 rfl) .nil))) rfl

private theorem distance_four : (lineProblem 4 (by decide)).classDistance = 4 :=
  line_distance (by decide)
    (.cons (line_edge 4 0 1 rfl) (.cons (line_edge 4 1 2 rfl)
      (.cons (line_edge 4 2 3 rfl) (.cons (line_edge 4 3 4 rfl) .nil)))) rfl

-- The exact equations include actual laws attaining the bounds and all-law lower bounds.
example :
    (lineProblem 3 (by decide)).jointProfile = ENNReal.ofReal (1 / 3 : ℝ) ∧
      (lineProblem 3 (by decide)).correctProfile = ENNReal.ofReal (1 / 2 : ℝ) ∧
      (lineProblem 3 (by decide)).neighborhoodProfile = 1 := by
  obtain ⟨hj, hc, hn⟩ := (lineProblem 3 (by decide)).finite_profiles distance_three
  exact ⟨by norm_num at hj ⊢; exact hj, by norm_num at hc ⊢; exact hc,
    by norm_num at hn ⊢; exact hn⟩

example :
    IsOptimum (lineProblem 4 (by decide)).Correct (lineProblem 4 (by decide)).Boundary (1 / 2) ∧
      IsOptimum (lineProblem 4 (by decide)).NeighborhoodCorrect
        (lineProblem 4 (by decide)).Boundary 1 := by
  constructor
  · have h := (lineProblem 4 (by decide)).correct_optimum distance_four
    norm_num at h
    exact h
  · have h := (lineProblem 4 (by decide)).neighborhood_optimum distance_four (by decide)
    norm_num at h
    exact h

private theorem distance_one : (lineProblem 1 (by decide)).classDistance = 1 :=
  line_distance (by decide) (.cons (line_edge 1 0 1 rfl) .nil) rfl

private theorem distance_two : (lineProblem 2 (by decide)).classDistance = 2 :=
  line_distance (by decide) (.cons (line_edge 2 0 1 rfl) (.cons (line_edge 2 1 2 rfl) .nil)) rfl

example : (lineProblem 1 (by decide)).neighborhoodProfile = ⊤ :=
  (lineProblem 1 (by decide)).neighborhoodProfile_eq_top distance_one (by decide)

example : ¬∃ f, (lineProblem 2 (by decide)).NeighborhoodCorrect f :=
  (lineProblem 2 (by decide)).not_neighborhoodCorrect_of_classDistance_le_two
    distance_two (by decide)

-- On the two-edge line the joint mixture consists only of the two constants.
example : (lineProblem 2 (by decide)).jointProfile = ENNReal.ofReal (1 / 2 : ℝ) := by
  simpa using
    ((lineProblem 2 (by decide)).finite_profiles distance_two).1

private def disconnected : Problem Bool where
  graph := ⊥
  forcedZero := {false}
  forcedOne := {true}
  disjoint := by simp

private theorem disconnected_distance : disconnected.classDistance = ⊤ := by
  simp [disconnected, Problem.classDistance, Problem.distanceFrom, SimpleGraph.edist_bot]

example : disconnected.jointProfile = 0 ∧ disconnected.correctProfile = 0 ∧
    disconnected.neighborhoodProfile = 0 :=
  disconnected.infinite_profiles disconnected_distance

private def emptyClass : Problem Unit where
  graph := ⊥
  forcedZero := ∅
  forcedOne := Set.univ
  disjoint := by simp

example : emptyClass.jointProfile = 0 ∧ emptyClass.correctProfile = 0 ∧
    emptyClass.neighborhoodProfile = 0 := by
  apply emptyClass.infinite_profiles
  simp [emptyClass, Problem.classDistance, Problem.distanceFrom]

-- Non-singleton acceptable sets represent indifference, with both answers permitted.
example (G : SimpleGraph Bool) :
    ∀ v b, (Problem.ofAcceptableSets G (fun _ => Set.univ)).Accepts v b := by
  intro v b
  exact (Problem.ofAcceptableSets_accepts_iff G (fun _ => Set.univ)
    (fun _ => Set.univ_nonempty) v b).mpr (Set.mem_univ b)

end ComplexityTests.ReplicableDecisions
