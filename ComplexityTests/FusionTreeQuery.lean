/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.FusionTree.Static

/-! Concrete instruction executions and satisfiable complete endpoint premises. -/

-- Nonvacuity of the fusion branch uses 512-bit physical words.
set_option exponentiation.threshold 512

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree
open Cslib.Algorithms.WordRAM.FusionTree
open Cslib.Algorithms.WordRAM.FusionTree.QueryProgram

namespace FusionTreeQueryTests

private theorem small_parameters : parameterWords 16 = fun _ _ => 0 := by
  funext t
  cases t with
  | leaf xs => exact parameterWords_leaf 16 xs
  | node m cs => exact parameterWords_small (by decide) m cs

private def smallInput (xs : List ℕ) (q : ℕ) : Data registers :=
  ⟨fun i => if i = query then q else if i = pointer then 32 else 0,
    memory (fun _ _ => 0) (Tree.build (branching 16) xs) 32⟩

example (xs : List ℕ) (q : ℕ) : initial 16 xs 32 q = smallInput xs q := by
  simp only [initial, small_parameters, smallInput]

private theorem built3 : Tree.build (branching 16) [3, 8, 15] =
    .node 3 [.node 3 [.leaf [3], .leaf [8]], .leaf [15]] := by
  rw [show branching 16 = 2 from by decide]
  simp [Tree.build, Tree.buildAux, Tree.join, Tree.chunks, Tree.keys,
    Nat.clog, Nat.clog.go, List.splitLengths, List.take, List.drop]

private theorem built4 : Tree.build (branching 16) [0, 3, 8, 15] =
    .node 0 [.node 0 [.leaf [0], .leaf [3]], .node 8 [.leaf [8], .leaf [15]]] := by
  rw [show branching 16 = 2 from by decide]
  simp [Tree.build, Tree.buildAux, Tree.join, Tree.chunks, Tree.keys,
    Nat.clog, Nat.clog.go, List.splitLengths, List.take, List.drop]

-- Kernel evaluation of actual charged instructions, including two levels of pointers.
example :
    ((code 16).eval 16 5 (smallInput [] 0)).map (fun yn => answer yn.1) = some none ∧
    ((code 16).eval 16 5 (smallInput [0] 0)).map (fun yn => answer yn.1) = some (some 0) ∧
    ((code 16).eval 16 5 (smallInput [3] 2)).map (fun yn => answer yn.1) = some none ∧
    ((code 16).eval 16 5 (smallInput [3] 3)).map (fun yn => answer yn.1) = some (some 3) ∧
    ((code 16).eval 16 5 (smallInput [3, 8, 15] 0)).map (fun yn => answer yn.1) = some none ∧
    ((code 16).eval 16 5 (smallInput [0, 3, 8, 15] 0)).map (fun yn => answer yn.1) =
      some (some 0) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · dsimp only [smallInput]; rw [built3]; decide
  · dsimp only [smallInput]; rw [built4]; decide

private theorem small_query (q : ℕ) (hq : Fits 16 q) :
    ∃ y k, k + 1 ≤ 3100000 * (Nat.log 16 4 + 1) ∧
      Executes 16 (program 16) ⟨0, initial 16 [0, 3, 8, 15] 32 q⟩ (y.regs value) (k + 1) ∧
      Done q ((Tree.build (branching 16) [0, 3, 8, 15]).predecessor q)
        (initial 16 [0, 3, 8, 15] 32 q).mem y := by
  obtain ⟨_, _, y, k, htime, _, he, hy⟩ :=
    query_spec (p := 32) (by decide : 2 ≤ 16) (by decide) (by simp [Fits])
      (arenaFits_build_of_bound (two_le_branching 16) [0, 3, 8, 15] (by decide)) hq
  exact ⟨y, k, htime, he, hy⟩

example :
    (∃ y k, k + 1 ≤ 3100000 * (Nat.log 16 4 + 1) ∧
      Executes 16 (program 16) ⟨0, initial 16 [0, 3, 8, 15] 32 3⟩ (y.regs value) (k + 1) ∧
      answer y = some 3) ∧
    (∃ y k, k + 1 ≤ 3100000 * (Nat.log 16 4 + 1) ∧
      Executes 16 (program 16) ⟨0, initial 16 [0, 3, 8, 15] 32 7⟩ (y.regs value) (k + 1) ∧
      answer y = some 3) ∧
    (∃ y k, k + 1 ≤ 3100000 * (Nat.log 16 4 + 1) ∧
      Executes 16 (program 16) ⟨0, initial 16 [0, 3, 8, 15] 32 8⟩ (y.regs value) (k + 1) ∧
      answer y = some 8) ∧
    (∃ y k, k + 1 ≤ 3100000 * (Nat.log 16 4 + 1) ∧
      Executes 16 (program 16) ⟨0, initial 16 [0, 3, 8, 15] 32 65535⟩
        (y.regs value) (k + 1) ∧ answer y = some 15) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨y, k, ht, he, hy⟩ := small_query 3 (by decide)
    exact ⟨y, k, ht, he, (answer_some_iff (by decide) hy).mpr (by simp)⟩
  · obtain ⟨y, k, ht, he, hy⟩ := small_query 7 (by decide)
    exact ⟨y, k, ht, he, (answer_some_iff (by decide) hy).mpr (by simp)⟩
  · obtain ⟨y, k, ht, he, hy⟩ := small_query 8 (by decide)
    exact ⟨y, k, ht, he, (answer_some_iff (by decide) hy).mpr (by simp)⟩
  · obtain ⟨y, k, ht, he, hy⟩ := small_query 65535 (by decide)
    exact ⟨y, k, ht, he, (answer_some_iff (by decide) hy).mpr (by simp)⟩

-- Nonvacuity of the complete flat endpoint, including the large-width fusion branch.
private theorem large_arena : ArenaFits 512 32 (Tree.build (branching 512) [0, 1, 2]) := by
  apply arenaFits_build_of_bound (two_le_branching 512)
  have hs : 32 + 126 * ([0, 1, 2] : List ℕ).length + 18 < 2 ^ 9 := by decide
  exact hs.trans (Nat.pow_lt_pow_right (a := 2) (m := 9) (n := 512)
    (by decide) (by decide))

private theorem large_keys : ∀ k ∈ ([0, 1, 2] : List ℕ), Fits 512 k := by
  intro k hk
  have hle : k ≤ 2 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hlt : k < 2 ^ 9 := by omega
  exact hlt.trans (Nat.pow_lt_pow_right (a := 2) (m := 9) (n := 512)
    (by decide) (by decide))

/-- An unordered finite set is accepted directly by the public static endpoint. -/
def sampleSet : Finset ℕ := {15, 0, 8, 3}

example :
    ((initial 512 [0, 1, 2] 32 1).Bounded 512 ∧
      ∃ y k, k + 1 ≤ 3100000 * (Nat.log 512 3 + 1) ∧
        Executes 512 (program 512) ⟨0, initial 512 [0, 1, 2] 32 1⟩ (y.regs value) (k + 1) ∧
        answer y = some 1) ∧
    (initial 16 [] 32 0).Bounded 16 ∧
    (initial 16 [0] 32 0).Bounded 16 ∧
    ((Static.initial 16 sampleSet 32 7).Bounded 16 ∧
      ∃ y k, k + 1 ≤ 3100000 * (Nat.log 16 sampleSet.card + 1) ∧
        Executes 16 (program 16) ⟨0, Static.initial 16 sampleSet 32 7⟩
          (y.regs value) (k + 1) ∧ Static.IsPredecessor sampleSet 7 (answer y)) ∧
    Static.workingWords 16 ∅ ≤ 1042 ∧
    Static.workingWords 16 sampleSet ≤ 1168 * sampleSet.card := by
  refine ⟨?_,
    initial_bounded (by simp) (arenaFits_build_of_bound (two_le_branching 16) [] (by decide))
      (fits_zero 16),
    initial_bounded (by simp [fits_zero])
      (arenaFits_build_of_bound (two_le_branching 16) [0] (by decide)) (fits_zero 16),
    ?_, by simpa using Static.workingWords_le 16 ∅,
    Static.workingWords_le_of_nonempty 16 (by decide)⟩
  · have hq : Fits 512 1 := fits_one (by decide)
    obtain ⟨hb, _, y, k, htime, _, he, hy⟩ :=
      query_spec (by decide : 2 ≤ 512) (by decide) large_keys large_arena hq
    refine ⟨hb, y, k, htime, he, ?_⟩
    apply (answer_some_iff (by decide) hy).mpr
    simp
  · obtain ⟨hb, _, y, k, ht, _, he, hp, _, _⟩ :=
      Static.query_spec (w := 16) (base := 32) (q := 7) sampleSet
        (by decide) (by decide) (Static.arenaFits_of_bound sampleSet (by decide)) (by decide)
    exact ⟨hb, y, k, ht, he, hp⟩

end FusionTreeQueryTests
