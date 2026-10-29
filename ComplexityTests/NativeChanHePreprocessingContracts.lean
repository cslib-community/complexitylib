/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

-- This test module exports no library declarations.
set_option linter.privateModule false

/-!
# Admitted whole-program native preprocessing clients

These clients discharge the width and input promises and retain the actual complete native
execution and memory witness. In particular, the negative two-position case still emits an
instance; it is never replaced by an empty output as a shortcut.
-/

namespace ComplexityTests.NativeChanHePreprocessingContracts

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.ThreeSum.ChanHe
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

private theorem promise {κ : ℕ} (input : List ℤ)
    (h : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ (out : List (ℕ × Node)) (y : Data 128) (steps : ℕ),
      Executes (width κ input.length) (flatProgram κ)
        (State.init (input.map Signed.encode)) out.length steps ∧
      Runs (width κ input.length) (flatProgram κ)
        (State.init (input.map Signed.encode)) ⟨(program κ).size, y⟩ (steps - 1) ∧
      steps ≤ cost κ input.length ∧
      out.map (fun p : ℕ × Node => p.2.oneArray (2 * (input.length + 2) ^ κ)) =
        instances input.length ((input.length + 2) ^ κ) (fun i => input[i]) ∧
      Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.StoredNodes
        (2 * (input.length + 2) ^ κ)
        (2 * mPar input.length (2 * (input.length + 2) ^ κ) ^ 2)
        (arena κ input.length y.mem).table out y.mem := by
  obtain ⟨out, y, steps, he, hr, ht, ho, hm, _, _, _, _⟩ := runs_input input le_rfl h
  exact ⟨out, y, steps, he, hr, ht, ho, hm⟩

-- Empty input retains the complete initialization/prime/forest execution, with no output.
example : ∃ y steps,
    Executes (width 0 0) (flatProgram 0) (State.init []) 0 steps ∧
      Runs (width 0 0) (flatProgram 0) (State.init []) ⟨(program 0).size, y⟩ (steps - 1) ∧
      steps ≤ cost 0 0 := by
  obtain ⟨out, y, steps, he, hr, ht, ho, _⟩ := promise (κ := 0) [] (by simp)
  have hempty : instances 0 1 (Fin.elim0 : Fin 0 → ℤ) = [] := by decide
  have hfun : (fun i : Fin 0 => ([] : List ℤ)[i]) = (Fin.elim0 : Fin 0 → ℤ) := by
    funext i
    exact Fin.elim0 i
  have hlen := congrArg List.length ho
  simp only [List.length_nil, Nat.zero_add, pow_zero, hfun, hempty, List.length_map] at hlen
  simp only [List.length_nil, List.map_nil] at he hr ht
  rw [hlen] at he
  exact ⟨y, steps, he, hr, ht⟩

-- One negative input also runs the complete program rather than supplying empty descriptors.
example : ∃ steps, Executes (width 0 1) (flatProgram 0)
    (State.init [Signed.encode (-1)]) 0 steps ∧ steps ≤ cost 0 1 := by
  obtain ⟨out, y, steps, he, _, ht, ho, _⟩ := promise (κ := 0) [-1] (by
    intro z hz
    simp only [List.mem_singleton] at hz
    subst z
    decide)
  have hempty : instances 1 1 (fun _ : Fin 1 => (-1 : ℤ)) = [] := by decide
  have hfun : (fun i : Fin 1 => ([-1] : List ℤ)[i]) = (fun _ : Fin 1 => (-1 : ℤ)) := by
    funext i
    fin_cases i
    rfl
  change out.map (fun p : ℕ × Node => p.2.oneArray 2) =
    instances 1 1 (fun i : Fin 1 => ([-1] : List ℤ)[i]) at ho
  rw [hfun, hempty] at ho
  have hlen := congrArg List.length ho
  simp only [List.length_map, List.length_nil] at hlen
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil] at he ht
  rw [hlen] at he
  exact ⟨steps, he, ht⟩

private def pair : Fin 2 → ℤ := fun _ => 1

private def pairNode : Node :=
  ⟨{2}, {0}, {1}, modulus (Nat.primesLE (mPar 2 2)) (labelBits 2) {2} {0} {1}⟩

private theorem pair_node_mem : pairNode ∈ allNodes 2 1 pair := by
  apply mem_allNodes_iff.mpr
  refine ⟨{2}, {0}, {1}, ?_, ?_⟩
  · have ht : twiceSet pair = {2} := by decide
    have hi : Finset.univ.image pair = {1} := by decide
    simpa only [ht, hi] using (IsInput.twice (U := 1) (x := pair))
  · change pairNode ∈ nodes (Nat.primesLE (mPar 2 2)) (labelBits 2) 4 {2} {0} {1}
    rw [nodes]
    simp only [Finset.singleton_ne_empty, false_or, ↓reduceIte, List.mem_cons]
    exact Or.inl rfl

-- Two equal values have no distinct-position 3SUM solution, yet their exact reduction is nonempty.
example : ∃ (out : List (ℕ × Node)) (y : Data 128) (steps : ℕ),
    Executes (width 0 2) (flatProgram 0) (State.init [Signed.encode 1, Signed.encode 1])
      out.length steps ∧ steps ≤ cost 0 2 ∧ out ≠ [] ∧
      out.map (fun p : ℕ × Node => p.2.oneArray 2) = instances 2 1 pair ∧
      Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.StoredNodes 2
        (2 * mPar 2 2 ^ 2) (arena 0 2 y.mem).table out y.mem ∧
      ¬∃ f ∈ out.map (fun p : ℕ × Node => p.2.oneArray 2), Convolution (8 * mPar 2 2 ^ 2) f := by
  obtain ⟨out, y, steps, he, _, ht, ho, hm⟩ := promise (κ := 0) [1, 1] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hz
    subst z
    decide)
  change out.map (fun p : ℕ × Node => p.2.oneArray 2) = instances 2 1 pair at ho
  have hmem : pairNode.oneArray 2 ∈ instances 2 1 pair :=
    List.mem_map.mpr ⟨pairNode, pair_node_mem, rfl⟩
  refine ⟨out, y, steps, he, ht, ?_, ho, hm, ?_⟩
  · intro hnil
    rw [← ho, hnil, List.map_nil] at hmem
    exact List.not_mem_nil hmem
  · rw [ho, ← instances_correct 2 1 (by decide) pair (by unfold pair; decide)]
    unfold HasSolution pair
    decide

-- The same program covers a genuine equal-value positive instance and its native memory.
example : ∃ (out : List (ℕ × Node)) (y : Data 128) (steps : ℕ),
    Executes (width 1 3) (flatProgram 1)
      (State.init ([(-2 : ℤ), 1, 1].map Signed.encode)) out.length steps ∧
      steps ≤ cost 1 3 ∧
      out.map (fun p : ℕ × Node => p.2.oneArray 10) =
        instances 3 5 (fun i : Fin 3 => ([(-2 : ℤ), 1, 1] : List ℤ)[i]) ∧
      Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.StoredNodes 10
        (2 * mPar 3 10 ^ 2) (arena 1 3 y.mem).table out y.mem ∧
      ∃ f ∈ out.map (fun p : ℕ × Node => p.2.oneArray 10), Convolution (8 * mPar 3 10 ^ 2) f := by
  have hv : ∀ z ∈ ([(-2 : ℤ), 1, 1] : List ℤ), |z| ≤ ((3 + 2) ^ 1 : ℕ) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hz
    rcases hz with rfl | rfl <;> decide
  obtain ⟨out, y, steps, he, _, ht, ho, hm⟩ := promise (κ := 1) [-2, 1, 1] hv
  change out.map (fun p : ℕ × Node => p.2.oneArray 10) =
    instances 3 5 (fun i : Fin 3 => ([(-2 : ℤ), 1, 1] : List ℤ)[i]) at ho
  refine ⟨out, y, steps, he, ht, ho, hm, ?_⟩
  rw [ho]
  apply (instances_correct 3 5 (by decide) _ (by decide)).mp
  unfold HasSolution
  decide

end ComplexityTests.NativeChanHePreprocessingContracts
