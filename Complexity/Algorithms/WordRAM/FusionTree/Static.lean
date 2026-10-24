/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Query

/-!
# Static fusion trees for finite sets

Every finite set of distinct unsigned word keys has a static fusion-tree representation.
Preprocessing sorts the set, builds the tree, and chooses its proved compression parameters;
no RAM preprocessing-time bound is claimed. Query execution uses the actual standard-basis
program, whose bounded-size nonuniform code family depends only on physical word width.

The explicit arena contract covers the whole allocation frontier, in addition to the keys
and query fitting words. The returned option is two words: presence in register 32 and a key
in register 33. This distinguishes absence from key zero without requiring an extra data bit.

## Main definitions

* `Static.orderedKeys`: the elements of a finite set as a strictly increasing list.
* `Static.tree`: the tree constructed from an arbitrary finite set.
* `Static.initial`: its actual preprocessed memory and query registers.
* `Static.IsPredecessor`: conventional inclusive predecessor semantics.
* `Static.workingWords`: allocated data words plus all 1024 query registers.

## Main results

* `Static.query_spec`: actual halting RAM execution in `3100000 (1 + log_w n)` instructions.
* `Static.workingWords_le`: at most `126n + 1042` data and register words.
* `Static.workingWords_le_of_nonempty`: at most `1168n` words for nonempty sets.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.Static

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- Sorting is part of static preprocessing; queries do not scan this list. -/
def orderedKeys (s : Finset ℕ) : List ℕ := s.sort (· ≤ ·)

/-- The concrete tree for a finite key set. -/
def tree (w : ℕ) (s : Finset ℕ) : Tree := Tree.build (branching w) (orderedKeys s)

/-- Preprocessed memory, query, and base address, with zero initial workspace registers. -/
noncomputable def initial (w : ℕ) (s : Finset ℕ) (base q : ℕ) : Data QueryProgram.registers :=
  QueryProgram.initial w (orderedKeys s) base q

/-- Conventional inclusive predecessor, with a separate case for absence. -/
def IsPredecessor (s : Finset ℕ) (q : ℕ) : Option ℕ → Prop
  | none => ∀ k ∈ s, q < k
  | some a => a ∈ s ∧ a ≤ q ∧ ∀ k ∈ s, k ≤ q → k ≤ a

/-- All allocated data and working registers. The compiled program has a separate uniform
size bound of 201051 instructions, including halt; it contains the width-only constants. -/
def workingWords (w : ℕ) (s : Finset ℕ) : ℕ := span (tree w s) + QueryProgram.registers

/-- A uniform linear bound, including the empty structure and all query registers. -/
theorem workingWords_le (w : ℕ) (s : Finset ℕ) : workingWords w s ≤ 126 * s.card + 1042 := by
  have h := span_build_le (two_le_branching w) (orderedKeys s)
  simp only [orderedKeys, Finset.length_sort] at h
  change span (Tree.build (branching w) (orderedKeys s)) + 1024 ≤ _
  simp only [orderedKeys]
  omega

/-- For nonempty sets, the additive workspace and empty-root constants are absorbed in `n`. -/
theorem workingWords_le_of_nonempty (w : ℕ) {s : Finset ℕ} (hs : s.Nonempty) :
    workingWords w s ≤ 1168 * s.card := by
  have hn := Finset.card_pos.mpr hs
  have h := workingWords_le w s
  omega

/-- A sufficient input-size-only address condition for the actual allocation. -/
theorem arenaFits_of_bound {w base : ℕ} (s : Finset ℕ)
    (ha : Fits w (base + 126 * s.card + 18)) : ArenaFits w base (tree w s) := by
  apply arenaFits_build_of_bound (two_le_branching w)
  simpa only [orderedKeys, Finset.length_sort] using ha

/-- Every arbitrary finite key set receives an actual bounded RAM representation and correct
halting predecessor execution. Time includes initialization, all node instructions, traversal,
and halt. Space includes the allocated records, auxiliary data, and all working registers.
Width selects the code family; the key set, address, and query are runtime data. -/
theorem query_spec {w base q : ℕ} (s : Finset ℕ) (hw : 2 ≤ w)
    (hk : ∀ k ∈ s, Fits w k) (ha : ArenaFits w base (tree w s)) (hq : Fits w q) :
    (initial w s base q).Bounded w ∧ workingWords w s ≤ 126 * s.card + 1042 ∧
      ∃ y k, k + 1 ≤ 3100000 * (Nat.log w s.card + 1) ∧
        Runs w (QueryProgram.program w) ⟨0, initial w s base q⟩
          ⟨(QueryProgram.code w).size, y⟩ k ∧
        Executes w (QueryProgram.program w) ⟨0, initial w s base q⟩
          (y.regs QueryProgram.value) (k + 1) ∧
        IsPredecessor s q (QueryProgram.answer y) ∧
        y.mem = (initial w s base q).mem ∧ y.regs QueryProgram.query = q := by
  have hs : (orderedKeys s).Pairwise (· < ·) := s.sortedLT_sort.pairwise
  have hkeys : ∀ k ∈ orderedKeys s, Fits w k := by
    simpa only [orderedKeys, Finset.mem_sort] using hk
  obtain ⟨hb, _, y, k, ht, hr, he, hy⟩ := QueryProgram.query_spec hw hs hkeys ha hq
  refine ⟨hb, workingWords_le w s, y, k, ?_, hr, he, ?_, hy.mem_eq, hy.query_eq⟩
  · simpa only [orderedKeys, Finset.length_sort] using ht
  · cases hans : QueryProgram.answer y with
    | none =>
      have hnone := (QueryProgram.answer_none_iff hs hy).mp hans
      simpa only [IsPredecessor, orderedKeys, Finset.mem_sort] using hnone
    | some a =>
      have hsome := (QueryProgram.answer_some_iff hs hy).mp hans
      simpa only [IsPredecessor, orderedKeys, Finset.mem_sort] using hsome

end Cslib.Algorithms.WordRAM.FusionTree.Static
