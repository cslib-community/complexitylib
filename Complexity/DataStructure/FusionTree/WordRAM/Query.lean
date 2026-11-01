/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.DataStructure.FusionTree.WordRAM.Query.Traversal

/-!
# Concrete fusion-tree RAM predecessor endpoint

At each physical word width, one standard-basis program with 1024 registers traverses any
represented preprocessed tree. Its code depends only on width, with a uniform code-size
bound. Query, record base, keys and all node parameters are runtime data. The query returns
an inclusive predecessor as presence in register 32 and a full key in register 33; key zero
is distinct from absence. The flat program halts with register 33, and the proved final
state also exposes register 32.

For a sorted distinct list of `n` fitting full keys, initialization, traversal, all node
calls, pointer loads, loop overhead and halt together take at most
`3100000 * (Nat.log w n + 1)` instructions for every `w ≥ 2`. The concrete representation
uses at most `126n + 18` words, including empty roots. The arena's one-past-end frontier
must fit a word separately from the keys and query. No RAM preprocessing-time bound is
claimed; preprocessing is a classical static construction.

## Main definitions

* `QueryProgram.initial`: actual preprocessed memory and query/base input registers.

## Main results

* `QueryProgram.exec`: complete structured query from arbitrary workspace registers.
* `QueryProgram.exec_build`: the uniform word-logarithmic bound for constructed trees.
* `QueryProgram.query_spec`: concrete bounded memory, linear allocation, final flag/value
  observation and flat-program halt, with all instructions charged.
* `QueryProgram.answer_some_iff`, `QueryProgram.answer_none_iff`: conventional predecessor
  semantics, including empty inputs and equality with stored keys.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.DataStructure.FusionTree.WordRAM.QueryProgram

open Cslib.WordRAM
open Cslib.DataStructure.FusionTree

/-- One fixed size bound for all physical widths. Only width selects the node code. -/
theorem size_code (w : ℕ) : (code w).size ≤ 201050 := by
  have hn : (node w).size ≤ 201000 := by
    unfold node
    split
    · exact NodeProgram.size_code w
    · decide
  simp only [code, setup, loop, body, internal, follow, leaf, Code.size]
  omega

/-- The compiled family has a uniform finite size bound, including its final halt. -/
theorem length_program (w : ℕ) : (program w).length ≤ 201051 := by
  have hs := size_code w
  simp only [program, Code.program, List.length_append, Code.length_assemble,
    List.length_singleton]
  omega

/-- Complete structured query, including installation of every persistent constant.
Only the query and initial pointer need to be supplied in registers. -/
theorem exec {w q p : ℕ} {t : Tree} {x : Data registers}
    (hxq : x.regs query = q) (hxp : x.regs pointer = p)
    (ht : Tree.Valid (branching w) t) (hs : t.keys.Pairwise (· < ·))
    (hk : ∀ k ∈ t.keys, Fits w k)
    (hr : Rep (parameterWords w) t p x.mem) (ha : ArenaFits w p t) (hq : Fits w q) :
    ∃ y, ExecWithin w (code w) x y (201022 * (t.height + 1) + 7) ∧
      Done q (t.predecessor q) x.mem y := by
  obtain ⟨hsetup, hentry⟩ := exec_initialize x ha.allocation.2.2
  have hentry' : Entry q p (initialized x) := by
    simpa only [hxq, hxp] using hentry
  obtain ⟨y, hey, hy⟩ := exec_loop hentry' ht hs hk hr ha hq
  exact ⟨y, (hsetup.within.seq hey).mono (by omega), hy⟩

private theorem total_time_le {h w n : ℕ} (hh : h ≤ 14 * (Nat.log w n + 1)) :
    201022 * (h + 1) + 7 ≤ 3100000 * (Nat.log w n + 1) - 1 := by
  omega

/-- The constructed tree has a uniform word-logarithmic query bound. One instruction
is reserved for the flat program's halt. All node and representation premises are
discharged from the sorted full keys and actual preprocessing, with no node oracle. -/
theorem exec_build {w q p : ℕ} {xs : List ℕ} {x : Data registers}
    (hw : 2 ≤ w) (hxq : x.regs query = q) (hxp : x.regs pointer = p)
    (hs : xs.Pairwise (· < ·)) (hk : ∀ k ∈ xs, Fits w k)
    (hr : Rep (parameterWords w) (Tree.build (branching w) xs) p x.mem)
    (ha : ArenaFits w p (Tree.build (branching w) xs)) (hq : Fits w q) :
    ∃ y, ExecWithin w (code w) x y (3100000 * (Nat.log w xs.length + 1) - 1) ∧
      Done q ((Tree.build (branching w) xs).predecessor q) x.mem y := by
  have ht := Tree.valid_build (two_le_branching w) xs
  have hs' : (Tree.build (branching w) xs).keys.Pairwise (· < ·) := by
    simpa only [Tree.keys_build (two_le_branching w)] using hs
  have hk' : ∀ k ∈ (Tree.build (branching w) xs).keys, Fits w k := by
    simpa only [Tree.keys_build (two_le_branching w)] using hk
  obtain ⟨y, hey, hy⟩ := exec hxq hxp ht hs' hk' hr ha hq
  exact ⟨y, hey.mono (total_time_le (height_build_branching_le hw xs)), hy⟩

/-- Concrete preprocessed RAM, with only query and record base in the register file.
All other registers initially hold zero. This is static construction, not a RAM instruction. -/
noncomputable def initial (w : ℕ) (xs : List ℕ) (p q : ℕ) : Data registers :=
  ⟨fun i => if i = query then q else if i = pointer then p else 0,
    memory (parameterWords w) (Tree.build (branching w) xs) p⟩

/-- The actual initial register and memory words fit under the explicit query/key/arena bounds. -/
theorem initial_bounded {w p q : ℕ} {xs : List ℕ} (hk : ∀ k ∈ xs, Fits w k)
    (ha : ArenaFits w p (Tree.build (branching w) xs)) (hq : Fits w q) :
    (initial w xs p q).Bounded w := by
  refine ⟨?_, memory_fits ha (preprocessed_contentFits_build w xs hk)⟩
  intro i
  dsimp only [initial]
  split
  · exact hq
  · split
    · exact ha.allocation.1
    · exact fits_zero w

/-- Full concrete endpoint. The final-state observation exposes the presence flag as well
as the halted value. The bound includes the halt; memory and query are preserved exactly.
Allocation is `O(n+1)` for all inputs and `O(n)` for nonempty inputs. -/
theorem query_spec {w p q : ℕ} {xs : List ℕ} (hw : 2 ≤ w)
    (hs : xs.Pairwise (· < ·)) (hk : ∀ k ∈ xs, Fits w k)
    (ha : ArenaFits w p (Tree.build (branching w) xs)) (hq : Fits w q) :
    (initial w xs p q).Bounded w ∧
      (encode (parameterWords w) p (Tree.build (branching w) xs)).length ≤
        126 * xs.length + 18 ∧
      ∃ y k, k + 1 ≤ 3100000 * (Nat.log w xs.length + 1) ∧
        Runs w (program w) ⟨0, initial w xs p q⟩ ⟨(code w).size, y⟩ k ∧
        Executes w (program w) ⟨0, initial w xs p q⟩ (y.regs value) (k + 1) ∧
        Done q ((Tree.build (branching w) xs).predecessor q)
          (initial w xs p q).mem y := by
  have hqr : (initial w xs p q).regs query = q := by simp [initial]
  have hpr : (initial w xs p q).regs pointer = p := by simp +decide [initial]
  obtain ⟨y, ⟨k, hkbound, he⟩, hy⟩ := exec_build hw hqr hpr hs hk
    (rep_memory _ _ _) ha hq
  refine ⟨initial_bounded hk ha hq, ?_, y, k, ?_, ?_, he.executes value, hy⟩
  · rw [encode_length]
    exact span_build_le (two_le_branching w) xs
  · omega
  · simpa only [Nat.zero_add] using
      he.runs ((Program.Contains.self (program w)).append_left)

/-- Returned full keys are exactly the inclusive predecessors of the stored set. -/
theorem answer_some_iff {w q a : ℕ} {xs : List ℕ} {mem : ℕ → ℕ}
    {y : Data registers} (hs : xs.Pairwise (· < ·))
    (hy : Done q ((Tree.build (branching w) xs).predecessor q) mem y) :
    answer y = some a ↔ a ∈ xs ∧ a ≤ q ∧ ∀ k ∈ xs, k ≤ q → k ≤ a := by
  rw [hy.answer_eq]
  exact Tree.predecessor_build_eq_some_iff (two_le_branching w) hs

/-- Absence is exactly the case where every stored key is greater than the query. -/
theorem answer_none_iff {w q : ℕ} {xs : List ℕ} {mem : ℕ → ℕ} {y : Data registers}
    (hs : xs.Pairwise (· < ·))
    (hy : Done q ((Tree.build (branching w) xs).predecessor q) mem y) :
    answer y = none ↔ ∀ k ∈ xs, q < k := by
  rw [hy.answer_eq]
  exact Tree.predecessor_build_eq_none_iff (two_le_branching w) hs

end Cslib.DataStructure.FusionTree.WordRAM.QueryProgram
