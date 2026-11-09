/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORNativeBalance
import Mathlib.Tactic.IntervalCases

/-!
# Native maximum smaller-class traversal

The concrete nonuniform arrays below are the actual forward/backward counts of
the original five-bit chain, with backward complement indexing. Further runs
distinguish reversed addressing, ties, empty arrays and width-zero multiplicity.
This client supplies counter arrays; it does not claim a combined dissection run.
-/

-- The checked examples and private fixtures export no library API.
set_option linter.privateModule false

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR Native

private def operands : Fin 3 → BitVec 5 := ![3#5, 8#5, 5#5]

private def counters : Data 18 :=
  { regs := fun r => if r = source then 20 else if r = destination then 30
      else if r = modulus then 4 else 99
    mem := fun z => if 20 ≤ z ∧ z < 24 then [2, 0, 2, 4].getD (z - 20) 0
      else if 30 ≤ z ∧ z < 34 then [2, 4, 2, 0].getD (z - 30) 0 else if z = 100 then 17 else 0 }

private theorem forward_cells : ∀ g : BitVec 2,
    counters.mem (20 + g.toNat) = forwardClassCount 2 operands 10#5 g := by
  decide +kernel

private theorem backward_cells : ∀ g : BitVec 2,
    counters.mem (30 + (~~~g).toNat) = backwardClassCount 2 operands 7#5 g := by
  decide +kernel

private theorem counters_bounded : counters.Bounded 8 := by
  constructor
  · intro r
    fin_cases r <;> decide
  · intro z
    by_cases hf : 20 ≤ z ∧ z < 24
    · obtain ⟨_, _⟩ := hf
      interval_cases z <;> decide
    · by_cases hb : 30 ≤ z ∧ z < 34
      · obtain ⟨_, _⟩ := hb
        interval_cases z <;> decide
      · simp only [counters, hf, hb, ↓reduceIte]
        split <;> decide

/-- A concrete finite support cover includes the dirty sentinel at address 100. -/
example : ∃ y n ts, n + 1 ≤ 14 * 4 + 7 ∧
    TraceExec 8 Balance.scan counters y n ts ∧
    Executes 8 (Balance.scan.program answer) ⟨0, counters⟩
      (classBalance 2 operands operands 10#5 7#5) (n + 1) ∧
    y.regs answer = classBalance 2 operands operands 10#5 7#5 ∧
    ∀ k u, Runs 8 (Balance.scan.program answer) ⟨0, counters⟩ u k →
      u.data.Bounded 8 ∧ ∃ live : Finset ℕ,
        (∀ a, u.data.mem a ≠ 0 ↔ a ∈ live) ∧
        (live.card + 18) * 8 ≤ (101 + 18) * 8 := by
  apply Balance.scan_classes_resources operands operands 10#5 7#5 counters
    counters_bounded (Finset.range 101) ?_ (by decide) (by decide) (by decide)
    forward_cells backward_cells (by decide)
  intro a ha
  simp only [counters] at ha
  split_ifs at ha <;> simp only [Finset.mem_range] <;> omega

/-- Every input hypothesis of the semantic bridge is supplied on a real chain. -/
example : ∃ y, ExecWithin 8 Balance.scan counters y (14 * 4 + 6) ∧
    y.regs answer = classBalance 2 operands operands 10#5 7#5 ∧ y.mem = counters.mem ∧
    ∀ g : BitVec 2, min (forwardClassCount 2 operands 10#5 g)
      (backwardClassCount 2 operands 7#5 g) ≤ y.regs answer :=
  Balance.scan_classes_exec operands operands 10#5 7#5 counters
    (by decide) (by decide) (by decide) forward_cells backward_cells (by decide)

/-- Execute the comparisons and loops, rather than reducing only the observer. -/
example : (Balance.scan.eval 8 8 counters).map
    (fun r => (r.1.regs answer, decide (r.2 ≤ 14 * 4 + 6), r.1.mem 100)) =
      some (2, true, 17) := by decide +kernel

/-- Omitting complemented backward addresses would incorrectly return zero. -/
example : (Balance.scan.eval 8 8
    { regs := fun r => if r = source then 20 else if r = destination then 30
        else if r = modulus then 4 else 99
      mem := fun z => if z = 20 ∨ z = 33 then 8 else 0 }).map
    (fun r => r.1.regs answer) = some 8 := by decide +kernel

/-- Tied counters preserve multiplicity when the projected state has width zero. -/
example : (Balance.scan.eval 8 3
    { regs := fun r => if r = source then 20 else if r = destination then 30
        else if r = modulus then 1 else 99
      mem := fun _ => 8 }).map
    (fun r => r.1.regs answer) = some 8 := by decide +kernel

/-- The generic traversal also handles an empty interval, without reading memory. -/
example : (Balance.scan.eval 8 1 (counters.set modulus 0)).map
    (fun r => (r.1.regs answer, r.2)) = some (0, 6) := by decide +kernel

/-- Occupancy includes every initial nonzero cell, even those never read. -/
example {W k : ℕ} (x : Data 18) (u : State 18)
    (h : Runs W (Balance.scan.program answer) ⟨0, x⟩ u k) (a : ℕ) :
    u.data.mem a = x.mem a := congrFun (Balance.scan_prefix_memory x u h) a

example : Balance.scan.IsRandFree ∧ ¬Balance.scan.ReadsWidth := by decide
