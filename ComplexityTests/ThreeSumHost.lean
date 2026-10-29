/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.Host.Program
import Mathlib.Tactic.IntervalCases

/-! # Initialized native Convolution-3SUM host clients

The small test solver inspects only the first cell of each matrix. Its correctness is certified
below only for the empty input and the listed singleton inputs. It is not a general Exact
Triangle solver. These clients check that the host's conditional execution theorem is usable.
-/

namespace ComplexityTests.ThreeSumHost

open Cslib WordRAM WordRAM.Signed
open Algorithms.WordRAM.ThreeSum
open Algorithms.ThreeSum

private abbrev ab : Fin 7 := 2
private abbrev bc : Fin 7 := 3
private abbrev ac : Fin 7 := 4
private abbrev zero : Fin 7 := 5
private abbrev out : Fin 7 := 6

private def probe : Code .standard 7 := ram[
  ab ← *ab; bc ← *bc; ac ← *ac; zero ← #0;
  if ab = zero then [
    if bc = zero then [
      if ac = zero then [ out ← #1 ] else [ out ← #0 ]
    ] else [ out ← #0 ]
  ] else [ out ← #0 ] ]

private theorem probe_exec {w : ℕ} (x : Data 7) (h1 : Fits w 1) :
    ∃ y, ExecWithin w probe x y 9 ∧
      y.regs out = (if x.mem (x.regs ab) = 0 ∧ x.mem (x.regs bc) = 0 ∧
        x.mem (x.regs ac) = 0 then 1 else 0) ∧ y.mem = x.mem := by
  let b := if x.mem (x.regs ab) = 0 ∧ x.mem (x.regs bc) = 0 ∧
    x.mem (x.regs ac) = 0 then 1 else 0
  let y := x.set ab (x.mem (x.regs ab)) |>.set bc (x.mem (x.regs bc))
    |>.set ac (x.mem (x.regs ac)) |>.set zero 0 |>.set out b
  refine ⟨y, ?_, by simp [y, b], rfl⟩
  by_cases hab : x.mem (x.regs ab) = 0 <;>
    by_cases hbc : x.mem (x.regs bc) = 0 <;>
    by_cases hac : x.mem (x.regs ac) = 0 <;>
    ram_eval [probe, y, b, hab, hbc, hac, h1, ab, bc, ac, zero, out,
      true_and, false_and, and_true, and_false, Fin.mk.injEq]

/-- Every supplied first-cell answer is charged, and the probe writes no memory. -/
example {w : ℕ} (x : Data 7) (h1 : Fits w 1) :
    ∃ y, ExecWithin w probe x y 9 ∧ y.regs out ≤ 1 ∧ y.mem = x.mem := by
  obtain ⟨y, he, ho, hm⟩ := probe_exec x h1
  refine ⟨y, he, ?_, hm⟩
  rw [ho]
  split_ifs <;> decide

private theorem probe_spec (input : List ℤ)
    (hinput : input = [] ∨ input = [-1] ∨ input = [0] ∨ input = [1])
    (w : ℕ) (h1 : Fits (w + 2) 1) :
    let N := input.length; let U := (N + 2) ^ 0;
      let μ : ℕ → ℤ := fun i => input.getD i 0;
      ∀ s < 2 * Host.sideLength N, ∀ (a : Data 7) (mem : ℕ → ℕ),
      a.regs (Host.solverArg 0) = Host.sideLength N → a.regs (Host.solverArg 1) = 2 * U + 1 →
      a.regs (Host.solverArg 2) = N + 1 →
      a.regs (Host.solverArg 3) = N + 1 + Host.sideLength N * Host.sideLength N →
      a.regs (Host.solverArg 4) = N + 1 + 2 * (Host.sideLength N * Host.sideLength N) →
      a.regs (Host.solverArg 5) = N + 1 + 3 * (Host.sideLength N * Host.sideLength N) →
      a.mem = (Host.instanceArgs N U s μ).filled mem (Host.sideLength N * Host.sideLength N) →
      ∃ b, ExecWithin (w + 2) probe a b 9 ∧ b.regs (Host.solverArg 6) ≤ 1 ∧
        (b.regs (Host.solverArg 6) = 1 ↔ Host.hit N U s μ) ∧
        (∀ a < N + 1, b.mem a = mem a) := by
  dsimp only [Nat.pow_zero]
  intro s hs a mem ht hF hab hbc hac hfree hm
  change a.regs ab = _ at hab
  change a.regs bc = _ at hbc
  change a.regs ac = _ at hac
  obtain ⟨y, he, ho, hym⟩ := probe_exec a h1
  refine ⟨y, he, ?_, ?_, ?_⟩
  · change y.regs out ≤ 1
    rw [ho]
    split_ifs <;> decide
  · change y.regs out = 1 ↔ _
    rw [ho, hab, hbc, hac, hm]
    rcases hinput with rfl | rfl | rfl | rfl
    all_goals norm_num [Host.sideLength] at hs
    all_goals interval_cases s <;>
      norm_num [Host.instanceArgs, Host.instanceArgsAt, Fill.Args.filled,
        Fill.Args.valueAB, Fill.Args.valueBC,
        Fill.Args.valueAC, pick, encode, Host.hit, Algorithms.ExactTriangle.HasZeroTriangle,
        weightAB, weightBC, weightAC] <;> decide
  · intro k hk
    rw [hym, hm]
    apply Fill.Args.outside_filled
    all_goals dsimp only [Host.instanceArgs, Host.instanceArgsAt]; omega

/-- The full quantitative theorem is inhabited for empty, positive and negative singleton
inputs, and the output witness is the actual native pre-halt state. -/
example (input : List ℤ)
    (hinput : input = [] ∨ input = [-1] ∨ input = [0] ∨ input = [1]) :
    ∃ y t, t ≤ Host.time 0 input.length 9 ∧
      Runs 252 ((Host.body 0 probe).program (Host.hostRegisters Host.found))
        (State.init (input.map encode)) ⟨(Host.body 0 probe).size, y⟩ (t - 1) ∧
      Executes 252 ((Host.body 0 probe).program (Host.hostRegisters Host.found))
        (State.init (input.map encode)) (y.regs (Host.hostRegisters Host.found)) t ∧
      (y.regs (Host.hostRegisters Host.found) = 1 ↔
        Convolution input.length (fun i => input.getD i 0)) ∧ y.mem 0 = input.length := by
  have hw : Host.width 0 input.length ≤ 250 := by
    rcases hinput with rfl | rfl | rfl | rfl <;> decide
  have hv : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ 0 : ℕ) := by
    rcases hinput with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨y, t, ht, hr, he, -, ha, hm, -⟩ :=
    Host.runs_input input probe hw hv (probe_spec input hinput 250 (by decide))
  exact ⟨y, t, ht, hr, he, ha,
    (hm 0 (by omega)).trans (by simp only [Data.init_mem_zero, List.length_map])⟩

section Interpreter

-- Kernel reduction traverses the parameter routine and sixteen fully expanded cell computations.
set_option maxRecDepth 16384

/-- Actual host execution sees the zero singleton solution. -/
example : ((Host.body 0 probe).eval 252 10 (.init [encode 0])).map
    (fun yn => yn.1.regs (Host.hostRegisters Host.found)) = some 1 := by decide

/-- Actual host execution rejects a positive singleton. -/
example : ((Host.body 0 probe).eval 252 10 (.init [encode 1])).map
    (fun yn => yn.1.regs (Host.hostRegisters Host.found)) = some 0 := by decide

/-- Actual host execution rejects a negative singleton. -/
example : ((Host.body 0 probe).eval 252 10 (.init [encode (-1)])).map
    (fun yn => yn.1.regs (Host.hostRegisters Host.found)) = some 0 := by decide

/-- Empty input constructs only filler matrices and returns false. -/
example : ((Host.body 0 probe).eval 127 10 (.init [])).map
    (fun yn => yn.1.regs (Host.hostRegisters Host.found)) = some 0 := by decide

end Interpreter

end ComplexityTests.ThreeSumHost
