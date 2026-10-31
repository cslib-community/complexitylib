/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.Table
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationReader

/-!
# Initialized fair-coin table runs

A concrete machine's entire 1458-bit table is emitted from zero registers on its original framed
one-bit input. At one fixed row and column, the two output bits change from `[true, false]` to
`[false, false]` when only the original input bit changes, and to `[true, true]` when the two coin
successors coincide. The output index is the ordinary row-major index, not an assumed oracle.
The empty input and exponent-zero compact box also have actual initialized runs.
-/

namespace ComplexityTests.FairCoinTable

open Cslib.Turing Turing MultiTapeTM CounterProgram Instr
open MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph

private def machine (different : Bool) : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ bit :=
    .step
      { inputTape := 0
        workTapes := Fin.elim0
        output := some (symbol.getD false && (if different then bit else true))
        state := none }
      Empty.elim Empty.elim

private def running (input : Bool) : FiniteCfg 0 Bool Unit :=
  ⟨[input], some (), 1, Fin.elim0, []⟩

private def stopped (input output : Bool) : FiniteCfg 0 Bool Unit :=
  ⟨[input], none, 1, Fin.elim0, [output]⟩

private theorem viewCoinStep_running (different input bit : Bool) :
    (machine different).viewCoinStep (running input) bit =
      stopped input (input && (if different then bit else true)) := by
  cases different <;> cases input <;> cases bit <;>
    simp [MultiTapePTM.viewCoinStep, running, FiniteCfg.inputSymbol_eq_getD, machine,
      MultiTapePTM.withCoin, MultiTapeMachine.toTM, MultiTapeMachine.Action.emptyOracleEquiv,
      FiniteCfg.step, FiniteCfg.summarizeOutput, MultiTapeNTM.outputClass, stopped, funext_iff]

private theorem stopped_injective (input : Bool) : Function.Injective (stopped input) := by
  intro a b h
  have ho := congrArg FiniteCfg.output h
  simpa only [stopped, List.cons.injEq, and_true] using ho

private theorem fits_three (v : FiniteCfg 0 Bool Unit) (hinput : v.input.length = 1) :
    Fits 3 (registers v) := by
  intro i
  cases i with
  | inputPos =>
    change v.inputPos.val < 3
    simpa only [hinput] using v.inputPos.isLt
  | control =>
    have h : stateCode v.state < 2 := (Fintype.equivFin (Option Unit) v.state).isLt
    exact h.trans_le (by decide)
  | output => exact outputCode_lt _
  | head i => exact Fin.elim0 i
  | left i => exact Fin.elim0 i
  | right i => exact Fin.elim0 i

private noncomputable def source : ℕ := vertexID 3 (running true)

private noncomputable def target : ℕ := vertexID 3 (stopped true true)

private noncomputable def address : ℕ := 2 * (source * 27 + target)

-- Input symbols are absent from the compact IDs, so all runs use the same table address.
example (input : Bool) : vertexID 3 (running input) = source ∧
    vertexID 3 (stopped input true) = target := ⟨rfl, rfl⟩

private theorem count_input (different input : Bool) :
    coinCountWithSymbol (machine different) 3 1 source target
      [input][queryIndex (k := 0) 3 source]? =
        if input then (if different then 1 else 2) else 0 := by
  change coinCountWithSymbol (machine different) 3 1
    (vertexID 3 (running input)) (vertexID 3 (stopped input true))
    [input][queryIndex (k := 0) 3 (vertexID 3 (running input))]? = _
  have hcoin (bit : Bool) := edgeWithSymbol_withCoin_iff (machine different)
    (a := running input) (b := stopped input true) rfl
    (by simp [running, MultiTapeNTM.outputClass])
    (by simp [stopped, MultiTapeNTM.outputClass])
    (fits_three _ rfl) (fits_three _ rfl) bit
  simp only [viewCoinStep_running, (stopped_injective input).eq_iff] at hcoin
  have hfalse := hcoin false
  have htrue := hcoin true
  rw [coinCountWithSymbol]
  cases input <;> cases different <;> simp_all [running]

private theorem table_bits (different input : Bool) :
    (coinTable (machine different) 1 [input]).getD address false = input ∧
      (coinTable (machine different) 1 [input]).getD (address + 1) false =
        (input && !different) := by
  have hbox : vertexBound (k := 0) 3 = 27 := by decide
  have hu : source < vertexBound (k := 0) 3 := vertexID_lt (fits_three (running true) rfl)
  have hv : target < vertexBound (k := 0) 3 := vertexID_lt (fits_three (stopped true true) rfl)
  let u : Fin (vertexBound (k := 0) (radix 1 [input].length)) := ⟨source, hu⟩
  let v : Fin (vertexBound (k := 0) (radix 1 [input].length)) := ⟨target, hv⟩
  have h0 := getD_coinTable (machine different) 1 [input] u v 0
  have h1 := getD_coinTable (machine different) 1 [input] u v 1
  change (coinTable (machine different) 1 [input]).getD
    (2 * (source * vertexBound (k := 0) 3 + target) + 0) false =
      decide (0 < coinCountWithSymbol (machine different) 3 1 source target
        [input][queryIndex (k := 0) 3 source]?) at h0
  change (coinTable (machine different) 1 [input]).getD
    (2 * (source * vertexBound (k := 0) 3 + target) + 1) false =
      decide (1 < coinCountWithSymbol (machine different) 3 1 source target
        [input][queryIndex (k := 0) 3 source]?) at h1
  rw [hbox, count_input] at h0 h1
  cases input <;> cases different <;> simp_all [address]

private theorem initialized_run (different input : Bool) :
    ∃ regs out, (coinTableProgram (machine different) 1).ReachesOut (frame [input])
      ((coinTableProgram (machine different) 1).Active 27)
      (0, [0, 0, 0, 0]) (22, regs) out ∧
      out.length = 1458 ∧ out.getD address false = input ∧
      out.getD (address + 1) false = (input && !different) := by
  obtain ⟨regs, hr, _⟩ := reachesOut_coinTableProgram (machine different) 1 [input]
    (S := 27) (by simp) (by change 27 ≤ 27; rfl) (by decide)
  exact ⟨regs, coinTable (machine different) 1 [input], hr,
    by rw [length_coinTable]; change 2 * 27 ^ 2 = 1458; norm_num, (table_bits different input).1,
    (table_bits different input).2⟩

-- One accepting coin, with all parameters counted or enumerated from zero registers.
example : ∃ regs out, (coinTableProgram (machine true) 1).ReachesOut (frame [true])
    ((coinTableProgram (machine true) 1).Active 27)
    (0, [0, 0, 0, 0]) (22, regs) out ∧
    out.length = 1458 ∧ out.getD address false = true ∧
    out.getD (address + 1) false = false := initialized_run true true

-- Changing just the original input bit changes the same table entry to count zero.
example : ∃ regs out, (coinTableProgram (machine true) 1).ReachesOut (frame [false])
    ((coinTableProgram (machine true) 1).Active 27)
    (0, [0, 0, 0, 0]) (22, regs) out ∧
    out.length = 1458 ∧ out.getD address false = false ∧
    out.getD (address + 1) false = false := initialized_run true false

-- The same entry records two when the two coin successors coincide.
example : ∃ regs out, (coinTableProgram (machine false) 1).ReachesOut (frame [true])
    ((coinTableProgram (machine false) 1).Active 27)
    (0, [0, 0, 0, 0]) (22, regs) out ∧
    out.length = 1458 ∧ out.getD address false = true ∧
    out.getD (address + 1) false = true := initialized_run false true

-- Empty original input still counts its marker correctly and emits all 8 × 8 entries.
example : ∃ regs out, (coinTableProgram (machine true) 1).ReachesOut (frame [])
    ((coinTableProgram (machine true) 1).Active 8)
    (0, [0, 0, 0, 0]) (22, regs) out ∧ out.length = 128 := by
  obtain ⟨regs, hr, _⟩ := reachesOut_coinTableProgram (machine true) 1 []
    (S := 8) (by decide) (by decide) (by decide)
  exact ⟨regs, _, hr, by rw [length_coinTable]; decide⟩

-- Exponent zero produces a one-entry ambient box, with the count scratch still bounded by two.
example : ∃ regs out, (coinTableProgram (machine true) 0).ReachesOut (frame [])
    ((coinTableProgram (machine true) 0).Active 2)
    (0, [0, 0, 0, 0]) (22, regs) out ∧ out.length = 2 := by
  obtain ⟨regs, hr, _⟩ := reachesOut_coinTableProgram (machine true) 0 []
    (S := 2) (by decide) (by decide) (by decide)
  exact ⟨regs, _, hr, by rw [length_coinTable]; decide⟩

-- The final label is a halt; the entire counted table is emitted before reaching it.
example (different : Bool) : (coinTableProgram (machine different) 1).instr 22 = halt [] := rfl

end ComplexityTests.FairCoinTable
