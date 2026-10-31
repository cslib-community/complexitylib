/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.ReadInput
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationReader

/-!
# Fair-coin count blocks on actual framed inputs

The shared reader obtains true, false, and absent symbols from actual framed words. A concrete
zero-work-tape machine then makes its output depend on both the input symbol and its coin. With
the same source and target compact IDs, changing the original input bit changes the block's
answer from one to zero. Making both coin branches coincide changes one to two. All representation
and runtime register bounds in these runs are discharged.
-/

namespace ComplexityTests.FairCoinInput

open Cslib.Turing Turing MultiTapeTM CounterProgram Instr Expr
open MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph

private def symbolProgram : CounterProgram where
  code := readSymbolCode 0 2 5 (reg 0) (reg 1) ++ [halt []]
  registers := 3

-- The first original true bit is read from its data cell, not from a frame marker.
example : symbolProgram.ReachesOut (frame [true, false]) (symbolProgram.Active 2)
    (0, [2, 0, 0]) (5, [2, 0, 2]) [] := by
  have hcode : symbolProgram.CodeAt 0 (readSymbolCode 0 2 5 (reg 0) (reg 1)) :=
    codeAt_of_code_eq (pre := []) (post := [halt []]) rfl
  simpa [symbolCode] using reachesOut_readSymbolCode (w := [true, false])
    (regs := [2, 0, 0]) hcode rfl (by simp)

-- The second data cell is false, whose ternary code is one.
example : symbolProgram.ReachesOut (frame [true, false]) (symbolProgram.Active 2)
    (0, [2, 1, 0]) (5, [2, 1, 1]) [] := by
  have hcode : symbolProgram.CodeAt 0 (readSymbolCode 0 2 5 (reg 0) (reg 1)) :=
    codeAt_of_code_eq (pre := []) (post := [halt []]) rfl
  simpa [symbolCode] using reachesOut_readSymbolCode (w := [true, false])
    (regs := [2, 1, 0]) hcode rfl (by simp)

-- An index at the original length returns no symbol, despite the trailing frame marker.
example : symbolProgram.ReachesOut (frame [true, false]) (symbolProgram.Active 2)
    (0, [2, 2, 1]) (5, [2, 2, 0]) [] := by
  have hcode : symbolProgram.CodeAt 0 (readSymbolCode 0 2 5 (reg 0) (reg 1)) :=
    codeAt_of_code_eq (pre := []) (post := [halt []]) rfl
  simpa [symbolCode] using reachesOut_readSymbolCode (w := [true, false])
    (regs := [2, 2, 1]) hcode rfl (by simp)

-- Empty original input also returns no symbol and overwrites stale scratch data.
example : symbolProgram.ReachesOut (frame []) (symbolProgram.Active 2)
    (0, [0, 0, 2]) (5, [0, 0, 0]) [] := by
  have hcode : symbolProgram.CodeAt 0 (readSymbolCode 0 2 5 (reg 0) (reg 1)) :=
    codeAt_of_code_eq (pre := []) (post := [halt []]) rfl
  simpa [symbolCode] using reachesOut_readSymbolCode (w := [])
    (regs := [0, 0, 2]) hcode rfl (by simp)

/-- A true input symbol enables acceptance. When `different` is true, only the true coin accepts;
otherwise both coins accept. A false or absent input symbol always emits false. -/
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

private theorem count_input (different input : Bool) :
    coinCountWithSymbol (machine different) 3 1
      (vertexID 3 (running input)) (vertexID 3 (stopped input true))
      [input][queryIndex (k := 0) 3 (vertexID 3 (running input))]? =
        if input then (if different then 1 else 2) else 0 := by
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

private noncomputable def source : ℕ := vertexID 3 (running true)

private noncomputable def target : ℕ := vertexID 3 (stopped true true)

-- The original bit is not part of the compact ID; all runs below use these same two IDs.
example (input : Bool) : vertexID 3 (running input) = source ∧
    vertexID 3 (stopped input true) = target := ⟨rfl, rfl⟩

private theorem count_program (different input : Bool) :
    (coinCountProgram (machine different) 1).ReachesOut (frame [input])
      ((coinCountProgram (machine different) 1).Active 27)
      (0, [1, source, target, 0])
      (6, [1, source, target, if input then (if different then 1 else 2) else 0]) [] := by
  have hbox : vertexBound (k := 0) 3 = 27 := by decide
  have hu : source < 27 := by
    simpa only [source, hbox] using vertexID_lt (fits_three (running true) rfl)
  have hv : target < 27 := by
    simpa only [target, hbox] using vertexID_lt (fits_three (stopped true true) rfl)
  have hbound : ∀ r ∈ [1, source, target, 0], r ≤ 27 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hr := reachesOut_coinCountProgram (machine different) (D := 1) (w := [input])
    hbound (by decide : 2 ≤ 27)
  have hc : coinCountWithSymbol (machine different) (radix 1 [input].length) [input].length
      source target [input][queryIndex (k := 0) (radix 1 [input].length) source]? =
      if input then (if different then 1 else 2) else 0 := count_input different input
  rw [hc] at hr
  simpa only [List.length_singleton] using hr

-- One accepting coin on the true input: the actual framed input reaches a count of one.
example : (coinCountProgram (machine true) 1).ReachesOut (frame [true])
    ((coinCountProgram (machine true) 1).Active 27)
    (0, [1, source, target, 0]) (6, [1, source, target, 1]) [] := count_program true true

-- Changing only that input bit to false changes the count to zero.
example : (coinCountProgram (machine true) 1).ReachesOut (frame [false])
    ((coinCountProgram (machine true) 1).Active 27)
    (0, [1, source, target, 0]) (6, [1, source, target, 0]) [] := count_program true false

-- Coincident accepting successors retain multiplicity two in the register result.
example : (coinCountProgram (machine false) 1).ReachesOut (frame [true])
    ((coinCountProgram (machine false) 1).Active 27)
    (0, [1, source, target, 0]) (6, [1, source, target, 2]) [] := count_program false true

-- The returned label is an actual halt of the concrete program.
example (different : Bool) : (coinCountProgram (machine different) 1).instr 6 = halt [] := rfl

end ComplexityTests.FairCoinInput
