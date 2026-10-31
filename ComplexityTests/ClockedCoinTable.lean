/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ClockedTable

/-!
# Initialized clocked coin-table regressions

An empty-input, zero-work-tape machine gives a small nonzero table: three clock layers of an
eight-ID base box, with 1152 output bits. The actual zero-initialized writer emits one or two at
the same pair from clock one to clock two, depending on whether the coin successors coincide.
Off-clock pairs and terminal rows give zero. The decoded bits recover the semantic matrix entry.
The ordinary writer is definitionally the same 23-label program after extracting the shared code.
-/

namespace ComplexityTests.ClockedCoinTable

open Cslib.Turing Turing MultiTapeTM CounterProgram Instr Expr Matrix
open MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph

private def machine (different : Bool) : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit :=
    .step
      { inputTape := 0
        workTapes := Fin.elim0
        output := some (if different then bit else true)
        state := none }
      Empty.elim Empty.elim

private def running : FiniteCfg 0 Bool Unit := ⟨[], some (), 1, Fin.elim0, []⟩

private def stopped (output : Bool) : FiniteCfg 0 Bool Unit :=
  ⟨[], none, 1, Fin.elim0, [output]⟩

private theorem viewCoinStep_running (different bit : Bool) :
    (machine different).viewCoinStep running bit = stopped (if different then bit else true) := by
  cases different <;> cases bit <;>
    simp [MultiTapePTM.viewCoinStep, running, machine, MultiTapePTM.withCoin,
      MultiTapeMachine.toTM, MultiTapeMachine.Action.emptyOracleEquiv,
      FiniteCfg.step, FiniteCfg.summarizeOutput, MultiTapeNTM.outputClass, stopped, funext_iff]

private theorem stopped_injective : Function.Injective stopped := by
  intro a b h
  have ho := congrArg FiniteCfg.output h
  simpa only [stopped, List.cons.injEq, and_true] using ho

private theorem running_fits : Fits 2 (registers running) := by
  intro i
  cases i with
  | inputPos => decide
  | control => exact (Fintype.equivFin (Option Unit) (some ())).isLt
  | output => decide
  | head i => exact Fin.elim0 i
  | left i => exact Fin.elim0 i
  | right i => exact Fin.elim0 i

private theorem stopped_fits : Fits 2 (registers (stopped true)) := by
  intro i
  cases i with
  | inputPos => decide
  | control => exact (Fintype.equivFin (Option Unit) none).isLt
  | output => decide
  | head i => exact Fin.elim0 i
  | left i => exact Fin.elim0 i
  | right i => exact Fin.elim0 i

private noncomputable def source : Fin 8 := ⟨vertexID 2 running, vertexID_lt running_fits⟩
private noncomputable def target : Fin 8 := ⟨vertexID 2 (stopped true), vertexID_lt stopped_fits⟩

private noncomputable def clockSource : Fin 24 :=
  ⟨8 + source.val, by have h := source.isLt; omega⟩

private noncomputable def clockTarget : Fin 24 :=
  ⟨16 + target.val, by have h := target.isLt; omega⟩

private noncomputable def address : ℕ := 2 * (clockSource.val * 24 + clockTarget.val)

private theorem count_base (different : Bool) :
    coinCountWithSymbol (machine different) 2 0 source target none =
      if different then 1 else 2 := by
  have hcoin (bit : Bool) := edgeWithSymbol_withCoin_iff (machine different)
    (a := running) (b := stopped true) rfl
    (by simp [running, MultiTapeNTM.outputClass])
    (by simp [stopped, MultiTapeNTM.outputClass]) running_fits stopped_fits bit
  simp only [viewCoinStep_running, stopped_injective.eq_iff] at hcoin
  have hfalse := hcoin false
  have htrue := hcoin true
  change edgeWithSymbol ((machine different).withCoin false).toTM.toMultiTapeNTM
    2 0 source target none = true ↔ _ at hfalse
  change edgeWithSymbol ((machine different).withCoin true).toTM.toMultiTapeNTM
    2 0 source target none = true ↔ _ at htrue
  rw [coinCountWithSymbol]
  cases different <;> simp_all

private theorem count_clocked (different : Bool) :
    clockedCoinCountWithSymbol (machine different) 2 0 clockSource clockTarget none =
      if different then 1 else 2 := by
  have hs := source.isLt
  have ht := target.isLt
  have hsdiv : clockSource.val / 8 = 1 := by dsimp only [clockSource]; omega
  have htdiv : clockTarget.val / 8 = 2 := by dsimp only [clockTarget]; omega
  have hsmod : clockSource.val % 8 = source := by dsimp only [clockSource]; omega
  have htmod : clockTarget.val % 8 = target := by dsimp only [clockTarget]; omega
  change (if clockSource.val / 8 + 1 = clockTarget.val / 8 then
    coinCountWithSymbol (machine different) 2 0 (clockSource.val % 8)
      (clockTarget.val % 8) none else 0) = _
  rw [hsdiv, htdiv, hsmod, htmod]
  simpa only [ite_true] using count_base different

private theorem table_bits (different : Bool) :
    (clockedCoinTable (machine different) 1 0 []).getD address false = true ∧
      (clockedCoinTable (machine different) 1 0 []).getD (address + 1) false = !different := by
  have h0 := getD_clockedCoinTable (machine different) 1 0 [] clockSource clockTarget 0
  have h1 := getD_clockedCoinTable (machine different) 1 0 [] clockSource clockTarget 1
  change (clockedCoinTable (machine different) 1 0 []).getD
    (2 * (clockSource.val * 24 + clockTarget.val) + 0) false =
      decide (0 < clockedCoinCountWithSymbol (machine different) 2 0
        clockSource clockTarget none) at h0
  change (clockedCoinTable (machine different) 1 0 []).getD
    (2 * (clockSource.val * 24 + clockTarget.val) + 1) false =
      decide (1 < clockedCoinCountWithSymbol (machine different) 2 0
        clockSource clockTarget none) at h1
  rw [count_clocked] at h0 h1
  cases different <;> simp_all [address]

private theorem initialized_run (different : Bool) :
    ∃ regs out, (clockedCoinTableProgram (machine different) 1 0).ReachesOut (frame [])
      ((clockedCoinTableProgram (machine different) 1 0).Active 24)
      (0, [0, 0, 0, 0]) (22, regs) out ∧
      out.length = 1152 ∧ out.getD address false = true ∧
      out.getD (address + 1) false = !different := by
  obtain ⟨regs, hr, _⟩ := reachesOut_clockedCoinTableProgram (machine different) 1 0 []
    (S := 24) (by decide) (by decide) (by decide)
  exact ⟨regs, _, hr, by rw [length_clockedCoinTable]; decide,
    (table_bits different).1, (table_bits different).2⟩

-- One accepting successor at a source in clock one, with no preloaded length or IDs.
example : ∃ regs out, (clockedCoinTableProgram (machine true) 1 0).ReachesOut (frame [])
    ((clockedCoinTableProgram (machine true) 1 0).Active 24)
    (0, [0, 0, 0, 0]) (22, regs) out ∧
    out.length = 1152 ∧ out.getD address false = true ∧
    out.getD (address + 1) false = false := initialized_run true

-- Coincident successors retain count two at the same clocked entry.
example : ∃ regs out, (clockedCoinTableProgram (machine false) 1 0).ReachesOut (frame [])
    ((clockedCoinTableProgram (machine false) 1 0).Active 24)
    (0, [0, 0, 0, 0]) (22, regs) out ∧
    out.length = 1152 ∧ out.getD address false = true ∧
    out.getD (address + 1) false = true := initialized_run false

-- Same-clock targets are zero even when the underlying base transition has nonzero count.
example (different : Bool) (b : Fin 2) :
    (clockedCoinTable (machine different) 1 0 []).getD
      (2 * (clockSource.val * 24 + (8 + target.val)) + b.val) false = false := by
  let v : Fin 24 := ⟨8 + target.val, by have h := target.isLt; omega⟩
  have h := getD_clockedCoinTable (machine different) 1 0 [] clockSource v b
  have hs := source.isLt
  have ht := target.isLt
  have hclock : clockSource.val / 8 + 1 ≠ v.val / 8 := by
    dsimp only [clockSource, v]
    omega
  change (clockedCoinTable (machine different) 1 0 []).getD
    (2 * (clockSource.val * 24 + (8 + target.val)) + b.val) false =
      decide (b.val < if clockSource.val / 8 + 1 = v.val / 8 then _ else 0) at h
  simpa only [ite_eq_right hclock, Nat.not_lt_zero, decide_false] using h

-- Every column of the terminal row is zero, without assuming a valid target configuration.
example (different : Bool) (v : Fin 24) (b : Fin 2) :
    (clockedCoinTable (machine different) 1 0 []).getD
      (2 * (clockTarget.val * 24 + v.val) + b.val) false = false := by
  apply getD_clockedCoinTable_terminal
  change clockTarget.val / 8 = 2
  have h := target.isLt
  dsimp only [clockTarget]
  omega

-- The actual initialized output decodes to the existing semantic matrix, in a field.
example (different : Bool) :
    finTimeLayer 2 (compactCoinMatrix (machine different) ℚ 2 []) clockSource clockTarget =
      if different then 1 / 2 else 1 := by
  have h := finTimeLayer_compactCoinMatrix_eq_clockedCoinTable
    (machine := machine different) (R := ℚ) 1 0 [] clockSource clockTarget
  change finTimeLayer 2 (compactCoinMatrix (machine different) ℚ 2 []) clockSource clockTarget =
    (((clockedCoinTable (machine different) 1 0 []).getD address false).toNat +
      ((clockedCoinTable (machine different) 1 0 []).getD (address + 1) false).toNat : ℕ) / 2 at h
  rw [h, (table_bits different).1, (table_bits different).2]
  cases different <;> norm_num

-- The local native reward predicate selects the accepting target at the terminal clock.
example :
    finTimeLayerReward 2 (compactAcceptVec (k := 0) (State := Unit) ℚ 2 0) clockTarget = 1 ∧
      clockedAccept (k := 0) (State := Unit) 2 0 2 clockTarget = true := by
  have ht := target.isLt
  have hdiv : clockTarget.val / 8 = 2 := by dsimp only [clockTarget]; omega
  have hmod : clockTarget.val % 8 = target := by dsimp only [clockTarget]; omega
  have hb : bad (k := 0) (State := Unit) 2 0 target = true :=
    (bad_vertexID stopped_fits).mpr ⟨rfl, rfl⟩
  have hc : clockedAccept (k := 0) (State := Unit) 2 0 2 clockTarget = true := by
    change (if clockTarget.val / 8 = 2 then
      bad (k := 0) (State := Unit) 2 0 (clockTarget.val % 8) else false) = true
    rw [hdiv, hmod]
    simpa only [ite_true] using hb
  have hr := finTimeLayerReward_eq_clockedAccept (k := 0) (State := Unit) (R := ℚ)
    2 0 2 clockTarget
  rw [hc] at hr
  exact ⟨by simpa using hr, hc⟩

-- The ordinary writer's instruction list and register count are definitionally preserved.
example {k : ℕ} {State : Type} [Fintype State] (M : MultiTapePTM k Bool State) (D : ℕ) :
    coinTableProgram M D =
      { code := Words.headerCode ++
          forCode 4 1 (vertexBoundExpr k (radixExpr D (reg 0))) 7 22 ++
          forCode 7 2 (vertexBoundExpr k (radixExpr D (reg 0))) 10 6 ++
          coinCountCode M D 10 16 ++
          [lt (const 0) (reg 3) 17 18, emit true 19, emit false 19,
            lt (const 1) (reg 3) 20 21, emit true 9, emit false 9, halt []]
        registers := 4 } := rfl

end ComplexityTests.ClockedCoinTable
