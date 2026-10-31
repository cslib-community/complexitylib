/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.CompactTimeLayer
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.Amplification
import Mathlib.Tactic.NormNum

/-!
# Compact ambient matrix and numeric clock regressions

A zero-work-tape machine outputs its coin and halts. Its actual acceptance probability is one
half. At radix two, the rejecting output tag overflows, so the ambient row has mass one half;
it is not falsely claimed stochastic. A radix-three ID with an invalid control tag has a zero
row and zero reward. Numeric time layers advance the clock and pay only at the terminal layer.
The always-accepting variant also discharges the complete BPL witness hypotheses.

The one-coin replay and halting proof follow the concrete fixture in `RandomizedLogSpace`.
-/

namespace ComplexityTests.CompactConfigurationMatrix

open Cslib Turing MultiTapeTM Matrix
open MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph

private def machine (always : Bool) : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit :=
    .step { inputTape := 0, workTapes := Fin.elim0, output := some (always || bit), state := none }
      Empty.elim Empty.elim

private theorem stepCoins (always : Bool) (input : List Bool) (bit : Bool) :
    (machine always).stepCoins [bit] ((machine always).toNTM.initCfg input) =
      ⟨none, 1, Fin.elim0, Fin.elim0, [always || bit]⟩ := by
  rw [MultiTapePTM.initCfg_toNTM, ← MultiTapePTM.tapes_runClosedConfigFromCoins]
  exact Cfg.ext_zero_tapes rfl rfl rfl

private theorem timeBound (always : Bool) (input : List Bool) :
    (machine always).toNTM.RunsInTime input 1 := by
  refine (MultiTapePTM.runsInTime_toNTM_iff _).mpr fun final hfinal => ?_
  rw [MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins] at hfinal
  obtain ⟨coins, hcoins, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  obtain ⟨bit, rfl⟩ : ∃ bit, coins = [bit] := by
    rw [BitString.mem_support_uniformList_iff, List.length_eq_one_iff] at hcoins
    exact hcoins
  rw [MultiTapePTM.tapes_runClosedConfigFromCoins]
  exact congrArg Cfg.state (stepCoins always input bit)

private theorem accept_one (input : List Bool) : (machine false).acceptCoins input 1 = 1 := by
  rw [MultiTapePTM.acceptCoins, Finset.card_eq_one]
  refine ⟨fun _ => true, Finset.ext fun w => ?_⟩
  have hw : List.ofFn w = [w 0] := by simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hw, stepCoins]
  refine ⟨fun h => funext fun i => ?_, fun h => ?_⟩
  · rw [Fin.fin_one_eq_zero i]
    simpa using h
  · subst h
    simp

private theorem accept_two (input : List Bool) : (machine true).acceptCoins input 1 = 2 := by
  have h (w : Fin 1 → Bool) :
      ((machine true).stepCoins (List.ofFn w) ((machine true).toNTM.initCfg input)).Halted ∧
        ((machine true).stepCoins (List.ofFn w) ((machine true).toNTM.initCfg input)).output =
          [true] := by
    have hw : List.ofFn w = [w 0] := by simp
    rw [hw, stepCoins]
    simp [Cfg.Halted]
  rw [MultiTapePTM.acceptCoins, Finset.filter_eq_self.mpr (fun w _ => h w)]
  simp

private theorem spaceBound (always : Bool) (input : List Bool) :
    (machine always).toNTM.RunsInSpace input (0 * (Nat.log2 input.length + 1)) := by
  rw [Nat.zero_mul]
  exact MultiTapeNTM.runsInSpace_zero_tapes _ _ _

-- The full (large) canonical box gives the actual probability without summing its rows by hand.
example (input : List Bool) :
    let B := radix (radixExponent Unit 0) input.length
    (compactCoinMatrix (machine false) ℚ B input ^ 1 *ᵥ
      compactAcceptVec (k := 0) (State := Unit) ℚ B input.length)
      (compactStart (machine false) 0 (spaceBound false input)) = 1 / 2 := by
  dsimp only
  rw [compactCoinMatrix_pow_accept, accept_one]
  norm_num

example (input : List Bool) :
    let B := radix (radixExponent Unit 0) input.length
    let N := vertexBound (k := 0) B
    finTimeLayerPotential 1 (compactCoinMatrix (machine false) ℝ B input)
      (compactAcceptVec (k := 0) (State := Unit) ℝ B input.length)
      ((timeLayerEquiv 1 N).symm (toLex (0, compactStart (machine false) 0
        (spaceBound false input)))) = 1 / 2 := by
  dsimp only
  rw [finTimeLayer_compactCoinMatrix_acceptance, accept_one]
  norm_num

private def malformedRegisters : Register 0 → ℕ
  | .control => 2
  | _ => 0

private theorem malformedFits : Fits 3 malformedRegisters := by
  intro i
  cases i <;> simp [malformedRegisters]

private noncomputable def malformed : Fin (vertexBound (k := 0) 3) :=
  ⟨Radix.pack 3 malformedRegisters, Radix.pack_lt (by decide) malformedFits⟩

private theorem malformed_read : readRegisters 3 malformed = malformedRegisters := by
  funext i
  exact Radix.component_pack (by decide) malformedFits i

private theorem malformed_invalid : valid (k := 0) (State := Unit) 3 0 malformed = false := by
  simp [valid, malformed_read, malformedRegisters]

-- This invalid source lies inside the ambient box; out-of-range guards alone would miss it.
example (v : Fin (vertexBound (k := 0) 3)) :
    compactCoinMatrix (machine false) ℚ 3 [] malformed v = 0 ∧
      compactAcceptVec (k := 0) (State := Unit) ℚ 3 0 malformed = 0 := by
  simp [compactCoinMatrix, coinCountWithSymbol, edgeWithSymbol, malformed_invalid,
    compactAcceptVec, bad]

private def initial : FiniteCfg 0 Bool Unit := ⟨[], some (), 1, Fin.elim0, []⟩
private def stopped (bit : Bool) : FiniteCfg 0 Bool Unit :=
  ⟨[], none, 1, Fin.elim0, [bit]⟩

private theorem step_initial (bit : Bool) :
    (machine false).viewCoinStep initial bit = stopped bit := by
  cases bit <;>
    simp [MultiTapePTM.viewCoinStep, machine, initial, stopped, MultiTapePTM.withCoin,
      MultiTapeMachine.toTM, MultiTapeMachine.Action.emptyOracleEquiv, FiniteCfg.step,
      FiniteCfg.summarizeOutput, MultiTapeNTM.outputClass, funext_iff]

private theorem initial_fits : Fits 2 (registers initial) := by
  intro i
  cases i with
  | inputPos => decide
  | control => exact (Fintype.equivFin (Option Unit) (some ())).isLt
  | output => decide
  | head i => exact Fin.elim0 i
  | left i => exact Fin.elim0 i
  | right i => exact Fin.elim0 i

private theorem accept_fits : Fits 2 (registers (stopped true)) := by
  intro i
  cases i with
  | inputPos => decide
  | control => exact (Fintype.equivFin (Option Unit) none).isLt
  | output => decide
  | head i => exact Fin.elim0 i
  | left i => exact Fin.elim0 i
  | right i => exact Fin.elim0 i

private noncomputable def source : Fin (vertexBound (k := 0) 2) :=
  ⟨vertexID 2 initial, vertexID_lt initial_fits⟩
private noncomputable def accepting : Fin (vertexBound (k := 0) 2) :=
  ⟨vertexID 2 (stopped true), vertexID_lt accept_fits⟩

private theorem accepting_entry :
    compactCoinMatrix (machine false) ℚ 2 [] source accepting = 1 / 2 := by
  have hcoin (bit : Bool) := edgeWithSymbol_withCoin_iff (machine false)
    (a := initial) (b := stopped true) rfl
    (by simp [initial, MultiTapeNTM.outputClass])
    (by simp [stopped, MultiTapeNTM.outputClass]) initial_fits accept_fits bit
  simp only [step_initial] at hcoin
  have ht := (hcoin true).mpr rfl
  have hf : edgeWithSymbol ((machine false).withCoin false).toTM.toMultiTapeNTM
      2 0 source accepting ([] : List Bool)[queryIndex (k := 0) 2 source]? = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have ho := congrArg FiniteCfg.output ((hcoin false).mp he)
    simp [stopped] at ho
  change edgeWithSymbol ((machine false).withCoin false).toTM.toMultiTapeNTM
    2 0 source accepting none = false at hf
  change edgeWithSymbol ((machine false).withCoin true).toTM.toMultiTapeNTM
    2 0 source accepting none = true at ht
  change ((edgeWithSymbol ((machine false).withCoin false).toTM.toMultiTapeNTM
      2 0 source accepting none).toNat +
    (edgeWithSymbol ((machine false).withCoin true).toTM.toMultiTapeNTM
      2 0 source accepting none).toNat : ℕ) / 2 = (1 / 2 : ℚ)
  rw [hf, ht]
  norm_num

private theorem other_entry (v : Fin (vertexBound (k := 0) 2)) (hv : v ≠ accepting) :
    compactCoinMatrix (machine false) ℚ 2 [] source v = 0 := by
  have hzero (bit : Bool) : edgeWithSymbol ((machine false).withCoin bit).toTM.toMultiTapeNTM
      2 0 source v ([] : List Bool)[queryIndex (k := 0) 2 source]? = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨next, hstep, _, hid, hfit⟩ := edge_sound initial_fits he
    have hn := (MultiTapePTM.viewStep_withCoin_iff (machine false) bit).mp hstep
    rw [step_initial] at hn
    subst next
    cases bit
    · have hbad := hfit .output
      norm_num [registers, stopped, outputCode] at hbad
    · exact hv (Fin.ext hid)
  simp only [List.getElem?_nil] at hzero
  simp [compactCoinMatrix, coinCountWithSymbol, hzero]

-- The false branch leaves radix two through output tag 2; exactly one half of the row remains.
example : (compactCoinMatrix (machine false) ℚ 2 [] *ᵥ 1) source = 1 / 2 := by
  classical
  rw [mulVec, dotProduct, Finset.sum_eq_single accepting]
  · simpa only [Pi.one_apply, mul_one] using accepting_entry
  · intro v _ hv
    rw [other_entry v hv, zero_mul]
  · simp

-- The finite clock layout is quotient/remainder arithmetic, including a terminal index.
example : timeLayerEquiv 2 8 (17 : Fin 24) = toLex ((2 : Fin 3), (1 : Fin 8)) := rfl

example :
    let P := compactCoinMatrix (machine false) ℚ 2 []
    let E := timeLayerEquiv 2 (vertexBound (k := 0) 2)
    finTimeLayer 2 P (E.symm (toLex (0, source))) (E.symm (toLex (1, accepting))) = 1 / 2 ∧
      finTimeLayer 2 P (E.symm (toLex (0, source))) (E.symm (toLex (0, accepting))) = 0 ∧
      finTimeLayer 2 P (E.symm (toLex (2, accepting))) (E.symm (toLex (0, source))) = 0 := by
  simp [finTimeLayer, timeLayer, accepting_entry]

example :
    let e := compactAcceptVec (k := 0) (State := Unit) ℚ 2 0
    let E := timeLayerEquiv 2 (vertexBound (k := 0) 2)
    finTimeLayerReward 2 e (E.symm (toLex (1, accepting))) = 0 ∧
      finTimeLayerReward 2 e (E.symm (toLex (2, accepting))) = 1 := by
  have hb := (bad_vertexID accept_fits).mpr (by simp [stopped])
  change bad (k := 0) (State := Unit) 2 0 (vertexID 2 (stopped true)) = true at hb
  simp [finTimeLayerReward, timeLayerReward, compactAcceptVec, accepting, hb]

-- A concrete always-accepting machine supplies all the class theorem's assumptions.
private theorem univ_mem_BPL :
    (Set.univ : Set (List Bool)) ∈ Complexity.BPL encBits := by
  refine ⟨0, Unit, inferInstance, machine true, 0, fun input =>
    ⟨spaceBound true input, 1, timeBound true input, fun _ => ?_, fun h => False.elim (h trivial)⟩⟩
  rw [accept_two]
  norm_num

example : ∃ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (e p : Fin N → ℝ) (x : Fin N),
    S.IsStrictUpperTriangular ∧ (1 - S)⁻¹ *ᵥ e = p ∧ p ∈ Set.Icc 0 1 ∧ 2 / 3 ≤ p x := by
  obtain ⟨k, State, _, M, c, d, hM⟩ := Complexity.exists_compactTimeLayer_of_mem_BPL univ_mem_BPL
  obtain ⟨hs, _, _, hS, _, _, _, _, hinv, hp, hyes, _⟩ := hM []
  exact ⟨_, _, _, _, _, hS, hinv, hp, hyes trivial⟩

end ComplexityTests.CompactConfigurationMatrix
