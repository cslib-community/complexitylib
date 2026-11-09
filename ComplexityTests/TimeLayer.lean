/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.TimeLayer
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Clocked matrix and machine examples

An absorbing two-state matrix has a self-loop at its running state and acceptance probability
`3/4` after two steps. Clocking removes every cycle and pays the reward only at final time.
The same example is realized by a concrete zero-work-tape fair-coin machine: false continues,
true outputs true and halts. Thus the finite-horizon theorem also applies when no uniform
halting bound exists. Zero horizons and the actual compact-count reader are checked too.
-/

namespace ComplexityTests.TimeLayer

open Matrix Finset

private def P : Matrix (Fin 2) (Fin 2) ℚ := ![![1 / 2, 1 / 2], ![0, 1]]
private def e : Fin 2 → ℚ := ![0, 1]

private theorem P_nonneg (x y : Fin 2) : 0 ≤ P x y := by
  fin_cases x <;> fin_cases y <;> norm_num [P]

private theorem P_row : P *ᵥ 1 ≤ 1 := by
  intro x
  fin_cases x <;> norm_num [P, mulVec, dotProduct, Fin.sum_univ_two]

private theorem e_bounds : e ∈ Set.Icc 0 1 := by
  constructor <;> intro x <;> fin_cases x <;> norm_num [e]

example : ¬ P.IsStrictUpperTriangular ∧ (timeLayer 2 P).IsStrictUpperTriangular := by
  refine ⟨fun h => ?_, timeLayer_isStrictUpperTriangular _ _⟩
  have h00 := h (i := 0) (j := 0) (by decide)
  norm_num [P] at h00

example : timeLayerPotential 2 P e (toLex (0, 0)) = 3 / 4 ∧
    timeLayerPotential 2 P e (toLex (1, 0)) = 1 / 2 ∧
    timeLayerPotential 2 P e (toLex (2, 0)) = 0 := by
  change (P ^ 2 *ᵥ e) 0 = 3 / 4 ∧ (P ^ 1 *ᵥ e) 0 = 1 / 2 ∧ (P ^ 0 *ᵥ e) 0 = 0
  rw [pow_two, ← mulVec_mulVec, pow_one, pow_zero]
  norm_num [P, e, mulVec, dotProduct, Fin.sum_univ_two]

-- An absorbing state still advances its clock; the reward is withheld until the last layer.
example : timeLayer 2 P (toLex (1, 1)) (toLex (2, 1)) = 1 ∧
    timeLayerReward 2 e (toLex (1, 1)) = 0 ∧ timeLayerReward 2 e (toLex (2, 1)) = 1 := by
  norm_num [timeLayer, timeLayerReward, P, e]

example : timeLayerPotential 2 P e ∈ Set.Icc 0 1 :=
  timeLayerPotential_mem_Icc P_nonneg P_row e_bounds 2

example : (1 - timeLayer 2 P) *ᵥ timeLayerPotential 2 P e = timeLayerReward 2 e ∧
    (1 - timeLayer 2 P)⁻¹ *ᵥ timeLayerReward 2 e = timeLayerPotential 2 P e :=
  ⟨one_sub_timeLayer_mulVec _ _ _, inv_one_sub_timeLayer_mulVec _ _ _⟩

example (x : Fin 2) (b : Lex (Fin 1 × Fin 2)) :
    timeLayer 0 P (toLex (0, x)) b = 0 := timeLayer_last 0 P x b

example (x : Fin 2) : timeLayerPotential 0 P e (toLex (0, x)) = e x := by
  rw [timeLayerPotential_zero, pow_zero, one_mulVec]

example : Fintype.card (Lex (Fin 3 × Fin 2)) = 6 := card_timeLayer (V := Fin 2) 2

open Cslib.Turing Turing MultiTapeTM

/-- False repeats the current running view; true accepts immediately. -/
private def machine : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit :=
    .step
      { inputTape := 0
        workTapes := Fin.elim0
        output := if bit then some true else none
        state := if bit then none else some () }
      Empty.elim Empty.elim

private def view (done : Bool) : FiniteCfg 0 Bool Unit :=
  ⟨[], if done then none else some (), 1, Fin.elim0, if done then [true] else []⟩

private theorem start_eq : machine.toNTM.initView [] = view false := by
  simp [MultiTapeNTM.initView, MultiTapePTM.toNTM, MultiTapePTM.branches,
    MultiTapeMachine.toNTM, FiniteCfg.init, machine, view, funext_iff]

private theorem step_view (done bit : Bool) :
    machine.viewCoinStep (view done) bit = view (done || bit) := by
  cases done <;> cases bit <;>
    simp [MultiTapePTM.viewCoinStep, machine, view, MultiTapePTM.withCoin,
      MultiTapeMachine.toTM, MultiTapeMachine.Action.emptyOracleEquiv, FiniteCfg.step,
      FiniteCfg.summarizeOutput, MultiTapeNTM.outputClass, funext_iff]

private theorem view_injective : Function.Injective view := by
  intro a b h
  cases a <;> cases b <;> simp_all [view]

open scoped Classical in
private noncomputable def views : Finset (FiniteCfg 0 Bool Unit) := univ.image view

open scoped Classical in
private noncomputable def vertex (done : Bool) : views :=
  ⟨view done, mem_image.mpr ⟨done, mem_univ _, rfl⟩⟩

private theorem closed : ∀ x ∈ views, ∀ bit, machine.viewCoinStep x bit ∈ views := by
  classical
  intro x hx bit
  obtain ⟨done, _, rfl⟩ := mem_image.mp hx
  rw [step_view]
  exact mem_image.mpr ⟨done || bit, mem_univ _, rfl⟩

private noncomputable def loopMatrix : Matrix views views ℚ :=
  (2 : ℚ)⁻¹ • machine.configMatrix ℚ views

private theorem loop_mulVec (g : views → ℚ) (done : Bool) :
    (loopMatrix *ᵥ g) (vertex done) = (g (vertex done) + g (vertex true)) / 2 := by
  classical
  have hcoin (bit : Bool) :
      (⟨machine.viewCoinStep (vertex done) bit, closed _ (vertex done).property bit⟩ : views) =
        vertex (done || bit) := Subtype.ext (step_view done bit)
  rw [loopMatrix, Matrix.smul_mulVec, Pi.smul_apply, MultiTapePTM.configMatrix,
    Matrix.coinStepMatrix_mulVec closed]
  simp only [hcoin, Fintype.sum_bool, Bool.or_false, Bool.or_true, smul_eq_mul]
  ring

open scoped Classical in
private theorem loop_probability :
    timeLayerPotential 2 loopMatrix (FiniteCfg.acceptVec ℚ views) (toLex (0, vertex false)) =
      3 / 4 := by
  classical
  rw [timeLayerPotential_zero, pow_two, ← mulVec_mulVec, loop_mulVec, loop_mulVec, loop_mulVec]
  norm_num [FiniteCfg.acceptVec, vertex, view]

-- This is the native machine's actual accepting-coin frequency, derived through the new bridge.
example : (machine.acceptCoins [] 2 : ℚ) / 2 ^ 2 = 3 / 4 := by
  classical
  have hinit : machine.toNTM.initView [] ∈ views := start_eq ▸ (vertex false).property
  have hstart : (⟨machine.toNTM.initView [], hinit⟩ : views) = vertex false :=
    Subtype.ext start_eq
  have h := machine.timeLayer_configMatrix_acceptance (R := ℚ) closed hinit 2
  rw [hstart] at h
  exact h.symm.trans loop_probability

-- The machine potential bound has all graph assumptions discharged on these actual two views.
open scoped Classical in
example : timeLayerPotential 2 loopMatrix (FiniteCfg.acceptVec ℚ views) ∈ Set.Icc 0 1 :=
  machine.timeLayer_configMatrix_potential_mem_Icc closed 2

private theorem reachable (v : FiniteCfg 0 Bool Unit) (hv : v ∈ views) :
    Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView []) v := by
  classical
  obtain ⟨done, _, rfl⟩ := mem_image.mp hv
  cases done
  · rw [start_eq]
  · refine Relation.ReflTransGen.tail .refl (MultiTapePTM.viewStep_toNTM_iff.mpr ⟨true, ?_⟩)
    rw [start_eq, step_view]
    rfl

open MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph

-- The same nonzero edge is read from actual compact IDs using the machine's zero-space bound.
example :
    let B := radix (radixExponent Unit 0) 0
    (coinCountWithSymbol machine B 0 (vertexID B (view false)) (vertexID B (view true))
      ([] : List Bool)[queryIndex (k := 0) B (vertexID B (view false))]? : ℚ) / 2 = 1 / 2 := by
  classical
  have hs : machine.toNTM.RunsInSpace [] (0 * (Nat.log2 ([] : List Bool).length + 1)) := by
    rw [Nat.zero_mul]
    exact MultiTapeNTM.runsInSpace_zero_tapes _ _ _
  have hentry : timeLayer 2 loopMatrix (toLex (0, vertex false)) (toLex (1, vertex true)) =
      1 / 2 := by
    norm_num [timeLayer, loopMatrix, MultiTapePTM.configMatrix, Matrix.coinStepMatrix,
      Fintype.sum_bool, vertex, step_view, view_injective.eq_iff]
  have h := timeLayer_configMatrix_eq_coinCountWithSymbol_of_reachable (R := ℚ)
    machine 0 hs reachable (T := 2) 0 1 (vertex false) (vertex true)
  change timeLayer 2 loopMatrix (toLex (0, vertex false)) (toLex (1, vertex true)) = _ at h
  rw [hentry] at h
  exact h.symm

end ComplexityTests.TimeLayer
