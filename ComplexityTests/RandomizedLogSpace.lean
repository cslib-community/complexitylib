/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.Amplification
import Complexity.Computability.Complexity.Classes.LogSpace.USTCON

/-!
# Tests for randomized logarithmic space
-/

namespace ComplexityTests.RandomizedLogSpace

open Cslib.Complexity

-- Undirected connectivity, in `L` by Reingold, is in `RL` and in `BPL`.
example : USTCON ∈ RL encUSTCON := L_subset_RL USTCON_mem_L

example : USTCON ∈ BPL encUSTCON := L_subset_BPL USTCON_mem_L

-- Going through `RL` recovers `USTCON ∈ NL`.
example : USTCON ∈ NL encUSTCON := RL_subset_NL (L_subset_RL USTCON_mem_L)

section HaltingTime

open Cslib.Turing Turing

/-- The single action of `haltAtOnce`: halt without moving or writing. -/
private def haltAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

/-- A machine without work tapes that halts at its first step. -/
private def haltAtOnce : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = haltAction

/-- Every computation path of `haltAtOnce` with at least one step ends halted. -/
private theorem haltAtOnce_runsInTime (input : List Bool) : haltAtOnce.RunsInTime input 1 := by
  intro p hp
  have hlen : 1 ≤ p.toRunPath.length := by
    simpa [MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time] using hp
  have hstep := p.toRunPath.step ⟨0, hlen⟩
  have hhead : p.toRunPath ⟨0, by omega⟩ = haltAtOnce.initCfg input := p.head_eq
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.zero_add] at hstep
  change haltAtOnce.Step _ _ at hstep
  rw [hhead] at hstep
  obtain ⟨action, rfl, h1⟩ := hstep
  have hhalt : (p.toRunPath ⟨1, by omega⟩).Halted := by rw [h1]; rfl
  rw [MultiTapeNTM.RunPath.last_eq_of_halted _ _ hhalt]
  exact hhalt

-- The derived clock on a concrete machine: zero work tapes use no space, so the view bound
-- with `s = 0` is a halting time.
example (input : List Bool) :
    haltAtOnce.RunsInTime input
      (2 ^ (2 * MultiTapeNTM.coreLengthBound 0 Unit input.length 0 + 1)) :=
  MultiTapeNTM.runsInTime_of_runsInSpace (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    (haltAtOnce_runsInTime input)

-- The polynomial clock applies with a single exponent for all inputs.
example : ∃ d, ∀ input : List Bool,
    haltAtOnce.RunsInTime input (2 * (2 * (input.length + 1)) ^ d) := by
  obtain ⟨d, hd⟩ := MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log haltAtOnce 0
  exact ⟨d, fun input => hd (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    (haltAtOnce_runsInTime input)⟩

end HaltingTime

section Amplification

open Cslib Turing MultiTapeMachine

/-- A machine without work tapes that outputs its first coin and halts. -/
private def coinFlip : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit :=
    .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
      Empty.elim Empty.elim

/-- After one coin, `coinFlip` has halted with that coin as its output. -/
private theorem stepCoins_coinFlip (input : List Bool) (bit : Bool) :
    coinFlip.stepCoins [bit] (coinFlip.toNTM.initCfg input) =
      ⟨none, 1, Fin.elim0, Fin.elim0, [bit]⟩ := by
  rw [MultiTapePTM.initCfg_toNTM, ← MultiTapePTM.tapes_runClosedConfigFromCoins]
  exact Cfg.ext_zero_tapes rfl rfl rfl

private theorem runsInTime_coinFlip (input : List Bool) : coinFlip.toNTM.RunsInTime input 1 := by
  refine (MultiTapePTM.runsInTime_toNTM_iff _).mpr fun final hfinal => ?_
  rw [MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins] at hfinal
  obtain ⟨coins, hcoins, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  obtain ⟨bit, rfl⟩ : ∃ bit, coins = [bit] := by
    rw [BitString.mem_support_uniformList_iff, List.length_eq_one_iff] at hcoins
    exact hcoins
  rw [MultiTapePTM.tapes_runClosedConfigFromCoins]
  exact congrArg Cfg.state (stepCoins_coinFlip input bit)

-- `coinFlip` accepts on one of the two coin strings of length one.
private theorem acceptCoins_coinFlip (input : List Bool) : coinFlip.acceptCoins input 1 = 1 := by
  rw [MultiTapePTM.acceptCoins, Finset.card_eq_one]
  refine ⟨fun _ => true, Finset.ext fun w => ?_⟩
  have hw : List.ofFn w = [w 0] := by simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hw,
    stepCoins_coinFlip]
  refine ⟨fun h => funext fun i => ?_, fun h => ?_⟩
  · rw [Fin.fin_one_eq_zero i]
    simpa using h
  · subst h
    simp

-- Running `coinFlip` twice rejects only when both coins are `false`: three quarters of the
-- `2 ^ (n + 4)` coin strings are accepted.
example (input : List Bool) :
    (coinFlip.orElse coinFlip).acceptCoins input (1 + (input.length + 2 + 1)) =
      12 * 2 ^ input.length := by
  have h := MultiTapePTM.acceptCoins_orElse coinFlip coinFlip (runsInTime_coinFlip input)
    (runsInTime_coinFlip input)
  have hle := (coinFlip.orElse coinFlip).acceptCoins_le input (1 + (input.length + 2 + 1))
  rw [acceptCoins_coinFlip, show 1 + (input.length + 2 + 1) = input.length + 4 by omega,
    pow_add] at *
  norm_num at h hle
  omega

-- Every language is in `RL` through `coinFlip`, which accepts with probability exactly `1/2`;
-- amplification then places it in `BPL`.
example (enc : ℕ ↪ List Bool) : (Set.univ : Set ℕ) ∈ Cslib.Complexity.RL enc :=
  ⟨0, Unit, inferInstance, coinFlip, 0, fun a =>
    ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, 1, runsInTime_coinFlip _,
      fun _ => by rw [acceptCoins_coinFlip]; rfl, fun ha => absurd trivial ha⟩⟩

example (enc : ℕ ↪ List Bool) : (Set.univ : Set ℕ) ∈ Cslib.Complexity.BPL enc :=
  Cslib.Complexity.RL_subset_BPL
    ⟨0, Unit, inferInstance, coinFlip, 0, fun a =>
      ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, 1, runsInTime_coinFlip _,
        fun _ => by rw [acceptCoins_coinFlip]; rfl, fun ha => absurd trivial ha⟩⟩

-- With error at most `1/8`, through the amplification characterization.
example (enc : ℕ ↪ List Bool) : ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (M : MultiTapePTM k Bool State) (c : ℕ), ∀ a,
      M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
      ∃ t, M.toNTM.RunsInTime (enc a) t ∧ (7 * 2 ^ t ≤ 8 * M.acceptCoins (enc a) t) := by
  obtain ⟨k, State, hfin, M, c, hM⟩ :=
    (Cslib.Complexity.mem_RL_iff_error_le (A := (Set.univ : Set ℕ)) (enc := enc) (r := 3)
      (by norm_num)).mp
      ⟨0, Unit, inferInstance, coinFlip, 0, fun a =>
        ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, 1, runsInTime_coinFlip _,
          fun _ => by rw [acceptCoins_coinFlip]; rfl, fun ha => absurd trivial ha⟩⟩
  refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
  obtain ⟨t, ht, hmem, -⟩ := (hM a).2
  exact ⟨t, ht, by simpa using hmem trivial⟩

end Amplification

end ComplexityTests.RandomizedLogSpace
