/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.DyadicExecution
import Mathlib.Data.List.GetD

/-!
# Actual selected-prime runs at the natural subcubic allowance

The original zero, positive and negative constant inputs discharge all premises and run the
existing real program from State.init. Prefix, charged halt, literal verdict, natural time and
original-input frame use the same final state. These are kernel clients on large admitted
geometry, not enormous interpreter fixtures or supplied executions.
-/

namespace ComplexityTests.WordRAMCallableDyadicExecution

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
open ParameterChoice

private def data (n : ℕ) (z : ℤ) : List ℤ := List.replicate (3 * (n * n)) z
private def width (n : ℕ) : ℕ := 246659 * Nat.clog 2 (n + 2)
private def words (n p : ℕ) (z : ℤ) : List ℕ :=
  PreparationInput.input n (window n) (groups n) p (data n z)

private theorem pair_lt {n : ℕ} (a b : Fin n) : pairIndex (a, b) < n * n := by
  simpa [pairIndex, Nat.mul_comm, Nat.add_comm] using (finProdFinEquiv (a, b)).isLt

private theorem triangle_iff {n : ℕ} (hn : 0 < n) (z : ℤ) :
    HasZeroTriangle (fun _ _ : Fin n => z) (fun _ _ => z) (fun _ _ => z) ↔ z = 0 := by
  constructor
  · rintro ⟨a, b, c, h⟩
    dsimp only [weightSum] at h
    omega
  · intro hz
    exact ⟨⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩, by simp [hz]⟩

private def TimedConstant (z : ℤ) (answer : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ^ 1296 ≤ N ∧ ∀ n ≥ N,
    ∃ p y t,
      IsSelectedPrime (fun _ _ : Fin n => z) (fun _ _ => z) (fun _ _ => z) (window n) p ∧
      InputFits (width n) (words n p z) ∧
      Runs (width n) (entryProgram.program Reg.found) (State.init (words n p z))
        ⟨entryProgram.size, y⟩ t ∧
      Executes (width n) (entryProgram.program Reg.found) (State.init (words n p z))
        answer (t + 1) ∧
      t + 1 ≤ dyadicTime n 1 ∧ (dyadicTime n 1 : ℝ) ≤ C * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) ∧
      y.regs Reg.found = answer ∧
      ∀ q < workspaceBase n, y.mem q = (Data.init (words n p z) : Data 640).mem q

-- Permit the existing concrete fast-threshold numeral during this original-input client.
set_option exponentiation.threshold 1296 in
private theorem timed_constant (z : ℤ) (hz : z.natAbs ≤ 1) :
    TimedConstant z (if z = 0 then 1 else 0) := by
  obtain ⟨C, hC, N, hN, hrun⟩ := exists_dyadic_runs_threshold (by decide : 1 ≤ (1 : ℕ))
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hnN
  have hn : 0 < n := (Nat.two_pow_pos 1296).trans_le (hN.trans hnN)
  have hf := (blocks_pos_iff n).mpr (hN.trans hnN)
  obtain ⟨p, hp⟩ := exists_isSelectedPrime (fun _ _ : Fin n => z)
    (fun _ _ => z) (fun _ _ => z) (window n) (window_ge_sixteen hf)
  have hab (a b : Fin n) : (data n z).getD (pairIndex (a, b)) 0 = z :=
    List.getD_replicate z (by have h := pair_lt a b; omega)
  have hbc (a b : Fin n) : (data n z).getD (n * n + pairIndex (a, b)) 0 = z :=
    List.getD_replicate z (by have h := pair_lt a b; omega)
  have hac (a b : Fin n) : (data n z).getD (2 * (n * n) + pairIndex (a, b)) 0 = z :=
    List.getD_replicate z (by have h := pair_lt a b; omega)
  have hp' : IsSelectedPrime
      (fun a b : Fin n => (data n z).getD (pairIndex (a, b)) 0)
      (fun a b => (data n z).getD (n * n + pairIndex (a, b)) 0)
      (fun a b => (data n z).getD (2 * (n * n) + pairIndex (a, b)) 0) (window n) p := by
    simpa only [hab, hbc, hac] using hp
  have hlen : (data n z).length = 3 * (n * n) := by simp only [data, List.length_replicate]
  have hv : ∀ v ∈ data n z, v.natAbs ≤ 1 := by
    intro v hv
    have heq : v = z := (List.mem_replicate.mp hv).2
    simpa only [heq] using hz
  obtain ⟨hi, y, t, hr, he, ht, htime, hbounded, hflag, hiff, hwitness, hframe⟩ :=
    hrun n hnN 1 (data n z) p (width n) hlen hv (by simp) hp' (by exact le_rfl)
  have hiff' : y.regs Reg.found = 1 ↔ z = 0 := by
    have ht : HasZeroTriangle
        (fun a b : Fin n => (data n z).getD (pairIndex (a, b)) 0)
        (fun a b => (data n z).getD (n * n + pairIndex (a, b)) 0)
        (fun a b => (data n z).getD (2 * (n * n) + pairIndex (a, b)) 0) ↔ z = 0 := by
      simpa only [hab, hbc, hac] using triangle_iff hn z
    exact hiff.trans ht
  have hanswer : y.regs Reg.found = (if z = 0 then 1 else 0) := by
    split_ifs with hz0
    · exact hiff'.mpr hz0
    · exact hflag.resolve_right (fun h => hz0 (hiff'.mp h))
  exact ⟨p, y, t, hp, hi, hr, by simpa only [words, hanswer] using he,
    ht, htime, hanswer, hframe⟩

example : TimedConstant 0 1 := by simpa using timed_constant 0 (by decide)
example : TimedConstant 1 0 := by simpa using timed_constant 1 (by decide)
example : TimedConstant (-1) 0 := by simpa using timed_constant (-1) (by decide)

end ComplexityTests.WordRAMCallableDyadicExecution
