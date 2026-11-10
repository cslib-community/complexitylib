/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
import Mathlib.Data.List.GetD

/-!
# Fully admitted initialized calls to the box-backed fixed-prime controller

Both clients use actual header delivery, signed copies, computed source width, the memory-window
compiler and real solver from State.init, at valid positive thin geometry.
The constant257 negative input has modular false positives at prime257, but no original zero;
its unsuccessful records collectively receive no additive successful-scan allowance. These
kernel proofs do not evaluate the enormous catalogue or encoder through the interpreter.
-/

namespace CslibFrontierTests.WordRAMCallableBoxFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private def side : ℕ := D 9 ^ 18
private def weights (N : ℕ) (z : ℤ) : List ℤ := List.replicate (3 * (N * N)) z
private def width (N : ℕ) (z : ℤ) : ℕ :=
  CallableFixedPrime.inputWidth N (D 9) 1 257 (weights N z)

private theorem prime : 257 ∈ Nat.sqrtPrimeWindow (D 9) :=
  Nat.mem_sqrtPrimeWindow_iff_sq.mpr
    ⟨by norm_num, by norm_num [D], by norm_num [D]⟩

/-- Complete finite charge for the same positive initialized run, including header and halt. -/
private noncomputable def zeroCharge (N : ℕ) : ℝ :=
  24 * (N : ℝ) ^ 2 +
    24669 * (Nat.clog 2 (N + D 9 + 1 + 257 + CallableFixedPrime.rawTotal N (weights N 0) + 4)
      : ℕ) + 483 +
    3 * (690 * (N : ℝ) ^ 2 * D 9 +
      125829120 * ((189 * 1 + 1 : ℕ) : ℝ) ^ 2 * ((9 * 1 + 1 : ℕ) : ℝ) *
        (D 9 : ℝ) ^ (-(8 / 125 : ℝ)) * (N : ℝ) ^ 3 +
      (4 * (N : ℝ)) * ((5 * Nat.sqrt (D 9) + 8 * queryCap N (D 9) + 61 : ℕ) : ℝ) +
      (((42 * pieceSize (D 9) 1 + 28) * (0 + 1) + 7 : ℕ) : ℝ)) + 14

/-- The complete actual program returns one and an original witness on all-zero input. -/
private theorem initialized_zero (N : ℕ) (hgeo : D 9 ^ 18 ≤ N) : ∃ y : Data 640, ∃ t : ℕ,
    Runs (width N 0) (CallableFixedPrime.entryProgram.program CallableFixedPrime.Reg.found)
      (State.init (PreparationInput.input N (D 9) 1 257 (weights N 0)))
      ⟨CallableFixedPrime.entryProgram.size, y⟩ t ∧
    Executes (width N 0) (CallableFixedPrime.entryProgram.program CallableFixedPrime.Reg.found)
      (State.init (PreparationInput.input N (D 9) 1 257 (weights N 0))) 1 (t + 1) ∧
    y.regs CallableFixedPrime.Reg.found = 1 ∧ y.regs CallableFixedPrime.Reg.scans ≤ 1 ∧
    ((t + 1 : ℕ) : ℝ) ≤ zeroCharge N ∧
    (∀ q < CallableFixedPrime.workspaceBase N, y.mem q =
      (Data.init (PreparationInput.input N (D 9) 1 257 (weights N 0)) : Data 640).mem q) ∧
    (∀ j : Fin 640, j.val < 160 → y.regs j = 0) ∧
    ∃ u v c : Fin N,
      y.regs CallableFixedPrime.Reg.witnessA = u.val ∧
      y.regs CallableFixedPrime.Reg.witnessB = v.val ∧
      y.regs CallableFixedPrime.Reg.witnessC = c.val := by
  obtain ⟨hi, a, hout, y, t, ht, hr, he, yb, yf, ys, yiff, yw, frame, regs⟩ :=
    CallableFixedPrime.runs_input (m := 9) (n := N) (g := 1) (p := 257)
      (W := width N 0) (weights N 0) (by simp only [weights, List.length_replicate])
      (by decide) (by decide) prime hgeo le_rfl
  let V := fun q => (weights N 0).getD q 0
  have hval (q : ℕ) : V q = 0 := List.getElem?_getD_replicate_default_eq _ _ _
  have hzero : HasZeroTriangle (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) := by
    let v : Fin N := ⟨0, lt_of_lt_of_le (by decide : 0 < D 9 ^ 18) hgeo⟩
    exact ⟨v, v, v, by simp only [hval, zero_add]⟩
  have hf : y.regs CallableFixedPrime.Reg.found = 1 := yiff.mpr hzero
  have hF : falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) 257 = 0 := by
    simp only [falsePositiveCount, IsFalsePositive, weightSum, hval, zero_add,
      ne_eq, not_true_eq_false, false_and, Finset.filter_false, Finset.card_empty]
  obtain ⟨u, v, c, hu, hv, hc, _⟩ := yw hf
  refine ⟨y, t, hr, ?_, hf, ?_, ?_, ?_, regs, u, v, c, hu, hv, hc⟩
  · simpa only [hf] using he
  · have hs : y.regs CallableFixedPrime.Reg.scans ≤
        falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
          (fun b c => V (N * N + pairIndex (b, c)))
          (fun u c => V (2 * (N * N) + pairIndex (u, c))) 257 +
          y.regs CallableFixedPrime.Reg.found := ys
    simpa only [hF, hf, zero_add] using hs
  · have hcharge := CallableFixedPrime.timeBound_le (k := 1) (n := N) (g := 1) (p := 257)
        (lt_of_lt_of_le (by decide : 0 < D 9 ^ 18) hgeo) (weights N 0) a.mem
        (by decide) (by decide) prime hgeo
    dsimp only [V] at hF
    have hbound : ((t + 1 : ℕ) : ℝ) ≤
        ((CallableFixedPrime.timeBound (m := 9)
          (lt_of_lt_of_le (by decide : 0 < D 9 ^ 18) hgeo) 1 257 (weights N 0) a.mem + 1 : ℕ)
            : ℝ) + 14 := by exact_mod_cast ht
    have h := hbound.trans (add_le_add hcharge (le_refl (14 : ℝ)))
    simpa only [Nat.mul_one, Nat.cast_one, hF, zero_add, mul_one, zeroCharge] using h
  · exact fun q hq => frame q (Or.inl hq)

/-- Even with nonzero modular candidates, exhaustion of every actual record returns zero
exactly. The total scan bound is the single global false-positive count, with no extra one. -/
private theorem initialized_false_positive (N : ℕ) (hgeo : D 9 ^ 18 ≤ N) :
    let V := fun q => (weights N 257).getD q 0
    let F := falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) 257
    ∃ y : Data 640, ∃ t : ℕ,
      Runs (width N 257) (CallableFixedPrime.entryProgram.program CallableFixedPrime.Reg.found)
        (State.init (PreparationInput.input N (D 9) 1 257 (weights N 257)))
        ⟨CallableFixedPrime.entryProgram.size, y⟩ t ∧
      Executes (width N 257) (CallableFixedPrime.entryProgram.program
        CallableFixedPrime.Reg.found)
        (State.init (PreparationInput.input N (D 9) 1 257 (weights N 257))) 0 (t + 1) ∧
      y.regs CallableFixedPrime.Reg.found = 0 ∧ y.regs CallableFixedPrime.Reg.scans ≤ F := by
  obtain ⟨hi, a, hout, y, t, ht, hr, he, yb, yf, ys, yiff, yw, frame, regs⟩ :=
    CallableFixedPrime.runs_input (m := 9) (n := N) (g := 1) (p := 257)
      (W := width N 257) (weights N 257) (by simp only [weights, List.length_replicate])
      (by decide) (by decide) prime hgeo le_rfl
  let V := fun q => (weights N 257).getD q 0
  have hval (q : ℕ) (hq : q < 3 * (N * N)) : V q = 257 :=
    List.getD_replicate (257 : ℤ) hq
  have pair_bound (u v : Fin N) : pairIndex (u, v) < N * N := by
    have hu := Nat.mul_le_mul_right N (Nat.succ_le_of_lt u.isLt)
    rw [Nat.succ_mul] at hu
    change u.val * N + v.val < N * N
    have hv := v.isLt
    omega
  have hn : ¬ HasZeroTriangle (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) := by
    rintro ⟨u, v, c, hz⟩
    change V (pairIndex (u, v)) + V (N * N + pairIndex (v, c)) +
      V (2 * (N * N) + pairIndex (u, c)) = 0 at hz
    rw [hval (pairIndex (u, v)) (by have := pair_bound u v; omega),
      hval (N * N + pairIndex (v, c)) (by have := pair_bound v c; omega),
      hval (2 * (N * N) + pairIndex (u, c)) (by have := pair_bound u c; omega)] at hz
    norm_num at hz
  have hf : y.regs CallableFixedPrime.Reg.found = 0 := by
    rcases yf with h | h
    · exact h
    · exact False.elim (hn (yiff.mp h))
  refine ⟨y, t, hr, ?_, hf, ?_⟩
  · simpa only [hf] using he
  · simpa only [hf, Nat.add_zero] using ys

example : ∃ y : Data 640, ∃ t : ℕ,
    Runs (width side 0) (CallableFixedPrime.entryProgram.program CallableFixedPrime.Reg.found)
      (State.init (PreparationInput.input side (D 9) 1 257 (weights side 0)))
      ⟨CallableFixedPrime.entryProgram.size, y⟩ t ∧
    Executes (width side 0) (CallableFixedPrime.entryProgram.program
      CallableFixedPrime.Reg.found)
      (State.init (PreparationInput.input side (D 9) 1 257 (weights side 0))) 1 (t + 1) ∧
    y.regs CallableFixedPrime.Reg.found = 1 ∧ y.regs CallableFixedPrime.Reg.scans ≤ 1 ∧
    ((t + 1 : ℕ) : ℝ) ≤ zeroCharge side ∧
    (∀ q < CallableFixedPrime.workspaceBase side, y.mem q =
      (Data.init (PreparationInput.input side (D 9) 1 257 (weights side 0)) : Data 640).mem q) ∧
    (∀ j : Fin 640, j.val < 160 → y.regs j = 0) ∧
    ∃ u v c : Fin side,
      y.regs CallableFixedPrime.Reg.witnessA = u.val ∧
      y.regs CallableFixedPrime.Reg.witnessB = v.val ∧
      y.regs CallableFixedPrime.Reg.witnessC = c.val :=
  initialized_zero side (by decide)

example :
    let V := fun q => (weights side 257).getD q 0
    let F := falsePositiveCount (fun u v : Fin side => V (pairIndex (u, v)))
      (fun b c => V (side * side + pairIndex (b, c)))
      (fun u c => V (2 * (side * side) + pairIndex (u, c))) 257
    ∃ y : Data 640, ∃ t : ℕ,
      Runs (width side 257) (CallableFixedPrime.entryProgram.program
        CallableFixedPrime.Reg.found)
        (State.init (PreparationInput.input side (D 9) 1 257 (weights side 257)))
        ⟨CallableFixedPrime.entryProgram.size, y⟩ t ∧
      Executes (width side 257) (CallableFixedPrime.entryProgram.program
        CallableFixedPrime.Reg.found)
        (State.init (PreparationInput.input side (D 9) 1 257 (weights side 257))) 0 (t + 1) ∧
      y.regs CallableFixedPrime.Reg.found = 0 ∧ y.regs CallableFixedPrime.Reg.scans ≤ F :=
  initialized_false_positive side (by decide)

end CslibFrontierTests.WordRAMCallableBoxFixedPrime
