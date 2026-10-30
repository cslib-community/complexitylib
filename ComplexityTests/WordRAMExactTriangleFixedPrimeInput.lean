/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime
import Mathlib.Data.List.GetD

/-!
# Fully admitted original-input fixed-prime decisions

Both clients retain the actual same-state prefix and halt at valid positive thin geometry.
The all-one negative input has modular false positives at prime three, but no original zero;
its unsuccessful records collectively receive no additive successful-scan allowance. These
kernel proofs do not evaluate the enormous catalogue or encoder through the interpreter.
-/

namespace ComplexityTests.WordRAMExactTriangleFixedPrimeInput

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private def side : ℕ := 16 ^ 18
private def weights (N : ℕ) (z : ℤ) : List ℤ := List.replicate (3 * (N * N)) z
private def width (N A : ℕ) : ℕ := FixedPrime.admissionWidth N (D 2) 1 3 A

private theorem prime : 3 ∈ Nat.sqrtPrimeWindow (D 2) :=
  Nat.mem_sqrtPrimeWindow_iff_sq.mpr ⟨by decide, by decide, by decide⟩

/-- The complete actual program returns one and an original witness on all-zero input. -/
private theorem initialized_zero (N : ℕ) (hgeo : D 2 ^ 18 ≤ N) : ∃ y : Data 416, ∃ t : ℕ,
    Runs (width N 0) (FixedPrime.program.program FixedPrime.Reg.found)
      (State.init (PreparationInput.input N (D 2) 1 3 (weights N 0)))
      ⟨FixedPrime.program.size, y⟩ t ∧
    Executes (width N 0) (FixedPrime.program.program FixedPrime.Reg.found)
      (State.init (PreparationInput.input N (D 2) 1 3 (weights N 0))) 1 (t + 1) ∧
    y.regs FixedPrime.Reg.found = 1 ∧ y.regs FixedPrime.Reg.scans ≤ 1 ∧
    ∃ u v c : Fin N,
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) = u.val ∧
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) = v.val ∧
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC) = c.val := by
  have hmag : ∀ z ∈ weights N 0, z.natAbs ≤ 0 := by
    intro z hz
    have he := List.eq_of_mem_replicate hz
    subst z
    decide
  obtain ⟨hi, a, ha, hout, y, t, ht, hr, he, yb, yf, ys, yiff, yw, frame, regs⟩ :=
    FixedPrime.runs_input (m := 2) (n := N) (g := 1) (p := 3) (A := 0)
      (W := width N 0) (weights N 0) (by simp only [weights, List.length_replicate])
      (by decide) (by decide) prime hgeo hmag le_rfl
  let V := fun q => (weights N 0).getD q 0
  have hval (q : ℕ) : V q = 0 := List.getElem?_getD_replicate_default_eq _ _ _
  have hzero : HasZeroTriangle (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) := by
    let v : Fin N := ⟨0, lt_of_lt_of_le (by decide : 0 < D 2 ^ 18) hgeo⟩
    exact ⟨v, v, v, by simp only [hval, zero_add]⟩
  have hf : y.regs FixedPrime.Reg.found = 1 := yiff.mpr hzero
  have hF : falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) 3 = 0 := by
    simp only [falsePositiveCount, IsFalsePositive, weightSum, hval, zero_add,
      ne_eq, not_true_eq_false, false_and, Finset.filter_false, Finset.card_empty]
  obtain ⟨u, v, c, hu, hv, hc, _⟩ := yw hf
  refine ⟨y, t, hr, ?_, hf, ?_, u, v, c, hu, hv, hc⟩
  · simpa only [hf] using he
  · have hs : y.regs FixedPrime.Reg.scans ≤
        falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
          (fun b c => V (N * N + pairIndex (b, c)))
          (fun u c => V (2 * (N * N) + pairIndex (u, c))) 3 +
          y.regs FixedPrime.Reg.found := ys
    simpa only [hF, hf, zero_add] using hs

/-- Even with nonzero modular candidates, exhaustion of every actual record returns zero
exactly. The total scan bound is the single global false-positive count, with no extra one. -/
private theorem initialized_one (N : ℕ) (hgeo : D 2 ^ 18 ≤ N) :
    let V := fun q => (weights N 1).getD q 0
    let F := falsePositiveCount (fun u v : Fin N => V (pairIndex (u, v)))
      (fun b c => V (N * N + pairIndex (b, c)))
      (fun u c => V (2 * (N * N) + pairIndex (u, c))) 3
    ∃ y : Data 416, ∃ t : ℕ,
      Runs (width N 1) (FixedPrime.program.program FixedPrime.Reg.found)
        (State.init (PreparationInput.input N (D 2) 1 3 (weights N 1)))
        ⟨FixedPrime.program.size, y⟩ t ∧
      Executes (width N 1) (FixedPrime.program.program FixedPrime.Reg.found)
        (State.init (PreparationInput.input N (D 2) 1 3 (weights N 1))) 0 (t + 1) ∧
      y.regs FixedPrime.Reg.found = 0 ∧ y.regs FixedPrime.Reg.scans ≤ F := by
  have hmag : ∀ z ∈ weights N 1, z.natAbs ≤ 1 := by
    intro z hz
    have he := List.eq_of_mem_replicate hz
    subst z
    decide
  obtain ⟨hi, a, ha, hout, y, t, ht, hr, he, yb, yf, ys, yiff, yw, frame, regs⟩ :=
    FixedPrime.runs_input (m := 2) (n := N) (g := 1) (p := 3) (A := 1)
      (W := width N 1) (weights N 1) (by simp only [weights, List.length_replicate])
      (by decide) (by decide) prime hgeo hmag le_rfl
  let V := fun q => (weights N 1).getD q 0
  have hval (q : ℕ) (hq : q < 3 * (N * N)) : V q = 1 :=
    List.getD_replicate (1 : ℤ) hq
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
  have hf : y.regs FixedPrime.Reg.found = 0 := by
    rcases yf with h | h
    · exact h
    · exact False.elim (hn (yiff.mp h))
  refine ⟨y, t, hr, ?_, hf, ?_⟩
  · simpa only [hf] using he
  · simpa only [hf, Nat.add_zero] using ys


example : ∃ y : Data 416, ∃ t : ℕ,
    Runs (width side 0) (FixedPrime.program.program FixedPrime.Reg.found)
      (State.init (PreparationInput.input side (D 2) 1 3 (weights side 0)))
      ⟨FixedPrime.program.size, y⟩ t ∧
    Executes (width side 0) (FixedPrime.program.program FixedPrime.Reg.found)
      (State.init (PreparationInput.input side (D 2) 1 3 (weights side 0))) 1 (t + 1) ∧
    y.regs FixedPrime.Reg.found = 1 ∧ y.regs FixedPrime.Reg.scans ≤ 1 ∧
    ∃ u v c : Fin side,
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) = u.val ∧
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) = v.val ∧
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC) = c.val :=
  initialized_zero side (by decide)

example :
    let V := fun q => (weights side 1).getD q 0
    let F := falsePositiveCount (fun u v : Fin side => V (pairIndex (u, v)))
      (fun b c => V (side * side + pairIndex (b, c)))
      (fun u c => V (2 * (side * side) + pairIndex (u, c))) 3
    ∃ y : Data 416, ∃ t : ℕ,
      Runs (width side 1) (FixedPrime.program.program FixedPrime.Reg.found)
        (State.init (PreparationInput.input side (D 2) 1 3 (weights side 1)))
        ⟨FixedPrime.program.size, y⟩ t ∧
      Executes (width side 1) (FixedPrime.program.program FixedPrime.Reg.found)
        (State.init (PreparationInput.input side (D 2) 1 3 (weights side 1))) 0 (t + 1) ∧
      y.regs FixedPrime.Reg.found = 0 ∧ y.regs FixedPrime.Reg.scans ≤ F :=
  initialized_one side (by decide)

end ComplexityTests.WordRAMExactTriangleFixedPrimeInput
