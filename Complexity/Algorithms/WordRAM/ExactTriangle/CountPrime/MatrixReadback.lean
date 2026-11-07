/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Matrix
public import Complexity.Algorithms.ExactTriangle.CountPrime

/-!
# Native CountPrime matrices agree with the existing coefficient specification

Actual residue readback and the preceding native table construction feed the real padded
matrix loop. Every resulting word is the canonical encoding of the existing P/Q coefficient
at that exact Morton/coefficient index. No alternative matrix or triangle definition is
introduced. Both padding and the actual BC transpose are included.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The complete computed native matrix agrees with existing P coefficients, or Q
coefficients for the real transposed branch, at every occupied coefficient index. -/
theorem exec_matrix_coefficients {w n p k source destination table : ℕ}
    (src dst : Fin 128) (transpose : Bool) (x : Data 128) (weights : Fin n → Fin n → ℤ)
    (hpositive : 0 < p) (hdstReg : dst ≠ Reg.residueSource)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hN : x.regs Reg.paddedSide = 2 ^ k) (harea : x.regs Reg.paddedCells = 4 ^ k)
    (hsrc : x.regs src = source) (hdst : x.regs dst = destination) (ht : x.regs Reg.spread = table)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (hsourceBefore : source + n * n ≤ destination) (htableBefore : table + 2 ^ k ≤ destination)
    (htable : ∀ j < 2 ^ k, x.mem (table + j) = Nat.Morton.spread j)
    (hresidue : ∀ a b : Fin n, x.mem (source + a.val * n + b.val) =
      (weights a b % (p : ℤ)).toNat)
    (hw : Fits w (destination + 4 ^ k * p + table + 4 ^ k + 2 ^ k +
      source + n * n + p + 16)) :
    ∃ y, ExecWithin w (matrix src dst transpose) x y ((7 * p + 24) * 4 ^ k + 5) ∧
      (∀ i < 4 ^ k * p, y.mem (destination + i) = encode
        (if transpose then Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients p weights i
        else Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients p weights i)) ∧
      (∀ d, d < destination ∨ destination + 4 ^ k * p ≤ d → y.mem d = x.mem d) ∧
      ∀ r, ¬MatrixLocal r → r ≠ Reg.residueSource → r ≠ Reg.destination → y.regs r = x.regs r := by
  obtain ⟨y, he, values, memory, regs⟩ := exec_matrix src dst transpose x hdstReg
    hn hp hN harea hsrc hdst ht h0 h1 h2 hsourceBefore htableBefore htable hw
  refine ⟨y, he, ?_, memory, regs⟩
  intro i hi
  let cell := i / p
  let a := Nat.Morton.row cell
  let b := Nat.Morton.column cell
  let N := 2 ^ k
  have hcell : cell < 4 ^ k := (Nat.div_lt_iff_lt_mul hpositive).mpr hi
  obtain ⟨ha, hb⟩ := Nat.Morton.row_column_lt hcell
  change a < N at ha
  change b < N at hb
  have hNpos : 0 < N := by positivity
  have hsquare : N * N = 4 ^ k := by dsimp only [N]; rw [← mul_pow]; rfl
  let j := a * N + b
  have hj : j < 4 ^ k := by
    have hm := Nat.mul_le_mul_right N (Nat.succ_le_of_lt ha)
    rw [Nat.succ_mul] at hm
    dsimp only [j]
    rw [← hsquare]
    omega
  have hjDiv : j / N = a := by
    dsimp only [j]
    rw [Nat.mul_comm a N, Nat.mul_add_div hNpos, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hjMod : j % N = b := by
    dsimp only [j]
    rw [Nat.mul_comm a N, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have hpos : Nat.Morton.index a b = cell := Nat.Morton.index_row_column cell
  have hidx : cell * p + i % p = i := by
    simpa only [cell, Nat.mul_comm] using Nat.div_add_mod i p
  have hr : i % p < p := Nat.mod_lt i hpositive
  have hv := values j hj (i % p) hr
  rw [hjDiv, hjMod, hpos, Nat.add_assoc, hidx] at hv
  cases transpose with
  | false =>
    change y.mem (destination + i) = encode
      (Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients p weights i)
    unfold Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients
    change y.mem (destination + i) = encode (if h : a < n ∧ b < n then
      if i % p = (weights ⟨a, h.1⟩ ⟨b, h.2⟩ % (p : ℤ)).toNat then 1 else 0 else 0)
    by_cases h : a < n ∧ b < n
    · rw [dite_eq_left h]
      simp only [h, and_self, ite_true, Bool.false_eq_true, ite_false] at hv
      rw [← Nat.add_assoc, hresidue ⟨a, h.1⟩ ⟨b, h.2⟩] at hv
      rw [hv]
      split_ifs <;> rfl
    · rw [dite_eq_right h]
      simp only [h, ite_false, show i % p ≠ p by omega] at hv
      exact hv
  | true =>
    change y.mem (destination + i) = encode
      (Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients p weights i)
    unfold Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients
    change y.mem (destination + i) = encode (if h : a < n ∧ b < n then
      if i % p = (weights ⟨b, h.2⟩ ⟨a, h.1⟩ % (p : ℤ)).toNat then 1 else 0 else 0)
    by_cases h : a < n ∧ b < n
    · rw [dite_eq_left h]
      simp only [h, and_self, ite_true] at hv
      rw [← Nat.add_assoc, hresidue ⟨b, h.2⟩ ⟨a, h.1⟩] at hv
      rw [hv]
      split_ifs <;> rfl
    · rw [dite_eq_right h]
      simp only [h, ite_false, show i % p ≠ p by omega] at hv
      exact hv

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
