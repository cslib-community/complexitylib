/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Setup
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.MatrixReadback

/-!
# Computed spread table and both real cyclic coefficient matrices

The table is constructed once by actual code and reused by both charged padded writers.
The returned P/Q words agree with the existing mathematical specification, including the BC
transpose and every padding zero. Memory below the table, including all residue arrays and
original caller data, is preserved. The complete counter supplies residues through native code.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

private theorem spread_keeps_metadata (j : Fin 128) (hj : MetadataRegister j) :
    spreadTable.Preserves j := by decide +kernel +revert

private theorem matrix_keeps_metadata (transpose : Bool) (j : Fin 128)
    (hj : MetadataRegister j) :
    (matrix (if transpose then Reg.residueBC else Reg.residueAC)
      (if transpose then Reg.matrixQ else Reg.matrixP) transpose).Preserves j := by
  cases transpose <;> decide +kernel +revert

/-- Build the actual table and both coefficient matrices from the three-matrix residue prefix.
No table, monomial array, padding layout or matrix-result certificate is an algorithm input. -/
theorem exec_coefficientMatrices {w n p k scratch a b c : ℕ} (x : Data 128)
    (wBC wAC : Fin n → Fin n → ℤ) (hp : 0 < p)
    (ready : CounterRegisters n p k scratch a b c x)
    (hBC : ∀ u v : Fin n, x.mem (x.regs Reg.residueBC + u.val * n + v.val) =
      (wBC u v % (p : ℤ)).toNat)
    (hAC : ∀ u v : Fin n, x.mem (x.regs Reg.residueAC + u.val * n + v.val) =
      (wAC u v % (p : ℤ)).toNat)
    (hw : Fits w (addressBudget n p k scratch a b c)) :
    ∃ y, ExecWithin w coefficientMatrices x y
        ((14 * p + 48) * 4 ^ k + 11 * (2 ^ k - 1) + 15) ∧
      CounterRegisters n p k scratch a b c y ∧
      (∀ j < 2 ^ k, y.mem (x.regs Reg.spread + j) = Nat.Morton.spread j) ∧
      (∀ i < 4 ^ k * p, y.mem (x.regs Reg.matrixP + i) = encode
        (Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients p wAC i)) ∧
      (∀ i < 4 ^ k * p, y.mem (x.regs Reg.matrixQ + i) = encode
        (Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients p wBC i)) ∧
      ∀ d, d < x.regs Reg.spread ∨ x.regs Reg.matrixR ≤ d → y.mem d = x.mem d := by
  have h4 : 0 < 4 ^ k := by positivity
  have h2 : 0 < 2 ^ k := by positivity
  have harea : 0 < 4 ^ k * p := Nat.mul_pos h4 hp
  have pair_lt (u v : Fin n) : u.val * n + v.val < n * n := by
    have h := (finProdFinEquiv (u, v)).isLt
    change v.val + n * u.val < n * n at h
    simpa only [Nat.add_comm, Nat.mul_comm] using h
  have hTP : x.regs Reg.spread + 2 ^ k = x.regs Reg.matrixP := by
    rw [ready.layout.spread_eq, ready.layout.matrixP_eq]
  have hPQ : x.regs Reg.matrixP + 4 ^ k * p = x.regs Reg.matrixQ := by
    rw [ready.layout.matrixP_eq, ready.layout.matrixQ_eq]
  have hQR : x.regs Reg.matrixQ + 4 ^ k * p = x.regs Reg.matrixR := by
    rw [ready.layout.matrixQ_eq, ready.layout.matrixR_eq]
    omega
  have hBCbefore : x.regs Reg.residueBC + n * n ≤ x.regs Reg.spread := by
    rw [ready.layout.residueBC_eq, ready.layout.spread_eq]
    omega
  have hACbefore : x.regs Reg.residueAC + n * n ≤ x.regs Reg.spread := by
    rw [ready.layout.residueAC_eq, ready.layout.spread_eq]
    omega
  obtain ⟨s, tableRun, table, tableFrame, _⟩ := exec_spreadTable x ready.layout.paddedSide_eq
    ready.zero ready.one ready.two ready.four (by
      rw [ready.layout.spread_eq]
      exact hw.of_le (by unfold addressBudget; omega))
  have keep1 (j : Fin 128) (hj : MetadataRegister j) : s.regs j = x.regs j :=
    tableRun.regs_eq (spread_keeps_metadata j hj)
  have ready1 := ready.congr keep1
  obtain ⟨t, leftRun, left, leftFrame, _⟩ := exec_matrix_coefficients
    Reg.residueAC Reg.matrixP false s wAC hp (by decide)
    ready1.layout.side_eq ready1.layout.modulus_eq ready1.layout.paddedSide_eq
    ready1.layout.paddedCells_eq (keep1 _ (by decide)) (keep1 _ (by decide))
    (keep1 _ (by decide)) ready1.zero ready1.one ready1.two
    (by omega) (by omega) table
    (by
      intro u v
      rw [tableFrame _ (Or.inl (by have := pair_lt u v; omega))]
      exact hAC u v)
    (by
      rw [ready.layout.matrixP_eq, ready.layout.spread_eq, ready.layout.residueAC_eq]
      exact hw.of_le (by unfold addressBudget; omega))
  have keep2 (j : Fin 128) (hj : MetadataRegister j) : t.regs j = x.regs j :=
    (leftRun.regs_eq (matrix_keeps_metadata false j hj)).trans (keep1 j hj)
  have ready2 := ready.congr keep2
  obtain ⟨y, rightRun, right, rightFrame, _⟩ := exec_matrix_coefficients
    Reg.residueBC Reg.matrixQ true t wBC hp (by decide)
    ready2.layout.side_eq ready2.layout.modulus_eq ready2.layout.paddedSide_eq
    ready2.layout.paddedCells_eq (keep2 _ (by decide)) (keep2 _ (by decide))
    (keep2 _ (by decide)) ready2.zero ready2.one ready2.two
    (by omega) (by omega)
    (by
      intro j hj
      rw [leftFrame _ (Or.inl (by omega))]
      exact table j hj)
    (by
      intro u v
      rw [leftFrame _ (Or.inl (by have := pair_lt u v; omega)),
        tableFrame _ (Or.inl (by have := pair_lt u v; omega))]
      exact hBC u v)
    (by
      rw [ready.layout.matrixQ_eq, ready.layout.spread_eq, ready.layout.residueBC_eq]
      exact hw.of_le (by unfold addressBudget; omega))
  have keep3 (j : Fin 128) (hj : MetadataRegister j) : y.regs j = x.regs j :=
    (rightRun.regs_eq (matrix_keeps_metadata true j hj)).trans (keep2 j hj)
  refine ⟨y, (tableRun.seq (leftRun.seq rightRun)).mono (by nlinarith),
    ready.congr keep3, ?_, ?_, right, ?_⟩
  · intro j hj
    rw [rightFrame _ (Or.inl (by omega)), leftFrame _ (Or.inl (by omega))]
    exact table j hj
  · intro i hi
    rw [rightFrame _ (Or.inl (by omega))]
    exact left i hi
  · intro d hd
    rw [rightFrame _ (hd.imp (fun h => by omega) (fun h => by omega)),
      leftFrame _ (hd.imp (fun h => by omega) (fun h => by omega)),
      tableFrame _ (hd.imp id (fun h => by omega))]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
