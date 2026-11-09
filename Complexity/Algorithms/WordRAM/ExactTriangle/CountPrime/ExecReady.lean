/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Bounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.ResidueArrays
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.CoefficientMatrices
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Solve
public import Complexity.Computability.GenericRAM.Signed.Fits

/-!
# Complete actual counter tail from original signed arrays

Only the register metadata has been established by setup. Every residue, table, coefficient
matrix and product is constructed by real code here. The final scan returns the existing
modular count. The original arrays and all caller memory outside the explicit workspace are
preserved, including when the workspace starts dirty.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Compose the actual residue/matrix/seven-product/extraction pipeline. This internal theorem
consumes setup's computed register meaning, not any intermediate table, matrix or run oracle. -/
theorem exec_ready {w n p k scratch a b c A : ℕ} (x : Data 128)
    (u v z : ℕ → ℤ) (hp : 0 < p) (hn : n ≤ 2 ^ k)
    (ready : CounterRegisters n p k scratch a b c x)
    (ha : a + n * n ≤ scratch) (hb : b + n * n ≤ scratch) (hc : c + n * n ≤ scratch)
    (hu : ∀ i < n * n, (u i).natAbs ≤ A)
    (hv : ∀ i < n * n, (v i).natAbs ≤ A)
    (hz : ∀ i < n * n, (z i).natAbs ≤ A)
    (hinU : ∀ i < n * n, x.mem (a + i) = encode (u i))
    (hinV : ∀ i < n * n, x.mem (b + i) = encode (v i))
    (hinZ : ∀ i < n * n, x.mem (c + i) = encode (z i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBudget p k A : ℤ))
    (hw : Fits (w + 2) (addressBudget n p k scratch a b c)) :
    ∃ y, ExecWithin (w + 2)
        (.seq residueArrays (.seq coefficientMatrices (.seq product count))) x y
        (readyCost n p k) ∧
      CounterRegisters n p k scratch a b c y ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => u (α.val * n + β.val))
        (fun α β : Fin n => v (α.val * n + β.val))
        (fun α β : Fin n => z (α.val * n + β.val)) p ∧
      ∀ d, d < scratch ∨ memoryEnd n p k scratch ≤ d → y.mem d = x.mem d := by
  have h16 : 0 < 16 ^ k := by positivity
  have h4 : 0 < 4 ^ k := by positivity
  have h2 : 0 < 2 ^ k := by positivity
  have harea : 0 < 4 ^ k * p := Nat.mul_pos h4 hp
  have hA : A ≤ magnitudeBudget p k A := by unfold magnitudeBudget; omega
  have hP : p ≤ magnitudeBudget p k A := by unfold magnitudeBudget; omega
  have hM : 2 * (p + 4) * 16 ^ k ≤ magnitudeBudget p k A := by
    unfold magnitudeBudget
    omega
  have modFit : GenericRAM.Signed.Fits w (p : ℤ) :=
    hmag.of_natAbs_le (by simpa only [Int.natAbs_natCast] using hP)
  obtain ⟨x1, residueRun, ready1, resAB, resBC, resAC, residueFrame⟩ := exec_residueArrays x
    u v z hp ready ha hb hc modFit
    (fun i hi => hmag.of_natAbs_le ((hu i hi).trans hA))
    (fun i hi => hmag.of_natAbs_le ((hv i hi).trans hA))
    (fun i hi => hmag.of_natAbs_le ((hz i hi).trans hA)) hinU hinV hinZ hw
  let wAB := fun α β : Fin n => u (α.val * n + β.val)
  let wBC := fun α β : Fin n => v (α.val * n + β.val)
  let wAC := fun α β : Fin n => z (α.val * n + β.val)
  have pair_lt (α β : Fin n) : α.val * n + β.val < n * n := by
    have h := (finProdFinEquiv (α, β)).isLt
    change β.val + n * α.val < n * n at h
    simpa only [Nat.add_comm, Nat.mul_comm] using h
  obtain ⟨x2, matrixRun, ready2, table, left, right, matrixFrame⟩ :=
    exec_coefficientMatrices x1 wBC wAC hp ready1
    (by
      intro α β
      simpa only [ready1.layout.residueBC_eq, Nat.add_assoc, wBC] using
        resBC _ (pair_lt α β))
    (by
      intro α β
      simpa only [ready1.layout.residueAC_eq, Nat.add_assoc, wAC] using
        resAC _ (pair_lt α β)) hw
  obtain ⟨y, solveRun, ready3, result, solveFrame⟩ := exec_product_count x2
    wAB wBC wAC hp hn ready2
    (by
      intro α β
      rw [ready2.layout.residueAB_eq]
      rw [matrixFrame _ (Or.inl (by
        rw [ready1.layout.spread_eq]
        have := pair_lt α β
        omega))]
      simpa only [Nat.add_assoc, wAB] using resAB _ (pair_lt α β))
    (by simpa only [ready2.layout.spread_eq, ready1.layout.spread_eq] using table)
    (by simpa only [ready2.layout.matrixP_eq, ready1.layout.matrixP_eq] using left)
    (by simpa only [ready2.layout.matrixQ_eq, ready1.layout.matrixQ_eq] using right)
    (hmag.of_natAbs_le (by simpa only [Int.natAbs_natCast] using hM)) hw
  refine ⟨y, (residueRun.seq (matrixRun.seq solveRun)).mono (by
    unfold readyCost
    nlinarith), ready3, result, ?_⟩
  intro d hd
  have hs : d < x2.regs Reg.matrixR ∨
      x2.regs Reg.productScratch + 4 ^ k * p + 7 * (k + 1) ≤ d := by
    rw [ready2.layout.matrixR_eq, ready2.layout.productScratch_eq]
    unfold memoryEnd at hd
    rcases hd with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hm : d < x1.regs Reg.spread ∨ x1.regs Reg.matrixR ≤ d := by
    rw [ready1.layout.spread_eq, ready1.layout.matrixR_eq]
    unfold memoryEnd at hd
    rcases hd with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [solveFrame d hs, matrixFrame d hm]
  exact residueFrame d (hd.imp id (by intro h; unfold memoryEnd at h; omega))

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
