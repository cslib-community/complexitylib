/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Setup
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Product
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.ScanReadback

/-!
# Actual cyclic Strassen product followed by native coefficient counting

The actual seven-product program runs in the low bank and protects the computed residue and
spread prefix. Its proved coefficient output feeds the real scan, which returns the existing
modular triangle count. This internal composition theorem assumes the preceding producer's
ordinary array meaning, never a multiplication, execution, count or time oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

private theorem metadata_not_scan (j : Fin 128) (hj : MetadataRegister j) : ¬ScanLocal j := by
  decide +kernel +revert

/-- Invoke the concrete native Strassen controller and count its actual computed coefficients.
The entire original/residue/table prefix and all memory beyond the explicit scratch/stack
window survive; dirty product and scratch words require no clearing hypothesis. -/
theorem exec_product_count {w n p k scratch a b c : ℕ} (x : Data 128)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (hp : 0 < p) (hn : n ≤ 2 ^ k)
    (ready : CounterRegisters n p k scratch a b c x)
    (hAB : ∀ u v : Fin n, x.mem (x.regs Reg.residueAB + u.val * n + v.val) =
      (wAB u v % (p : ℤ)).toNat)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hleft : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixP + i) = encode
      (Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients p wAC i))
    (hright : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixQ + i) = encode
      (Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients p wBC i))
    (hmag : GenericRAM.Signed.Fits w ((2 * (p + 4) * 16 ^ k : ℕ) : ℤ))
    (hw : Fits (w + 2) (addressBudget n p k scratch a b c)) :
    ∃ y, ExecWithin (w + 2) (.seq product count) x y
        (Strassen.traceBudget p k + 4 * k + 22 * (n * n) + 42) ∧
      CounterRegisters n p k scratch a b c y ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod wAB wBC wAC p ∧
      ∀ d, d < x.regs Reg.matrixR ∨
        x.regs Reg.productScratch + 4 ^ k * p + 7 * (k + 1) ≤ d → y.mem d = x.mem d := by
  have h4 : 0 < 4 ^ k := by positivity
  have h2 : 0 < 2 ^ k := by positivity
  have harea : 0 < 4 ^ k * p := Nat.mul_pos h4 hp
  have hPQ : x.regs Reg.matrixP + 4 ^ k * p ≤ x.regs Reg.matrixQ := by
    rw [ready.layout.matrixP_eq, ready.layout.matrixQ_eq]
  have hQR : x.regs Reg.matrixQ + 4 ^ k * p ≤ x.regs Reg.matrixR := by
    rw [ready.layout.matrixQ_eq, ready.layout.matrixR_eq]
    omega
  have hRS : x.regs Reg.matrixR + 4 ^ k * p ≤ x.regs Reg.productScratch := by
    rw [ready.layout.matrixR_eq, ready.layout.productScratch_eq]
    omega
  obtain ⟨s, productRun, productValues, productFrame, productRegs⟩ := exec_product x
    (Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients p wAC)
    (Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients p wBC)
    hp ready.layout.modulus_eq ready.layout.depth_eq hPQ hQR hRS
    (fun i _ => Cslib.Algorithms.ExactTriangle.CountPrime.pCoefficients_natAbs_le_one p wAC i)
    (fun i _ => Cslib.Algorithms.ExactTriangle.CountPrime.qCoefficients_natAbs_le_one p wBC i)
    hleft hright hmag (by
      unfold Strassen.addressBound
      rw [ready.layout.productScratch_eq]
      exact hw.of_le (by unfold addressBudget; omega))
  have keep1 (j : Fin 128) (hj : MetadataRegister j) : s.regs j = x.regs j :=
    productRegs j hj.1
  have ready1 := ready.congr keep1
  have before (d : ℕ) (hd : d < x.regs Reg.matrixR) : s.mem d = x.mem d := by
    apply productFrame d
    unfold Strassen.NodeWrites
    omega
  have pair_lt (u v : Fin n) : u.val * n + v.val < n * n := by
    have h := (finProdFinEquiv (u, v)).isLt
    change v.val + n * u.val < n * n at h
    simpa only [Nat.add_comm, Nat.mul_comm] using h
  obtain ⟨y, scanRun, scanMemory, result, scanRegs⟩ := exec_count_coefficients s
    wAB wBC wAC hp hn ready1.layout.side_eq ready1.layout.modulus_eq ready1.layout.cells_eq
    (by
      intro u v
      rw [keep1 Reg.residueAB (by decide), before _ (by
        rw [ready.layout.residueAB_eq, ready.layout.matrixR_eq]
        have := pair_lt u v
        omega)]
      exact hAB u v)
    (by simpa only [keep1 Reg.matrixR (by decide)] using productValues)
    ready1.zero ready1.one ready1.two
    (by
      intro j hj
      rw [keep1 Reg.spread (by decide), before _ (by
        rw [ready.layout.spread_eq, ready.layout.matrixR_eq]
        omega)]
      exact htable j hj)
    (by
      rw [keep1 Reg.spread (by decide), keep1 Reg.residueAB (by decide),
        keep1 Reg.matrixR (by decide), ready.layout.spread_eq, ready.layout.residueAB_eq,
        ready.layout.matrixR_eq]
      exact hw.of_le (by unfold addressBudget; omega))
  refine ⟨y, (productRun.seq scanRun).mono (by omega),
    ready1.congr (fun j hj => scanRegs j (metadata_not_scan j hj)), result, ?_⟩
  intro d hd
  rw [scanMemory]
  apply productFrame d
  unfold Strassen.NodeWrites
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
