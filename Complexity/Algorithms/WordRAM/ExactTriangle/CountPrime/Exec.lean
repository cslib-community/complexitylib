/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.ExecReady

/-!
# Complete native modular counter from original caller data

The fixed 128-register program computes its logarithm, padding, layout, residues, table,
coefficient matrices, real seven-product recursion and selected count. No intermediate
layout, table, matrix, execution or time certificate is an argument. Original signed arrays
may alias each other below the dirty workspace. Its outside memory and persistent original
parameters are preserved. Bounds refer solely to the original scalars, pointers and weights.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Complete actual caller execution from ordinary runtime arguments and original signed
array words, with raw count, computed metadata, dirty-workspace frame and all native costs.
The final halt is excluded here and is charged by initialized flat clients. -/
theorem exec {w n p scratch a b c A : ℕ} (x : Data 128) (u v z : ℕ → ℤ)
    (hp0 : 0 < p) (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hAB : x.regs Reg.inputAB = a) (hBC : x.regs Reg.inputBC = b)
    (hAC : x.regs Reg.inputAC = c) (hs : x.regs Reg.scratch = scratch)
    (ha : a + n * n ≤ scratch) (hb : b + n * n ≤ scratch) (hc : c + n * n ≤ scratch)
    (hu : ∀ i < n * n, (u i).natAbs ≤ A)
    (hv : ∀ i < n * n, (v i).natAbs ≤ A)
    (hz : ∀ i < n * n, (z i).natAbs ≤ A)
    (hinU : ∀ i < n * n, x.mem (a + i) = encode (u i))
    (hinV : ∀ i < n * n, x.mem (b + i) = encode (v i))
    (hinZ : ∀ i < n * n, x.mem (c + i) = encode (z i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBudget p (Nat.clog 2 n) A : ℤ))
    (hw : Fits (w + 2) (addressBudget n p (Nat.clog 2 n) scratch a b c)) :
    ∃ y, ExecWithin (w + 2) program x y (cost n p) ∧
      CounterRegisters n p (Nat.clog 2 n) scratch a b c y ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => u (α.val * n + β.val))
        (fun α β : Fin n => v (α.val * n + β.val))
        (fun α β : Fin n => z (α.val * n + β.val)) p ∧
      ∀ d, d < scratch ∨ memoryEnd n p (Nat.clog 2 n) scratch ≤ d → y.mem d = x.mem d := by
  let k := Nat.clog 2 n
  have h2 : 0 < 2 ^ k := by positivity
  have h4 : 0 < 4 ^ k := by positivity
  have harea : 0 < 4 ^ k * p := Nat.mul_pos h4 hp0
  obtain ⟨x0, setupRun, ready, memory⟩ := exec_setup x hp0 hn hp hAB hBC hAC hs
    (hw.of_le (by unfold addressBudget layoutWordBound; dsimp only [k] at *; omega))
  obtain ⟨y, tailRun, finalRegisters, result, frame⟩ := exec_ready x0 u v z hp0
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n) ready ha hb hc hu hv hz
    (by simpa only [memory] using hinU) (by simpa only [memory] using hinV)
    (by simpa only [memory] using hinZ) hmag hw
  refine ⟨y, (setupRun.seq tailRun).mono (by unfold cost; omega), finalRegisters, result, ?_⟩
  intro d hd
  exact (frame d hd).trans (congrFun memory d)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
