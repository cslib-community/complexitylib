/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Delivery
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Properties

/-!
# Actual exhaustive branch of the assembled ExactTriangle solver

The complete24-register reference program executes on the real original matrices, including
aliased spans and empty input. Six argument copies and the raw return copy are charged. Every
memory cell and all saved original high-register arguments survive. No fast geometry, supplied
verdict, source run, layout or time contract is used for the small branch.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Real small-input solving from the saved original arguments, with arbitrary old registers
and aliased matrices. This execution rule also applies to zero vertices or zero weight bound. -/
theorem exec_slow {W n F b : ℕ} (x : Data 640) (A B C : Fin n → Fin n → ℤ)
    (hn : x.regs CallableFixedPrime.Reg.n = n)
    (hAB : x.regs CallableFixedPrime.Reg.ab + n * n ≤ b)
    (hBC : x.regs CallableFixedPrime.Reg.bc + n * n ≤ b)
    (hAC : x.regs CallableFixedPrime.Reg.ac + n * n ≤ b)
    (hfit : Fits W (b + n * (n * n) + 6 * F + 10))
    (hmA : ∀ i j, x.mem (x.regs CallableFixedPrime.Reg.ab + i.val * n + j.val) =
      Signed.encode (A i j))
    (hmB : ∀ i j, x.mem (x.regs CallableFixedPrime.Reg.bc + i.val * n + j.val) =
      Signed.encode (B i j))
    (hmC : ∀ i j, x.mem (x.regs CallableFixedPrime.Reg.ac + i.val * n + j.val) =
      Signed.encode (C i j))
    (hA : ∀ i j, |A i j| ≤ (F : ℤ)) (hB : ∀ i j, |B i j| ≤ (F : ℤ))
    (hC : ∀ i j, |C i j| ≤ (F : ℤ)) :
    ∃ y, ExecWithin W slow x y (39 * (n * (n * n)) + 16) ∧
      y.regs CallableFixedPrime.Reg.found ≤ 1 ∧
      (y.regs CallableFixedPrime.Reg.found = 1 ↔ HasZeroTriangle A B C) ∧ y.mem = x.mem ∧
      ∀ j : Fin 640, 24 ≤ j.val → j ≠ CallableFixedPrime.Reg.found → y.regs j = x.regs j := by
  obtain ⟨a, ha, am, an, _, aAB, aBC, aAC, ab, ar⟩ := exec_slowArguments (W := W) x
  obtain ⟨z, hz, zbool, ziff, zm⟩ := ThreeSum.Host.Slow.exec_at A B C
    (a.comap slowBank) (an.trans hn) aAB aBC aAC hAB hBC hAC hfit
    (fun i j => (congrFun am _).trans (hmA i j))
    (fun i j => (congrFun am _).trans (hmB i j))
    (fun i j => (congrFun am _).trans (hmC i j)) hA hB hC
  let z' := z.extend slowBank a
  have solve : ExecWithin W (ThreeSum.Host.Slow.program.rename slowBank) a z'
      (39 * (n * (n * n)) + 9) := hz.rename slowBank_injective
  have reg (i : Fin 24) : z'.regs (slowBank i) = z.regs i :=
    slowBank_injective.extend_apply _ _ _
  let y := z'.set CallableFixedPrime.Reg.found (z'.regs Reg.result)
  have copy : ExecWithin (B := .standard) W
      (ram[ CallableFixedPrime.Reg.found ← Reg.result ]) z' y 1 := ExecWithin.copy
  have he : ExecWithin W slow x y (39 * (n * (n * n)) + 16) := by
    exact (ha.seq (solve.seq copy)).mono (le_of_eq (by ring))
  have yf : y.regs CallableFixedPrime.Reg.found = z.regs ThreeSum.Host.Slow.out :=
    (show y.regs CallableFixedPrime.Reg.found = z'.regs Reg.result from rfl).trans
      (reg ThreeSum.Host.Slow.out)
  refine ⟨y, he, yf.trans_le zbool, ?_, zm.trans am, ?_⟩
  · simpa only [yf] using ziff
  · intro j hj hneq
    have hs : (ThreeSum.Host.Slow.program.rename slowBank).Preserves j :=
      ThreeSum.Host.Slow.program.preserves_rename_of_forall_ne slowBank j (by
        intro i hi
        have h := congrArg (fun k : Fin 640 => k.val) hi
        have := i.isLt
        dsimp only [slowBank, Fin.val_castLE] at h
        omega)
    exact (show y.regs j = z'.regs j from Function.update_of_ne hneq _ _).trans
      ((solve.regs_eq hs).trans (ar j (by omega)))

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
