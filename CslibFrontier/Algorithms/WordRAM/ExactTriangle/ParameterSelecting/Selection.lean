/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Properties
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Exec
import CslibFrontier.Computability.WordRAM.Call

/-!
# Complete concrete prime selection within the assembled solver

The whole160-register selector, including actual primality tests and cyclic-Strassen calls,
executes on the original matrices. The saved magnitude and all computed parameters survive.
Admission here is the existing original-scalar numerical stage admission, not a counting or
execution contract; the complete caller derives it from its original-input threshold.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Execute actual counting-based selection and retain all saved original/parameter registers. -/
theorem exec_selectPrime {w W n D b ap bp cp F : ℕ} (x : Data 640) (u v z : ℕ → ℤ)
    (hD : 16 ≤ D) (hn : x.regs (selectorBank PrimeSelection.Reg.side) = n)
    (hd : x.regs (selectorBank PrimeSelection.Reg.window) = D)
    (ha : x.regs (selectorBank PrimeSelection.Reg.inputAB) = ap)
    (hb : x.regs (selectorBank PrimeSelection.Reg.inputBC) = bp)
    (hc : x.regs (selectorBank PrimeSelection.Reg.inputAC) = cp)
    (hs : x.regs (selectorBank PrimeSelection.Reg.scratch) = b)
    (haEnd : ap + n * n ≤ b) (hbEnd : bp + n * n ≤ b) (hcEnd : cp + n * n ≤ b)
    (hu : ∀ i < n * n, (u i).natAbs ≤ F)
    (hv : ∀ i < n * n, (v i).natAbs ≤ F)
    (hz : ∀ i < n * n, (z i).natAbs ≤ F)
    (hinU : ∀ i < n * n, x.mem (ap + i) = Signed.encode (u i))
    (hinV : ∀ i < n * n, x.mem (bp + i) = Signed.encode (v i))
    (hinZ : ∀ i < n * n, x.mem (cp + i) = Signed.encode (z i))
    (hmag : GenericRAM.Signed.Fits w
      (CountPrime.magnitudeBudget (Nat.sqrt D) (Nat.clog 2 n) F : ℤ))
    (hw : Fits (w + 2) (CountPrime.addressBudget n (Nat.sqrt D) (Nat.clog 2 n) b ap bp cp))
    (hwidth : w + 2 ≤ W) (hctrl : Fits W (4 * (D + 2) * (D + 2) + 4)) :
    ∃ y, ExecWithin W selectPrime x y (PrimeSelection.timeBound n D) ∧
      IsSelectedPrime (fun i j : Fin n => u (i.val * n + j.val))
        (fun i j => v (i.val * n + j.val)) (fun i j => z (i.val * n + j.val)) D
        (y.regs (selectorBank PrimeSelection.Reg.best)) ∧
      y.regs (selectorBank PrimeSelection.Reg.bestCount) = countZeroMod
        (fun i j : Fin n => u (i.val * n + j.val))
        (fun i j => v (i.val * n + j.val)) (fun i j => z (i.val * n + j.val))
        (y.regs (selectorBank PrimeSelection.Reg.best)) ∧
      (∀ q, q < b ∨ CountPrime.memoryEnd n (Nat.sqrt D) (Nat.clog 2 n) b ≤ q →
        y.mem q = x.mem q) ∧
      ∀ j : Fin 640, 143 ≤ j.val → y.regs j = x.regs j := by
  obtain ⟨y, hy, ⟨_, hp, hcount, frame, regs⟩, outside⟩ :=
    ExecWithin.rename_post selectorBank_injective (PrimeSelection.exec (x.comap selectorBank)
      u v z hD hn hd ha hb hc hs haEnd hbEnd hcEnd hu hv hz hinU hinV hinZ hmag hw hwidth hctrl)
  refine ⟨y, hy, hp, hcount, frame, ?_⟩
  intro j hj
  by_cases hlt : j.val < 160
  · let i : Fin 160 := ⟨j.val, hlt⟩
    have hi : selectorBank i = j := Fin.ext rfl
    rw [← hi]
    exact regs i (Or.inr hj)
  · exact outside j (by
      intro i hi
      have hv := congrArg Fin.val hi
      have := i.isLt
      change i.val = j.val at hv
      omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
