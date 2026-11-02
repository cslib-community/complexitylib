/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Input
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Width
public import Complexity.Computability.WordRAM.Width

/-!
# Original-input width admission for concrete prime selection

The physical threshold depends only on the original dimension, window parameter and weight
bound. It covers the actual counter at every candidate modulus and the selector's square
tests. No intermediate fit, primality list or counting execution is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- Counter admission plus sufficient width for all selector square tests. -/
@[expose] def admissionWidth (n D A : ℕ) : ℕ :=
  CountPrime.admissionWidth n (Nat.sqrt D) A + Nat.clog 2 (4 * (D + 2) * (D + 2) + 5)

/-- The threshold is positive, including for empty input matrices. -/
theorem admissionWidth_pos (n D A : ℕ) : 0 < admissionWidth n D A :=
  (CountPrime.admissionWidth_pos n (Nat.sqrt D) A).trans_le (Nat.le_add_right _ _)

/-- Every sufficiently wide physical machine executes the initialized concrete selector and
returns an attained minimum, with the actual original-input and outside-workspace frame. -/
theorem exec_input {W n D A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n D A ≤ W) :
    InputFits W (CountPrime.inputWords n D values) ∧
    ∃ y, ExecWithin W entryProgram (.init (CountPrime.inputWords n D values)) y
        (timeBound n D + 15) ∧
      y.regs Reg.found = 1 ∧
      Cslib.Algorithms.ExactTriangle.IsSelectedPrime
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0)
        D (y.regs Reg.best) ∧
      y.regs Reg.bestCount = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0)
        (y.regs Reg.best) ∧ y.Bounded W ∧
      ∀ d, d < 3 + 3 * (n * n) ∨
          CountPrime.memoryEnd n (Nat.sqrt D) (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (CountPrime.inputWords n D values) : Data 160).mem d := by
  obtain ⟨hmag, haddr⟩ := CountPrime.admission_fits n (Nat.sqrt D) A
  have hc : CountPrime.admissionWidth n (Nat.sqrt D) A ≤ W :=
    (Nat.le_add_right _ _).trans hW
  have hsquare : Fits (Nat.clog 2 (4 * (D + 2) * (D + 2) + 5))
      (4 * (D + 2) * (D + 2) + 4) :=
    (by omega : 4 * (D + 2) * (D + 2) + 4 < 4 * (D + 2) * (D + 2) + 5).trans_le
      (Nat.le_pow_clog (by decide) _)
  exact exec_input_at values hlen hD hv hmag
    (by simpa only [CountPrime.admissionWidth, Nat.add_assoc] using haddr)
    (by simpa only [CountPrime.admissionWidth, Nat.add_assoc] using hc)
    (hsquare.mono ((Nat.le_add_left _ _).trans hW))

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
