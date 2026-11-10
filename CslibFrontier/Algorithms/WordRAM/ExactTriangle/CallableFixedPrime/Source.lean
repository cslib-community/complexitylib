/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Program
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Source

/-!
# Complete box-backed fixed-prime execution with dirty source memory

The actual catalogue/setup prefix feeds the one-slot streaming loop on arbitrary dirty
registers and remaining memory. A derived all-record reference is used only for mathematical
indexing and the conservative old time envelope; the reused slot never claims its Output.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Actual complete source execution from only the original input prefix. Old registers and
all remaining memory may be dirty. The genuine standalone reference is derived alongside the shared
catalogue prefix, rather than supplied as a layout, run, answer or time certificate. -/
theorem exec_source {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : FixedPrime.admissionWidth n (D m) g p A ≤ w + 2)
    (initial : Data 416)
    (hinput : ∀ q < 5 + 3 * (n * n), initial.mem q =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem q) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64,
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y, ExecWithin (w + 2) StreamingFixedPrime.program initial y
          (FixedPrime.timeBound (m := m) hn g p values a.mem) ∧
        (y.regs FixedPrime.Reg.found = 0 ∨ y.regs FixedPrime.Reg.found = 1) ∧
        y.regs FixedPrime.Reg.scans ≤ falsePositiveCount wAB wBC wAC p +
          y.regs FixedPrime.Reg.found ∧
        (y.regs FixedPrime.Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs FixedPrime.Reg.found = 1 →
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) < n ∧
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) < n ∧
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC) < n ∧
          V (y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) * n +
              y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB)) +
            V (n * n + (y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) * n +
              y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC))) +
            V (2 * (n * n) + (y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) * n +
              y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC))) = 0) ∧
        ∀ q, q < 5 + 3 * (n * n) ∨
          a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ q →
          y.mem q = initial.mem q := by
  obtain ⟨a, hout, y, hy, yf, ys, yiff, yw, frame⟩ :=
    StreamingFixedPrime.exec_source values hlen hD hg hp hN hv hW initial hinput
  exact ⟨a, hout, y, hy.mono (Nat.sub_le _ _), yf, ys, yiff, yw, frame⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
