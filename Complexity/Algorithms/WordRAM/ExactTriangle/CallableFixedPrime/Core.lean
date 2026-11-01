/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Source
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Parameters
public import Complexity.Computability.WordRAM.MemoryWindow

/-!
# Actual translated fixed-prime solver execution

This internal stage composes the proved original-input source execution with the existing
memory-window compiler. The caller's real setup supplies normalized source registers and the
computed modulus. No source execution, list of records, readback, solver or time contract is
a premise. Dirty physical memory is clipped by each translated load itself.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Canonical original inputs fit the width computed from a bounding raw-word sum. -/
theorem input_fits_source {m n g p total : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ total) :
    InputFits (sourceWidth n (D m) g p total)
      (PreparationInput.input n (D m) g p values) := by
  have hr := FixedPrime.record_admitted (source_admission n (D m) g p total)
  have hprep : PreparationInput.width n (D m) g p total ≤ sourceWidth n (D m) g p total := by
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  exact (PreparationInput.input_fits values hlen hv).mono hprep

/-- Translate the actual complete source computation into its dirty physical window. Source
register fits here are an internal setup postcondition, not a final caller admission premise.
The one global scan allowance and both positive/negative decisions are preserved exactly. -/
theorem exec_compiled {W b m n g p total : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ total)
    (x : Data 419) (hb : x.regs MemoryWindow.Reg.base = b)
    (hm : x.regs MemoryWindow.Reg.modulus = windowSize n (D m) g p total)
    (hregs : ∀ i : Fin 416, Fits (sourceWidth n (D m) g p total) (x.regs (i.castAdd 3)))
    (hinput : ∀ q < 5 + 3 * (n * n), x.mem (b + q) =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem q)
    (hw : sourceWidth n (D m) g p total ≤ W)
    (hfit : Fits W (b + windowSize n (D m) g p total)) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64,
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y, ExecWithin W (MemoryWindow.compile FixedPrime.program) x y
          (3 * FixedPrime.timeBound (m := m) hn g p values a.mem) ∧
        (y.regs (FixedPrime.Reg.found.castAdd 3) = 0 ∨
          y.regs (FixedPrime.Reg.found.castAdd 3) = 1) ∧
        y.regs (FixedPrime.Reg.scans.castAdd 3) ≤ falsePositiveCount wAB wBC wAC p +
          y.regs (FixedPrime.Reg.found.castAdd 3) ∧
        (y.regs (FixedPrime.Reg.found.castAdd 3) = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs (FixedPrime.Reg.found.castAdd 3) = 1 →
          y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessA).castAdd 3) < n ∧
          y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessB).castAdd 3) < n ∧
          y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessC).castAdd 3) < n ∧
          V (y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessA).castAdd 3) * n +
              y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessB).castAdd 3)) +
            V (n * n + (y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessB).castAdd 3) * n +
              y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessC).castAdd 3))) +
            V (2 * (n * n) +
              (y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessA).castAdd 3) * n +
              y.regs ((FixedPrime.recordBank RecordWitness.Reg.witnessC).castAdd 3))) = 0) ∧
        ∀ q, q < b ∨ b + windowSize n (D m) g p total ≤ q → y.mem q = x.mem q := by
  let v := MemoryWindow.view (sourceWidth n (D m) g p total) b x
  have vb := MemoryWindow.view_bounded (sourceWidth n (D m) g p total) b x hregs
  have hi := Data.Bounded.init (r := 64)
    (input_fits_source (m := m) (g := g) (p := p) values hlen hv)
  have vi (q : ℕ) (hq : q < 5 + 3 * (n * n)) : v.mem q =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem q := by
    change x.mem (b + q) % 2 ^ sourceWidth n (D m) g p total = _
    rw [hinput q hq, Nat.mod_eq_of_lt (hi.2 q)]
  have htwo : sourceWidth n (D m) g p total - 2 + 2 = sourceWidth n (D m) g p total :=
    Nat.sub_add_cancel (by have := sourceWidth_two_lt n (D m) g p total; omega)
  have hs := exec_source (w := sourceWidth n (D m) g p total - 2) values hlen hD hg hp hN hv
    (by simpa only [htwo] using source_admission n (D m) g p total) v vi
  rw [htwo] at hs
  obtain ⟨a, hout, z, hz, zf, zs, ziff, zw, -⟩ := hs
  obtain ⟨y, hy, hm', hf⟩ := MemoryWindow.execWithin hz FixedPrime.program_not_readsWidth
    vb (show MemoryWindow.Matches (sourceWidth n (D m) g p total) b v x from
      ⟨rfl, hb, hm⟩) hw hfit
  refine ⟨a, hout, y, hy, ?_, ?_, ?_, ?_, hf⟩
  · simpa only [hm'.regs] using zf
  · simpa only [hm'.regs] using zs
  · simpa only [hm'.regs] using ziff
  · simpa only [hm'.regs] using zw

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
