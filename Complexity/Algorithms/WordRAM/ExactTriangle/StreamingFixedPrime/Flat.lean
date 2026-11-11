/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Source

/-!
# Initialized halting one-slot ExactTriangle solver

The real catalogue/setup prefix and streaming loop decide the original signed input. The
halt and prefix end in the same actual state. The existing all-record state appears only as
a derived mathematical index for the unchanged conservative time envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Actual initialized streaming execution, original-coordinate witness, exact negative
exhaustion and one global failure-scan allowance, including the charged final halt. -/
theorem runs_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : FixedPrime.admissionWidth n (D m) g p A ≤ W) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    InputFits W (PreparationInput.input n (D m) g p values) ∧
    ∃ a : Data 64,
      Instances.Output n (D m) g p V (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y t, t + 1 ≤ FixedPrime.timeBound (m := m) hn g p values a.mem ∧
        Runs W (program.program FixedPrime.Reg.found)
          (State.init (PreparationInput.input n (D m) g p values)) ⟨program.size, y⟩ t ∧
        Executes W (program.program FixedPrime.Reg.found)
          (State.init (PreparationInput.input n (D m) g p values))
          (y.regs FixedPrime.Reg.found) (t + 1) ∧
        y.Bounded W ∧ (y.regs FixedPrime.Reg.found = 0 ∨ y.regs FixedPrime.Reg.found = 1) ∧
        y.regs FixedPrime.Reg.scans ≤
          falsePositiveCount wAB wBC wAC p + y.regs FixedPrime.Reg.found ∧
        (y.regs FixedPrime.Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs FixedPrime.Reg.found = 1 → ∃ u v c : Fin n,
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA) = u.val ∧
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB) = v.val ∧
          y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC) = c.val ∧
          weightSum wAB wBC wAC u v c = 0) ∧
        (∀ u, u < 5 + 3 * (n * n) ∨
          a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ u →
          y.mem u = (Data.init (PreparationInput.input n (D m) g p values) : Data 416).mem u) := by
  have htwo : 2 ≤ W := by
    have hr := FixedPrime.record_admitted hW
    unfold RecordWitness.admissionWidth at hr
    omega
  have heq : W - 2 + 2 = W := Nat.sub_add_cancel htwo
  let input := PreparationInput.input n (D m) g p values
  have h := exec_source (w := W - 2) values hlen hD hg hp hN hv
    (by simpa only [heq] using hW) (Data.init input) (fun _ _ => rfl)
  rw [heq] at h
  obtain ⟨a, hout, y, he, yf, ys, yiff, yw, frame⟩ := h
  have hprep : PreparationInput.width n (D m) g p A ≤ W := by
    have hr := FixedPrime.record_admitted hW
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  have hinput : InputFits W input := (PreparationInput.input_fits values hlen hv).mono hprep
  obtain ⟨t, ht, hex⟩ := he
  have hpos : 1 ≤ FixedPrime.timeBound (m := m)
      (lt_of_lt_of_le (by omega : 0 < D m)
        ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)) g p values a.mem := by
    dsimp only [FixedPrime.timeBound, RecordProduct.preparationTime, Instances.timeBound]
    omega
  refine ⟨hinput, a, hout, y, t, ?_, ?_, ?_, ?_, yf, ys, yiff, ?_, frame⟩
  · omega
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := program.program FixedPrime.Reg.found) (Program.Contains.self _).append_left
  · simpa only [State.init] using hex.executes FixedPrime.Reg.found
  · exact hex.bounded (Data.Bounded.init hinput)
  · intro hf
    obtain ⟨ha, hb, hc, hz⟩ := yw hf
    exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl, rfl, rfl, hz⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
