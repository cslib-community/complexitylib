/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Entry

/-!
# Initialized halting fixed-prime ExactTriangle decision

The actual fixed 416-register standard-native program decides the original signed input at
every admitted physical width. Its prefix witness and halt share the same state, which retains
the original-coordinate witness on success and a single global failure-scan bound. Global
parameter/prime selection and the final source exponent are not supplied by this component.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Actual one-time preparation, all occupied record charges, one global failed-scan budget,
and all controller/loop/halt work. No whole-window initialization is charged or performed. -/
@[expose] noncomputable def timeBound {m n : ℕ} (hn : 0 < n) (g p : ℕ)
    (values : List ℤ) (mem : ℕ → ℕ) : ℕ :=
  let V := fun q => values.getD q 0
  let wAB := fun u v : Fin n => V (pairIndex (u, v))
  let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
  let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
  RecordProduct.preparationTime n (D m) g p values +
    (∑ idx ∈ instanceIndices wAB (D m) g p, recordBase (m := m) hn V mem idx) +
    (42 * pieceSize (D m) g + 28) * (falsePositiveCount wAB wBC wAC p + 1) + 7

/-- Same-state prefix and charged halt, with exact original positive and negative ET decisions.
All geometric, prime, original-input and every-wide-width premises are explicit. -/
theorem runs_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    InputFits W (PreparationInput.input n (D m) g p values) ∧
    ∃ a : Data 64,
      ExecWithin W Instances.program (.init (PreparationInput.input n (D m) g p values)) a
        (RecordProduct.preparationTime n (D m) g p values - 1) ∧
      Instances.Output n (D m) g p V (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y t, t + 1 ≤ timeBound (m := m) hn g p values a.mem ∧
        Runs W (program.program Reg.found)
          (State.init (PreparationInput.input n (D m) g p values)) ⟨program.size, y⟩ t ∧
        Executes W (program.program Reg.found)
          (State.init (PreparationInput.input n (D m) g p values)) (y.regs Reg.found) (t + 1) ∧
        y.Bounded W ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
        y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
        (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs Reg.found = 1 → ∃ u v c : Fin n,
          y.regs (recordBank RecordWitness.Reg.witnessA) = u.val ∧
          y.regs (recordBank RecordWitness.Reg.witnessB) = v.val ∧
          y.regs (recordBank RecordWitness.Reg.witnessC) = c.val ∧
          weightSum wAB wBC wAC u v c = 0) ∧
        (∀ u, u < a.regs Instances.heap ∨
          a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ u → y.mem u = a.mem u) ∧
        ∀ j : Fin 64, y.regs
          (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j := by
  have htwo : 2 ≤ W := by
    have hr := record_admitted hW
    unfold RecordWitness.admissionWidth at hr
    omega
  have heq : W - 2 + 2 = W := Nat.sub_add_cancel htwo
  have h := exec_input (w := W - 2) values hlen hD hg hp hN hv
    (by simpa only [heq] using hW)
  rw [heq] at h
  obtain ⟨hi, a, ha, hout, y, he, yb, yf, ys, yiff, yw, frame, regs⟩ := h
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, a, ha, hout, y, t, ?_, ?_, ?_, yb, yf, ys, yiff, ?_, frame, regs⟩
  · simpa only [timeBound, Nat.add_assoc] using Nat.add_le_add_right ht 1
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := program.program Reg.found) (Program.Contains.self _).append_left
  · simpa only [State.init] using hex.executes Reg.found
  · intro hf
    obtain ⟨ha, hb, hc, hz⟩ := yw hf
    exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl, rfl, rfl, hz⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
