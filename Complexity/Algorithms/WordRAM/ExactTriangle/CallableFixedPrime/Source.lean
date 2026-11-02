/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime

/-!
# Complete fixed-prime execution with dirty source memory

The unchanged producer runs on arbitrary old registers and dirty remaining memory. Its actual
prepared prefix supplies the all-record controller. A proof-only reference state frames that
prefix against the canonical original input; it does not assert a zero external frame for the
real computation. Neither the reference state nor its readback is an algorithm input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Actual complete source execution from only the original input prefix. Old registers and
all remaining memory may be dirty. The reference prepared state is derived from the executed
producer, rather than supplied as a layout, run, answer or time certificate. -/
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
      ∃ y, ExecWithin (w + 2) FixedPrime.program initial y
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
  let V := fun q => values.getD q 0
  let canonical : Data 64 := .init (PreparationInput.input n (D m) g p values)
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.pos
  have hw : PreparationInput.width n (D m) g p A ≤ w + 2 := by
    have hr := FixedPrime.record_admitted hW
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  have header (q : ℕ) (hq : q < 5 + 3 * (n * n)) : initial.mem q = canonical.mem q :=
    hinput q hq
  have hf : Function.Injective RecordProduct.producerBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 320 => k.val) h)
  have hf' : Function.Injective RecordWitness.productBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 400 => k.val) h)
  have hf'' : Function.Injective FixedPrime.recordBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 416 => k.val) h)
  let c₀ := initial.comap FixedPrime.recordBank
  let b₀ := c₀.comap RecordWitness.productBank
  let a₀ := b₀.comap RecordProduct.producerBank
  obtain ⟨a, ha, hout⟩ := PreparationInput.exec_at values hlen a₀
    (by change initial.mem 1 = D m
        simpa [canonical, PreparationInput.input, Data.init] using header 1 (by omega))
    (by change initial.mem 2 = g
        simpa [canonical, PreparationInput.input, Data.init] using header 2 (by omega))
    (by change initial.mem 3 = n
        simpa [canonical, PreparationInput.input, Data.init] using header 3 (by omega))
    (by change initial.mem 4 = p
        simpa [canonical, PreparationInput.input, Data.init] using header 4 (by omega))
    (fun q hq => (header (5 + q) (by omega)).trans
      (PreparationInput.input_word n (D m) g p values q))
    (by omega) hDn hg hp0 hv hw
  have hend := hout.inputEnd_le_heap
  have haframe (q : ℕ) (hq : q < 5 + 3 * (n * n) ∨ a.regs Instances.heap ≤ q) :
      a.mem q = initial.mem q := by
    obtain ⟨-, -, -, -, -, hh, -, -, -, -, -, hframe⟩ := hout
    exact hframe q (by simpa only [hh] using hq)
  let reference : Data 64 := ⟨a.regs,
    fun q => if q < a.regs Instances.heap then a.mem q else canonical.mem q⟩
  have reference_mem (q : ℕ) (hq : q < a.regs Instances.heap) : reference.mem q = a.mem q :=
    ite_eq_left hq
  have reference_out : Instances.Output n (D m) g p V canonical reference :=
    hout.transfer V rfl (fun q hq => reference_mem q hq) (by
      intro q hq
      change (if q < a.regs Instances.heap then a.mem q else canonical.mem q) = canonical.mem q
      by_cases h : q < a.regs Instances.heap
      · rw [ite_eq_left h]
        have hin : q < 5 + 3 * (n * n) := by
          change _ ∨ a.regs Instances.heap ≤ q at hq
          omega
        exact (haframe q (Or.inl hin)).trans (header q hin)
      · rw [ite_eq_right h])
  have heap : reference.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A := by
    have hh := hout.heap_le_budget V (by omega) hDn hg
    change a.regs Instances.heap ≤ _
    unfold PreparationInput.wordBound PreparationInput.envelope
    omega
  let b := a.extend RecordProduct.producerBank b₀
  have hb : ExecWithin (w + 2) RecordProduct.produce b₀ b
      (RecordProduct.preparationTime n (D m) g p values - 1) := ha.rename hf
  let c := b.extend RecordWitness.productBank c₀
  have hc : ExecWithin (w + 2) RecordWitness.produce c₀ c
      (RecordProduct.preparationTime n (D m) g p values - 1) := hb.rename hf'
  let x := c.extend FixedPrime.recordBank initial
  have hx : ExecWithin (w + 2) FixedPrime.produce initial x
      (RecordProduct.preparationTime n (D m) g p values - 1) := hc.rename hf''
  have bank (j : Fin 64) : x.regs
      (FixedPrime.recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) =
        reference.regs j :=
    (hf''.extend_apply _ _ _).trans ((hf'.extend_apply _ _ _).trans (hf.extend_apply _ _ _))
  have hmem : Set.EqOn x.mem reference.mem (Set.Iio (reference.regs Instances.heap)) := by
    intro q hq
    exact (reference_mem q hq).symm
  obtain ⟨y, hy, yf, ys, yiff, yw, frame, -⟩ := FixedPrime.exec_traverse values hlen
    hD hg hp hN hv hW reference x reference_out bank hmem heap
  refine ⟨reference, reference_out, y, (hx.seq hy).mono ?_, yf, ys, yiff, yw, ?_⟩
  · dsimp only [FixedPrime.timeBound, V]
    omega
  · intro q hq
    have houtside : q < reference.regs Instances.heap ∨
        reference.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ q :=
      hq.elim (fun h => Or.inl (h.trans_le hend)) Or.inr
    apply (frame q houtside).trans
    apply haframe q
    change q < 5 + 3 * (n * n) ∨
      a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ q at hq
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
