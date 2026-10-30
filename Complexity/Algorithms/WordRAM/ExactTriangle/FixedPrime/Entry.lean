/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Loop

/-!
# Initialized fixed-prime ExactTriangle computation

The original input alone supplies scalar headers and canonical signed weights. The producer
runs once, its actual heap and occupied records feed the complete native traversal, and the
returned flag decides original ExactTriangle across every record. All fits follow from the
original numerical admission; no intermediate producer, layout or solver result is an input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- One real preparation followed by the entire actual fixed-prime traversal. Its structured
bound excludes the final halt, and retains the preparation charge separately from record work.
The physical width may be any larger admitted width. -/
theorem exec_input {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    InputFits (w + 2) (PreparationInput.input n (D m) g p values) ∧
    ∃ a : Data 64,
      ExecWithin (w + 2) Instances.program
        (.init (PreparationInput.input n (D m) g p values)) a
        (RecordProduct.preparationTime n (D m) g p values - 1) ∧
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      ∃ y, ExecWithin (w + 2) program
          (.init (PreparationInput.input n (D m) g p values)) y
          (RecordProduct.preparationTime n (D m) g p values +
            (∑ idx ∈ instanceIndices wAB (D m) g p, recordBase (m := m) hn V a.mem idx) +
            (42 * pieceSize (D m) g + 28) * (falsePositiveCount wAB wBC wAC p + 1) + 6) ∧
        y.Bounded (w + 2) ∧
        (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
        y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
        (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
        (y.regs Reg.found = 1 →
          y.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
          y.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
          y.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
          V (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
              y.regs (recordBank RecordWitness.Reg.witnessB)) +
            V (n * n + (y.regs (recordBank RecordWitness.Reg.witnessB) * n +
              y.regs (recordBank RecordWitness.Reg.witnessC))) +
            V (2 * (n * n) + (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
              y.regs (recordBank RecordWitness.Reg.witnessC))) = 0) ∧
        (∀ u, u < a.regs Instances.heap ∨
          a.regs Instances.heap + CallableProduct.windowSize n (n * n) ≤ u → y.mem u = a.mem u) ∧
        ∀ j : Fin 64, y.regs
          (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j := by
  let V := fun q => values.getD q 0
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.pos
  have hw : PreparationInput.width n (D m) g p A ≤ w + 2 := by
    have hr := record_admitted hW
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  obtain ⟨a, ha, hout, hinput, -⟩ := PreparationInput.exec_input values hlen
    (by omega) hDn hg hp0 hv hw
  have ha' : ExecWithin (w + 2) Instances.program
      (.init (PreparationInput.input n (D m) g p values)) a
      (RecordProduct.preparationTime n (D m) g p values - 1) := ha
  have hf : Function.Injective RecordProduct.producerBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 320 => k.val) h)
  have hf' : Function.Injective RecordWitness.productBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 400 => k.val) h)
  have hf'' : Function.Injective recordBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 416 => k.val) h)
  let x₀ : Data 320 := .init (PreparationInput.input n (D m) g p values)
  let b := a.extend RecordProduct.producerBank x₀
  have hb : ExecWithin (w + 2) RecordProduct.produce x₀ b
      (RecordProduct.preparationTime n (D m) g p values - 1) := ha'.rename hf
  let b₀ : Data 400 := .init (PreparationInput.input n (D m) g p values)
  let c := b.extend RecordWitness.productBank b₀
  have hc : ExecWithin (w + 2) RecordWitness.produce b₀ c
      (RecordProduct.preparationTime n (D m) g p values - 1) := hb.rename hf'
  let c₀ : Data 416 := .init (PreparationInput.input n (D m) g p values)
  let x := c.extend recordBank c₀
  have hx : ExecWithin (w + 2) produce c₀ x
      (RecordProduct.preparationTime n (D m) g p values - 1) := hc.rename hf''
  have bank (j : Fin 64) : x.regs
      (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j :=
    (hf''.extend_apply _ _ _).trans ((hf'.extend_apply _ _ _).trans (hf.extend_apply _ _ _))
  have mem : x.mem = a.mem := rfl
  have heap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A := by
    obtain ⟨t, ht, he⟩ := ha'
    have hr : Runs (w + 2) PreparationInput.flatProgram
        (State.init (PreparationInput.input n (D m) g p values)) ⟨Instances.program.size, a⟩ t := by
      simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
        (p := PreparationInput.flatProgram) (Program.Contains.self _).append_left
    exact ((PreparationInput.bounded_reachable values hlen (by omega) hDn hg hp0 hv hw
      ⟨Instances.program.size, a⟩ t hr).1 Instances.heap).le
  obtain ⟨y, hy, yf, ys, yiff, yw, frame, regs⟩ :=
    exec_traverse values hlen hD hg hp hN hv hW a x hout bank (fun _ _ => rfl) heap
  have hpos : 1 ≤ RecordProduct.preparationTime n (D m) g p values := by
    dsimp only [RecordProduct.preparationTime, Instances.timeBound]
    omega
  have hex : ExecWithin (w + 2) program
      (.init (PreparationInput.input n (D m) g p values)) y
      (RecordProduct.preparationTime n (D m) g p values +
        (∑ idx ∈ instanceIndices (fun u v : Fin n => V (pairIndex (u, v))) (D m) g p,
          recordBase (m := m) (lt_of_lt_of_le (by omega : 0 < D m) hDn) V a.mem idx) +
        (42 * pieceSize (D m) g + 28) *
          (falsePositiveCount (fun u v : Fin n => V (pairIndex (u, v)))
            (fun b c => V (n * n + pairIndex (b, c)))
            (fun u c => V (2 * (n * n) + pairIndex (u, c))) p + 1) + 6) :=
    (hx.seq hy).mono (by dsimp only [V]; omega)
  refine ⟨hinput, a, ha', hout, y, hex, hex.bounded (Data.Bounded.init hinput),
    yf, ys, yiff, yw, ?_, regs⟩
  simpa only [mem] using frame

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
