/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Width

/-!
# Real initialized preparation for candidate recovery

This internal composition rule executes the existing producer on its complete renamed bank,
then selects ordinal zero with one real instruction. Nonemptiness and the producer's original
word bound are derived from the original input and actual execution. No prepared catalogue,
index, run or intermediate fit certificate is an input to this rule.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual preparation and charged first-record selection, from the original initialized
input. All later structured/flat clients reuse this same producer state and selected record. -/
theorem prepare_input {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2) :
    InputFits (w + 2) (PreparationInput.input n (D m) g p values) ∧
      ∃ a : Data 64, ∃ idx : InstanceIndex p, ∃ z : Data 400,
        ExecWithin (w + 2) Instances.program
          (.init (PreparationInput.input n (D m) g p values)) a
          (RecordProduct.preparationTime n (D m) g p values - 1) ∧
        Instances.Output n (D m) g p (fun q => values.getD q 0)
          (.init (PreparationInput.input n (D m) g p values)) a ∧
        idx ∈ instanceIndices (fun a b : Fin n => values.getD (pairIndex (a, b)) 0) (D m) g p ∧
        RecordProduct.recordOrdinal n (D m) g p (fun q => values.getD q 0) idx = 0 ∧
        ExecWithin (w + 2)
          (.seq produce (.op (.const (productBank RecordProduct.Reg.ordinal) 0)))
          (.init (PreparationInput.input n (D m) g p values)) z
          (RecordProduct.preparationTime n (D m) g p values) ∧
        (z.comap productBank).comap RecordProduct.producerBank = a ∧
        z.regs (productBank RecordProduct.Reg.ordinal) = 0 ∧
        z.regs (productBank 42) ≤ PreparationInput.wordBound n (D m) g p A := by
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hw : PreparationInput.width n (D m) g p A ≤ w + 2 := by
    unfold admissionWidth RecordProduct.admissionWidth at hW
    omega
  obtain ⟨a, ha, hout, hi, -⟩ := PreparationInput.exec_input values hlen
    (by omega) hDn hg hp hv hw
  have ha' : ExecWithin (w + 2) Instances.program
      (.init (PreparationInput.input n (D m) g p values)) a
      (RecordProduct.preparationTime n (D m) g p values - 1) := ha
  have hf : Function.Injective RecordProduct.producerBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 320 => k.val) h)
  have hf' : Function.Injective productBank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 400 => k.val) h)
  let x₀ : Data 320 := .init (PreparationInput.input n (D m) g p values)
  let x := a.extend RecordProduct.producerBank x₀
  have hx : ExecWithin (w + 2) RecordProduct.produce x₀ x
      (RecordProduct.preparationTime n (D m) g p values - 1) := ha'.rename hf
  let y₀ : Data 400 := .init (PreparationInput.input n (D m) g p values)
  let y := x.extend productBank y₀
  have hy : ExecWithin (w + 2) produce y₀ y
      (RecordProduct.preparationTime n (D m) g p values - 1) := hx.rename hf'
  let z := y.set (productBank RecordProduct.Reg.ordinal) 0
  have hz : ExecWithin (B := .standard) (w + 2)
      (.op (.const (productBank RecordProduct.Reg.ordinal) 0)) y z 1 :=
    ExecWithin.const (fits_zero _)
  have low (j : Fin 64) : y.regs (productBank (RecordProduct.producerBank j)) = a.regs j :=
    (hf'.extend_apply _ _ _).trans (hf.extend_apply _ _ _)
  have zmap : (z.comap productBank).comap RecordProduct.producerBank = a := by
    ext j
    · change Function.update y.regs (productBank RecordProduct.Reg.ordinal) 0
        (productBank (RecordProduct.producerBank j)) = a.regs j
      have hne : productBank (RecordProduct.producerBank j) ≠
          productBank RecordProduct.Reg.ordinal := by
        intro he
        have hh := congrArg (fun k : Fin 400 => k.val) he
        change j.val = 64 at hh
        omega
      rw [Function.update_of_ne hne]
      exact low j
    · rfl
  obtain ⟨idx, hidx, hord⟩ := RecordProduct.first_index (fun q => values.getD q 0)
    hD hDn hg (by omega : p ≠ 0)
  obtain ⟨t, ht, he⟩ := ha'
  have hr : Runs (w + 2) PreparationInput.flatProgram
      (State.init (PreparationInput.input n (D m) g p values))
      ⟨Instances.program.size, a⟩ t := by
    simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := PreparationInput.flatProgram) (Program.Contains.self _).append_left
  have hb := PreparationInput.bounded_reachable values hlen (by omega) hDn hg hp hv hw
    ⟨Instances.program.size, a⟩ t hr
  refine ⟨hi, a, idx, z, ⟨t, ht, he⟩, hout, hidx, hord, ?_, zmap, rfl, ?_⟩
  · have hpos : 1 ≤ RecordProduct.preparationTime n (D m) g p values := by
      dsimp only [RecordProduct.preparationTime, Instances.timeBound]
      omega
    exact (hy.seq hz).mono (by omega)
  · have hheap : z.regs (productBank 42) = a.regs Instances.heap :=
      congrArg (fun d : Data 64 => d.regs Instances.heap) zmap
    rw [hheap]
    exact (hb.1 Instances.heap).le

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
