/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.First

/-!
# Initialized producer-to-adapter composition

One fixed native program runs the complete producer from its original four headers and three
signed weight arrays, selects actual ordinal zero and invokes the actual record consumer.
The general caller interface handles any occupied ordinal; the initialized client here chooses
the first one with real code. Its existence follows from the original positive geometry.

The producer's pre-halt native witness and polynomial word bound derive every source pointer,
coordinate, caller base and dirty-word bound used by the record consumer. No producer layout,
run, solver or time certificate is an input hypothesis.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The complete real producer, using its original low bank. -/
@[expose] def produce : Code .standard 320 := Instances.program.rename producerBank

/-- One fixed initialized composition; selecting the first record costs one actual instruction. -/
@[expose] def entryProgram : Code .standard 320 :=
  .seq produce (.seq (.op (.const Reg.ordinal 0)) program)

/-- The unchanged producer's original-header budget, including its standalone halt. -/
@[expose] def preparationTime (n D g p : ℕ) (values : List ℤ) : ℕ :=
  let C := fun rho => Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = rho) (n * n)
  Instances.timeBound n D p (ChunkCatalogue.before C (queryCap n D) p) (numPieces n D g)

private theorem producerBank_injective : Function.Injective producerBank := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 320 => k.val) h

/-- Complete initialized structured execution. The actual producer execution is a conclusion,
and its same native memory supplies the coordinate list consumed by the composed adapter. -/
theorem exec_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    InputFits W (PreparationInput.input n (D m) g p values) ∧
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64, ∃ idx : InstanceIndex p,
      ExecWithin W Instances.program (.init (PreparationInput.input n (D m) g p values)) a
        (preparationTime n (D m) g p values - 1) ∧
      idx ∈ instanceIndices (fun a b : Fin n => values.getD (pairIndex (a, b)) 0) (D m) g p ∧
      recordOrdinal n (D m) g p (fun q => values.getD q 0) idx = 0 ∧
      let qs := decodedQueries hn a.mem (recordQueries n (D m) p idx)
        (recordQueryCount n (D m) p (fun q => values.getD q 0) idx)
      ∃ y, ExecWithin W entryProgram (.init (PreparationInput.input n (D m) g p values)) y
          (preparationTime n (D m) g p values + timeBound (m := m) qs) ∧
        y.regs Reg.result = a.regs Instances.heap +
          QueriedProduct.outputBase (19 * m) m n qs.length ∧
        (∀ j : Fin qs.length,
          y.mem (a.regs Instances.heap +
            (QueriedProduct.outputBase (19 * m) m n qs.length + j.val)) =
            Signed.encode ((leftMatrix m n g p (fun q => values.getD q 0) idx *
              rightMatrix m n g p (fun q => values.getD q 0) idx) (qs.get j).1 (qs.get j).2)) ∧
        (∀ u, u < a.regs Instances.heap ∨
          a.regs Instances.heap + CallableProduct.windowSize n qs.length ≤ u →
          y.mem u = a.mem u) ∧
        (∀ j : Fin 64, y.regs (producerBank j) = a.regs j) ∧
        qs.length * 2 ^ m ≤ n ^ 2 := by
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hw : PreparationInput.width n (D m) g p A ≤ W := by
    unfold admissionWidth at hW
    omega
  obtain ⟨a, ha, houtput, hinput, abound⟩ := PreparationInput.exec_input values hlen
    (by omega) hDn hg hp hv hw
  have ha' : ExecWithin W Instances.program (.init (PreparationInput.input n (D m) g p values)) a
      (preparationTime n (D m) g p values - 1) := ha
  let x₀ : Data 320 := .init (PreparationInput.input n (D m) g p values)
  let x := a.extend producerBank x₀
  have hx : ExecWithin W produce x₀ x (preparationTime n (D m) g p values - 1) :=
    ha'.rename producerBank_injective
  obtain ⟨t, ht, he⟩ := ha'
  have hr : Runs W PreparationInput.flatProgram
      (State.init (PreparationInput.input n (D m) g p values))
      ⟨Instances.program.size, a⟩ t := by
    simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := PreparationInput.flatProgram) (Program.Contains.self _).append_left
  have hwords := PreparationInput.bounded_reachable values hlen (by omega) hDn hg hp hv hw
    ⟨Instances.program.size, a⟩ t hr
  obtain ⟨idx, hidx, hord⟩ := first_index (n := n) (D := D m) (g := g) (p := p)
    (fun q => values.getD q 0) hD hDn hg (by omega)
  let z := x.set Reg.ordinal 0
  have hz : ExecWithin (B := .standard) W (.op (.const Reg.ordinal 0)) x z 1 :=
    ExecWithin.const (fits_zero W)
  have zmap : z.comap producerBank = a := by
    ext j
    · change Function.update x.regs Reg.ordinal 0 (producerBank j) = a.regs j
      have hne : producerBank j ≠ Reg.ordinal := by
        intro heq
        have hh := congrArg Fin.val heq
        change j.val = 64 at hh
        omega
      rw [Function.update_of_ne hne]
      exact producerBank_injective.extend_apply _ _ j
    · rfl
  have hheap : z.regs 42 = a.regs Instances.heap := by
    exact congrArg (fun d : Data 64 => d.regs Instances.heap) zmap
  have hQ : recordQueryCount n (D m) p (fun q => values.getD q 0) idx ≤ n ^ 2 := by
    unfold recordQueryCount
    rw [pow_two]
    exact (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.count_le _))
  have hfit := physical_fits (b := z.regs 42) (n := n) (D := D m) (g := g) (p := p) (A := A)
    (Q := recordQueryCount n (D m) p (fun q => values.getD q 0) idx)
    (by rw [hheap]; exact (hwords.1 Instances.heap).le) hQ hW
  have zout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) (z.comap producerBank) := by
    rw [zmap]
    exact houtput
  obtain ⟨y, hy, yr, yv, yf, yg, yQ⟩ := exec_of_output (fun q => values.getD q 0)
    (.init (PreparationInput.input n (D m) g p values)) z zout hD hg (by omega) hN
    rfl rfl idx hidx (by
      simpa only [z, Data.set_regs, Function.update_self] using hord.symm) hfit
  have hmem : z.mem = a.mem := rfl
  simp only [hheap, hmem] at hy yr yv yf yQ
  refine ⟨hinput, a, idx, ⟨t, ht, he⟩, hidx, hord, y, ?_, yr, yv, yf, ?_, yQ⟩
  · have hpos : 1 ≤ preparationTime n (D m) g p values := by
      dsimp only [preparationTime, Instances.timeBound]
      omega
    exact (hx.seq (hz.seq hy)).mono (by omega)
  · intro j
    have hj : j.val < 64 := j.isLt
    rw [yg (producerBank j) (by change j.val < 65; omega)]
    exact congrArg (fun d : Data 64 => d.regs j) zmap

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
