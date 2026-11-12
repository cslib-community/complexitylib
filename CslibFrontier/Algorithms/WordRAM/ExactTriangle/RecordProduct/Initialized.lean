/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.First
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.NumericBounds
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Program
import CslibFrontier.Computability.WordRAM.Sequence

/-!
# Initialized native preparation of the first record

`prepare_first_input` runs the actual producer and selects ordinal zero with one instruction.
Its `InitializedFirstRecord` certificate supplies the original producer run, the selected native
state and the input-derived physical fit to either record-product adapter. The certificate's
`exec_consumer` and `producer_frame` rules compose a consumer without repeating preparation or
register-bank reasoning. Product correctness and the consumer's time bound remain its own work.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The producer's low bank embeds its registers injectively. -/
theorem producerBank_injective : Function.Injective producerBank :=
  Fin.castLE_injective (by decide)

/-- An actual initialized producer run followed by the selection of its first occupied record.
The same native memory and low register bank are available to either record-product adapter. -/
structure InitializedFirstRecord (W m n g p : ℕ) (values : List ℤ) where
  /-- The actual producer's pre-halt state. -/
  producer : Data 64
  /-- The occupied record selected by ordinal zero. -/
  index : InstanceIndex p
  /-- The extended native state after the real ordinal-selection instruction. -/
  state : Data 320
  /-- The producer ran from the original headers and signed weights. -/
  producerExec : ExecWithin W Instances.program
    (.init (PreparationInput.input n (D m) g p values)) producer
    (preparationTime n (D m) g p values - 1)
  /-- The selected record belongs to the producer's instance list. -/
  index_mem : index ∈
    instanceIndices (fun a b : Fin n => values.getD (pairIndex (a, b)) 0) (D m) g p
  /-- Its actual ordinal is zero. -/
  ordinal_zero : recordOrdinal n (D m) g p (fun q => values.getD q 0) index = 0
  /-- Preparation includes the producer and the charged ordinal-selection instruction. -/
  exec_prefix : ExecWithin W (.seq produce (.op (.const Reg.ordinal 0)))
    (.init (PreparationInput.input n (D m) g p values)) state
    (preparationTime n (D m) g p values)
  /-- Selection preserves the complete producer bank and memory. -/
  comap_eq : state.comap producerBank = producer
  /-- The consumer sees a genuine producer output in that same state. -/
  output : Instances.Output n (D m) g p (fun q => values.getD q 0)
    (.init (PreparationInput.input n (D m) g p values)) (state.comap producerBank)
  /-- The consumer's ordinal register selects the occupied record. -/
  selected : state.regs Reg.ordinal =
    recordOrdinal n (D m) g p (fun q => values.getD q 0) index
  /-- Original input bounds cover the selected record's physical product window. -/
  fits : Fits W (2 * state.regs 42 +
    4 * CallableProduct.windowSize n
      (recordQueryCount n (D m) p (fun q => values.getD q 0) index) + 1024)

variable {W m n g p : ℕ} {values : List ℤ}

/-- The selected state retains the producer's heap pointer. -/
theorem InitializedFirstRecord.heap_eq (ready : InitializedFirstRecord W m n g p values) :
    ready.state.regs 42 = ready.producer.regs Instances.heap :=
  congrArg (fun d : Data 64 => d.regs Instances.heap) ready.comap_eq

/-- The selected state retains the producer's actual memory, including dirty unused words. -/
theorem InitializedFirstRecord.mem_eq (ready : InitializedFirstRecord W m n g p values) :
    ready.state.mem = ready.producer.mem :=
  congrArg Data.mem ready.comap_eq

/-- Append a certified consumer to the original initialized producer and ordinal selection.
The preparation budget already includes the selection instruction. -/
theorem InitializedFirstRecord.exec_consumer (ready : InitializedFirstRecord W m n g p values)
    {consumer : Code .standard 320} {y : Data 320} {T : ℕ}
    (hy : ExecWithin W consumer ready.state y T) :
    ExecWithin W (.seq produce (.seq (.op (.const Reg.ordinal 0)) consumer))
      (.init (PreparationInput.input n (D m) g p values)) y
      (preparationTime n (D m) g p values + T) :=
  ExecWithin.seq_assoc.mp (ready.exec_prefix.seq hy)

/-- A consumer preserving the low 65 registers retains the complete original producer bank. -/
theorem InitializedFirstRecord.producer_frame (ready : InitializedFirstRecord W m n g p values)
    {y : Data 320} (hy : ∀ j : Fin 320, j.val < 65 → y.regs j = ready.state.regs j) :
    ∀ j : Fin 64, y.regs (producerBank j) = ready.producer.regs j := by
  intro j
  rw [hy (producerBank j) (by change j.val < 65; omega)]
  exact congrArg (fun d : Data 64 => d.regs j) ready.comap_eq

/-- Produce the first actual occupied record from original input alone. No layout, native run,
selected index or intermediate physical-fit certificate is an input hypothesis. -/
theorem prepare_first_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    InputFits W (PreparationInput.input n (D m) g p values) ∧
      Nonempty (InitializedFirstRecord W m n g p values) := by
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hw : PreparationInput.width n (D m) g p A ≤ W := by
    unfold admissionWidth at hW
    omega
  obtain ⟨a, ha, houtput, hinput, -⟩ := PreparationInput.exec_input values hlen
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
  have hheap : z.regs 42 = a.regs Instances.heap :=
    congrArg (fun d : Data 64 => d.regs Instances.heap) zmap
  have hQ : recordQueryCount n (D m) p (fun q => values.getD q 0) idx ≤ n ^ 2 := by
    unfold recordQueryCount
    rw [pow_two]
    exact (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.count_le _))
  have hfit := physical_fits (b := z.regs 42) (n := n) (D := D m) (g := g) (p := p) (A := A)
    (Q := recordQueryCount n (D m) p (fun q => values.getD q 0) idx)
    (by rw [hheap]; exact (hwords.1 Instances.heap).le) hQ hW
  refine ⟨hinput, ⟨{
    producer := a
    index := idx
    state := z
    producerExec := ⟨t, ht, he⟩
    index_mem := hidx
    ordinal_zero := hord
    exec_prefix := ?_
    comap_eq := zmap
    output := by rw [zmap]; exact houtput
    selected := by simpa only [z, Data.set_regs, Function.update_self] using hord.symm
    fits := hfit }⟩⟩
  have hpos : 1 ≤ preparationTime n (D m) g p values := by
    dsimp only [preparationTime, Instances.timeBound]
    omega
  exact (hx.seq hz).mono (by omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
