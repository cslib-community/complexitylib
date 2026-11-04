/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (supplied branch witness and concrete Backend regressions)

public import Complexity.Computability.WordRAM.Realization.Branch
public import Complexity.Computability.WordRAM.Realization.Backend
public import Complexity.Computability.WordRAM.Realization.Primitive

/-! One fixed native conditional selects between two allocating arms. The shared Backend keeps
the supplied two-word scratch bank and factor six. Both paths retain the complete dirty memory
update, frontier and live arguments; their admission is only that of the selected allocation.
These are body executions: argument delivery, host observation and halt are not charged. -/

@[expose] public section

namespace ComplexityTests.WordRAMRealizationBranchWitness

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

abbrev Input := Fin 3 → ℕ
abbrev input : Input ↪ Input := .refl _
abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

def allocatingBranch := Realizes.Witness.branch (.eq 0 1)
  (Realizes.allocWitness input 1) (Realizes.allocWitness input 2)

def certificates (_ : Unit) : Certificate .exact := ⟨allocatingBranch⟩

-- Each arm needs two auxiliary words, but only their maximum is reserved.
example : allocatingBranch.scratchSize = 2 := rfl
example : allocatingBranch.factor = 6 := rfl
example (d : Input) (s : Memory.State) : (certificates ()).work d s = 2 := by
  change (if test (.eq 0 1) d then 0 else 0) + 2 = 2
  split <;> rfl

/-- The supplied branch packs into eight registers through the existing Backend. -/
theorem registers_eq : Backend.registers certificates = 8 := by decide
private theorem factor_eq : Backend.factor certificates = 6 := by decide

-- The previous sum reservation would use ten registers in this same Backend layout:
-- three inputs, one result, four auxiliary words, one extra word and the frontier.
example : Backend.registers certificates + 2 = 3 + (1 + (2 + 2) + 1) + 1 := by
  rw [registers_eq]

-- The constructor also handles a zero-scratch alternative without adding its scratch twice.
example : (Realizes.Witness.branch (.eq 0 1)
    (Realizes.allocWitness input 1) (Realizes.readWitness (B := .exact) input 2)).scratchSize = 2 :=
  rfl

private def count (d : Input) : ℕ := if d 0 = d 1 then d 1 else d 2

private theorem program_eq (d : Input) : (certificates ()).prog d = Memory.alloc (count d) := by
  change (if d 0 = d 1 then Memory.alloc (d 1) else Memory.alloc (d 2)) = _
  unfold count
  split <;> rfl

private noncomputable abbrev frontier := Backend.frontier certificates
private noncomputable abbrev outputReg := Backend.tmp certificates () 0

-- This uses the same fixed body and generic execution theorem at every width and runtime input.
private theorem runs {w : ℕ} (d : Input) (x : Data (Backend.registers certificates))
    (hx : x.Bounded w) (hin : ∀ i, Fits w (d i))
    (hv : Fits w (x.regs frontier + count d)) :
    ∃ y n, Exec w (Backend.code certificates ()) (Backend.install certificates () d x) y n ∧
      n ≤ 6 * (count d + 4) ∧
      y.mem = clear x.mem (x.regs frontier) (count d) ∧
      y.regs frontier = x.regs frontier + count d ∧
      y.regs outputReg = x.regs frontier ∧ y.Bounded w ∧
      (∀ i, y.regs (Backend.src certificates () i) =
        (Backend.install certificates () d x).regs (Backend.src certificates () i)) := by
  have hvalid : (Memory.spec w).ValidHistory (memoryState frontier x)
      ((Memory.spec w).clientHistory (memoryState frontier x) ((certificates ()).prog d)) := by
    rw [program_eq]
    exact ⟨hv, trivial⟩
  have hsafe : (certificates ()).safe w d (memoryState frontier x) := by
    change if test (.eq 0 1) d then True else True
    split <;> trivial
  obtain ⟨y, n, he, hn, hm, hout, hy, hframe⟩ :=
    Backend.exists_exec_frame certificates () d hx hin hsafe hvalid
  rw [program_eq] at hn hm hout
  have hwork : (certificates ()).work d (memoryState frontier x) = 2 := by
    change (if test (.eq 0 1) d then 0 else 0) + 2 = 2
    split <;> rfl
  rw [factor_eq, hwork] at hn
  change n ≤ 6 * ((count d + 1) + 2 + 1) at hn
  change memoryState frontier y =
    ⟨clear x.mem (x.regs frontier) (count d), x.regs frontier + count d⟩ at hm
  have ho := hout (0 : Fin 1)
  change y.regs outputReg = x.regs frontier at ho
  refine ⟨y, n, he, by omega, congrArg Memory.State.mem hm,
    congrArg Memory.State.frontier hm, ho, hy, ?_⟩
  intro i
  exact hframe _ (Backend.src_ne_frontier certificates () i)
    (fun j => (Backend.src_ne_tmp certificates () () i j).symm)

private noncomputable def dirty : Data (Backend.registers certificates) :=
  ⟨fun _ => 1, fun _ => 3⟩

private theorem dirty_bounded : dirty.Bounded 2 := by
  constructor
  · intro i; change Fits 2 1; decide
  · intro a; change Fits 2 3; decide

-- Equal selector/left count: allocate one cell, retaining the next dirty cell and all others.
example : ∃ y n, Exec 2 (Backend.code certificates ())
      (Backend.install certificates () ![1, 1, 2] dirty) y n ∧ n ≤ 30 ∧
      y.mem = clear dirty.mem 1 1 ∧ y.regs frontier = 2 ∧ y.regs outputReg = 1 ∧
      y.mem 1 = 0 ∧ y.mem 2 = 3 ∧ y.mem 9 = 3 := by
  obtain ⟨y, n, he, hn, hm, hf, ho, -, -⟩ :=
    runs ![1, 1, 2] dirty dirty_bounded (by intro i; fin_cases i <;> decide) (by decide)
  exact ⟨y, n, he, hn, hm, hf, ho, by rw [hm]; decide,
    by rw [hm]; decide, by rw [hm]; decide⟩

-- Unequal selector/left count: the SAME body allocates two cells instead.
example : ∃ y n, Exec 2 (Backend.code certificates ())
      (Backend.install certificates () ![0, 1, 2] dirty) y n ∧ n ≤ 36 ∧
      y.mem = clear dirty.mem 1 2 ∧ y.regs frontier = 3 ∧ y.regs outputReg = 1 ∧
      y.mem 1 = 0 ∧ y.mem 2 = 0 ∧ y.mem 9 = 3 := by
  obtain ⟨y, n, he, hn, hm, hf, ho, -, -⟩ :=
    runs ![0, 1, 2] dirty dirty_bounded (by intro i; fin_cases i <;> decide) (by decide)
  exact ⟨y, n, he, hn, hm, hf, ho, by rw [hm]; decide,
    by rw [hm]; decide, by rw [hm]; decide⟩

-- The unused allocation count fits as an input word, but its end address does not fit.
example : ¬ Fits 2 (1 + 3) := by decide

example : ∃ y n, Exec 2 (Backend.code certificates ())
      (Backend.install certificates () ![1, 1, 3] dirty) y n ∧
      y.mem = clear dirty.mem 1 1 ∧ y.regs frontier = 2 := by
  obtain ⟨y, n, he, -, hm, hf, -, -, -⟩ :=
    runs ![1, 1, 3] dirty dirty_bounded (by intro i; fin_cases i <;> decide) (by decide)
  exact ⟨y, n, he, hm, hf⟩

example : ∃ y n, Exec 2 (Backend.code certificates ())
      (Backend.install certificates () ![0, 3, 1] dirty) y n ∧
      y.mem = clear dirty.mem 1 1 ∧ y.regs frontier = 2 := by
  obtain ⟨y, n, he, -, hm, hf, -, -, -⟩ :=
    runs ![0, 3, 1] dirty dirty_bounded (by intro i; fin_cases i <;> decide) (by decide)
  exact ⟨y, n, he, hm, hf⟩

-- The selected allocator does not materialize one on its empty-allocation path at width zero.
example : ∃ y n, Exec 0 (Backend.code certificates ())
      (Backend.install certificates () (fun _ => 0)
        ⟨fun _ => 0, fun _ => 0⟩) y n ∧ n ≤ 24 ∧
      y.mem = (fun _ => 0) ∧ y.regs frontier = 0 ∧ y.regs outputReg = 0 := by
  obtain ⟨y, n, he, hn, hm, hf, ho, -, -⟩ :=
    runs (fun _ => 0) ⟨fun _ => 0, fun _ => 0⟩
      ⟨fun _ => fits_zero _, fun _ => fits_zero _⟩ (fun _ => fits_zero _) (fits_zero _)
  refine ⟨y, n, he, hn, ?_, hf, ho⟩
  simpa [count, clear, Block.Owns] using hm

-- The negative path also handles an empty allocation, retaining arbitrary fitting dirty cells.
example : ∃ y n, Exec 1 (Backend.code certificates ())
      (Backend.install certificates () ![1, 0, 0]
        ⟨fun _ => 0, fun _ => 1⟩) y n ∧ n ≤ 24 ∧
      y.mem = (fun _ => 1) ∧ y.regs frontier = 0 := by
  obtain ⟨y, n, he, hn, hm, hf, -, -, -⟩ :=
    runs (w := 1) ![1, 0, 0] ⟨fun _ => 0, fun _ => 1⟩
      ⟨fun _ => fits_zero _, fun _ => by change Fits 1 1; decide⟩
      (by intro i; fin_cases i <;> decide) (by decide)
  refine ⟨y, n, he, hn, ?_, hf⟩
  simpa [count, clear, Block.Owns] using hm

-- An arm may even have an impossible explicit domain; the other domain still suffices.
private def forbiddenArm : Realizes.Witness .exact (fun d : Input => Memory.alloc (d 2))
    input word (fun _ _ _ => False) (fun _ _ => 0) where
  scratchSize := 2
  factor := 4
  code := (Realizes.allocWitness input 2).code
  code_spec := by
    intro r f src tmp hi hd hf hs
    refine ⟨((Realizes.allocWitness input 2).code_spec f src tmp hi hd hf hs).1, ?_⟩
    intro w d x hx hin hsafe
    exact hsafe.elim

private def restrictedCertificates (_ : Unit) : Certificate .exact :=
  ⟨Realizes.Witness.branch (.eq 0 1) (Realizes.allocWitness input 1) forbiddenArm⟩

example : Backend.code restrictedCertificates () = Backend.code certificates () := rfl

example : ∃ y n, Exec 2 (Backend.code restrictedCertificates ())
    (Backend.install restrictedCertificates () ![1, 1, 3] dirty) y n := by
  obtain ⟨y, n, he, -⟩ := Backend.exists_exec restrictedCertificates () ![1, 1, 3]
    dirty_bounded (by intro i; fin_cases i <;> decide) (by
      change if (1 : ℕ) = 1 then True else False
      decide) (by
      change Fits 2 (1 + 1) ∧ True
      decide)
  exact ⟨y, n, he⟩

end ComplexityTests.WordRAMRealizationBranchWitness
