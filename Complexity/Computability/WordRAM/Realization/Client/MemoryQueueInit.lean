/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.ExactNotation
import Mathlib.Tactic.FinCases

/-!
# Native initialization of runtime queue layouts

Two fixed straight-line kernels reserve the register-level span of two array stacks and install
all eight fields of their runtime layouts. The register embedding is chosen before the runtime
base, capacity and word width. Both kernels leave all memory unchanged, including an existing
input prefix. Clearing storage and establishing the memory queue's invariant are separate work.

The ABI uses layout registers `0..7`, capacity `3`, frontier `11`, saved base `12`, and one `15`.
The span kernel takes six instructions; the layout kernel takes seven. Arithmetic is exact and
its word-fit assumptions refer only to the final frontier `base + 2 * (capacity + 1)`.

## Main definitions

* `spanCode`: save the old frontier and reserve the two stack blocks.
* `setupCode`: install count/item bases and lengths from the saved base and capacity.

## Main results

* `span_exec`, `setup_exec`: bounded native executions, memory preservation and register frames.

These kernels initialize registers only. They do not claim a complete queue realization,
allocation/clearing certificate, or a cost bound for arbitrary host computations. An appended
flat-program halt is separate from the inline instruction budgets.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueInit

variable {r : ℕ}

/-- Save the runtime frontier in register `12`, then advance it past two blocks of `C + 1`
cells, using the runtime capacity in register `3`. The code is independent of both values. -/
def spanCode (ρ : Fin 16 ↪ Fin r) : Code .exact r :=
  .seq (.op (.copy (ρ 12) (ρ 11)))
    (.seq (.op (.const (ρ 15) 1))
      (.seq (.op (.exactBin .add (ρ 11) (ρ 11) (ρ 3)))
        (.seq (.op (.exactBin .add (ρ 11) (ρ 11) (ρ 3)))
          (.seq (.op (.exactBin .add (ρ 11) (ρ 11) (ρ 15)))
            (.op (.exactBin .add (ρ 11) (ρ 11) (ρ 15)))))))

/-- Install both full layouts from the saved runtime base in `12` and capacity in `3`.
Register `3` already is the first stack's item length and is not overwritten. -/
def setupCode (ρ : Fin 16 ↪ Fin r) : Code .exact r :=
  .seq (.op (.copy (ρ 0) (ρ 12)))
    (.seq (.op (.const (ρ 1) 1))
      (.seq (.op (.exactBin .add (ρ 2) (ρ 12) (ρ 1)))
        (.seq (.op (.copy (ρ 7) (ρ 3)))
          (.seq (.op (.exactBin .add (ρ 4) (ρ 2) (ρ 3)))
            (.seq (.op (.const (ρ 5) 1))
              (.op (.exactBin .add (ρ 6) (ρ 4) (ρ 1))))))))

@[simp] theorem spanCode_size (ρ : Fin 16 ↪ Fin r) : (spanCode ρ).size = 6 := rfl

@[simp] theorem setupCode_size (ρ : Fin 16 ↪ Fin r) : (setupCode ρ).size = 7 := rfl

/-- The fixed span code saves the base, advances the frontier, preserves the capacity and every
other register except its frontier/base/one destinations, and leaves all memory unchanged. -/
theorem span_exec (ρ : Fin 16 ↪ Fin r) (w base C : ℕ) (x : Data r) (hx : x.Bounded w)
    (hfront : x.regs (ρ 11) = base) (hcap : x.regs (ρ 3) = C)
    (hfit : Fits w (base + 2 * (C + 1))) :
    ∃ y, ExecWithin w (spanCode ρ) x y 6 ∧ y.mem = x.mem ∧ y.Bounded w ∧
      y.regs (ρ 12) = base ∧ y.regs (ρ 11) = base + 2 * (C + 1) ∧
      y.regs (ρ 3) = C ∧ y.regs (ρ 15) = 1 ∧
      ∀ i, i ∉ ({ρ 11, ρ 12, ρ 15} : Finset (Fin r)) → y.regs i = x.regs i := by
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have hBC : Fits w (base + C) := hfit.of_le (by omega)
  have hBCC : Fits w (base + C + C) := hfit.of_le (by omega)
  have hBCC1 : Fits w (base + C + C + 1) := hfit.of_le (by omega)
  have hBCC2 : Fits w (base + C + C + 1 + 1) := hfit.of_le (by omega)
  let y := (((((x.set (ρ 12) base).set (ρ 15) 1).set (ρ 11) (base + C)).set
    (ρ 11) (base + C + C)).set (ρ 11) (base + C + C + 1)).set
      (ρ 11) (base + C + C + 1 + 1)
  have hy : ExecWithin w (spanCode ρ) x y 6 := by
    ram_exact_eval [spanCode, y, hfront, hcap, h1, hBC, hBCC, hBCC1, hBCC2,
      ρ.injective.eq_iff]
  refine ⟨y, hy, rfl, hy.bounded hx, ?_, ?_, ?_, ?_, ?_⟩
  · simp [y, ρ.injective.eq_iff]
  · simp only [y, Data.set_regs, Function.update_self]
    omega
  · simpa [y, ρ.injective.eq_iff] using hcap
  · simp [y, ρ.injective.eq_iff]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hy.regs_eq (by simp [spanCode, Code.Preserves, Op.dest, Op.exactBin,
      Ne.symm hi.1, Ne.symm hi.2.1, Ne.symm hi.2.2])

/-- The fixed layout code installs the two count/item blocks. It preserves the saved base,
frontier, capacity, all registers outside `0..7`, and every memory cell. -/
theorem setup_exec (ρ : Fin 16 ↪ Fin r) (w base C : ℕ) (x : Data r) (hx : x.Bounded w)
    (hbase : x.regs (ρ 12) = base) (hcap : x.regs (ρ 3) = C)
    (hfit : Fits w (base + 2 * (C + 1))) :
    ∃ y, ExecWithin w (setupCode ρ) x y 7 ∧ y.mem = x.mem ∧ y.Bounded w ∧
      (∀ i : Fin 8, y.regs (ρ (Fin.castLE (by decide) i)) =
        ![base, 1, base + 1, C, base + 1 + C, 1, base + 1 + C + 1, C] i) ∧
      y.regs (ρ 11) = x.regs (ρ 11) ∧ y.regs (ρ 12) = base ∧ y.regs (ρ 3) = C ∧
      ∀ i, i ∉ ({ρ 0, ρ 1, ρ 2, ρ 3, ρ 4, ρ 5, ρ 6, ρ 7} : Finset (Fin r)) →
        y.regs i = x.regs i := by
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have hB1 : Fits w (base + 1) := hfit.of_le (by omega)
  have hB1C : Fits w (base + 1 + C) := hfit.of_le (by omega)
  have hB1C1 : Fits w (base + 1 + C + 1) := hfit.of_le (by omega)
  let y := ((((((x.set (ρ 0) base).set (ρ 1) 1).set (ρ 2) (base + 1)).set
    (ρ 7) C).set (ρ 4) (base + 1 + C)).set (ρ 5) 1).set (ρ 6) (base + 1 + C + 1)
  have hy : ExecWithin w (setupCode ρ) x y 7 := by
    ram_exact_eval [setupCode, y, hbase, hcap, h1, hB1, hB1C, hB1C1,
      ρ.injective.eq_iff]
  refine ⟨y, hy, rfl, hy.bounded hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [y, hcap, ρ.injective.eq_iff]
  · simp [y, ρ.injective.eq_iff]
  · simpa [y, ρ.injective.eq_iff] using hbase
  · simpa [y, ρ.injective.eq_iff] using hcap
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hy.regs_eq (by simp [setupCode, Code.Preserves, Op.dest, Op.exactBin,
      Ne.symm hi.1, Ne.symm hi.2.1, Ne.symm hi.2.2.1, Ne.symm hi.2.2.2.2.1,
      Ne.symm hi.2.2.2.2.2.1, Ne.symm hi.2.2.2.2.2.2.1,
      Ne.symm hi.2.2.2.2.2.2.2])

end Cslib.WordRAM.Realization.MemoryQueueInit
