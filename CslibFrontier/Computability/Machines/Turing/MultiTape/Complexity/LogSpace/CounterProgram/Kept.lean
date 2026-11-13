/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Registers kept by a block of counter code

`Kept B base regs regs'` says that a block of counter code, run on the registers `regs`, left the
registers `regs'` of the same length, unchanged below `base`, with every register at most `B`.
Compiled formulas and closure loops state their effect on the registers this way, and blocks run
in sequence compose by `Kept.trans`.

## Main definitions

* `Turing.CounterProgram.Kept`: the registers after a block.

## Main results

* `Turing.CounterProgram.Kept.trans`, `Turing.CounterProgram.Kept.mono`: composing blocks and
  forgetting registers.
* `Turing.CounterProgram.Kept.facts`: the cardinality and the free-variable registers survive a
  block that keeps the registers below them.
-/

public section

namespace Turing

namespace CounterProgram

/-- The registers after a block: the same length, unchanged below `base`, each at most `B`. -/
structure Kept (B base : ℕ) (regs regs' : List ℕ) : Prop where
  /-- The block does not change the number of registers. -/
  length_eq : regs'.length = regs.length
  /-- The block does not change the registers below `base`. -/
  getD_eq : ∀ i < base, regs'.getD i 0 = regs.getD i 0
  /-- Every register is at most `B` after the block. -/
  bounded : ∀ r ∈ regs', r ≤ B

namespace Kept

variable {B base : ℕ}

theorem refl {regs : List ℕ} (hB : ∀ r ∈ regs, r ≤ B) : Kept B base regs regs :=
  ⟨rfl, fun _ _ => rfl, hB⟩

theorem trans {r₁ r₂ r₃ : List ℕ} (h₁ : Kept B base r₁ r₂) (h₂ : Kept B base r₂ r₃) :
    Kept B base r₁ r₃ :=
  ⟨h₂.length_eq.trans h₁.length_eq, fun i hi => (h₂.getD_eq i hi).trans (h₁.getD_eq i hi),
    h₂.bounded⟩

/-- Keeping the registers below `base'` keeps those below any `base ≤ base'`. -/
theorem mono {base' : ℕ} {regs regs' : List ℕ} (h : Kept B base' regs regs') (hle : base ≤ base') :
    Kept B base regs regs' :=
  ⟨h.length_eq, fun i hi => h.getD_eq i (by omega), h.bounded⟩

/-- Setting a register at or above `base` to a value at most `B` keeps the registers. -/
theorem set_right {j m : ℕ} {regs regs' : List ℕ} (h : Kept B base regs regs') (hj : base ≤ j)
    (hm : m ≤ B) : Kept B base regs (regs'.set j m) :=
  ⟨by rw [List.length_set, h.length_eq], fun i hi => by
    rw [List.getD_set_ne (by omega), h.getD_eq i hi],
    List.forall_mem_set_of_forall_mem h.bounded hm⟩

/-- A block that keeps the registers below `base + 1` after register `base` was set keeps the
registers below `base` of the original registers. -/
theorem of_set {m : ℕ} {regs regs' : List ℕ} (hk : Kept B (base + 1) (regs.set base m) regs') :
    Kept B base regs regs' :=
  ⟨by rw [hk.length_eq, List.length_set], fun i hi => by
    rw [hk.getD_eq i (by omega), List.getD_set_ne (by omega)], hk.bounded⟩

/-- The cardinality in register `0` and the values of free variables in registers `fv x` below
`base` survive a block that keeps the registers below `base`. -/
theorem facts {d n : ℕ} {regs regs' : List ℕ} {α : Type*} {fv : α → ℕ} {val : α → Fin n}
    (hk : Kept B base regs regs') (hbase : 0 < base) (hfv : ∀ x, fv x < base)
    (hd : base + d ≤ regs.length) (h0 : regs.getD 0 0 = n)
    (hv : ∀ x, regs.getD (fv x) 0 = val x) :
    base + d ≤ regs'.length ∧ regs'.getD 0 0 = n ∧ ∀ x, regs'.getD (fv x) 0 = val x :=
  ⟨by rw [hk.length_eq]; exact hd, by rw [hk.getD_eq 0 hbase, h0],
    fun x => by rw [hk.getD_eq _ (hfv x), hv]⟩

end Kept

end CounterProgram

end Turing
