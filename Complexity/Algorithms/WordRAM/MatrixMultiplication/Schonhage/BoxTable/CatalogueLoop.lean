/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.CatalogueWrite

/-!
# Complete native shared-catalogue scan

The actual outer loop visits every directory slot once. Its digit scans and all
directory/record stores are charged; the compact count is Mathlib's count of the
computed eligibility predicate. Dirty memory outside the written prefixes survives.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Persistent scalar contents used by the native catalogue loop, with no run or cost fields. -/
structure CatalogueParameters (L H D R : ℕ) (x : Data registers) : Prop where
  /-- Original depth. -/
  levels : x.regs Reg.levels = L
  /-- Computed P0/star limit. -/
  height : x.regs Reg.height = H
  /-- Computed decimal capacity. -/
  span : x.regs Reg.span = 10 ^ L
  /-- Caller directory base. -/
  directory : x.regs Reg.directory = D
  /-- Computed compact-record base. -/
  records : x.regs Reg.records = R
  /-- Computed complete slot count. -/
  slots : x.regs Reg.slots = (H + 1) * 10 ^ L
  /-- Scalar one. -/
  one : x.regs Reg.one = 1
  /-- Scalar radix. -/
  ten : x.regs Reg.ten = 10
  /-- Scalar P0 digit. -/
  nine : x.regs Reg.nine = 9
  /-- Scalar record width. -/
  three : x.regs Reg.three = 3
  /-- Scalar zero outside signed arithmetic. -/
  nil : x.regs Reg.nil = 0

private def parameterRegisters : Finset (Fin registers) :=
  {Reg.levels, Reg.height, Reg.span, Reg.directory, Reg.records, Reg.slots,
    Reg.one, Reg.ten, Reg.nine, Reg.three, Reg.nil}

private theorem CatalogueParameters.of_eq {L H D R : ℕ} {x y : Data registers}
    (hx : CatalogueParameters L H D R x)
    (h : ∀ i ∈ parameterRegisters, y.regs i = x.regs i) :
    CatalogueParameters L H D R y :=
  ⟨(h _ (by decide)).trans hx.levels, (h _ (by decide)).trans hx.height,
    (h _ (by decide)).trans hx.span, (h _ (by decide)).trans hx.directory,
    (h _ (by decide)).trans hx.records, (h _ (by decide)).trans hx.slots,
    (h _ (by decide)).trans hx.one, (h _ (by decide)).trans hx.ten,
    (h _ (by decide)).trans hx.nine, (h _ (by decide)).trans hx.three,
    (h _ (by decide)).trans hx.nil⟩

/-- Scalar registers changed by a complete catalogue iteration. -/
@[expose] def CatalogueLocal (i : Fin registers) : Prop := InspectLocal i ∨ WriteLocal i

instance (i : Fin registers) : Decidable (CatalogueLocal i) :=
  inferInstanceAs (Decidable (InspectLocal i ∨ WriteLocal i))

private theorem catalogueStep_preserves (i : Fin registers) :
    ¬CatalogueLocal i → catalogueStep.Preserves i := by decide +revert

private theorem parameter_not_local :
    ∀ i ∈ parameterRegisters, ¬CatalogueLocal i := by decide

/-- Compose the complete native digit scan with the real compact stores. -/
theorem exec_catalogueStep {w L H D R s : ℕ} (x : Data registers)
    (hx : CatalogueParameters L H D R x) (hs : x.regs Reg.slot = s)
    (hc : x.regs Reg.count = Nat.count (Eligible L H) s)
    (hslt : s < (H + 1) * 10 ^ L)
    (hfit : Fits w (D + R + 6 * ((H + 1) * 10 ^ L) + 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w catalogueStep x y (11 * L + 26) ∧
      y.mem = catalogueWrite L H D R s x.mem ∧ y.regs Reg.slot = s + 1 ∧
      y.regs Reg.count = Nat.count (Eligible L H) (s + 1) ∧
      CatalogueParameters L H D R y ∧
      (∀ i, ¬CatalogueLocal i → y.regs i = x.regs i) := by
  have hscan : Fits w (s + 10 ^ L + L + 12) := hfit.of_le (by omega)
  have hwrite : Fits w (D + R + 6 * (s + 1) + 12) := hfit.of_le
    (Nat.add_le_add_right ((Nat.add_le_add_left
      (Nat.mul_le_mul_left 6 (Nat.succ_le_of_lt hslt)) (D + R)).trans
        ((Nat.le_add_right _ (10 ^ L)).trans (Nat.le_add_right _ L))) 12)
  obtain ⟨u, hu, he, hcode, hpop, hstride, hmem, hframe⟩ :=
    exec_inspect x hx.levels hx.span hs hx.one hx.ten hx.nine hscan
  have hf (i : Fin registers) (hi : ¬InspectLocal i) : u.regs i = x.regs i := hframe i hi
  obtain ⟨y, hy, hym, hys, hyc, _⟩ := exec_writeSlot u
    ((hf _ (by decide)).trans hx.directory) ((hf _ (by decide)).trans hx.records)
    ((hf _ (by decide)).trans hs) ((hf _ (by decide)).trans hx.height)
    ((hf _ (by decide)).trans hc) hcode he hpop hstride
    ((hf _ (by decide)).trans hx.one) ((hf _ (by decide)).trans hx.three)
    ((hf _ (by decide)).trans hx.nil) hwrite
  have hwhole : ExecWithin w catalogueStep x y (11 * L + 26) :=
    (hu.seq hy).mono (by omega)
  have hregs (i : Fin registers) (hi : ¬CatalogueLocal i) : y.regs i = x.regs i :=
    hwhole.regs_eq (catalogueStep_preserves i hi)
  refine ⟨y, hwhole, ?_, hys, hyc, hx.of_eq (fun i hi =>
    hregs i (parameter_not_local i hi)), hregs⟩
  simpa only [hmem] using hym

/-- The actual scan fills every directory word and emits every eligible compact record once. -/
theorem exec_catalogueLoop {w L H D R : ℕ} (x : Data registers)
    (hx : CatalogueParameters L H D R x)
    (hslot : x.regs Reg.slot = 0) (hcount : x.regs Reg.count = 0)
    (hsep : D + (H + 1) * 10 ^ L ≤ R)
    (hfit : Fits w (D + R + 6 * ((H + 1) * 10 ^ L) + 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w (.loop (.lt Reg.slot Reg.slots) catalogueStep) x y
        ((11 * L + 28) * ((H + 1) * 10 ^ L) + 2) ∧
      CatalogueParameters L H D R y ∧ y.regs Reg.slot = (H + 1) * 10 ^ L ∧
      y.regs Reg.count = Nat.count (Eligible L H) ((H + 1) * 10 ^ L) ∧
      CataloguePrefix L H D R ((H + 1) * 10 ^ L) x.mem y.mem := by
  let S := (H + 1) * 10 ^ L
  let I (y : Data registers) : Prop :=
    CatalogueParameters L H D R y ∧ y.regs Reg.slot ≤ S ∧
      y.regs Reg.count = Nat.count (Eligible L H) (y.regs Reg.slot) ∧
      CataloguePrefix L H D R (y.regs Reg.slot) x.mem y.mem
  have hi : I x := by
    refine ⟨hx, by simp [hslot, S], by simp [hslot, hcount], ?_⟩
    simpa only [hslot] using CataloguePrefix.zero L H D R x.mem
  have hb (y : Data registers) (hy : I y) (hg : (Cond.lt Reg.slot Reg.slots).Holds y) :
      ∃ z, ExecWithin w catalogueStep y z (11 * L + 26) ∧ I z ∧
        S - z.regs Reg.slot < S - y.regs Reg.slot := by
    obtain ⟨hp, hle, hc, hprefix⟩ := hy
    have hlt : y.regs Reg.slot < S := by
      simpa only [Cond.holds_lt, hp.slots, S] using hg
    obtain ⟨z, hz, hzm, hzs, hzc, hzp, _⟩ :=
      exec_catalogueStep y hp rfl hc hlt hfit
    refine ⟨z, hz, ⟨hzp, by omega, ?_, ?_⟩, by omega⟩
    · simpa only [hzs] using hzc
    · rw [hzs, hzm]
      exact hprefix.step hlt hsep
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => S - y.regs Reg.slot) hb hi
  obtain ⟨hp, hle, hc, hprefix⟩ := hIy
  have hdone : y.regs Reg.slot = S := by
    simp only [Cond.holds_lt, hp.slots, not_lt] at hstop
    exact Nat.le_antisymm hle hstop
  refine ⟨y, ?_, hp, hdone, ?_, ?_⟩
  · simpa only [hslot, Nat.sub_zero, S, Nat.mul_comm, Nat.add_assoc] using hy
  · simpa only [hdone] using hc
  · simpa only [hdone] using hprefix

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
