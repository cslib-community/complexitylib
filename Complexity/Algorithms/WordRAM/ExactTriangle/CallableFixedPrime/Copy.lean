/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Header

/-!
# Charged copies in the caller's high register bank

This internal call rule embeds the actual eight-register copy/sum loop. Only the source,
destination and sum bounds are needed; the caller metadata and low selector bank are framed
without unfolding the loop. The full adapter discharges these bounds from original inputs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

private theorem copyBank_injective : Function.Injective copyBank := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext (by simpa only [copyBank] using Nat.add_left_cancel hv)

/-- Deliver the original AB arguments and zero accumulator after the real header. -/
theorem exec_firstCopy {W : ℕ} (x : Data 640) (hc : x.regs Reg.constant = 5)
    (hfit : Fits W (x.regs Reg.base + 5)) :
    ∃ y, ExecWithin W firstCopy x y 4 ∧ y.mem = x.mem ∧
      y.regs (copyBank 0) = x.regs Reg.ab ∧
      y.regs (copyBank 1) = x.regs Reg.base + 5 ∧
      y.regs (copyBank 2) = x.regs Reg.area ∧ y.regs (copyBank 7) = 0 ∧
      ∀ j : Fin 640, j.val < 620 → y.regs j = x.regs j := by
  let y := (((x.set (copyBank 0) (x.regs Reg.ab)).set (copyBank 1)
    (x.regs Reg.base + 5)).set (copyBank 2) (x.regs Reg.area)).set (copyBank 7) 0
  have he : ExecWithin W firstCopy x y 4 := by
    ram_eval [firstCopy, y, copyBank, hc, hfit, Reg.ab, Reg.base, Reg.area,
      Reg.constant, Fin.mk.injEq]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [y, copyBank]
  · simp [y, copyBank]
  · simp [y, copyBank]
  · simp [y, copyBank]
  · intro j hj
    apply he.regs_eq
    have hn (i : Fin 8) : copyBank i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      change 620 + i.val = j.val at hv
      omega
    simp [firstCopy, Code.Preserves, Op.dest, Op.bin, hn]

/-- Deliver a subsequent matrix pointer and advance only the destination span. -/
theorem exec_nextCopy {W : ℕ} (src : Fin 640) (x : Data 640)
    (hfit : Fits W (x.regs (copyBank 1) + x.regs (copyBank 2))) :
    ∃ y, ExecWithin W (nextCopy src) x y 2 ∧ y.mem = x.mem ∧
      y.regs (copyBank 0) = x.regs src ∧
      y.regs (copyBank 1) = x.regs (copyBank 1) + x.regs (copyBank 2) ∧
      y.regs (copyBank 2) = x.regs (copyBank 2) ∧
      y.regs (copyBank 7) = x.regs (copyBank 7) ∧
      ∀ j : Fin 640, j.val < 620 → y.regs j = x.regs j := by
  let a := x.set (copyBank 0) (x.regs src)
  let y := a.set (copyBank 1) (x.regs (copyBank 1) + x.regs (copyBank 2))
  have hfirst : ExecWithin (B := .standard) W (.op (.copy (copyBank 0) src)) x a 1 :=
    ExecWithin.copy
  have hsecond : ExecWithin W
      (.op (.bin .add (copyBank 1) (copyBank 1) (copyBank 2))) a y 1 := by
    simpa [a, y, copyBank, BinOp.eval] using
      (ExecWithin.bin (w := W) (f := .add) (d := copyBank 1) (i := copyBank 1)
        (j := copyBank 2) (x := a)
        (by simpa [a, copyBank] using hfit))
  have he : ExecWithin W (nextCopy src) x y 2 := hfirst.seq hsecond
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [y, a, copyBank]
  · simp [y, a, copyBank]
  · simp [y, a, copyBank]
  · simp [y, a, copyBank]
  · intro j hj
    apply he.regs_eq
    have hn (i : Fin 8) : copyBank i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      change 620 + i.val = j.val at hv
      omega
    simp [nextCopy, Code.Preserves, Op.dest, Op.bin, hn]

/-- Actual copied words and running sum, with all caller registers outside the eight scratch
registers unchanged. This stage theorem is an implementation interface. -/
theorem exec_copy {W : ℕ} (x : Data 640) (h1 : Fits W 1)
    (hs : Fits W (x.regs (copyBank ArrayCopySum.Reg.src) +
      x.regs (copyBank ArrayCopySum.Reg.len)))
    (hd : Fits W (x.regs (copyBank ArrayCopySum.Reg.dst) +
      x.regs (copyBank ArrayCopySum.Reg.len)))
    (ht : Fits W (x.regs (copyBank ArrayCopySum.Reg.total) +
      ArrayCopySum.wordSum x.mem (x.regs (copyBank ArrayCopySum.Reg.src))
        (x.regs (copyBank ArrayCopySum.Reg.len))))
    (hsep : x.regs (copyBank ArrayCopySum.Reg.src) +
      x.regs (copyBank ArrayCopySum.Reg.len) ≤ x.regs (copyBank ArrayCopySum.Reg.dst)) :
    ∃ y, ExecWithin W (ArrayCopySum.program.rename copyBank) x y
        (8 * x.regs (copyBank ArrayCopySum.Reg.len) + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (x.regs (copyBank ArrayCopySum.Reg.src))
        (x.regs (copyBank ArrayCopySum.Reg.dst)) (x.regs (copyBank ArrayCopySum.Reg.len)) ∧
      y.regs (copyBank ArrayCopySum.Reg.src) = x.regs (copyBank ArrayCopySum.Reg.src) ∧
      y.regs (copyBank ArrayCopySum.Reg.dst) = x.regs (copyBank ArrayCopySum.Reg.dst) ∧
      y.regs (copyBank ArrayCopySum.Reg.len) = x.regs (copyBank ArrayCopySum.Reg.len) ∧
      y.regs (copyBank ArrayCopySum.Reg.total) = x.regs (copyBank ArrayCopySum.Reg.total) +
        ArrayCopySum.wordSum x.mem (x.regs (copyBank ArrayCopySum.Reg.src))
          (x.regs (copyBank ArrayCopySum.Reg.len)) ∧
      ∀ j : Fin 640, j.val < 620 ∨ 628 ≤ j.val → y.regs j = x.regs j := by
  obtain ⟨a, ha, hm, hs', hd', hl, ht'⟩ := ArrayCopySum.exec (x.comap copyBank)
    h1 hs hd ht hsep
  let y := a.extend copyBank x
  have hy : ExecWithin W (ArrayCopySum.program.rename copyBank) x y
      (8 * x.regs (copyBank ArrayCopySum.Reg.len) + 4) := ha.rename copyBank_injective
  refine ⟨y, hy, hm,
    (copyBank_injective.extend_apply _ _ _).trans hs',
    (copyBank_injective.extend_apply _ _ _).trans hd',
    (copyBank_injective.extend_apply _ _ _).trans hl,
    (copyBank_injective.extend_apply _ _ _).trans ht', ?_⟩
  intro j hj
  apply hy.regs_eq
  apply Code.preserves_rename_of_forall_ne
  intro i he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change 620 + i.val = j.val at hv
  rcases hj with h | h <;> omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
