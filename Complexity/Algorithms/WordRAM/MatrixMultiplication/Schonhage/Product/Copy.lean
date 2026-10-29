/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Program

/-!
# Charged copies across the producer/consumer boundary

## Main results

* `QueriedProduct.exec_copyCall`: real argument setup and the unchanged dynamic native copy,
  with both address orders, equality, complete memory meaning and caller-register frame.

These are internal execution interfaces. Complete product clients derive the numerical fits
and separation from the original input and the explicit computed layout.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Each existing 96-register callee has exactly its original register semantics. -/
public theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 160 => i.val) h)

private theorem copyBank_injective : Function.Injective copyBank := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 160 => i.val) h)

/-- Dynamic native argument setup and every copy instruction are charged. The caller's
source/destination/length registers, and every register beyond the seven-register callee,
are preserved. Source and destination separation is a numerical layout obligation. -/
public theorem exec_copyCall {w : ℕ} (x : Data 160) (h1 : Fits w 1)
    (hs : Fits w (x.regs source + x.regs length))
    (hd : Fits w (x.regs destination + x.regs length))
    (hsep : x.regs source + x.regs length ≤ x.regs destination ∨
      x.regs destination + x.regs length ≤ x.regs source ∨
      x.regs source = x.regs destination) :
    ∃ y, ExecWithin w copyCall x y (7 * x.regs length + 7) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (x.regs source) (x.regs destination) (x.regs length) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  let x1 := x.set (0 : Fin 160) (x.regs source)
  let x2 := x1.set (1 : Fin 160) (x.regs destination)
  let x3 := x2.set (2 : Fin 160) (x.regs length)
  have h0 : ExecWithin (B := .standard) w (.op (.copy (0 : Fin 160) source)) x x1 1 :=
    ExecWithin.copy
  have h01 : ExecWithin (B := .standard) w (.op (.copy (1 : Fin 160) destination)) x1 x2 1 := by
    ram_eval [x1, x2, source, destination]
  have h02 : ExecWithin (B := .standard) w (.op (.copy (2 : Fin 160) length)) x2 x3 1 := by
    ram_eval [x1, x2, x3, source, destination, length]
  obtain ⟨z, hz, hm, _, _, _⟩ := ArrayCopy.exec_of_separated_or_eq (x3.comap copyBank) h1
    (by simpa [x1, x2, x3, copyBank, ArrayCopy.src, ArrayCopy.len] using hs)
    (by simpa [x1, x2, x3, copyBank, ArrayCopy.dst, ArrayCopy.len] using hd)
    (by simpa [x1, x2, x3, copyBank, ArrayCopy.src, ArrayCopy.dst, ArrayCopy.len] using hsep)
  let y := z.extend copyBank x3
  have he := hz.rename copyBank_injective
  refine ⟨y, ?_, ?_, ?_⟩
  · have hlen : (x3.comap copyBank).regs ArrayCopy.len = x.regs length := by
      simp [x1, x2, x3, copyBank, ArrayCopy.len]
    rw [hlen] at he
    exact (h0.seq (h01.seq (h02.seq he))).mono (by omega)
  · change z.mem = _
    simpa [x1, x2, x3, copyBank, ArrayCopy.src, ArrayCopy.dst, ArrayCopy.len] using hm
  · intro i hi
    have hnot : ¬∃ j, copyBank j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg (fun r : Fin 160 => r.val) hj
      change j.val = i.val at hv
      omega
    change Function.extend copyBank z.regs x3.regs i = x.regs i
    rw [Function.extend_apply' _ _ _ hnot]
    simp only [x3, x2, x1, Data.set_regs,
      Function.update_of_ne (show i ≠ (2 : Fin 160) by omega),
      Function.update_of_ne (show i ≠ (1 : Fin 160) by omega),
      Function.update_of_ne (show i ≠ (0 : Fin 160) by omega)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
