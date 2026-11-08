/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Program
import Complexity.Computability.WordRAM.Call
import Complexity.Tactic.Fits

/-!
# Charged physical gathering into the product snapshot

Only the destination snapshot is written. External sources may alias each other, with their
actual readback determining consistency. All one-past ends are checked; initial private memory
and unused registers may be arbitrary.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM

/-- Every native copy register has a distinct physical register. -/
theorem copyBank_injective : Function.Injective copyBank := by
  intro i j h
  have hv := congrArg (fun k : Fin 173 => k.val) h
  apply Fin.ext
  change 166 + i.val = 166 + j.val at hv
  omega

/-- Native copy execution with its disjoint physical scratch bank. -/
theorem exec_copy {W s d k : ℕ} (x : Data 173)
    (hs : x.regs Reg.source = s) (hd : x.regs Reg.destination = d)
    (hk : x.regs Reg.length = k) (hsep : s + k ≤ d)
    (hfit : Fits W (s + k + d + k + 1)) :
    ∃ y, ExecWithin W copy x y (7 * k + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem s d k ∧
      y.regs Reg.source = s ∧ y.regs Reg.destination = d ∧ y.regs Reg.length = k ∧
      ∀ i : Fin 173, i.val < 166 → y.regs i = x.regs i := by
  obtain ⟨y, he, ⟨ym, ys, yd, yk⟩, yf⟩ := ExecWithin.rename_post copyBank_injective
    (ArrayCopy.exec (x.comap copyBank) (hfit.of_le (by omega))
      (by change Fits W (x.regs Reg.source + x.regs Reg.length)
          rw [hs, hk]; fits)
      (by change Fits W (x.regs Reg.destination + x.regs Reg.length)
          rw [hd, hk]; fits)
      (by change x.regs Reg.source + x.regs Reg.length ≤ x.regs Reg.destination; omega))
  change y.regs Reg.source = _ at ys
  change y.regs Reg.destination = _ at yd
  change y.regs Reg.length = _ at yk
  refine ⟨y, ?_, ?_, ys.trans hs, yd.trans hd, yk.trans hk, ?_⟩
  · change ExecWithin W copy x y (7 * x.regs Reg.length + 4) at he
    simpa only [hk] using he
  · change y.mem = ArrayCopy.copyPrefix x.mem (x.regs Reg.source)
      (x.regs Reg.destination) (x.regs Reg.length) at ym
    simpa only [hs, hd, hk] using ym
  · intro i hi
    apply yf i
    intro j hj
    have hv := congrArg Fin.val hj
    change 166 + j.val = i.val at hv
    omega

/-- The actual memory meaning of the four destination blocks. -/
@[expose] def gatherMemory (mem : ℕ → ℕ) (b S A Q s t q : ℕ) : ℕ → ℕ :=
  let h := ArrayCopy.copyPrefix mem b (b + S) 5
  let l := ArrayCopy.copyPrefix h s (b + S + 5) A
  let r := ArrayCopy.copyPrefix l t (b + S + 5 + A) A
  ArrayCopy.copyPrefix r q (b + S + 5 + 2 * A) (2 * Q)

private theorem set_copy_arguments_frame (x : Data 173) (s d k : ℕ)
    (i : Fin 173) (hi : i.val < 166) :
    (x.set Reg.source s |>.set Reg.destination d |>.set Reg.length k).regs i = x.regs i := by
  have hne0 : i ≠ Reg.source := by intro he; subst i; simp [Reg.source, copyBank] at hi
  have hne1 : i ≠ Reg.destination := by intro he; subst i; simp [Reg.destination, copyBank] at hi
  have hne2 : i ≠ Reg.length := by intro he; subst i; simp [Reg.length, copyBank] at hi
  simp only [Data.set_regs, Function.update_of_ne hne0, Function.update_of_ne hne1,
    Function.update_of_ne hne2]

/-- Every physical header, address, load/store and loop step is included in the native charge. -/
theorem exec_gather {W b S A Q s t q : ℕ} (x : Data 173)
    (hb : x.regs Reg.base = b)
    (hS : x.regs (sourceBank QueriedProduct.Reg.snapshot) = S)
    (hA : x.regs (sourceBank QueriedProduct.Reg.matrixWords) = 2 * A)
    (hQ : x.regs (sourceBank QueriedProduct.Reg.queryCount) = Q)
    (h2 : x.regs (sourceBank QueriedProduct.Reg.two) = 2)
    (h5 : x.regs (sourceBank QueriedProduct.Reg.five) = 5)
    (hs : x.regs Reg.left = s) (ht : x.regs Reg.right = t)
    (hq : x.regs Reg.queries = q)
    (hS5 : 5 ≤ S) (hsb : s + A ≤ b) (htb : t + A ≤ b) (hqb : q + 2 * Q ≤ b)
    (hfit : Fits W (2 * b + 2 * S + 4 * A + 4 * Q + 32)) :
    ∃ y, ExecWithin W gather x y (gatherTime A Q) ∧
      y.mem = gatherMemory x.mem b S A Q s t q ∧
      ∀ i : Fin 173, i.val < 166 → y.regs i = x.regs i := by
  have hfH : Fits W (b + S) := by fits
  have hfL : Fits W (b + S + 5) := by fits
  have hfA : Fits W A := by fits
  have hfR : Fits W (b + S + 5 + A) := by fits
  have hfQ : Fits W (b + S + 5 + A + A) := by fits
  have hfQQ : Fits W (Q * 2) := by fits
  let h := x.set Reg.source b |>.set Reg.destination (b + S) |>.set Reg.length 5
  have hh : ExecWithin W headerArguments x h 3 := by
    ram_eval [headerArguments, h, hb, hS, h5, hfH, Reg.source, Reg.destination, Reg.length]
  obtain ⟨a, ha, am, asrc, adst, alen, ar⟩ := exec_copy (s := b) (d := b + S) (k := 5) h
    (by simp +decide [h, Reg.source, Reg.destination, Reg.length, copyBank])
    (by simp +decide [h, Reg.destination, Reg.length, copyBank]) (by simp [h])
    (by omega) (hfit.of_le (by omega))
  change a.regs (167 : Fin 173) = b + S at adst
  have af (i : Fin 173) (hi : i.val < 166) : a.regs i = x.regs i :=
    (ar i hi).trans (set_copy_arguments_frame x b (b + S) 5 i hi)
  let l := a.set Reg.source s |>.set Reg.destination (b + S + 5) |>.set Reg.length A
  have hl : ExecWithin W leftArguments a l 3 := by
    apply ExecWithin.of_eval (fuel := 0) (n := 3)
    · set_option linter.unusedSimpArgs false in
      simp +decide [Code.eval, Op.bin, Op.eval, Data.put, StandardOp.eval,
        BinOp.eval, Basis.standard_interp_bin,
        Function.update_apply, leftArguments, l, adst, af Reg.left (by decide), hs,
      af (sourceBank QueriedProduct.Reg.five) (by decide), h5,
      af (sourceBank QueriedProduct.Reg.matrixWords) (by decide), hA,
      af (sourceBank QueriedProduct.Reg.two) (by decide), h2, hfL, hfA,
      Reg.source, Reg.destination, Reg.length, copyBank]
    · omega
  obtain ⟨c, hc, cm, csrc, cdst, clen, cr⟩ := exec_copy (s := s) (d := b + S + 5) (k := A) l
    (by simp +decide [l, Reg.source, Reg.destination, Reg.length, copyBank])
    (by simp +decide [l, Reg.destination, Reg.length, copyBank]) (by simp [l])
    (by omega) (hfit.of_le (by omega))
  change c.regs (167 : Fin 173) = b + S + 5 at cdst
  change c.regs (168 : Fin 173) = A at clen
  have cf (i : Fin 173) (hi : i.val < 166) : c.regs i = x.regs i :=
    (cr i hi).trans ((set_copy_arguments_frame a s (b + S + 5) A i hi).trans (af i hi))
  let r := c.set Reg.source t |>.set Reg.destination (b + S + 5 + A)
  have hr : ExecWithin W rightArguments c r 2 := by
    apply ExecWithin.of_eval (fuel := 0) (n := 2)
    · set_option linter.unusedSimpArgs false in
      simp +decide [Code.eval, Op.bin, Op.eval, Data.put, StandardOp.eval,
        BinOp.eval, Basis.standard_interp_bin,
        Function.update_apply, rightArguments, r, cf Reg.right (by decide), ht, cdst, clen, hfR,
      Reg.source, Reg.destination, Reg.length, copyBank]
    · omega
  have rf (i : Fin 173) (hi : i.val < 166) : r.regs i = c.regs i := by
    have hne0 : i ≠ Reg.source := by intro he; subst i; simp [Reg.source, copyBank] at hi
    have hne1 : i ≠ Reg.destination := by intro he; subst i; simp [Reg.destination, copyBank] at hi
    simp only [r, Data.set_regs, Function.update_of_ne hne0, Function.update_of_ne hne1]
  obtain ⟨d, hd, dm, dsrc, ddst, dlen, dr⟩ := exec_copy (s := t) (d := b + S + 5 + A) (k := A) r
    (by simp +decide [r, Reg.source, Reg.destination, copyBank])
    (by simp [r])
    (by simpa +decide [r, Reg.source, Reg.destination, Reg.length, copyBank] using clen)
    (by omega) (hfit.of_le (by omega))
  change d.regs (167 : Fin 173) = b + S + 5 + A at ddst
  change d.regs (168 : Fin 173) = A at dlen
  have df (i : Fin 173) (hi : i.val < 166) : d.regs i = x.regs i :=
    (dr i hi).trans ((rf i hi).trans (cf i hi))
  let u := d.set Reg.source q |>.set Reg.destination (b + S + 5 + A + A)
    |>.set Reg.length (Q * 2)
  have hu : ExecWithin W queryArguments d u 3 := by
    apply ExecWithin.of_eval (fuel := 0) (n := 3)
    · set_option linter.unusedSimpArgs false in
      simp +decide [Code.eval, Op.bin, Op.eval, Data.put, StandardOp.eval,
        BinOp.eval, Basis.standard_interp_bin,
        Function.update_apply, queryArguments, u, df Reg.queries (by decide), hq, ddst, dlen,
      df (sourceBank QueriedProduct.Reg.queryCount) (by decide), hQ,
      df (sourceBank QueriedProduct.Reg.two) (by decide), h2, hfQ, hfQQ,
      Reg.source, Reg.destination, Reg.length, copyBank]
    · omega
  obtain ⟨y, hy, ym, _, _, _, yr⟩ := exec_copy (s := q) (d := b + S + 5 + A + A) (k := Q * 2) u
    (by simp +decide [u, Reg.source, Reg.destination, Reg.length, copyBank])
    (by simp +decide [u, Reg.destination, Reg.length, copyBank]) (by simp [u])
    (by omega) (hfit.of_le (by omega))
  refine ⟨y, ?_, ?_, fun i hi => (yr i hi).trans
    ((set_copy_arguments_frame d q (b + S + 5 + A + A) (Q * 2) i hi).trans (df i hi))⟩
  · exact (hh.seq (ha.seq (hl.seq (hc.seq (hr.seq (hd.seq (hu.seq hy))))))).mono
      (by unfold gatherTime; omega)
  · simpa only [gatherMemory, Nat.mul_comm Q 2,
      show b + S + 5 + A + A = b + S + 5 + 2 * A by omega,
      u, r, l, h, Data.set_mem, dm, cm, am] using ym

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
