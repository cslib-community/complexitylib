/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Program

/-!
# Checked production invocation of the physical pointer front

Physical pointers are delivered in four charged copies, outside the normalized source bank.
All raw readback and separation premises describe actual external memory. The callee computes
its layout, gathers and runs the existing product mathematics; no execution oracle is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open RecordProduct

private theorem pointerBank_injective : Function.Injective pointerBank := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change 128 + i.val = 128 + j.val at hv
  omega

/-- Invoke the actual pointer product with physically exact answers and the caller frame. -/
theorem exec_invoke {W b m t N s r q : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 320)
    (hb : x.regs Reg.base = b) (hs : x.regs Reg.left = s)
    (hr : x.regs Reg.right = r) (hq : x.regs Reg.queries = q)
    (hheader : ∀ a < 5, x.mem (b + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (b + QueriedProduct.inputEnd m N qs.length) = t)
    (hsb : s + N * D m ≤ b) (hrb : r + N * D m ≤ b) (hqb : q + 2 * qs.length ≤ b)
    (hleft : ∀ a < N * D m, x.mem (s + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < N * D m, x.mem (r + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + N * D m + a))
    (hqueries : ∀ a < 2 * qs.length, x.mem (q + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + 2 * (N * D m) + a))
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (ht : t ≤ m) (hN : D m ^ 18 ≤ N)
    (hfit : Fits W (2 * b + 4 * CallableProduct.windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W invoke x y (PointerBoxProduct.timeBound m t qs + 5) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (21 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < b ∨ b + CallableProduct.windowSize N qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 128 → i ≠ Reg.result → y.regs i = x.regs i := by
  let z := x.set (pointerBank PointerBoxProduct.Reg.base) b |>.set
    (pointerBank PointerBoxProduct.Reg.left) s |>.set
    (pointerBank PointerBoxProduct.Reg.right) r |>.set
    (pointerBank PointerBoxProduct.Reg.queries) q
  have hz : ExecWithin (B := .standard) W
      (ram[
        ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.base) Reg.base)⟫;
        ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.left) Reg.left)⟫;
        ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.right) Reg.right)⟫;
        ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.queries) Reg.queries)⟫ ]) x z 4 := by
    ram_eval [z, hb, hs, hr, hq, pointerBank, PointerBoxProduct.Reg.base,
      PointerBoxProduct.callableBank, CallableProduct.Reg.base, PointerBoxProduct.Reg.left,
      PointerBoxProduct.Reg.right, PointerBoxProduct.Reg.queries,
      Reg.base, Reg.left, Reg.right, Reg.queries, Fin.mk.injEq]
  obtain ⟨c, hc, ⟨cr, cv, _, cf, _, _, _⟩, hframe⟩ := ExecWithin.rename_post pointerBank_injective
    (PointerBoxProduct.exec X Y qs (z.comap pointerBank)
      (by simp +decide [z, pointerBank, PointerBoxProduct.Reg.base,
        PointerBoxProduct.callableBank, CallableProduct.Reg.base, PointerBoxProduct.Reg.left,
        PointerBoxProduct.Reg.right, PointerBoxProduct.Reg.queries])
      (by simp +decide [z, pointerBank, PointerBoxProduct.Reg.left,
        PointerBoxProduct.Reg.right, PointerBoxProduct.Reg.queries])
      (by simp +decide [z, pointerBank, PointerBoxProduct.Reg.right,
        PointerBoxProduct.Reg.queries]) (by simp [z])
      hheader hthreshold hsb hrb hqb hleft hright hqueries hX hY ht hN hfit)
  change c.regs (pointerBank (PointerBoxProduct.callableBank CallableProduct.Reg.result)) = _ at cr
  let y := c.set Reg.result (b + QueriedProduct.outputBase (21 * m) m N qs.length)
  have hy : ExecWithin (B := .standard) W (.op (.copy Reg.result
      (pointerBank (PointerBoxProduct.callableBank CallableProduct.Reg.result)))) c y 1 := by
    simpa only [y, cr] using (ExecWithin.copy (w := W) (x := c) (d := Reg.result)
      (s := pointerBank (PointerBoxProduct.callableBank CallableProduct.Reg.result)))
  refine ⟨y, (hz.seq (hc.seq hy)).mono (by omega), by simp [y], cv, cf, ?_⟩
  intro i hi hne
  have hbank (j) : pointerBank j ≠ i := by
    intro hj
    have hv := congrArg Fin.val hj
    change 128 + j.val = i.val at hv
    omega
  rw [Data.set_regs, Function.update_of_ne hne, hframe i hbank]
  simp only [z, Data.set_regs,
    Function.update_of_ne (hbank PointerBoxProduct.Reg.queries).symm,
    Function.update_of_ne (hbank PointerBoxProduct.Reg.right).symm,
    Function.update_of_ne (hbank PointerBoxProduct.Reg.left).symm,
    Function.update_of_ne (hbank PointerBoxProduct.Reg.base).symm]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
