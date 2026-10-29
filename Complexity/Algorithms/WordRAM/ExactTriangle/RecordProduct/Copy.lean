/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Header

/-!
# Three charged original-input copies

The left and right raw matrices and every interleaved query occurrence are copied separately.
Sources lie below the actual producer heap end. Only the destination spans are written; no
caller catalogue, virtual window or unrelated allocation is cleared or copied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM

/-- All three original arrays are copied with native loops, at fourteen instructions per
matrix cell/query pair plus constant argument and loop overhead. -/
theorem exec_copyInputs {W b A Q s t q : ℕ} (x : Data 320)
    (hb : x.regs Reg.base = b) (hA : x.regs Reg.area = A)
    (hQ : x.regs Reg.count = Q) (hs : x.regs Reg.left = s)
    (ht : x.regs Reg.right = t) (hq : x.regs Reg.queries = q)
    (hsb : s + A ≤ b) (htb : t + A ≤ b) (hqb : q + 2 * Q ≤ b)
    (hfit : Fits W (2 * b + 2 * A + 2 * Q + 64)) :
    ∃ y, ExecWithin W copyInputs x y (14 * A + 14 * Q + 21) ∧
      (∀ a < A, y.mem (b + 5 + a) = x.mem (s + a)) ∧
      (∀ a < A, y.mem (b + 5 + A + a) = x.mem (t + a)) ∧
      (∀ a < 2 * Q, y.mem (b + 5 + 2 * A + a) = x.mem (q + a)) ∧
      (∀ a, a < b + 5 ∨ b + 5 + 2 * A + 2 * Q ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 96 → i ≠ Reg.address → y.regs i = x.regs i := by
  have h5 : Fits W 5 := hfit.of_le (by omega)
  have hb5 : Fits W (b + 5) := hfit.of_le (by omega)
  have hbA : Fits W (b + 5 + A) := hfit.of_le (by omega)
  have hbAA : Fits W (b + 5 + A + A) := hfit.of_le (by omega)
  have hQQ : Fits W (Q + Q) := hfit.of_le (by omega)
  let l := x.set Reg.source s |>.set Reg.address 5 |>.set Reg.destination (b + 5)
    |>.set Reg.length A
  have hl : ExecWithin W deliverLeft x l 4 := by
    ram_eval [deliverLeft, l, hs, hb, hA, h5, hb5, Reg.source, Reg.left, Reg.address,
      Reg.destination, Reg.base, Reg.length, Reg.area]
  have lmeta (i : Fin 320) (hi : i.val < 96) (hne : i ≠ Reg.address) :
      l.regs i = x.regs i := by
    have hsource : i ≠ Reg.source := by intro h; subst i; simp [Reg.source] at hi
    have hdest : i ≠ Reg.destination := by intro h; subst i; simp [Reg.destination] at hi
    have hlen : i ≠ Reg.length := by intro h; subst i; simp [Reg.length] at hi
    simp only [l, Data.set_regs, Function.update_of_ne hsource, Function.update_of_ne hdest,
      Function.update_of_ne hlen, Function.update_of_ne hne]
  obtain ⟨a, ha, am, asrc, adst, alen, ar⟩ := exec_copy l
    (by simp +decide [l, Reg.source, Reg.address, Reg.destination, Reg.length])
    (by simp +decide [l, Reg.destination, Reg.length]) (by simp [l])
    (by omega : s + A ≤ b + 5) (hfit.of_le (by omega))
  have aA : a.regs Reg.area = A :=
    (ar _ (by decide)).trans ((lmeta _ (by decide) (by decide)).trans hA)
  have aRight : a.regs Reg.right = t :=
    (ar _ (by decide)).trans ((lmeta _ (by decide) (by decide)).trans ht)
  let r := a.set Reg.source t |>.set Reg.destination (b + 5 + A)
  have hr : ExecWithin W deliverRight a r 2 := by
    ram_eval [deliverRight, r, aRight, adst, aA, hbA, Reg.source, Reg.right,
      Reg.destination, Reg.area]
  obtain ⟨c, hc, cm, csrc, cdst, clen, cr⟩ := exec_copy r
    (by simp +decide [r, Reg.source, Reg.destination]) (by simp [r])
    (by simpa +decide [r, Reg.length, Reg.source, Reg.destination] using alen)
    (by omega : t + A ≤ b + 5 + A)
    (hfit.of_le (by omega))
  have rmeta (i : Fin 320) (hi : i.val < 96) : r.regs i = a.regs i := by
    have hsource : i ≠ Reg.source := by intro h; subst i; simp [Reg.source] at hi
    have hdest : i ≠ Reg.destination := by intro h; subst i; simp [Reg.destination] at hi
    simp only [r, Data.set_regs, Function.update_of_ne hsource, Function.update_of_ne hdest]
  have cA : c.regs Reg.area = A :=
    (cr _ (by decide)).trans ((rmeta _ (by decide)).trans aA)
  have cq : c.regs Reg.queries = q := (cr _ (by decide)).trans
    ((rmeta _ (by decide)).trans
      ((ar _ (by decide)).trans ((lmeta _ (by decide) (by decide)).trans hq)))
  have cQ : c.regs Reg.count = Q := (cr _ (by decide)).trans
    ((rmeta _ (by decide)).trans
      ((ar _ (by decide)).trans ((lmeta _ (by decide) (by decide)).trans hQ)))
  let z := c.set Reg.source q |>.set Reg.destination (b + 5 + A + A)
    |>.set Reg.length (Q + Q)
  have hz : ExecWithin W deliverQueries c z 3 := by
    ram_eval [deliverQueries, z, cq, cdst, cA, cQ, hbAA, hQQ, Reg.source,
      Reg.queries, Reg.destination, Reg.area, Reg.length, Reg.count]
  obtain ⟨y, hy, ym, ysrc, ydst, ylen, yr⟩ := exec_copy z
    (by simp +decide [z, Reg.source, Reg.destination, Reg.length])
    (by simp +decide [z, Reg.destination, Reg.length]) (by simp [z])
    (by omega : q + (Q + Q) ≤ b + 5 + A + A) (hfit.of_le (by omega))
  have arMem : a.mem = ArrayCopy.copyPrefix x.mem s (b + 5) A := am
  have crMem : c.mem = ArrayCopy.copyPrefix a.mem t (b + 5 + A) A := cm
  have yrMem : y.mem = ArrayCopy.copyPrefix c.mem q (b + 5 + A + A) (Q + Q) := ym
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hl.seq (ha.seq (hr.seq (hc.seq (hz.seq hy))))).mono (by omega)
  · intro j hj
    rw [yrMem, ArrayCopy.copyPrefix_outside (by omega), crMem,
      ArrayCopy.copyPrefix_outside (by omega), arMem, ArrayCopy.copyPrefix_read hj]
  · intro j hj
    rw [yrMem, ArrayCopy.copyPrefix_outside (by omega), crMem, ArrayCopy.copyPrefix_read hj,
      arMem, ArrayCopy.copyPrefix_outside (by omega)]
  · intro j hj
    have hj' : j < Q + Q := by omega
    rw [show b + 5 + 2 * A + j = b + 5 + A + A + j by omega,
      yrMem, ArrayCopy.copyPrefix_read hj', crMem,
      ArrayCopy.copyPrefix_outside (by omega), arMem,
      ArrayCopy.copyPrefix_outside (by omega)]
  · intro j hj
    rw [yrMem, ArrayCopy.copyPrefix_outside (by omega), crMem,
      ArrayCopy.copyPrefix_outside (by omega), arMem,
      ArrayCopy.copyPrefix_outside (by omega)]
  · intro i hi hne
    have hsource : i ≠ Reg.source := by intro h; subst i; simp [Reg.source] at hi
    have hdest : i ≠ Reg.destination := by intro h; subst i; simp [Reg.destination] at hi
    have hlen : i ≠ Reg.length := by intro h; subst i; simp [Reg.length] at hi
    rw [yr i (Or.inl hi)]
    simp only [z, Data.set_regs, Function.update_of_ne hsource,
      Function.update_of_ne hdest, Function.update_of_ne hlen]
    rw [cr i (Or.inl hi)]
    simp only [r, Data.set_regs, Function.update_of_ne hsource, Function.update_of_ne hdest]
    rw [ar i (Or.inl hi)]
    simp only [l, Data.set_regs, Function.update_of_ne hsource, Function.update_of_ne hdest,
      Function.update_of_ne hlen, Function.update_of_ne hne]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
