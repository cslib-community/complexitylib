/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Real counter residue-array calls

Four charged argument copies invoke the existing signed-remainder loop. Every resulting
residue is an unsigned key; canonical signed decoding is performed inside the actual callee.
The original high-bank metadata and all memory outside the destination are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Complete actual residue call for a matrix, with source and destination parameters in the
protected metadata bank. No residue array is supplied to the algorithm. -/
theorem exec_residues {w n p a b : ℕ} (src dst : Fin 128) (x : Data 128)
    (hsrc : 64 ≤ src.val) (hdst : 64 ≤ dst.val) (values : ℕ → ℤ)
    (hp : 0 < p) (hc : x.regs Reg.cells = n * n)
    (ha : x.regs src = a) (hb : x.regs dst = b)
    (hm : x.regs Reg.encodedModulus = encode (p : ℤ))
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hv : ∀ i < n * n, GenericRAM.Signed.Fits w (values i))
    (haf : Fits (w + 2) (a + n * n)) (hbf : Fits (w + 2) (b + n * n))
    (hdisjoint : a + n * n ≤ b)
    (hinput : ∀ i < n * n, x.mem (a + i) = encode (values i)) :
    ∃ y, ExecWithin (w + 2) (residues src dst) x y (23 * (n * n) + 8) ∧
      (∀ i < n * n, y.mem (b + i) = (values i % (p : ℤ)).toNat) ∧
      (∀ d, d < b ∨ b + n * n ≤ d → y.mem d = x.mem d) ∧
      ∀ j, 16 ≤ j.val → y.regs j = x.regs j := by
  let z := (((x.set Reg.low9 a).set Reg.low10 b).set Reg.low11 (n * n)).set
    Reg.low12 (encode (p : ℤ))
  have args : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.low9 ← src; Reg.low10 ← dst; Reg.low11 ← Reg.cells;
        Reg.low12 ← Reg.encodedModulus ]) x z 4 := by
    have hs : src ≠ Reg.low9 := by intro he; subst src; contradiction
    have hd9 : dst ≠ Reg.low9 := by intro he; subst dst; contradiction
    have hd10 : dst ≠ Reg.low10 := by intro he; subst dst; contradiction
    ram_eval [z, ha, hb, hc, hm, hs, hd9, hd10, Reg.low9, Reg.low10, Reg.low11, Reg.low12,
      Reg.cells, Reg.encodedModulus]
  let f : Fin 16 → Fin 128 := Fin.castLE (by decide)
  have za : (z.comap f).regs ThreeSum.ChanHe.Residues.src = a := by
    simp +decide [z, f, Data.comap, ThreeSum.ChanHe.Residues.src,
      Reg.low9, Reg.low10, Reg.low11, Reg.low12]
  have zb : (z.comap f).regs ThreeSum.ChanHe.Residues.dst = b := by
    simp +decide [z, f, Data.comap, ThreeSum.ChanHe.Residues.dst,
      Reg.low10, Reg.low11, Reg.low12]
  have zl : (z.comap f).regs ThreeSum.ChanHe.Residues.len = n * n := by
    simp +decide [z, f, Data.comap, ThreeSum.ChanHe.Residues.len, Reg.low11, Reg.low12]
  have zp : (z.comap f).regs ThreeSum.ChanHe.Residues.modulus = encode (p : ℤ) := by
    simp [z, f, Data.comap, ThreeSum.ChanHe.Residues.modulus, Reg.low12]
  obtain ⟨s, he, memory, _⟩ := ThreeSum.ChanHe.Residues.exec (z.comap f) values hp hmod zp
    (by simpa only [zl] using hv) (by simpa only [za, zl] using haf)
    (by simpa only [zb, zl] using hbf) (by simpa only [za, zb, zl] using hdisjoint)
    (by simpa only [za, zl, show (z.comap f).mem = x.mem from rfl] using hinput)
  let y := s.extend f z
  have call : ExecWithin (w + 2)
      (ThreeSum.ChanHe.Residues.program.rename f) z y (23 * (n * n) + 4) := by
    simpa only [zl] using he.rename (Fin.castLE_injective _)
  have full : ExecWithin (w + 2) (residues src dst) x y (23 * (n * n) + 8) :=
    (args.seq call).mono (by omega)
  have ym : y.mem = ThreeSum.ChanHe.Residues.memory x.mem values p b (n * n) := by
    change s.mem = _
    simpa only [zl, zb, show (z.comap f).mem = x.mem from rfl] using memory
  refine ⟨y, full, ?_, ?_, ?_⟩
  · intro i hi
    rw [ym]
    simp only [ThreeSum.ChanHe.Residues.memory, show b ≤ b + i ∧ b + i < b + n * n by omega,
      and_self, ite_true, Nat.add_sub_cancel_left]
  · intro d hd
    rw [ym]
    simp only [ThreeSum.ChanHe.Residues.memory, show ¬(b ≤ d ∧ d < b + n * n) by omega,
      ite_false]
  · intro j hj
    have hyj : y.regs j = z.regs j := by
      apply Function.extend_apply'
      rintro ⟨q, heq⟩
      have heqv := congrArg Fin.val heq
      change q.val = j.val at heqv
      omega
    apply hyj.trans
    simp only [z, Data.set,
      Function.update_of_ne (show j ≠ Reg.low9 by intro h; subst j; contradiction),
      Function.update_of_ne (show j ≠ Reg.low10 by intro h; subst j; contradiction),
      Function.update_of_ne (show j ≠ Reg.low11 by intro h; subst j; contradiction),
      Function.update_of_ne (show j ≠ Reg.low12 by intro h; subst j; contradiction)]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
