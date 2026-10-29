/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Program

/-!
# Charged original-weight zero-sum test

The internal cell rule composes the actual two loads, their address calculations and both
existing signed additions. Its result is the exact sum of the three original weights; no
modular product or candidate certificate can make a nonzero original sum pass this test.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

private theorem loads_preserve : ∀ i : Fin 32, 9 ≤ i.val → i ≠ Reg.address →
    loadBC.Preserves i ∧ loadAC.Preserves i := by decide

/-- Actual signed verification of one original candidate vertex, with every address and
arithmetic instruction charged. The first partial sum must fit the next kernel's signed
source range; the complete initialized caller derives this from the original weight bound. -/
theorem exec_testVertex {w rb ra c : ℕ} {ab bc ac : ℤ} (x : Data 32)
    (hrowB : x.regs Reg.rowB = rb) (hrowA : x.regs Reg.rowA = ra)
    (hindex : x.regs Reg.index = c) (hwab : x.regs Reg.wab = Signed.encode ab)
    (hBC : x.mem (rb + c) = Signed.encode bc)
    (hAC : x.mem (ra + c) = Signed.encode ac)
    (haddr : Fits (w + 2) (rb + ra + c + 1))
    (hab : GenericRAM.Signed.Fits w ab) (hbc : GenericRAM.Signed.Fits w bc)
    (hac : GenericRAM.Signed.Fits w ac) (hpartial : GenericRAM.Signed.Fits w (ab + bc)) :
    ∃ y, ExecWithin (w + 2) testVertex x y 36 ∧
      y.regs Signed.result = Signed.encode (ab + bc + ac) ∧ y.mem = x.mem ∧
      ∀ i : Fin 32, 9 ≤ i.val → i ≠ Reg.address → y.regs i = x.regs i := by
  let a := x.set Signed.left (Signed.encode ab) |>.set Reg.address (rb + c)
    |>.set Signed.right (Signed.encode bc)
  have hloadB : ExecWithin (w + 2) loadBC x a 3 := by
    have hf : Fits (w + 2) (rb + c) := haddr.of_le (by omega)
    ram_eval [loadBC, a, hrowB, hindex, hwab, hBC, hf,
      Reg.address, Reg.rowB, Reg.index, Reg.wab, Signed.left, Signed.right, Fin.mk.injEq]
  obtain ⟨b, hsumB, bsum, bframe⟩ := Signed.exec_add hab hbc a
    (by simp +decide [a, Signed.left, Signed.right, Reg.address])
    (by simp +decide [a, Signed.left, Signed.right, Reg.address])
  change b.regs Signed.result = Signed.encode (ab + bc) at bsum
  have bmeta (i : Fin 32) (hi : 9 ≤ i.val) (hne : i ≠ Reg.address) :
      b.regs i = x.regs i :=
    (bframe.2 i (Or.inr hi)).trans (hloadB.regs_eq (loads_preserve i hi hne).1)
  have bra : b.regs Reg.rowA = ra := (bmeta _ (by decide) (by decide)).trans hrowA
  have bindex : b.regs Reg.index = c := (bmeta _ (by decide) (by decide)).trans hindex
  have bmem : b.mem = x.mem := bframe.1
  let d := b.set Signed.left (Signed.encode (ab + bc)) |>.set Reg.address (ra + c)
    |>.set Signed.right (Signed.encode ac)
  have hloadA : ExecWithin (w + 2) loadAC b d 3 := by
    have hf : Fits (w + 2) (ra + c) := haddr.of_le (by omega)
    ram_eval [loadAC, d, bra, bindex, bsum, bmem, hAC, hf,
      Reg.address, Reg.rowA, Reg.index, Signed.left, Signed.right, Signed.result, Fin.mk.injEq]
  obtain ⟨y, hsumA, ysum, yframe⟩ := Signed.exec_add hpartial hac d
    (by simp +decide [d, Signed.left, Signed.right, Reg.address])
    (by simp +decide [d, Signed.left, Signed.right, Reg.address])
  refine ⟨y, hloadB.seq (hsumB.seq (hloadA.seq hsumA)), ysum, ?_, ?_⟩
  · exact yframe.1.trans bmem
  · intro i hi hne
    exact (yframe.2 i (Or.inr hi)).trans
      ((hloadA.regs_eq (loads_preserve i hi hne).2).trans (bmeta i hi hne))

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
