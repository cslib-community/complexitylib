/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.TileKernels
public import CslibFrontier.Computability.GenericRAM.Signed.Fits
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Complete native ten-child accumulation

The actual child loop reads each directory rank and signed child value once. Every
intermediate signed sum fits by one mathematical bound on the ten child magnitudes;
there is no separate intermediate-fit or execution certificate among the inputs.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM
open scoped BigOperators

/-- All ten actual child additions, including loop tests and the final exit, cost at most 312. -/
theorem exec_childLoop {w D V c e T p R C : ℕ} (x : Data registers)
    (b : ℕ → ℤ) (rank : ℕ → ℕ)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hc : x.regs Reg.completion = c) (he : x.regs Reg.stars = e)
    (hT : x.regs Reg.span = T) (hTpos : 0 < T) (hp : x.regs Reg.starPower = p)
    (hd : x.regs Reg.term = 0) (hacc : x.regs Reg.accumulator = 0)
    (h9 : x.regs Reg.nine = 9) (h1 : x.regs Reg.one = 1)
    (h10 : x.regs Reg.ten = 10)
    (hrank : ∀ d < 10,
      x.mem (D + ((e - 1) * T + (c - (9 - d) * p))) = rank d + 1)
    (hvalue : ∀ d < 10, x.mem (V + rank d) = Signed.encode (b d))
    (hrange : ∀ d < 10, rank d ≤ R)
    (hmag : ∀ d < 10, (b d).natAbs ≤ C)
    (hsigned : GenericRAM.Signed.Fits w (10 * C : ℕ))
    (hfit : Fits (w + 2) (D + V + c + e * T + 10 * p + R + 30)) :
    ∃ y, ExecWithin (w + 2) (.loop (.lt Reg.term Reg.ten) addChild) x y 312 ∧
      y.regs Reg.term = 10 ∧
      y.regs Reg.accumulator = Signed.encode (∑ d ∈ Finset.range 10, b d) ∧
      y.mem = x.mem ∧ (∀ i, ¬ChildLocal i → y.regs i = x.regs i) := by
  have hsum (k : ℕ) (hk : k ≤ 10) :
      (∑ d ∈ Finset.range k, b d).natAbs ≤ 10 * C := by
    calc
      _ ≤ ∑ d ∈ Finset.range k, (b d).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _d ∈ Finset.range k, C := Finset.sum_le_sum fun d hd =>
        hmag d ((Finset.mem_range.mp hd).trans_le hk)
      _ = k * C := by simp
      _ ≤ 10 * C := Nat.mul_le_mul_right C hk
  let P (j : ℕ) (y : Data registers) : Prop :=
    y.regs Reg.accumulator = Signed.encode (∑ d ∈ Finset.range j, b d) ∧
      y.mem = x.mem ∧ (∀ i, ¬ChildLocal i → y.regs i = x.regs i)
  have hi : P (x.regs Reg.term) x := by
    refine ⟨?_, rfl, fun _ _ => rfl⟩
    simp [hd, hacc, Signed.encode]
  have hb (y : Data registers) (hy : P (y.regs Reg.term) y) (hlt : y.regs Reg.term < 10) :
      ∃ z, ExecWithin (w + 2) addChild y z 29 ∧ P (y.regs Reg.term + 1) z ∧
        z.regs Reg.term = y.regs Reg.term + 1 := by
    obtain ⟨hsumy, hmem, hregs⟩ := hy
    have hchildmag : (b (y.regs Reg.term)).natAbs ≤ 10 * C :=
      (hmag _ hlt).trans (by omega)
    have hchildrank := hrange _ hlt
    obtain ⟨z, hz, hza, hzd, hzm, hzf⟩ := exec_addChild
      (hsigned.of_natAbs_le (hsum _ hlt.le)) (hsigned.of_natAbs_le hchildmag) y
      ((hregs _ (by decide)).trans hD) ((hregs _ (by decide)).trans hV)
      ((hregs _ (by decide)).trans hc) ((hregs _ (by decide)).trans he)
      ((hregs _ (by decide)).trans hT) hTpos ((hregs _ (by decide)).trans hp)
      rfl hsumy ((hregs _ (by decide)).trans h9) ((hregs _ (by decide)).trans h1)
      (by simpa only [hmem] using hrank _ hlt)
      (by simpa only [hmem] using hvalue _ hlt)
      (hfit.of_le (by omega))
    refine ⟨z, hz, ⟨?_, hzm.trans hmem,
      fun i hi => (hzf i hi).trans (hregs i hi)⟩, hzd⟩
    simpa only [Finset.sum_range_succ] using hza
  obtain ⟨y, hy, ⟨hya, hym, hyf⟩, hdone⟩ := ExecWithin.loop_count P
    (fun _ ⟨_, _, hf⟩ => (hf _ (by decide)).trans h10) hb (by simp [hd]) hi
  exact ⟨y, by simpa only [hd] using hy, hdone, hya, hym, hyf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
