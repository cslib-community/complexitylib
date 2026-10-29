/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Controls
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Width

/-!
# Complete native ordinary-host workspace initialization

The actual preprocessing outputs are copied before a fixed-exponent native loop computes the
polynomial word reservation. Every multiplication, loop test and final doubling is charged.

## Main results

* `exec_initialize`: exact raw metadata, computed matrix base, counter and Boolean frame.

These native initialization proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Compute all outer controls from actual preprocessing registers at the global width. -/
theorem exec_initialize {r κ n w tab num N d : ℕ} (x : Data (registerCount r))
    (hw : width κ d n ≤ w)
    (hn : x.regs (controllerRegisters r inputLength) = n)
    (ht : x.regs (preprocessingRegisters r ChanHe.Traversal.outputs) = tab)
    (hc : x.regs (preprocessingRegisters r ChanHe.Traversal.outputCount) = num)
    (hl : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = N) :
    ∃ y, ExecWithin w (.seq (setup κ) (.seq (power.rename (controllerRegisters r))
        (reserve.rename (controllerRegisters r)))) x y (4 * envelopeExponent κ + 14) ∧
      Controls tab num N ((n + 2) ^ envelopeExponent κ) y ∧
      y.regs (controllerRegisters r current) = 0 ∧
      y.regs (controllerRegisters r answer) = x.regs (controllerRegisters r answer) ∧
      y.mem = x.mem := by
  obtain ⟨hV, hE, hB, _⟩ := reservation_fits hw
  obtain ⟨a, ha, hat, hac, hal, has, hav, har, hak, hao, haz, haa, ham⟩ :=
    exec_setup x hn ht hc hl hB hE
  obtain ⟨b, hb, hbV, hb0, hbr, hbm⟩ := exec_power (a.comap (controllerRegisters r))
    (by omega : 1 ≤ n + 2) has har hav hao haz hV hE
  let V := (n + 2) ^ envelopeExponent κ
  let z := b.set workspace (2 * V)
  have hf : Fits w (2 * V) :=
    ((margin_fits hw).mono (show w - 3 ≤ w by omega)).of_le
      (by have := reservation_margin κ n; dsimp only [V]; omega)
  have hz : ExecWithin w reserve b z 1 := by
    have hf' : Fits w ((n + 2) ^ envelopeExponent κ + (n + 2) ^ envelopeExponent κ) := by
      simpa only [two_mul] using hf
    ram_eval [reserve, z, hbV, hf', V, two_mul, workspace, envelope, Fin.mk.injEq]
  have hzregs (i : Fin 16) (hi : i ≠ workspace) (hj : i ≠ envelope) (hk : i ≠ remaining) :
      z.regs i = a.regs (controllerRegisters r i) := by
    rw [Data.set_regs, Function.update_of_ne hi]
    exact hbr i hj hk
  let y := z.extend (controllerRegisters r) a
  have hy (i : Fin 16) : y.regs (controllerRegisters r i) = z.regs i :=
    extend_controller _ _ i
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · have he := ha.seq ((hb.seq hz).rename (controller_injective r))
    change ExecWithin w (.seq (setup κ) ((Code.seq power reserve).rename
      (controllerRegisters r))) x y (4 * envelopeExponent κ + 14)
    exact he.mono (by omega)
  · constructor
    · exact (hy _).trans ((hzregs _ (by decide) (by decide) (by decide)).trans hat)
    · exact (hy _).trans ((hzregs _ (by decide) (by decide) (by decide)).trans hac)
    · exact (hy _).trans ((hzregs _ (by decide) (by decide) (by decide)).trans hal)
    · rw [hy]
      simpa +decide [z, workspace, envelope] using hbV
    · rw [hy]
      change (b.set workspace (2 * V)).regs workspace = 2 * V
      rw [Data.set_regs, Function.update_self]
    · exact (hy _).trans ((hzregs _ (by decide) (by decide) (by decide)).trans hao)
  · exact (hy _).trans ((hzregs _ (by decide) (by decide) (by decide)).trans hak)
  · exact (hy _).trans ((hzregs _ (by decide) (by decide) (by decide)).trans haa)
  · exact hbm.trans ham

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
