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

The actual preprocessing outputs and live allocation frontier are copied before a fixed-exponent
native loop computes the independent polynomial value bound. Every copy, multiplication and loop
test is charged; matrix placement no longer depends on the value-bound exponent.

## Main results

* `exec_initialize`: exact raw metadata, computed matrix base, counter and Boolean frame.

These native initialization proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Compute all outer controls from actual preprocessing registers at the global width. -/
theorem exec_initialize {r κ n w tab num N H d : ℕ} (x : Data (registerCount r))
    (hw : width κ d n ≤ w)
    (hn : x.regs (controllerRegisters r inputLength) = n)
    (ht : x.regs (preprocessingRegisters r ChanHe.Traversal.outputs) = tab)
    (hc : x.regs (preprocessingRegisters r ChanHe.Traversal.outputCount) = num)
    (hl : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = N)
    (hh : x.regs (preprocessingRegisters r ChanHe.Traversal.heap) = H) :
    ∃ y, ExecWithin w (.seq (setup κ) (power.rename (controllerRegisters r))) x y
        (4 * envelopeExponent κ + 14) ∧
      Controls tab num N ((n + 2) ^ envelopeExponent κ) H y ∧
      y.regs (controllerRegisters r current) = 0 ∧
      y.regs (controllerRegisters r answer) = x.regs (controllerRegisters r answer) ∧
      y.mem = x.mem := by
  obtain ⟨hV, hE, hB, _⟩ := envelope_fits hw
  obtain ⟨a, ha, hat, hac, hal, hah, has, hav, har, hak, hao, haz, haa, ham⟩ :=
    exec_setup x hn ht hc hl hh hB hE
  obtain ⟨y, hb, ⟨hbV, _, hbr, hbm⟩, _⟩ :=
    ExecWithin.rename_post (controller_injective r) (exec_power (a.comap (controllerRegisters r))
      (by omega : 1 ≤ n + 2) has har hav hao haz hV hE)
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.seq hb).mono (by omega)
  · constructor
    · exact (hbr _ (by decide) (by decide)).trans hat
    · exact (hbr _ (by decide) (by decide)).trans hac
    · exact (hbr _ (by decide) (by decide)).trans hal
    · exact hbV
    · exact (hbr _ (by decide) (by decide)).trans hah
    · exact (hbr _ (by decide) (by decide)).trans hao
  · exact (hbr _ (by decide) (by decide)).trans hak
  · exact (hbr _ (by decide) (by decide)).trans haa
  · exact hbm.trans ham

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
