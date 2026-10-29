/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram

/-!
# Saving the actual frontend and parameter outputs

The outer controller retains every shared scalar in registers outside the complete root program's
write set. These are copies of computed frontend results, not inputs supplied by a caller.

## Main definitions

* `Saved`: exact native outer metadata after the snapshot instructions.

## Main results

* `snapshot_exec`: execute all thirteen scalar copies and constant initializations.

The native ABI and composition proof are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Exact computed metadata retained outside the root program's register bank. -/
structure Saved (κ n : ℕ) (x : Data 128) : Prop where
  /-- Descriptor table and count produced by the frontend. -/
  base : x.regs descriptors = (Frontend.layout κ n).descriptors
  count : x.regs roots = (Frontend.layout κ n).count
  /-- Exact numeric parameter outputs. -/
  fuel : x.regs levels = Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  magnitude : x.regs inputMagnitude = (n + 2) ^ κ
  limit : x.regs candidateLimit = Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
  digits : x.regs labels = (Frontend.layout κ n).digits
  length : x.regs packedLength =
    8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2
  endpoint : x.regs firstFree = (Frontend.layout κ n).endpoint
  /-- Actual index and small constants. -/
  index : x.regs current = 0
  stride : x.regs stride = 6
  one : x.regs one = 1
  zero : x.regs zero = 0
  four : x.regs four = 4

/-- Programs restricted to lower registers retain all computed outer metadata. -/
theorem Saved.congr {κ n : ℕ} {x y : Data 128} (h : Saved κ n x)
    (hr : ∀ i : Fin 128, 109 ≤ i.val → (i.val ≤ 120 ∨ i.val = 126) →
      y.regs i = x.regs i) : Saved κ n y := by
  exact ⟨(hr _ (by decide) (by decide)).trans h.base,
    (hr _ (by decide) (by decide)).trans h.count,
    (hr _ (by decide) (by decide)).trans h.fuel,
    (hr _ (by decide) (by decide)).trans h.magnitude,
    (hr _ (by decide) (by decide)).trans h.limit,
    (hr _ (by decide) (by decide)).trans h.digits,
    (hr _ (by decide) (by decide)).trans h.length,
    (hr _ (by decide) (by decide)).trans h.endpoint,
    (hr _ (by decide) (by decide)).trans h.index,
    (hr _ (by decide) (by decide)).trans h.stride,
    (hr _ (by decide) (by decide)).trans h.one,
    (hr _ (by decide) (by decide)).trans h.zero,
    (hr _ (by decide) (by decide)).trans h.four⟩

/-- Saving computed scalars and initializing the outer constants changes no memory. -/
theorem snapshot_exec {κ n w : ℕ} (x : Data 128)
    (hp : Parameters.Output n ((n + 2) ^ κ) (x.comap Frontend.parameterRegisters))
    (hb : x.regs Frontend.descriptorBase = (Frontend.layout κ n).descriptors)
    (hc : x.regs Frontend.descriptorCount = (Frontend.layout κ n).count)
    (he : x.regs Frontend.heapEnd = (Frontend.layout κ n).endpoint)
    (h6 : Fits w 6) : ∃ y, Exec w snapshot x y 13 ∧ Saved κ n y ∧ y.mem = x.mem := by
  let l := Frontend.layout κ n
  let y := x |>.set descriptors l.descriptors |>.set roots l.count
    |>.set levels (Cslib.Algorithms.ThreeSum.ChanHe.fuel n)
    |>.set inputMagnitude ((n + 2) ^ κ)
    |>.set candidateLimit (Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ))
    |>.set labels l.digits
    |>.set packedLength (8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2)
    |>.set firstFree l.endpoint |>.set current 0 |>.set stride 6
    |>.set one 1 |>.set zero 0 |>.set four 4
  have hf := hp.fuel
  have hU := hp.magnitude
  have hm := hp.primeBound
  have hΛ := hp.digits
  have hN := hp.packedLen
  simp only [Data.comap_regs] at hf hU hm hΛ hN
  have h1 : Fits w 1 := h6.of_le (by decide)
  have h4 : Fits w 4 := h6.of_le (by decide)
  refine ⟨y, ?_, ?_, rfl⟩
  · ram_eval [snapshot, y, l, hb, hc, he, hf, hU, hm, hΛ, hN, h1, h4, h6,
      Frontend.layout, descriptors, roots, levels, inputMagnitude, candidateLimit,
      labels, packedLength, firstFree, current, stride, one, zero, four]
  · constructor <;> simp +decide [y, l, descriptors, roots, levels, inputMagnitude,
      candidateLimit, labels, packedLength, firstFree, current, stride, one, zero, four]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
