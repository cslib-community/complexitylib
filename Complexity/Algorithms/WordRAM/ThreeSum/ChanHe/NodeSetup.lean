/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeProgram

/-!
# Charged runtime layout and tag setup for one Chan–He node

## Main definitions

* `NodePacking.Prepared`: exact computed layout, encoded tags and fixed constants.

## Main results

* `NodePacking.exec_layout`: all address calculations are native instructions.

## References

These native setup proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM

/-- The immutable caller arguments survive every phase of the node program. -/
def Parameters (x y : Data 64) : Prop :=
  ∀ i, 46 ≤ i.val ∧ i.val ≤ 55 → y.regs i = x.regs i

/-- Runtime arguments, computed bases, encoded tags and constants retained by every round.
Register 61 is the sole setup scratch register in this range. -/
def Frame (x y : Data 64) : Prop :=
  ∀ i, 46 ≤ i.val → i ≠ temporary → y.regs i = x.regs i

/-- The computed runtime layout and encoded tag constants. -/
def Prepared (L : Layout) (y : Data 64) : Prop :=
  y.regs scratch = L.scratch ∧ y.regs histogram = L.hist ∧ y.regs packed = L.packed ∧
    y.regs gap = 2 * L.gap ∧ y.regs padding = 4 * L.U + 2 ∧
    y.regs one = 1 ∧ y.regs four = 4

/-- A caller frame transports the prepared address/tag interface. -/
theorem Prepared.of_frame {L : Layout} {x y : Data 64} (hx : Prepared L x) (hr : Frame x y) :
    Prepared L y := by
  obtain ⟨hk, hh, hp, hg, hpad, h1, h4⟩ := hx
  exact ⟨(hr scratch (by decide) (by decide)).trans hk,
    (hr histogram (by decide) (by decide)).trans hh,
    (hr packed (by decide) (by decide)).trans hp,
    (hr gap (by decide) (by decide)).trans hg,
    (hr padding (by decide) (by decide)).trans hpad,
    (hr one (by decide) (by decide)).trans h1, (hr four (by decide) (by decide)).trans h4⟩

/-- A caller frame transports the immutable input/size interface. -/
theorem Parameters.of_frame {x y z : Data 64} (hy : Parameters x y) (hr : Frame y z) :
    Parameters x z := by
  intro i hi
  have hne : i ≠ temporary := by intro h; subst i; norm_num [temporary] at hi
  exact (hr i hi.1 hne).trans (hy i hi)

/-- Exact native arguments for writing the four-column padding pattern. -/
def PaddingReady (L : Layout) (y : Data 64) : Prop :=
  y.regs pdst = L.packed ∧ y.regs plen = L.N ∧
    y.regs pad0 = 120 * L.U + 80 ∧ y.regs pad1 = 16 * L.U + 10 ∧
    y.regs pad2 = 40 * L.U + 26 ∧ y.regs pad3 = 44 * L.U + 30

/-- Compute the disjoint addresses from the supplied runtime lengths and fresh base. -/
theorem exec_layout {w : ℕ} (x : Data 64) (hfit : Fits w (layout x).budget) :
    ∃ y, ExecWithin w layoutCode x y 12 ∧ Parameters x y ∧ y.mem = x.mem ∧
      y.regs packed = (layout x).packed ∧ y.regs scratch = (layout x).scratch ∧
      y.regs histogram = (layout x).hist ∧ y.regs one = 1 ∧ y.regs four = 4 ∧
      y.regs temporary = 3 := by
  let L := layout x
  have hfit' : Fits w L.budget := hfit
  have fb := hfit'.of_le L.bounds.1
  have f (v : ℕ) (hv : v ≤ L.endpoint) : Fits w v := fb.of_le hv
  have fc (v : ℕ) (hv : v ≤ 16) : Fits w v :=
    hfit'.of_le (by have := L.bounds.2.2; omega)
  have f1 : Fits w 1 := fc _ (by decide)
  have f3 : Fits w 3 := fc _ (by decide)
  have f4 : Fits w 4 := fc _ (by decide)
  have fp₀ : Fits w (x.regs base + 3) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fp₁ : Fits w (x.regs base + 3 + x.regs (length 0)) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fp₂ : Fits w (x.regs base + 3 + x.regs (length 0) + x.regs (length 1)) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fp : Fits w (x.regs base + 3 + x.regs (length 0) + x.regs (length 1) +
      x.regs (length 2)) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fn : Fits w (4 * x.regs groups) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fk : Fits w (x.regs base + 3 + x.regs (length 0) + x.regs (length 1) +
      x.regs (length 2) + 4 * x.regs groups) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fh₀ : Fits w (x.regs base + 3 + x.regs (length 0) + x.regs (length 1) +
      x.regs (length 2) + 4 * x.regs groups + x.regs (length 0)) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fh₁ : Fits w (x.regs base + 3 + x.regs (length 0) + x.regs (length 1) +
      x.regs (length 2) + 4 * x.regs groups + x.regs (length 0) + x.regs (length 1)) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  have fh : Fits w (x.regs base + 3 + x.regs (length 0) + x.regs (length 1) +
      x.regs (length 2) + 4 * x.regs groups + x.regs (length 0) + x.regs (length 1) +
      x.regs (length 2)) :=
    f _ (by dsimp only [L, layout, Layout.endpoint, Layout.hist, Layout.scratch,
      Layout.packed, Layout.total]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · ram_eval [layoutCode, f1, f3, f4, fp₀, fp₁, fp₂, fp, fn, fk, fh₀, fh₁, fh]
  · intro i hi
    fin_cases i <;> norm_num at hi <;> rfl
  · rfl
  · simp +decide only [Data.set_regs, Function.update_apply, packed, scratch, histogram,
      one, four, temporary, ↓reduceIte]
    dsimp only [layout, Layout.packed, Layout.total]
    omega
  · simp +decide only [Data.set_regs, Function.update_apply, packed, scratch, histogram,
      one, four, temporary, ↓reduceIte]
    dsimp only [layout, Layout.scratch, Layout.packed, Layout.total]
    omega
  · simp +decide only [Data.set_regs, Function.update_apply, packed, scratch, histogram,
      one, four, temporary, ↓reduceIte]
    dsimp only [layout, Layout.hist, Layout.scratch, Layout.packed, Layout.total]
    omega
  · rfl
  · rfl
  · rfl

/-- Compute encoded tags and signed padding through native arithmetic in sixteen instructions.
The single envelope supplies every intermediate fit, including the third-column subtraction. -/
theorem exec_constants {w : ℕ} (L : Layout) (x : Data 64)
    (hfit : Fits w L.budget) (hU : x.regs magnitude = L.U) (hN : x.regs groups = L.N)
    (hk : x.regs scratch = L.scratch) (hh : x.regs histogram = L.hist)
    (hp : x.regs packed = L.packed) (h1 : x.regs one = 1) (h4 : x.regs four = 4)
    (h3 : x.regs temporary = 3) :
    ∃ y, ExecWithin w constantsCode x y 16 ∧ Parameters x y ∧ y.mem = x.mem ∧
      Prepared L y ∧ PaddingReady L y := by
  have f (v : ℕ) (hv : v ≤ 120 * L.U + 80) : Fits w v :=
    (hfit.of_le L.bounds.2.1).of_le hv
  have f₂ : Fits w 2 := f _ (by omega)
  have f₃ : Fits w 3 := f _ (by omega)
  have f₁₀ : Fits w 10 := f _ (by omega)
  have fw₀ : Fits w (L.U + L.U) := f _ (by omega)
  have fw₁ : Fits w (L.U + L.U + 1) := f _ (by omega)
  have fw : Fits w (L.U + L.U + 1 + (L.U + L.U + 1)) := f _ (by omega)
  have fg₀ : Fits w (3 * (L.U + L.U + 1 + (L.U + L.U + 1))) := f _ (by omega)
  have fg : Fits w (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2) := f _ (by omega)
  have fp₀ : Fits w (10 * (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2)) := f _ (by omega)
  have fp₁ : Fits w (L.U + L.U + 1 + (L.U + L.U + 1) +
      (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2)) := f _ (by omega)
  have fp₂₀ : Fits w (3 * (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2)) := f _ (by omega)
  have fp₂ : Fits w (3 * (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2) +
      (L.U + L.U + 1 + (L.U + L.U + 1))) := f _ (by omega)
  have fp₃₀ : Fits w (4 * (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2)) := f _ (by omega)
  have fp₃ : Fits w (4 * (3 * (L.U + L.U + 1 + (L.U + L.U + 1)) + 2) -
      (L.U + L.U + 1 + (L.U + L.U + 1))) := f _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · ram_eval [constantsCode, hU, hN, hp, h1, h4, h3, f₂, f₃, f₁₀,
      fw₀, fw₁, fw, fg₀, fg, fp₀, fp₁, fp₂₀, fp₂, fp₃₀, fp₃]
  · intro i hi
    fin_cases i <;> norm_num at hi <;> rfl
  · rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hk
    · exact hh
    · exact hp
    · simp +decide [gap, padding, temporary, pdst, plen, pad0, pad1, pad2, pad3,
        paddingRegisters, Padding.dst, Padding.len, Padding.pad0, Padding.pad1,
        Padding.pad2, Padding.pad3, Layout.gap]
      omega
    · simp +decide [gap, padding, temporary, pdst, plen, pad0, pad1, pad2, pad3,
        paddingRegisters, Padding.dst, Padding.len, Padding.pad0, Padding.pad1,
        Padding.pad2, Padding.pad3]
      omega
    · exact h1
    · exact h4
  · simp +decide [PaddingReady, gap, padding, temporary, pdst, plen, pad0, pad1, pad2, pad3,
      paddingRegisters, Padding.dst, Padding.len, Padding.pad0, Padding.pad1,
      Padding.pad2, Padding.pad3]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
