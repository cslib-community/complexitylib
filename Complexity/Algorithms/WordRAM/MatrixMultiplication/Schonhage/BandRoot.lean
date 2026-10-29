/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram

/-!
# Native integer square root for band parameters

## Main results

* `BandPreparation.exec_root`: successive squared comparisons compute the ordinary natural
  square root within `5 * sqrt k + 6` instructions, with every trial square proved to fit.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM

/-- The root loop uses only increment, multiplication and unsigned comparison. The bound on
trial squares is derived from the original count, including the first failing trial. -/
theorem exec_root {w : ℕ} (k : ℕ) (x : Data 96)
    (hk : x.regs count = k) (ho : x.regs one = 1) (hfit : Fits w (4 * k + 4)) :
    ∃ y, ExecWithin w rootCode x y (5 * Nat.sqrt k + 6) ∧
      y.regs root = Nat.sqrt k ∧ y.regs square = Nat.sqrt k * Nat.sqrt k ∧
      y.mem = x.mem ∧
      (∀ i, i ≠ root → i ≠ square → i ≠ temporary → i ≠ limit → y.regs i = x.regs i) := by
  have h0 : Fits w 0 := hfit.of_le (by omega)
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have hnext : Fits w (k + 1) := hfit.of_le (by omega)
  let start := ((x.set root 0).set square 1).set limit (k + 1)
  have hs : ExecWithin w (ram[ root ← #0; square ← #1; limit ← count + one ])
      x start 3 := by
    ram_eval [start, hk, ho, h0, h1, hnext, root, square, limit, count, one, Fin.mk.injEq]
  let I (y : Data 96) : Prop :=
    y.mem = x.mem ∧ y.regs one = 1 ∧ y.regs limit = k + 1 ∧
      y.regs root ≤ Nat.sqrt k ∧
      y.regs square = (y.regs root + 1) * (y.regs root + 1)
  have hi : I start := by simp [I, start, ho, root, square, limit, one]
  have hb (y : Data 96) (hy : I y) (hc : (Cond.lt square limit).Holds y) :
      ∃ z, ExecWithin w rootBody y z 3 ∧ I z ∧
        Nat.sqrt k - z.regs root < Nat.sqrt k - y.regs root := by
    obtain ⟨hm, h1, hlimit, hr, hsq⟩ := hy
    have htrial : (y.regs root + 1) * (y.regs root + 1) ≤ k := by
      simpa only [Cond.holds_lt, hlimit, hsq, Nat.lt_add_one_iff] using hc
    have hrnext : y.regs root + 1 ≤ Nat.sqrt k := Nat.le_sqrt.mpr htrial
    have hlarge : (y.regs root + 2) * (y.regs root + 2) ≤ 4 * k + 4 := by
      nlinarith only [htrial]
    have hrfit : Fits w (y.regs root + 1) :=
      hfit.of_le (by have := Nat.sqrt_le_self k; omega)
    have htfit : Fits w (y.regs root + 2) :=
      hfit.of_le (by have := Nat.sqrt_le_self k; omega)
    have hsfit : Fits w ((y.regs root + 2) * (y.regs root + 2)) := hfit.of_le hlarge
    let z := ((y.set root (y.regs root + 1)).set temporary (y.regs root + 2)).set
      square ((y.regs root + 2) * (y.regs root + 2))
    have he : ExecWithin w rootBody y z 3 := by
      ram_eval [rootBody, z, h1, hrfit, htfit, hsfit,
        root, temporary, square, one, Fin.mk.injEq, Nat.add_assoc]
    refine ⟨z, he, ?_, ?_⟩
    · simpa +decide [I, z, root, temporary, square, one, limit, Function.update_apply,
        Nat.add_assoc] using
        (show y.mem = x.mem ∧ y.regs one = 1 ∧ y.regs limit = k + 1 ∧
          y.regs root + 1 ≤ Nat.sqrt k ∧
          (y.regs root + 2) * (y.regs root + 2) =
            (y.regs root + 1 + 1) * (y.regs root + 1 + 1) from
          ⟨hm, h1, hlimit, hrnext, by ring⟩)
    · have hz : z.regs root = y.regs root + 1 := by simp [z, root, square, temporary]
      rw [hz]
      omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => Nat.sqrt k - y.regs root) hb hi
  have hr : y.regs root = Nat.sqrt k := by
    have hstop : k < (y.regs root + 1) * (y.regs root + 1) := by
      simp only [Cond.holds_lt, hy.2.2.1, hy.2.2.2.2] at hc
      omega
    exact Nat.eq_sqrt.mpr ⟨(Nat.le_sqrt.mp hy.2.2.2.1), hstop⟩
  let z := y.set square (Nat.sqrt k * Nat.sqrt k)
  have ht : ExecWithin w (ram[ square ← root * root ]) y z 1 := by
    ram_eval [z, hr, hfit.of_le (Nat.sqrt_le k |>.trans (by omega)), square, root]
  have hwhole : ExecWithin w rootCode x z (5 * Nat.sqrt k + 6) := by
    apply (hs.seq (he.seq ht)).mono
    have hsroot : start.regs root = 0 := by simp [start, root, square, limit]
    rw [hsroot, Nat.sub_zero]
    omega
  refine ⟨z, hwhole, ?_, ?_, hy.1, ?_⟩
  · simpa [z, square, root] using hr
  · simp [z]
  · intro i hr hs ht hl
    apply hwhole.regs_eq
    have hf : ∀ i : Fin 96, i ≠ root → i ≠ square → i ≠ temporary → i ≠ limit →
        rootCode.Preserves i := by decide
    exact hf i hr hs ht hl

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
