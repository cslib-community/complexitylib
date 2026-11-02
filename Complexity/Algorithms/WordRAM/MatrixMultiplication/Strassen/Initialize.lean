/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Frame
import Mathlib.Tactic.FinCases

/-!
# Actual initialized Strassen root and power call

The existing native `Power.program` computes `4^L`; a real multiplication by p computes the
coefficient-array length. Actual additions locate the root frame, and all its fields are
stored. Only original numeric parameters occur in the admission bound. No power, stack
layout, initialized scratch or intermediate execution certificate is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

private theorem locateRoot_preserves (i : Fin 64) :
    i ≠ Reg.size → i ≠ Reg.frames → i ≠ Reg.frame → i ≠ Reg.phase → i ≠ Reg.active →
      locateRoot.Preserves i := by decide +kernel +revert

/-- Compute the runtime length, constants and explicit root frame in at most `4L+30`
instructions, including the actual power call and every frame store. -/
theorem exec_setup {w : ℕ} (x : Data 64)
    (hw : Fits w (x.regs Reg.scratch + x.regs Reg.modulus * 4 ^ x.regs Reg.depth +
      4 ^ x.regs Reg.depth + x.regs Reg.depth + 16)) :
    ∃ y, ExecWithin w setup x y (4 * x.regs Reg.depth + 30) ∧
      y.regs Reg.size = x.regs Reg.modulus * 4 ^ x.regs Reg.depth ∧
      y.regs Reg.frames = x.regs Reg.scratch + x.regs Reg.modulus * 4 ^ x.regs Reg.depth ∧
      y.regs Reg.frame = y.regs Reg.frames ∧ y.regs Reg.phase = 0 ∧ y.regs Reg.active = 1 ∧
      y.regs Reg.zero = 0 ∧ y.regs Reg.one = 1 ∧ y.regs Reg.four = 4 ∧
      y.regs Reg.frameWidth = 7 ∧
      (∀ i, i ∈ [Reg.inputA, Reg.inputB, Reg.output, Reg.scratch, Reg.depth, Reg.modulus] →
        y.regs i = x.regs i) ∧
      (∀ j : Fin 7, y.mem (y.regs Reg.frame + j.val) = y.regs (field j)) ∧
      ∀ a, a < y.regs Reg.frame ∨ y.regs Reg.frame + 7 ≤ a → y.mem a = x.mem a := by
  have hpow : 0 < 4 ^ x.regs Reg.depth := by positivity
  have h7 : Fits w 7 := hw.of_le (by omega)
  have h4 : Fits w 4 := hw.of_le (by omega)
  have h1 : Fits w 1 := hw.of_le (by omega)
  let r := (((((x.set Reg.zero 0).set Reg.one 1).set Reg.four 4).set Reg.frameWidth 7).set
    Reg.powerBase 4).set Reg.powerExponent (x.regs Reg.depth)
  have hr : ExecWithin w powerArguments x r 6 := by
    ram_eval [powerArguments, r, h1, h4, h7, Reg.zero, Reg.one, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent, Reg.depth]
  let f : Fin 5 → Fin 64 := Fin.castLE (by decide)
  obtain ⟨t, ht, hvalue, _, _, htm, _, _⟩ := Power.exec 4 (x.regs Reg.depth) (by decide)
    (r.comap f)
    (by simp +decide [r, f, Data.comap, Power.base, Reg.powerBase, Reg.powerExponent])
    (by simp [r, f, Data.comap, Power.exponent, Reg.powerExponent])
    (hw.of_le (by omega))
  let s := t.extend f r
  have hpower : ExecWithin w (Power.program.rename f) r s (4 * x.regs Reg.depth + 5) :=
    ht.rename (Fin.castLE_injective _)
  have hhigh (i : Fin 64) (hi : 32 ≤ i.val) : s.regs i = r.regs i := by
    have hn : ¬∃ j, f j = i := by
      rintro ⟨j, hj⟩
      have hj' := congrArg Fin.val hj
      change j.val = i.val at hj'
      omega
    exact Function.extend_apply' _ _ _ hn
  have hsvalue : s.regs Reg.powerValue = 4 ^ x.regs Reg.depth := by
    change (s.comap f).regs Power.value = _
    rw [Data.comap_extend (Fin.castLE_injective _)]
    exact hvalue
  have hsmod : s.regs Reg.modulus = x.regs Reg.modulus := by
    simpa +decide [r, Reg.zero, Reg.one, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent, Reg.modulus] using hhigh Reg.modulus (by decide)
  have hsscratch : s.regs Reg.scratch = x.regs Reg.scratch := by
    simpa +decide [r, Reg.zero, Reg.one, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent, Reg.scratch] using hhigh Reg.scratch (by decide)
  have hsmem : s.mem = x.mem := htm
  have hsize : Fits w (4 ^ x.regs Reg.depth * x.regs Reg.modulus) := by
    rw [Nat.mul_comm]
    exact hw.of_le (by omega)
  have hframe : Fits w (x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus) := by
    rw [Nat.mul_comm (4 ^ x.regs Reg.depth)]
    exact hw.of_le (by omega)
  let root := x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus
  let u := ((((s.set Reg.size (4 ^ x.regs Reg.depth * x.regs Reg.modulus)).set Reg.frames
    root).set Reg.frame root).set Reg.phase 0).set Reg.active 1
  have hu : ExecWithin w locateRoot s u 5 := by
    ram_eval [locateRoot, u, root, hsvalue, hsmod, hsscratch, hsize, hframe, h1,
      Reg.powerValue, Reg.modulus, Reg.size, Reg.frames, Reg.frame, Reg.scratch,
      Reg.phase, Reg.active]
  have hur (i : Fin 64) (hsize : i ≠ Reg.size) (hframes : i ≠ Reg.frames)
      (hframe : i ≠ Reg.frame) (hphase : i ≠ Reg.phase) (hactive : i ≠ Reg.active) :
      u.regs i = s.regs i :=
    hu.regs_eq (locateRoot_preserves i hsize hframes hframe hphase hactive)
  have hu1 : u.regs Reg.one = 1 := by
    rw [hur Reg.one (by decide) (by decide) (by decide) (by decide) (by decide),
      hhigh Reg.one (by decide)]
    simp +decide [r, Reg.one, Reg.zero, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent]
  have huframe : u.regs Reg.frame = root := by
    simp +decide [u, Reg.size, Reg.frames, Reg.frame, Reg.phase, Reg.active]
  obtain ⟨y, hy, values, frame, regs⟩ := exec_storeFrame u hu1 (by
    rw [huframe]
    dsimp only [root]
    rw [Nat.mul_comm (4 ^ x.regs Reg.depth)]
    exact hw.of_le (by omega))
  have he : ExecWithin w setup x y (4 * x.regs Reg.depth + 30) :=
    (hr.seq (hpower.seq (hu.seq hy))).mono (by omega)
  have hyframe : y.regs Reg.frame = root := (regs Reg.frame (by decide)).trans huframe
  have hyframes : y.regs Reg.frames = root := by
    rw [regs Reg.frames (by decide)]
    simp +decide [u, Reg.frames, Reg.frame, Reg.phase, Reg.active]
  have hparams (i : Fin 64)
      (hi : i ∈ [Reg.inputA, Reg.inputB, Reg.output, Reg.scratch, Reg.depth, Reg.modulus]) :
      y.regs i = x.regs i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [regs _ (by decide), hur _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hhigh _ (by decide)] <;>
      simp +decide [r, Reg.zero, Reg.one, Reg.four, Reg.frameWidth, Reg.powerBase,
        Reg.powerExponent, Reg.inputA, Reg.inputB, Reg.output, Reg.scratch, Reg.depth, Reg.modulus]
  refine ⟨y, he, ?_, ?_, hyframe.trans hyframes.symm, ?_, ?_, ?_, ?_, ?_, ?_, hparams, ?_, ?_⟩
  · rw [regs Reg.size (by decide)]
    simp +decide [u, Reg.size, Reg.frames, Reg.frame, Reg.phase, Reg.active, Nat.mul_comm]
  · simpa only [root, Nat.mul_comm] using hyframes
  · rw [regs Reg.phase (by decide)]
    simp +decide [u, Reg.phase, Reg.active]
  · rw [regs Reg.active (by decide)]
    simp [u]
  · rw [regs Reg.zero (by decide),
      hur Reg.zero (by decide) (by decide) (by decide) (by decide) (by decide),
      hhigh Reg.zero (by decide)]
    simp +decide [r, Reg.zero, Reg.one, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent]
  · exact (regs Reg.one (by decide)).trans hu1
  · rw [regs Reg.four (by decide),
      hur Reg.four (by decide) (by decide) (by decide) (by decide) (by decide),
      hhigh Reg.four (by decide)]
    simp +decide [r, Reg.zero, Reg.one, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent]
  · rw [regs Reg.frameWidth (by decide),
      hur Reg.frameWidth (by decide) (by decide) (by decide) (by decide) (by decide),
      hhigh Reg.frameWidth (by decide)]
    simp +decide [r, Reg.zero, Reg.one, Reg.four, Reg.frameWidth,
      Reg.powerBase, Reg.powerExponent]
  · intro j
    rw [regs Reg.frame (by decide), values j, regs (field j) (by fin_cases j <;> decide)]
  · intro a ha
    rw [frame a (by simpa only [hyframe, huframe] using ha)]
    change s.mem a = x.mem a
    exact congrFun hsmem a

end Cslib.Algorithms.WordRAM.Strassen
