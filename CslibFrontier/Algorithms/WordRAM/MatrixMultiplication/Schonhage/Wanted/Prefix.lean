/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.PrefixStep
public import CslibFrontier.Computability.WordRAM.Sequence

import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Complete native tile-prefix pass

## Main results

* `Wanted.exec_prefix`: compute every exact tile span and initialize its scatter cursor,
  including the terminal query-count offset, with native loads, stores and loop controls.

This is an internal implementation API of the complete routing program.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The actual prefix loop initializes every immutable span and mutable cursor. Neither
the offsets nor the total input length are supplied as precomputed memory certificates. -/
theorem exec_prefix {w L m N Q : ℕ} (key : ℕ → ℕ)
    (hkey : ∀ i < Q, key i < numBands L m N ^ 2) (x : Data 96)
    (hx : Parameters L m N Q x)
    (hcounts : ∀ t < numBands L m N ^ 2,
      x.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w prefixCode x y (10 * numBands L m N ^ 2 + 6) ∧
      Parameters L m N Q y ∧
      (∀ t ≤ numBands L m N ^ 2,
        y.mem (offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q) ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => key k < t) Q) ∧
      y.mem (offsetAddress L m N Q + numBands L m N ^ 2) = Q ∧
      (∀ a, a < offsetAddress L m N Q ∨ codeAddress L m N Q ≤ a → y.mem a = x.mem a) := by
  let T := numBands L m N ^ 2
  let P (j : ℕ) (z : Data 96) : Prop := Parameters L m N Q z ∧
    z.regs total = Nat.count (fun k => key k < j) Q ∧
    (∀ t < j,
      z.mem (offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q ∧
      z.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => key k < t) Q) ∧
    (∀ t < T, z.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) Q) ∧
    (∀ a, a < offsetAddress L m N Q ∨ codeAddress L m N Q ≤ a → z.mem a = x.mem a)
  let start := (x.set index 0).set total 0
  have hs : ExecWithin w (ram[index ← #0; total ← #0] : Code .standard 96) x start 2 := by
    ram_eval [start]
  have hp : Parameters L m N Q start := hx.reframe (by
    intro i hi
    apply hs.regs_eq
    have h : ∀ i ∈ parameterRegisters,
        (ram[index ← #0; total ← #0] : Code .standard 96).Preserves i := by decide +kernel
    exact h i hi)
  have hi : P (start.regs index) start := by
    refine ⟨hp, ?_, by simp [start, index, total],
      hcounts, by simp [start]⟩
    simp [start, index, total]
  have hb (z : Data 96) (hz : P (z.regs index) z) (hn : z.regs index < T) :
      ∃ u, ExecWithin w prefixStep z u 8 ∧
        P (z.regs index + 1) u ∧ u.regs index = z.regs index + 1 := by
    obtain ⟨u, he, hu, hidx, hsum, hoff, hcur, hf⟩ := exec_prefixStep key hn z hz.1 rfl
      hz.2.1 (hz.2.2.2.1 _ hn) hfit
    refine ⟨u, he, ⟨hu, hsum, ?_, ?_, ?_⟩, hidx⟩
    · intro t ht
      by_cases ht' : t = z.regs index
      · subst t
        exact ⟨hoff, hcur⟩
      · have hlt : t < z.regs index := by omega
        have hsep : offsetAddress L m N Q + t < cursorAddressBase L m N Q := by
          unfold cursorAddressBase
          omega
        have hsep' : offsetAddress L m N Q + z.regs index < cursorAddressBase L m N Q := by
          unfold cursorAddressBase
          dsimp [T] at hn
          omega
        rw [hf _ (by omega) (by omega), hf _ (by omega) (by omega)]
        exact hz.2.2.1 t hlt
    · intro t ht
      have hcount : countAddress L Q + t < offsetAddress L m N Q := by
        unfold offsetAddress
        exact Nat.add_lt_add_left ht _
      have hcursor : offsetAddress L m N Q ≤ cursorAddressBase L m N Q := by
        unfold cursorAddressBase
        omega
      rw [hf _ (by omega) (by omega)]
      exact hz.2.2.2.1 t ht
    · intro a ha
      have hsep : cursorAddressBase L m N Q + z.regs index < codeAddress L m N Q := by
        unfold codeAddress
        exact Nat.add_lt_add_left hn _
      have hsep' : offsetAddress L m N Q + z.regs index < codeAddress L m N Q := by
        unfold codeAddress cursorAddressBase
        dsimp [T] at hn
        omega
      rw [hf _ (by rcases ha with ha | ha <;> omega)
        (by rcases ha with ha | ha <;> unfold cursorAddressBase at * <;> omega)]
      exact hz.2.2.2.2 a ha
  obtain ⟨y, he, hy, _⟩ := ExecWithin.loop_count P (fun _ hy => hy.1.tileCount)
    hb (by simp [start, index, total]) hi
  have hsum : y.regs total = Nat.count (fun k => key k < T) Q := hy.2.1
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have haddr : Fits w (offsetAddress L m N Q + T) := hl.of_le (by
    unfold offsetAddress countAddress tableAddress inputLimit
    dsimp [T]
    omega)
  let z := (y.set pointer (offsetAddress L m N Q + T)).write
    (offsetAddress L m N Q + T) (Nat.count (fun k => key k < T) Q)
  have hz : ExecWithin w (ram[pointer ← offsets + tileCount; *pointer ← total] :
      Code .standard 96) y z 2 := by
    ram_eval [z, hy.1.offsets, hy.1.tileCount, hsum, haddr, T,
      pointer, offsets, tileCount, total, Fin.mk.injEq]
  have zp : Parameters L m N Q z := hy.1.reframe (by
    intro i hi
    apply hz.regs_eq
    have h : ∀ i ∈ parameterRegisters,
        (ram[pointer ← offsets + tileCount; *pointer ← total] : Code .standard 96).Preserves i := by
      decide +kernel
    exact h i hi)
  have hlast : Nat.count (fun k => key k < T) Q = Q := Nat.count_of_forall hkey
  refine ⟨z, ?_, zp, ?_, ?_, ?_, ?_⟩
  · apply (ExecWithin.seq_assoc.mp (hs.seq (he.seq hz))).mono
    have h0 : start.regs index = 0 := by simp [start, index, total]
    rw [h0, Nat.sub_zero]
    dsimp [T]
    omega
  · intro t ht
    by_cases h : t = T
    · subst t
      exact Function.update_self _ _ _
    · have ht' : t < T := by omega
      change Function.update y.mem (offsetAddress L m N Q + T)
        (Nat.count (fun k => key k < T) Q) (offsetAddress L m N Q + t) = _
      rw [Function.update_of_ne (by omega)]
      exact (hy.2.2.1 t ht').1
  · intro t ht
    change Function.update y.mem (offsetAddress L m N Q + T)
      (Nat.count (fun k => key k < T) Q) (cursorAddressBase L m N Q + t) = _
    rw [Function.update_of_ne (by unfold cursorAddressBase; omega)]
    exact (hy.2.2.1 t ht).2
  · change Function.update y.mem (offsetAddress L m N Q + T)
      (Nat.count (fun k => key k < T) Q) (offsetAddress L m N Q + T) = Q
    rw [Function.update_self, hlast]
  · intro a ha
    change Function.update y.mem (offsetAddress L m N Q + T)
      (Nat.count (fun k => key k < T) Q) a = x.mem a
    rw [Function.update_of_ne (by
      rcases ha with ha | ha
      · omega
      · unfold codeAddress cursorAddressBase at ha
        omega)]
    exact hy.2.2.2.2 a ha

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
