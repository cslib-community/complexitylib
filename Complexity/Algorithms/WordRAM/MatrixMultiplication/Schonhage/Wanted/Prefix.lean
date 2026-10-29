/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.PrefixStep
public import Complexity.Computability.WordRAM.Sequence

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
  let I (z : Data 96) : Prop := Parameters L m N Q z ∧ z.regs index ≤ T ∧
    z.regs total = Nat.count (fun k => key k < (z.regs index)) Q ∧
    (∀ t < z.regs index,
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
  have hi : I start := by
    refine ⟨hp, by simp [start, index, total], ?_, by simp [start, index, total],
      hcounts, by simp [start]⟩
    simp [start, index, total]
  have hb (z : Data 96) (hz : I z) (hc : (Cond.lt index tileCount).Holds z) :
      ∃ u, ExecWithin w prefixStep z u 8 ∧ I u ∧
        T - u.regs index < T - z.regs index := by
    have hn : z.regs index < T := by
      simpa only [Cond.holds_lt, hz.1.tileCount] using hc
    obtain ⟨u, he, hu, hidx, hsum, hoff, hcur, hf⟩ := exec_prefixStep key hn z hz.1 rfl
      hz.2.2.1 (hz.2.2.2.2.1 _ hn) hfit
    refine ⟨u, he, ⟨hu, by rw [hidx]; omega, ?_, ?_, ?_, ?_⟩, by rw [hidx]; omega⟩
    · simpa only [hidx] using hsum
    · intro t ht
      rw [hidx] at ht
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
        exact hz.2.2.2.1 t hlt
    · intro t ht
      have hcount : countAddress L Q + t < offsetAddress L m N Q := by
        unfold offsetAddress
        exact Nat.add_lt_add_left ht _
      have hcursor : offsetAddress L m N Q ≤ cursorAddressBase L m N Q := by
        unfold cursorAddressBase
        omega
      rw [hf _ (by omega) (by omega)]
      exact hz.2.2.2.2.1 t ht
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
      exact hz.2.2.2.2.2 a ha
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun z => T - z.regs index) hb hi
  have hn : y.regs index = T := by
    have := hy.2.1
    simp only [Cond.holds_lt, hy.1.tileCount] at hc
    dsimp [T] at *
    omega
  have hsum : y.regs total = Nat.count (fun k => key k < T) Q := by
    simpa only [hn] using hy.2.2.1
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
    · have ht' : t < y.regs index := by rw [hn]; omega
      change Function.update y.mem (offsetAddress L m N Q + T)
        (Nat.count (fun k => key k < T) Q) (offsetAddress L m N Q + t) = _
      rw [Function.update_of_ne (by omega)]
      exact (hy.2.2.2.1 t ht').1
  · intro t ht
    change Function.update y.mem (offsetAddress L m N Q + T)
      (Nat.count (fun k => key k < T) Q) (cursorAddressBase L m N Q + t) = _
    rw [Function.update_of_ne (by unfold cursorAddressBase; omega)]
    exact (hy.2.2.2.1 t (by rw [hn]; exact ht)).2
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
    exact hy.2.2.2.2.2 a ha

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
