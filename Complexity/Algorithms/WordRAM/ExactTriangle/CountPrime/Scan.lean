/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.ScanCell

/-!
# Complete native selected-coefficient scan

The invariant counts exactly the original row-major prefix and preserves all memory. The
numeric accumulator bound is derived by summing the nonnegative coefficient bound, rather
than assuming that the final answer fits. This is an internal composition contract; the
counter derives its residue and product readback from its actual preceding executions.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

private theorem scan_sum_le {n t : ℕ} (values : ℕ → ℕ)
    (hv : ∀ i < t, values i ≤ n) : ∑ i ∈ Finset.range t, values i ≤ t * n := by
  calc
    _ ≤ ∑ _i ∈ Finset.range t, n := Finset.sum_le_sum fun i hi => hv i (Finset.mem_range.mp hi)
    _ = t * n := by simp

/-- Execute the complete original-pair scan, including initialization, every coefficient
load/decoding/addition, all loop controls and exit. No memory word is changed. -/
theorem exec_count {w n p k : ℕ} (x : Data 128) (keys values : ℕ → ℕ)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hc : x.regs Reg.cells = n * n) (hpadding : n ≤ 2 ^ k)
    (hkeys : ∀ i < n * n, keys i < p) (hbound : ∀ i < n * n, values i ≤ n)
    (hresidues : ∀ i < n * n, x.mem (x.regs Reg.residueAB + i) = keys i)
    (hproduct : ∀ i < n * n,
      x.mem (x.regs Reg.matrixR + Nat.Morton.index (i / n) (i % n) * p +
        (if keys i = 0 then 0 else p - keys i)) = encode (values i : ℤ))
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hw : Fits w (x.regs Reg.spread + x.regs Reg.residueAB + x.regs Reg.matrixR +
      4 ^ k * p + 4 ^ k + 2 ^ k + n * n * n + n * n + p + 16)) :
    ∃ y, ExecWithin w count x y (22 * (n * n) + 4) ∧ y.mem = x.mem ∧
      y.regs Reg.result = ∑ i ∈ Finset.range (n * n), values i ∧
      ∀ j, ¬ScanLocal j → y.regs j = x.regs j := by
  let I (y : Data 128) : Prop :=
    (∀ j, ¬ScanLocal j → y.regs j = x.regs j) ∧ y.mem = x.mem ∧
    y.regs Reg.index ≤ n * n ∧
    y.regs Reg.result = ∑ i ∈ Finset.range (y.regs Reg.index), values i
  have body (y : Data 128) (hy : I y) (hcond : (Cond.lt Reg.index Reg.cells).Holds y) :
      ∃ z, ExecWithin w countStep y z 20 ∧ I z ∧
        n * n - z.regs Reg.index < n * n - y.regs Reg.index := by
    obtain ⟨regs, memory, index, result⟩ := hy
    have keep (j : Fin 128) (hj : ¬ScanLocal j) := regs j hj
    have hlt : y.regs Reg.index < n * n := by
      simpa only [Cond.holds_lt, keep Reg.cells (by decide), hc] using hcond
    obtain ⟨z, he, zm, zi, zr, keepz⟩ := exec_countStep y
      ((keep _ (by decide)).trans hn) ((keep _ (by decide)).trans hp) rfl hlt hpadding
      (by rw [memory, keep Reg.residueAB (by decide)]; exact hresidues _ hlt)
      (hkeys _ hlt)
      (by rw [memory, keep Reg.matrixR (by decide)]; exact hproduct _ hlt)
      (hbound _ hlt) result
      (scan_sum_le values (fun i hi => hbound i (hi.trans hlt)))
      ((keep _ (by decide)).trans h0) ((keep _ (by decide)).trans h1)
      ((keep _ (by decide)).trans h2)
      (by rw [memory, keep Reg.spread (by decide)]; exact htable)
      (by simpa only [keep Reg.spread (by decide), keep Reg.residueAB (by decide),
        keep Reg.matrixR (by decide)] using hw)
    refine ⟨z, he, ⟨fun j hj => (keepz j hj).trans (regs j hj), zm.trans memory,
      by omega, ?_⟩, by omega⟩
    rw [zi, Finset.sum_range_succ, zr]
  let start := (x.set Reg.result 0).set Reg.index 0
  have init : ExecWithin (B := .standard) w
      (ram[ Reg.result ← #0; Reg.index ← #0 ]) x start 2 := by
    ram_eval [start, fits_zero w]
  have startI : I start := by
    refine ⟨?_, rfl, by change 0 ≤ n * n; omega, ?_⟩
    · intro j hj
      have hi : j ≠ Reg.index := by intro h; subst j; exact hj (by decide)
      have hr : j ≠ Reg.result := by intro h; subst j; exact hj (by decide)
      simp only [start, Data.set, Function.update_of_ne hi, Function.update_of_ne hr]
    · change 0 = ∑ i ∈ Finset.range 0, values i
      simp
  obtain ⟨y, run, hy, stopped⟩ := ExecWithin.loop_invariant I
    (fun y => n * n - y.regs Reg.index) body startI
  obtain ⟨regs, memory, index, result⟩ := hy
  have ended : y.regs Reg.index = n * n := by
    simp only [Cond.holds_lt, regs Reg.cells (by decide), hc] at stopped
    omega
  have full : ExecWithin w count x y (22 * (n * n) + 4) := by
    obtain ⟨i, hi, he⟩ := init
    obtain ⟨j, hj, hf⟩ := run
    cases he with
    | seq ha hb =>
      exact ⟨_, by change j ≤ (n * n - 0) * (20 + 2) + 2 at hj; omega,
        .seq ha (.seq hb hf)⟩
  exact ⟨y, full, memory, by simpa only [ended] using result, regs⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
