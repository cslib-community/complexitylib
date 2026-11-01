/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.MatrixCell

/-!
# Complete native padded monomial matrix construction

The actual cell loop visits row-major coordinates, derives each distinct Morton block from
the computed spread table, and writes all p coefficients. The loop invariant protects prior
blocks using injectivity of the existing Morton projections. Original source/table words
are protected below the destination, which may start dirty. Every padding store is charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

private def cellPosition (N j : ℕ) : ℕ := Nat.Morton.index (j / N) (j % N)

private def cellKey (transpose : Bool) (n p N source : ℕ) (m : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j / N < n ∧ j % N < n then m (source +
    if transpose then j % N * n + j / N else j / N * n + j % N) else p

private theorem cellPosition_injective (N : ℕ) : Function.Injective (cellPosition N) := by
  intro i j he
  have hr := congrArg Nat.Morton.row he
  have hc := congrArg Nat.Morton.column he
  simp only [cellPosition, Nat.Morton.row_index] at hr
  simp only [cellPosition, Nat.Morton.column_index] at hc
  calc
    i = N * (i / N) + i % N := (Nat.div_add_mod i N).symm
    _ = N * (j / N) + j % N := by rw [hr, hc]
    _ = j := Nat.div_add_mod j N

private theorem cellPosition_lt {k j : ℕ} (hj : j < 4 ^ k) : cellPosition (2 ^ k) j < 4 ^ k := by
  have hN : 0 < 2 ^ k := by positivity
  have hsq : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; rfl
  exact Nat.Morton.index_lt ((Nat.div_lt_iff_lt_mul hN).mpr (by simpa only [hsq] using hj))
    (Nat.mod_lt _ hN)

/-- Build every padded matrix cell using the actual loop and computed Morton table.
The raw source is read only at admitted original coordinates, with actual BC transposition.
The numerical source/table separation is derived from the counter's real layout in composition. -/
theorem exec_matrix {w n p k source destination table : ℕ} (src dst : Fin 128)
    (transpose : Bool) (x : Data 128) (hdstReg : dst ≠ Reg.residueSource)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hN : x.regs Reg.paddedSide = 2 ^ k) (harea : x.regs Reg.paddedCells = 4 ^ k)
    (hsrc : x.regs src = source) (hdst : x.regs dst = destination) (ht : x.regs Reg.spread = table)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (hsourceBefore : source + n * n ≤ destination) (htableBefore : table + 2 ^ k ≤ destination)
    (htable : ∀ j < 2 ^ k, x.mem (table + j) = Nat.Morton.spread j)
    (hw : Fits w (destination + 4 ^ k * p + table + 4 ^ k + 2 ^ k +
      source + n * n + p + 16)) :
    ∃ y, ExecWithin w (matrix src dst transpose) x y ((7 * p + 24) * 4 ^ k + 5) ∧
      (∀ j < 4 ^ k, ∀ r < p,
        y.mem (destination + Nat.Morton.index (j / 2 ^ k) (j % 2 ^ k) * p + r) =
          if r = (if j / 2 ^ k < n ∧ j % 2 ^ k < n then x.mem (source +
            if transpose then j % 2 ^ k * n + j / 2 ^ k else j / 2 ^ k * n + j % 2 ^ k)
            else p) then 2 else 0) ∧
      (∀ d, d < destination ∨ destination + 4 ^ k * p ≤ d → y.mem d = x.mem d) ∧
      ∀ r, ¬MatrixLocal r → r ≠ Reg.residueSource → r ≠ Reg.destination → y.regs r = x.regs r := by
  let N := 2 ^ k
  let start := ((x.set Reg.residueSource source).set Reg.destination destination).set Reg.index 0
  have startRegs (r : Fin 128) (hr : ¬MatrixLocal r)
      (hs : r ≠ Reg.residueSource) (hd : r ≠ Reg.destination) : start.regs r = x.regs r := by
    simp only [start, Data.set, Function.update_of_ne hs, Function.update_of_ne hd,
      Function.update_of_ne (show r ≠ Reg.index by intro he; subst r; exact hr (by decide))]
  let I (y : Data 128) : Prop :=
    (∀ r, ¬MatrixLocal r → y.regs r = start.regs r) ∧
    y.regs Reg.index ≤ 4 ^ k ∧
    (∀ j < y.regs Reg.index, ∀ r < p,
      y.mem (destination + cellPosition N j * p + r) =
        if r = cellKey transpose n p N source x.mem j then 2 else 0) ∧
    ∀ d, d < destination ∨ destination + 4 ^ k * p ≤ d → y.mem d = x.mem d
  have body (y : Data 128) (hy : I y) (hc : (Cond.lt Reg.index Reg.paddedCells).Holds y) :
      ∃ z, ExecWithin w (matrixStep transpose) y z (7 * p + 22) ∧ I z ∧
        4 ^ k - z.regs Reg.index < 4 ^ k - y.regs Reg.index := by
    obtain ⟨hr, hi, values, memory⟩ := hy
    have keep (r : Fin 128) (hnr : ¬MatrixLocal r)
        (hs : r ≠ Reg.residueSource) (hd : r ≠ Reg.destination) : y.regs r = x.regs r :=
      (hr r hnr).trans (startRegs r hnr hs hd)
    have ysource : y.regs Reg.residueSource = source := by
      simpa +decide [start, Reg.residueSource, Reg.destination, Reg.index] using
        hr Reg.residueSource (by decide)
    have ydestination : y.regs Reg.destination = destination := by
      simpa +decide [start, Reg.destination, Reg.index] using hr Reg.destination (by decide)
    have yarea : y.regs Reg.paddedCells = 4 ^ k :=
      (keep _ (by decide) (by decide) (by decide)).trans harea
    have hlt : y.regs Reg.index < 4 ^ k := by simpa only [Cond.holds_lt, yarea] using hc
    obtain ⟨z, he, zi, newValues, cellFrame, zr⟩ := exec_matrixStep transpose y
      ((keep _ (by decide) (by decide) (by decide)).trans hn)
      ((keep _ (by decide) (by decide) (by decide)).trans hp)
      ((keep _ (by decide) (by decide) (by decide)).trans hN) rfl hlt
      ysource ydestination ((keep _ (by decide) (by decide) (by decide)).trans ht)
      ((keep _ (by decide) (by decide) (by decide)).trans h0)
      ((keep _ (by decide) (by decide) (by decide)).trans h1)
      ((keep _ (by decide) (by decide) (by decide)).trans h2)
      (by
        intro j hj
        rw [memory _ (Or.inl (by omega))]
        exact htable j hj) hw
    have keyFrame : cellKey transpose n p N source y.mem (y.regs Reg.index) =
        cellKey transpose n p N source x.mem (y.regs Reg.index) := by
      unfold cellKey
      split
      · rename_i hguard
        have hm₁ := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hguard.1)
        have hm₂ := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hguard.2)
        rw [Nat.succ_mul] at hm₁ hm₂
        apply memory
        cases transpose <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
      · rfl
    refine ⟨z, he, ⟨?_, by rw [zi]; omega, ?_, ?_⟩, by rw [zi]; omega⟩
    · intro r hnr
      exact (zr r hnr).trans (hr r hnr)
    · intro j hj r hrp
      rw [zi] at hj
      by_cases hjnew : j = y.regs Reg.index
      · subst j
        have hv := newValues r hrp
        change z.mem (destination + cellPosition N (y.regs Reg.index) * p + r) =
          (if r = cellKey transpose n p N source y.mem (y.regs Reg.index) then 2 else 0) at hv
        simpa only [keyFrame] using hv
      · have hprior : j < y.regs Reg.index := by omega
        have hne : cellPosition N j ≠ cellPosition N (y.regs Reg.index) :=
          fun h => hjnew (cellPosition_injective N h)
        have sep : destination + cellPosition N j * p + r <
            destination + cellPosition N (y.regs Reg.index) * p ∨
            destination + cellPosition N (y.regs Reg.index) * p + p ≤
              destination + cellPosition N j * p + r := by
          rcases lt_or_gt_of_ne hne with hlt' | hgt'
          · have hm := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hlt')
            rw [Nat.succ_mul] at hm
            omega
          · have hm := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hgt')
            rw [Nat.succ_mul] at hm
            omega
        rw [cellFrame _ sep]
        exact values j hprior r hrp
    · intro d hd
      have hm := Nat.mul_le_mul_right p (Nat.succ_le_of_lt (cellPosition_lt hlt))
      rw [Nat.succ_mul] at hm
      change cellPosition N (y.regs Reg.index) * p + p ≤ 4 ^ k * p at hm
      rw [cellFrame _ (by change d < destination + cellPosition N (y.regs Reg.index) * p ∨
        destination + cellPosition N (y.regs Reg.index) * p + p ≤ d; omega)]
      exact memory d hd
  have hinit : I start := by
    refine ⟨fun _ _ => rfl, ?_, ?_, fun _ _ => rfl⟩
    · change 0 ≤ 4 ^ k
      omega
    · intro j hj
      change j < 0 at hj
      omega
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => 4 ^ k - y.regs Reg.index) body hinit
  obtain ⟨hr, hi, values, memory⟩ := hIy
  have harea' : y.regs Reg.paddedCells = 4 ^ k :=
    (hr Reg.paddedCells (by decide)).trans
      ((startRegs _ (by decide) (by decide) (by decide)).trans harea)
  have hindex : y.regs Reg.index = 4 ^ k := by
    simp only [Cond.holds_lt, harea'] at hstop
    omega
  have hargs : ExecWithin (B := .standard) w
      (ram[ Reg.residueSource ← src; Reg.destination ← dst; Reg.index ← #0 ]) x start 3 := by
    ram_eval [start, hsrc, hdst, hdstReg, Reg.residueSource, Reg.destination, Reg.index]
  have he : ExecWithin w (matrix src dst transpose) x y ((7 * p + 24) * 4 ^ k + 5) := by
    obtain ⟨m, hm, argsRun⟩ := hargs
    obtain ⟨nSteps, hnSteps, loopRun⟩ := hy
    cases argsRun with
    | seq h₁ rest => cases rest with
      | seq h₂ h₃ =>
        refine ⟨_, ?_, .seq h₁ (.seq h₂ (.seq h₃ loopRun))⟩
        have hstart : start.regs Reg.index = 0 := by simp [start]
        rw [hstart, Nat.sub_zero] at hnSteps
        nlinarith
  refine ⟨y, he, ?_, memory, ?_⟩
  · simpa only [hindex, cellPosition, cellKey, N] using values
  · intro r hnr hs hd
    exact (hr r hnr).trans (startRegs r hnr hs hd)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
