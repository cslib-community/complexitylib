/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.StackMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Parameters

/-!
# Actual root-task initialization

The reusable query computes its stack base immediately after the retained compact
table, resets its accumulator and constants, and writes all five root fields before
the first native pop. Dirty stack memory and arbitrary old temporaries are supported.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Complete actual query setup with a real initialized root and exact memory frame. -/
theorem exec_setup {w L t Q AA BB D V K : ℕ} (x : Data registers) (η : OutStr L)
    (hL : x.regs BoxTable.Reg.levels = L) (ht : x.regs BoxTable.Reg.threshold = t)
    (hT : x.regs BoxTable.Reg.span = 10 ^ L) (hQ : x.regs Reg.query = Q)
    (hA : x.regs BoxTable.Reg.arrayA = AA) (hB : x.regs BoxTable.Reg.arrayB = BB)
    (hD : x.regs BoxTable.Reg.directory = D) (hV : x.regs BoxTable.Reg.values = V)
    (hK : x.regs BoxTable.Reg.count = K) (hfit : Fits w (V + K + 20)) :
    ∃ y, ExecWithin w setup x y 26 ∧ Parameters L t Q AA BB D V K (V + K) y ∧
      y.regs Reg.top = 1 ∧ y.regs Reg.answer = Signed.encode 0 ∧
      StackMemory η (V + K) [[]] y.mem ∧
      y.mem = writeTask (V + K) 0 0 0 0 0 1 x.mem := by
  obtain ⟨u, hu, u0, u1, u10, u9, _, um, uf⟩ := BoxTable.exec_constants x
    (hfit.of_le ((by decide : 10 ≤ 20).trans (Nat.le_add_left _ _)))
  have uV : u.regs BoxTable.Reg.values = V :=
    (uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hV
  have uK : u.regs BoxTable.Reg.count = K :=
    (uf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hf1 : Fits w 1 := hfit.of_le (by omega)
  have hf5 : Fits w 5 := hfit.of_le (by omega)
  have hfF : Fits w (V + K) := hfit.of_le (by omega)
  let v0 := ((u.set Reg.five 5).set Reg.answer 0).set Reg.stack (V + K)
  let v1 := ((v0.set Reg.top 0).set Reg.depth 0).set Reg.childCode 0
  let v := ((v1.set Reg.childUsed 0).set Reg.childStars 0).set Reg.childPower 1
  have hv : ExecWithin w setupScalars u v 9 := by
    ram_eval [setupScalars, v, v1, v0, uV, uK, hf0, hf1, hf5, hfF,
      Reg.five, Reg.answer, Reg.stack, Reg.top, Reg.depth, Reg.childCode,
      Reg.childUsed, Reg.childStars, Reg.childPower, BoxTable.Reg.values,
      BoxTable.Reg.count, Fin.mk.injEq]
  have vframe (i : Fin registers) (hi : setupScalars.Preserves i) : v.regs i = u.regs i :=
    hv.regs_eq hi
  have vu (i : Fin registers) (hi : setupScalars.Preserves i)
      (h0 : i ≠ BoxTable.Reg.nil) (h1 : i ≠ BoxTable.Reg.one)
      (h10 : i ≠ BoxTable.Reg.ten) (h9 : i ≠ BoxTable.Reg.nine)
      (h3 : i ≠ BoxTable.Reg.three) : v.regs i = x.regs i :=
    (vframe i hi).trans (uf i h0 h1 h10 h9 h3)
  obtain ⟨y, hy, hyt, hym, hyf⟩ :=
    exec_push (F := V + K) (n := 0) (k := 0) (c := 0) (u := 0) (e := 0) (p := 1) v
    (by simp [v, v1, v0, Reg.stack, Reg.top, Reg.depth, Reg.childCode,
      Reg.childUsed, Reg.childStars, Reg.childPower, Reg.five, Reg.answer])
    (by simp [v, v1, Reg.top, Reg.depth, Reg.childCode,
      Reg.childUsed, Reg.childStars, Reg.childPower])
    (by simp [v, v1, Reg.depth, Reg.childCode, Reg.childUsed, Reg.childStars, Reg.childPower])
    (by simp [v, v1, Reg.childCode, Reg.childUsed, Reg.childStars, Reg.childPower])
    (by simp [v, Reg.childUsed, Reg.childStars, Reg.childPower])
    (by simp [v, Reg.childStars, Reg.childPower]) (by simp [v])
    (by simp [v, v1, v0, Reg.five, Reg.answer, Reg.stack, Reg.top, Reg.depth,
      Reg.childCode, Reg.childUsed, Reg.childStars, Reg.childPower])
    ((vframe _ (by decide)).trans u1) (hfit.of_le (by omega))
  have he : ExecWithin w setup x y 26 := hu.seq (hv.seq hy)
  have yp (i : Fin registers) (hi : ¬PushLocal i) (hi' : setupScalars.Preserves i)
      (h0 : i ≠ BoxTable.Reg.nil) (h1 : i ≠ BoxTable.Reg.one)
      (h10 : i ≠ BoxTable.Reg.ten) (h9 : i ≠ BoxTable.Reg.nine)
      (h3 : i ≠ BoxTable.Reg.three) : y.regs i = x.regs i :=
    (hyf i hi).trans (vu i hi' h0 h1 h10 h9 h3)
  refine ⟨y, he, ?_, hyt, ?_, ?_, ?_⟩
  · constructor
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hL
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans ht
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hT
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hQ
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hA
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hB
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hD
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hV
    · exact (yp _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hK
    · rw [hyf _ (by decide)]
      simp [v, v1, v0, Reg.stack, Reg.top, Reg.depth, Reg.childCode,
        Reg.childUsed, Reg.childStars, Reg.childPower, Reg.five, Reg.answer]
    · rw [hyf _ (by decide)]
      simp [v, v1, v0, Reg.five, Reg.answer, Reg.stack, Reg.top, Reg.depth,
        Reg.childCode, Reg.childUsed, Reg.childStars, Reg.childPower]
    · exact (hyf _ (by decide)).trans ((vframe _ (by decide)).trans u1)
    · exact (hyf _ (by decide)).trans ((vframe _ (by decide)).trans u10)
    · exact (hyf _ (by decide)).trans ((vframe _ (by decide)).trans u9)
    · exact (hyf _ (by decide)).trans ((vframe _ (by decide)).trans u0)
  · rw [hyf _ (by decide)]
    simp [v, v1, v0, Reg.answer, Reg.stack, Reg.five, Reg.top, Reg.depth,
      Reg.childCode, Reg.childUsed, Reg.childStars, Reg.childPower, Signed.encode]
  · rw [hym]
    simpa only [List.length_nil, prefixCode_nil, usedFrom, starsFrom, pow_zero] using
      (show StackMemory η (V + K) [] v.mem from trivial).push []
  · simpa only [v, v1, v0, Data.set_mem, um] using hym

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
