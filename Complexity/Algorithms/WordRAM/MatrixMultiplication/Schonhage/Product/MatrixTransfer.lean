/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

/-!
# Actual matrix-word adaptation between producer inputs

## Main results

* `QueriedProduct.exec_prepareBits`: copy each original raw unsigned entry while actually
  doubling it for the canonical signed producer convention.

The conversion uses a native load/multiply/store loop. Its original-entry bound derives
every arithmetic fit; its invariant protects unread source words and all caller scalars.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Source and destination blocks in the actual matrix adaptation are disjoint and fit. -/
public theorem matrix_transfer_bounds (L m N Q : ℕ) :
    4 + 2 * (N * D m) ≤ snapshotBase L m N Q + 5 ∧
      snapshotBase L m N Q + 5 + 2 * (N * D m) ≤ memoryEnd L m N Q := by
  have h := transfer_bounds L m N Q
  unfold inputEnd at h
  omega

/-- Every raw entry is converted by an actual charged multiplication, with the complete
outside frame. The numerical bound concerns original source words, not intermediate states. -/
public theorem exec_prepareBits {w L m N Q A : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q))
    (hA : Fits w (2 * A))
    (hentries : ∀ i < 2 * (N * D m), x.mem (snapshotBase L m N Q + 5 + i) ≤ A) :
    ∃ y, ExecWithin w (prepareMatrices true) x y (8 * (2 * (N * D m)) + 4) ∧
      Parameters L m N Q y ∧
      (∀ i < 2 * (N * D m),
        y.mem (4 + i) = 2 * x.mem (snapshotBase L m N Q + 5 + i)) ∧
      (∀ a, a < 4 ∨ 4 + 2 * (N * D m) ≤ a → y.mem a = x.mem a) := by
  let M := 2 * (N * D m)
  let S := snapshotBase L m N Q + 5
  have hb := matrix_transfer_bounds L m N Q
  have hsource : Fits w S := allocated_fits hfit (by dsimp [S]; omega)
  let start := (x.set Reg.source S).set Reg.index 0
  have hs : ExecWithin (B := .standard) w
      (ram[ Reg.source ← Reg.snapshot + Reg.five; Reg.index ← #0 ])
      x start 2 := by
    ram_eval [start, hp.snapshot, hp.five, hsource, S, Reg.source, Reg.snapshot, Reg.five,
      Reg.index]
  have sp : Parameters L m N Q start :=
    (hp.set_work Reg.source (by decide) _).set_work Reg.index (by decide) _
  let I (z : Data 160) : Prop := Parameters L m N Q z ∧ z.regs Reg.source = S ∧
    z.regs Reg.index ≤ M ∧
    (∀ j < z.regs Reg.index, z.mem (4 + j) = 2 * x.mem (S + j)) ∧
    (∀ a, a < 4 ∨ 4 + z.regs Reg.index ≤ a → z.mem a = x.mem a)
  have hstart : I start := ⟨sp, by simp [start, Reg.source, Reg.index], by simp [start],
    by simp [start], by simp [start]⟩
  have hbody (z : Data 160) (hz : I z) (hc : (Cond.lt Reg.index Reg.matrixWords).Holds z) :
      ∃ u, ExecWithin w bitCopyStep z u 6 ∧ I u ∧ M - u.regs Reg.index < M - z.regs Reg.index := by
    have hi : z.regs Reg.index < M := by
      simpa only [Cond.holds_lt, hz.1.matrixWords, M] using hc
    have hload : z.mem (S + z.regs Reg.index) = x.mem (S + z.regs Reg.index) :=
      hz.2.2.2.2 _ (Or.inr (by dsimp [S, M] at *; omega))
    have hsrc : Fits w (S + z.regs Reg.index) := allocated_fits hfit (by
      dsimp [S, M] at *
      omega)
    have hdst : Fits w (4 + z.regs Reg.index) := allocated_fits hfit (by
      dsimp [S, M] at *
      omega)
    have hnext : Fits w (z.regs Reg.index + 1) := allocated_fits hfit (by
      dsimp [S, M] at *
      omega)
    have hvalue : Fits w (x.mem (S + z.regs Reg.index) * 2) := hA.of_le (by
      have hv := hentries (z.regs Reg.index) hi
      dsimp only [S]
      omega)
    let u := (((((z.set Reg.address (S + z.regs Reg.index)).set Reg.value
      (x.mem (S + z.regs Reg.index))).set Reg.value (x.mem (S + z.regs Reg.index) * 2)).set
      Reg.address (4 + z.regs Reg.index)).write (4 + z.regs Reg.index)
      (x.mem (S + z.regs Reg.index) * 2)).set Reg.index (z.regs Reg.index + 1)
    have he : ExecWithin w bitCopyStep z u 6 := by
      ram_eval [bitCopyStep, u, hz.2.1, hz.1.two, hz.1.four, hz.1.one, hload,
        hsrc, hdst, hnext, hvalue, Reg.source, Reg.address, Reg.index, Reg.value, Reg.two,
        Reg.four, Reg.one]
    have up : Parameters L m N Q u :=
      (((((hz.1.set_work Reg.address (by decide) _).set_work Reg.value (by decide) _).set_work
        Reg.value (by decide) _).set_work Reg.address (by decide) _).write _ _).set_work
        Reg.index (by decide) _
    have hn : u.regs Reg.index = z.regs Reg.index + 1 := by simp [u]
    refine ⟨u, he, ⟨up, ?_, by rw [hn]; omega, ?_, ?_⟩, by rw [hn]; omega⟩
    · simpa [u, Reg.source, Reg.address, Reg.index, Reg.value] using hz.2.1
    · intro j hj
      rw [hn] at hj
      change Function.update z.mem (4 + z.regs Reg.index) (x.mem (S + z.regs Reg.index) * 2)
        (4 + j) = 2 * x.mem (S + j)
      by_cases h : j = z.regs Reg.index
      · subst j
        simp only [Function.update_self, Nat.mul_comm]
      · rw [Function.update_of_ne (by omega)]
        exact hz.2.2.2.1 j (by omega)
    · intro a ha
      change Function.update z.mem (4 + z.regs Reg.index) (x.mem (S + z.regs Reg.index) * 2) a = _
      rw [Function.update_of_ne (by rw [hn] at ha; rcases ha with ha | ha <;> omega)]
      apply hz.2.2.2.2 a
      rw [hn] at ha
      rcases ha with ha | ha <;> omega
  obtain ⟨y, he, hy, hc⟩ :=
    ExecWithin.loop_invariant I (fun z => M - z.regs Reg.index) hbody hstart
  have hn : y.regs Reg.index = M := by
    have hu := hy.2.2.1
    simp only [Cond.holds_lt, hy.1.matrixWords] at hc
    dsimp only [M] at hu ⊢
    omega
  refine ⟨y, (hs.seq he).mono ?_, hy.1, ?_, ?_⟩
  · have hzero : start.regs Reg.index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    dsimp [M]
    omega
  · simpa only [hn, M, S] using hy.2.2.2.1
  · simpa only [hn, M] using hy.2.2.2.2

/-- Canonical signed inputs use actual dynamic copying with no conversion arithmetic. -/
public theorem exec_prepareSigned {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w (prepareMatrices false) x y (7 * (2 * (N * D m)) + 10) ∧
      Parameters L m N Q y ∧
      (∀ i < 2 * (N * D m),
        y.mem (4 + i) = x.mem (snapshotBase L m N Q + 5 + i)) ∧
      (∀ a, a < 4 ∨ 4 + 2 * (N * D m) ≤ a → y.mem a = x.mem a) := by
  have hb := matrix_transfer_bounds L m N Q
  have hs : Fits w (snapshotBase L m N Q + 5) := allocated_fits hfit (by omega)
  let z := ((x.set Reg.source (snapshotBase L m N Q + 5)).set Reg.destination 4).set
    Reg.length (2 * (N * D m))
  have hz : ExecWithin (B := .standard) w (ram[
      Reg.source ← Reg.snapshot + Reg.five;
      Reg.destination ← Reg.four;
      Reg.length ← Reg.matrixWords ]) x z 3 := by
    ram_eval [z, hp.snapshot, hp.five, hp.four, hp.matrixWords, hs,
      Reg.source, Reg.snapshot, Reg.five, Reg.destination, Reg.four, Reg.length, Reg.matrixWords]
  have zp : Parameters L m N Q z :=
    ((hp.set_work Reg.source (by decide) _).set_work Reg.destination (by decide) _).set_work
      Reg.length (by decide) _
  obtain ⟨y, he, hm, hf⟩ := exec_copyCall z (allocated_fits hfit (by omega))
    (by simpa [z, Reg.source, Reg.destination, Reg.length] using
      allocated_fits hfit (show snapshotBase L m N Q + 5 + 2 * (N * D m) ≤
        memoryEnd L m N Q + 16 by omega))
    (by simpa [z, Reg.source, Reg.destination, Reg.length] using
      allocated_fits hfit (show 4 + 2 * (N * D m) ≤ memoryEnd L m N Q + 16 by omega))
    (Or.inr (Or.inl (by simpa [z, Reg.source, Reg.destination, Reg.length] using hb.1)))
  have hy : y.mem = ArrayCopy.copyPrefix x.mem (snapshotBase L m N Q + 5) 4
      (2 * (N * D m)) := by simpa [z, Reg.source, Reg.destination, Reg.length] using hm
  refine ⟨y, ?_, zp.reframe (fun i hi => hf i (by omega)), ?_, ?_⟩
  · have hlen : z.regs Reg.length = 2 * (N * D m) := by simp [z]
    rw [hlen] at he
    exact (hz.seq he).mono (by omega)
  · intro i hi
    rw [hy]
    exact ArrayCopy.copyPrefix_read hi
  · intro a ha
    rw [hy]
    exact ArrayCopy.copyPrefix_outside (by rcases ha with ha | ha <;> omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
