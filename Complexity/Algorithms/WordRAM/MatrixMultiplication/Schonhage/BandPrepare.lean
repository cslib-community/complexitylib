/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandRead

/-!
# Complete native padded-band preparation

## Main results

* `BandPreparation.exec_prepareBand`: initialize and fill every band-array cell by actual
  native digit decoding, inverse-table lookup and guarded signed matrix loads.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

-- The static frame checks reduce finite programs over 96 registers and their parameter sets.
set_option maxRecDepth 4096

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every prepared-band cell is below the protected original input. -/
theorem band_input_le_snapshot (L m N : ℕ) : 2 + 7 ^ L ≤ snapshotBase L m N := by
  have h := workspace_le_snapshot L m N
  unfold Encoding.scratchBase Encoding.outputBase at h
  have := Nat.zero_le (10 ^ L)
  omega

private theorem split_preserves_parameters :
    ∀ i ∈ parameterRegisters, splitCode.Preserves i := by
  simp only [parameterRegisters, headerRegisters, splitCode, splitHead, splitBody,
    Code.Preserves, Op.dest, Op.bin]
  decide

private theorem prepare_preserves_parameters (side : Bool) :
    ∀ i ∈ parameterRegisters, (prepareBody side).Preserves i := by
  cases side <;> simp +decide only []

/-- The entire input band is materialized with charged initialization, digit/index work,
padding and loop control. No cell outside the depth header and the band input is changed. -/
theorem exec_prepareBand {w L m N : ℕ} (side : Bool) (β : ℕ) (x : Data 96)
    (hx : BandParameters L m N x) (hβ : β < numBands L m N) (hb : x.regs band = β)
    (htable : ∀ t < 2 ^ L, x.mem (inverseBase L m N + t) = MaskTable.lookup L m t)
    (matrix : ℕ → ℕ → ℤ)
    (hmat : ∀ r < N, ∀ k < D m,
      x.mem (matrixAddress L m N side r k) = encode (matrix r k))
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w (prepareBand side) x y ((13 * L + 39) * 7 ^ L + 5) ∧
      BandParameters L m N y ∧ y.regs band = β ∧ y.mem 1 = L ∧
      (∀ a < 7 ^ L, y.mem (2 + a) = encode (bandValue L m N β side matrix a)) ∧
      (∀ b, ¬(1 ≤ b ∧ b < 2 + 7 ^ L) → y.mem b = x.mem b) := by
  have hL : Fits w L := (local_fits hfit).of_le (by
    nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
      Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)])
  let start := ((x.set address 1).write 1 L).set index 0
  have hs : ExecWithin w prepareHead x start 3 := by
    ram_eval [prepareHead, start, hx.fixed.levels, hL,
      small_fits hfit (by decide : 1 ≤ 256), address, index, levels, Fin.mk.injEq]
  have hsp : BandParameters L m N start := parameters_reframe hx (by
    intro i hi
    apply hs.regs_eq
    have hp : ∀ i ∈ parameterRegisters, prepareHead.Preserves i := by
      simp only [parameterRegisters, headerRegisters, prepareHead, Code.Preserves, Op.dest]
      decide
    exact hp i hi)
  let I (y : Data 96) : Prop := BandParameters L m N y ∧ y.regs band = β ∧
    y.regs index ≤ 7 ^ L ∧ y.mem 1 = L ∧
    (∀ a < y.regs index, y.mem (2 + a) = encode (bandValue L m N β side matrix a)) ∧
    (∀ b, ¬(1 ≤ b ∧ b < 2 + 7 ^ L) → y.mem b = x.mem b)
  have hstart : I start := by
    refine ⟨hsp, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [start, band, address, index] using hb
    · simp [start]
    · simp [start]
    · simp [start]
    · intro b hbb
      have hne : b ≠ 1 := by
        have := Nat.one_le_pow L 7 (by decide)
        omega
      simp [start, hne]
  have hbody (y : Data 96) (hy : I y) (hc : (Cond.lt index cells).Holds y) :
      ∃ z, ExecWithin w (prepareBody side) y z (13 * L + 37) ∧ I z ∧
        7 ^ L - z.regs index < 7 ^ L - y.regs index := by
    let i := y.regs index
    have hi : i < 7 ^ L := by simpa only [Cond.holds_lt, hy.1.cells] using hc
    have hsplit : SplitParameters L y := ⟨hy.1.fixed.levels, hy.1.fixed.one,
      hy.1.fixed.two, hy.1.fixed.three, hy.1.fixed.four, hy.1.fixed.seven⟩
    obtain ⟨s, hes, _, hmask, houter, hinner, hsmem⟩ :=
      exec_split L i y hsplit rfl (split_fits hfit hi)
    have hsp : BandParameters L m N s := parameters_reframe hy.1
      (fun j hj => hes.regs_eq (split_preserves_parameters j hj))
    have hsband : s.regs band = β := (hes.regs_eq (by
      simp only [splitCode, splitHead, splitBody, Code.Preserves, Op.dest, Op.bin]
      decide)).trans hy.2.1
    have hsindex : s.regs index = i := hes.regs_eq (by
      simp only [splitCode, splitHead, splitBody, Code.Preserves, Op.dest, Op.bin]
      decide)
    have htable' (t : ℕ) (ht : t < 2 ^ L) :
        s.mem (inverseBase L m N + t) = MaskTable.lookup L m t := by
      rw [hsmem, hy.2.2.2.2.2 _ (by
        have hlow := band_input_le_snapshot L m N
        unfold inverseBase
        omega)]
      exact htable t ht
    have hmat' (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
        s.mem (matrixAddress L m N side r k) = encode (matrix r k) := by
      rw [hsmem, hy.2.2.2.2.2 _ (by
        have hlow := band_input_le_snapshot L m N
        unfold matrixAddress
        omega)]
      exact hmat r hr k hk
    obtain ⟨t, het, hv, htmem⟩ := exec_readCell side ⟨i, hi⟩ β s hsp hβ hsband
      hmask houter hinner htable' matrix hmat' hfit
    have htindex : t.regs index = i := (het.regs_eq (by
      cases side <;> simp only [readCell, Code.Preserves, Op.dest, Op.bin] <;> decide)).trans
      hsindex
    have htone : t.regs one = 1 := (het.regs_eq (by
      cases side <;> simp only [readCell, Code.Preserves, Op.dest, Op.bin] <;> decide)).trans
      hsp.fixed.one
    have httwo : t.regs two = 2 := (het.regs_eq (by
      cases side <;> simp only [readCell, Code.Preserves, Op.dest, Op.bin] <;> decide)).trans
      hsp.fixed.two
    have hadd : Fits w (i + 2) :=
      ((memory_fits hfit).of_le (snapshot_le_memoryEnd L m N)).of_le (by
        have hlow := band_input_le_snapshot L m N
        omega)
    have hinc : Fits w (i + 1) := hadd.of_le (by omega)
    let z := ((t.set address (i + 2)).write (i + 2)
      (encode (bandValue L m N β side matrix i))).set index (i + 1)
    have hez : ExecWithin w (ram[
        address ← index + two; *address ← value; index ← index + one ]) t z 3 := by
      ram_eval [z, htindex, htone, httwo, hv, hadd, hinc,
        address, index, two, one, value, Fin.mk.injEq]
    have he : ExecWithin w (prepareBody side) y z (13 * L + 37) := by
      simpa only [prepareBody, Nat.add_assoc] using hes.seq (het.seq hez)
    have hzindex : z.regs index = i + 1 := by simp [z]
    have hzmem : z.mem = Function.update y.mem (i + 2)
        (encode (bandValue L m N β side matrix i)) := by
      simp only [z, Data.set_mem, Data.write_mem, htmem, hsmem]
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨parameters_reframe hy.1 (fun j hj =>
        he.regs_eq (prepare_preserves_parameters side j hj)), ?_, ?_, ?_, ?_, ?_⟩
      · exact (he.regs_eq (by
          cases side <;>
            simp +decide only [])).trans hy.2.1
      · rw [hzindex]; omega
      · rw [hzmem, Function.update_of_ne (by omega : 1 ≠ i + 2)]
        exact hy.2.2.2.1
      · intro a ha
        rw [hzindex] at ha
        rw [hzmem]
        by_cases hai : a = i
        · subst a; rw [Nat.add_comm 2 i, Function.update_self]
        · rw [Function.update_of_ne (by omega : 2 + a ≠ i + 2)]
          exact hy.2.2.2.2.1 a (by omega)
      · intro b hbb
        rw [hzmem, Function.update_of_ne (by omega : b ≠ i + 2)]
        exact hy.2.2.2.2.2 b hbb
    · rw [hzindex]; change 7 ^ L - (i + 1) < 7 ^ L - i; omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => 7 ^ L - y.regs index) hbody hstart
  have hindex : y.regs index = 7 ^ L := by
    simp only [Cond.holds_lt, hy.1.cells] at hc
    have := hy.2.2.1
    omega
  refine ⟨y, ?_, hy.1, hy.2.1, hy.2.2.2.1, ?_, hy.2.2.2.2.2⟩
  · apply (hs.seq he).mono
    have hzero : start.regs index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    nlinarith only [Nat.zero_le (7 ^ L)]
  · simpa only [hindex] using hy.2.2.2.2.1

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
