/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandAll
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandTables
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCost

/-!
# Complete native shared-band execution

## Main results

* `BandPreparation.exec`: compute both tables and every shared encoding, from real scalar
  headers and matrix words, restoring the full original input prefix and every outside cell.
  All setup, copies, loops and encoder calls contribute to the instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

-- Static frame checks reduce the fixed parameter bank and finite native table code.
set_option maxRecDepth 4096

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The two tables and the protected input all precede the output catalogue. -/
theorem snapshot_le_catalogue (L m N : ℕ) : snapshotBase L m N ≤ catalogueBase L m N := by
  unfold catalogueBase tableBase inverseBase
  have := Nat.zero_le (2 ^ L)
  omega

/-- The one-side catalogue end is within the complete allocation. -/
theorem catalogue_side_end_le (L m N : ℕ) (side : Bool) :
    catalogueAddress L m N side (numBands L m N) 0 ≤ memoryEnd L m N := by
  unfold catalogueAddress memoryEnd
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
  all_goals nlinarith only [Nat.zero_le (numBands L m N * 10 ^ L)]

private theorem band_frame_protected {L m N : ℕ} {side : Bool} {μ ν : ℕ → ℕ}
    (h : ∀ b, ¬(1 ≤ b ∧ b < Encoding.scratchBase L + 10 ^ L) →
      ¬(catalogueAddress L m N side 0 0 ≤ b ∧
        b < catalogueAddress L m N side (numBands L m N) 0) → ν b = μ b)
    (a : ℕ) (ha : snapshotBase L m N ≤ a ∧ a < catalogueBase L m N) : ν a = μ a := by
  apply h
  · have := workspace_le_snapshot L m N
    omega
  · have := catalogue_le_address L m N 0 side
    omega

private theorem band_frame_above {L m N : ℕ} {side : Bool} {μ ν : ℕ → ℕ}
    (h : ∀ b, ¬(1 ≤ b ∧ b < Encoding.scratchBase L + 10 ^ L) →
      ¬(catalogueAddress L m N side 0 0 ≤ b ∧
        b < catalogueAddress L m N side (numBands L m N) 0) → ν b = μ b)
    (a : ℕ) (ha : memoryEnd L m N ≤ a) : ν a = μ a := by
  apply h
  · have := workspace_le_snapshot L m N
    have := (snapshot_le_catalogue L m N).trans (catalogue_le_memoryEnd L m N)
    omega
  · have := catalogue_side_end_le L m N side
    omega

/-- A coarse uniform bound for one actual shared-band call and its outer loop control. -/
theorem bandTime_le (L : ℕ) : bandTime L + 3 ≤ 512 * (L + 1) * 10 ^ L := by
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have ht : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  have hs := Nat.mul_le_mul_left (13 * L + 39) h7
  unfold bandTime Encoding.timeBound
  nlinarith only [hs, ht, Nat.zero_le L, Nat.zero_le (L * 10 ^ L)]

/-- The sum of the previously proved native component charges fits the generic bound. -/
theorem execution_time_le (L m N : ℕ) :
    (16 * L + 49) + ((7 * inputEnd m N + 7) +
      (((6 * L + 16) * 2 ^ L + 14) + (((6 * L + 17) * 2 ^ L + 4) +
        ((numBands L m N * (bandTime L + 3) + 3) +
          ((numBands L m N * (bandTime L + 3) + 3) + (7 * inputEnd m N + 7)))))) ≤
      timeBound L m N := by
  have hb := Nat.mul_le_mul_left (numBands L m N) (bandTime_le L)
  have h2 : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by decide)
  unfold timeBound inputEnd
  nlinarith only [hb, h2, Nat.zero_le L, Nat.zero_le (N * D m),
    Nat.zero_le (L * (N * D m)), Nat.zero_le (L * 2 ^ L),
    Nat.zero_le (numBands L m N * 10 ^ L),
    Nat.zero_le (L * (numBands L m N * 10 ^ L))]

/-- The full fixed native program. The caller supplies only ordinary `L,m,N` headers and
signed matrix words; both tables and every padded/encoded band are computed. Header zero
and arbitrary outside memory need not be zero or describe a standalone input list. -/
theorem exec {w L m N : ℕ} (hw : 0 < w) (hm : m ≤ L) (x : Data 96)
    (hL : x.mem 1 = L) (hm' : x.mem 2 = m) (hN : x.mem 3 = N)
    (matrix : Bool → ℕ → ℕ → ℤ)
    (hmat : ∀ side r, r < N → ∀ k, k < D m →
      x.mem (matrixOffset m N side r k + 4) = encode (matrix side r k))
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ side r, r < N → ∀ k, k < D m → |matrix side r k| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) :
    ∃ y, ExecWithin (w + 2) program x y (timeBound L m N) ∧
      BandParameters L m N y ∧
      (∀ side β, β < numBands L m N → ∀ p, p < 10 ^ L →
        y.mem (catalogueAddress L m N side β p) =
          encode (catalogueValue L m N side (matrix side) β p)) ∧
      (∀ a < 2 ^ L, y.mem (inverseBase L m N + a) = MaskTable.lookup L m a) ∧
      (∀ gh : Fin (K0 L m) × Fin (K0 L m),
        y.mem (tableBase L m N + (MaskTable.pairRank gh).val) =
          (MaskTable.selectedMask gh).val) ∧
      (∀ b, ¬(inputEnd m N ≤ b ∧ b < memoryEnd L m N) → y.mem b = x.mem b) := by
  obtain ⟨h, heh, hhp, hhmem⟩ := exec_header hm x hL hm' hN hfit
  obtain ⟨s, hes, hsmem, hsr⟩ := exec_saveInput h hhp hfit
  have hsp : HeaderPost L m N s := headerPost_reframe hhp (by
    intro i hi
    have hp : ∀ i ∈ headerRegisters, 7 ≤ i.val := by decide
    exact hsr i (hp i hi))
  obtain ⟨c, hec, hcp, hcmem⟩ := exec_countCode s hsp hfit
  have htableParams : TableParameters L m (inverseBase L m N) (tableBase L m N) c :=
    ⟨hcp.fixed.levels, hcp.fixed.inner, hcp.masks, hcp.inverse, hcp.table, hcp.square,
      hcp.fixed.zero, hcp.fixed.one, hcp.fixed.two⟩
  obtain ⟨t, het, _, hlookup, hforward, htframe⟩ := exec_tables L m
    (inverseBase L m N) (tableBase L m N) c htableParams (Nat.le_refl _)
      (tables_fit hfit)
  have htp : BandParameters L m N t := parameters_reframe hcp (by
    intro i hi
    apply het.regs_eq
    have hp : ∀ i ∈ parameterRegisters, tablesCode.Preserves i := by
      simp +decide only []
    exact hp i hi)
  have hinv : inverseBase L m N ≤ catalogueBase L m N := by
    unfold catalogueBase tableBase
    have := Nat.zero_le (2 ^ L)
    omega
  have hsnapshot (a : ℕ) (ha : a < inputEnd m N) :
      t.mem (snapshotBase L m N + a) = x.mem a := by
    rw [htframe _ (by unfold inverseBase; omega) (by unfold tableBase inverseBase; omega),
      hcmem, hsmem, ArrayCopy.copyPrefix_read ha, hhmem, Nat.zero_add]
  have hmatrix (side : Bool) (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
      t.mem (matrixAddress L m N side r k) = encode (matrix side r k) := by
    have hb := matrixAddress_lt_inverse (L := L) side hr hk
    unfold matrixAddress inverseBase at hb
    have ho : matrixOffset m N side r k + 4 < inputEnd m N := by omega
    rw [matrixAddress, hsnapshot _ ho]
    exact hmat side r hr k hk
  obtain ⟨l, hel, hlp, hlvalues, hlframe⟩ := exec_encodeBands hw false t htp
    hlookup (matrix false) (hmatrix false) A hA (ha false) hmag hfit
  have hlprotected := band_frame_protected hlframe
  have hinverse (a : ℕ) (ha : a < 2 ^ L) :
      snapshotBase L m N ≤ inverseBase L m N + a ∧
        inverseBase L m N + a < catalogueBase L m N := by
    have hs : snapshotBase L m N ≤ inverseBase L m N := Nat.le_add_right _ _
    have ht : inverseBase L m N + a < tableBase L m N := by
      change inverseBase L m N + a < inverseBase L m N + 2 ^ L
      omega
    exact ⟨hs.trans (Nat.le_add_right _ _), ht.trans_le (Nat.le_add_right _ _)⟩
  have hlookup' (a : ℕ) (ha : a < 2 ^ L) :
      l.mem (inverseBase L m N + a) = MaskTable.lookup L m a := by
    rw [hlprotected _ (hinverse a ha)]
    exact hlookup a ha
  have hmatrix' (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
      l.mem (matrixAddress L m N true r k) = encode (matrix true r k) := by
    have hb := matrixAddress_lt_inverse (L := L) true hr hk
    rw [hlprotected (matrixAddress L m N true r k) ⟨Nat.le_add_right _ _, hb.trans_le hinv⟩]
    exact hmatrix true r hr k hk
  obtain ⟨r, her, hrp, hrvalues, hrframe⟩ := exec_encodeBands hw true l hlp
    hlookup' (matrix true) hmatrix' A hA (ha true) hmag hfit
  have hrprotected := band_frame_protected hrframe
  obtain ⟨y, hey, hymem, hyr⟩ := exec_restoreInput r hrp.toHeaderPost hfit
  have hyp : BandParameters L m N y := parameters_reframe hrp (by
    intro i hi
    have hp : ∀ i ∈ parameterRegisters, 7 ≤ i.val := by decide
    exact hyr i (hp i hi))
  have hrestore (a : ℕ) (ha : inputEnd m N ≤ a) : y.mem a = r.mem a := by
    rw [hymem, ArrayCopy.copyPrefix_outside (by omega)]
  have hprotected (a : ℕ) (ha : snapshotBase L m N ≤ a ∧ a < catalogueBase L m N) :
      r.mem a = t.mem a := (hrprotected a ha).trans (hlprotected a ha)
  have hcatlow : Encoding.scratchBase L + 10 ^ L ≤ catalogueBase L m N :=
    (workspace_le_snapshot L m N).trans (snapshot_le_catalogue L m N)
  have hinputcat : inputEnd m N ≤ catalogueBase L m N :=
    (input_le_snapshot L m N).trans (snapshot_le_catalogue L m N)
  refine ⟨y, ?_, hyp, ?_, ?_, ?_, ?_⟩
  · apply (heh.seq (hes.seq (hec.seq (het.seq (hel.seq (her.seq hey)))))).mono
    exact execution_time_le L m N
  · intro side β hβ p hp
    have hlow : inputEnd m N ≤ catalogueAddress L m N side β p := by
      have := catalogue_le_address L m N β side
      unfold catalogueAddress at *
      omega
    rw [hrestore _ hlow]
    cases side
    · rw [hrframe _ ?_ ?_]
      · exact hlvalues β hβ p hp
      · unfold catalogueAddress
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · have hlt : catalogueAddress L m N false β p <
            catalogueAddress L m N true 0 0 := by
          unfold catalogueAddress
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
          have ht : 0 < 10 ^ L := Nat.pow_pos (by decide)
          nlinarith only [hβ, hp, ht]
        omega
    · exact hrvalues β hβ p hp
  · intro a ha
    have hb := hinverse a ha
    rw [hrestore _ ((input_le_snapshot L m N).trans hb.1), hprotected _ hb]
    exact hlookup a ha
  · intro gh
    have hK : K L m ≤ 2 ^ L := Nat.choose_le_two_pow _ _
    have hi := (MaskTable.pairRank gh).isLt
    have hb : snapshotBase L m N ≤ tableBase L m N + (MaskTable.pairRank gh).val ∧
        tableBase L m N + (MaskTable.pairRank gh).val < catalogueBase L m N := by
      unfold catalogueBase tableBase inverseBase
      omega
    rw [hrestore _ ((input_le_snapshot L m N).trans hb.1), hprotected _ hb]
    exact hforward gh
  · intro b hb
    by_cases hbin : b < inputEnd m N
    · have hread : y.mem b = r.mem (snapshotBase L m N + b) := by
        rw [hymem]
        simpa only [Nat.zero_add] using (ArrayCopy.copyPrefix_read
          (mem := r.mem) (src := snapshotBase L m N) (dst := 0) hbin)
      rw [hread, hprotected _ (by
        unfold catalogueBase tableBase inverseBase
        have := Nat.zero_le (2 ^ L)
        omega)]
      exact hsnapshot b hbin
    · have hbig : memoryEnd L m N ≤ b := by omega
      rw [hrestore b (by omega), band_frame_above hrframe b hbig,
        band_frame_above hlframe b hbig, htframe b ?_ ?_, hcmem, hsmem,
        ArrayCopy.copyPrefix_outside ?_, hhmem]
      · have hend := inverse_le_memoryEnd L m N
        change snapshotBase L m N + inputEnd m N ≤ memoryEnd L m N at hend
        omega
      · have hend := table_le_memoryEnd L m N
        change inverseBase L m N + 2 ^ L ≤ memoryEnd L m N at hend
        omega
      · have hend := catalogue_le_memoryEnd L m N
        change tableBase L m N + 2 ^ L ≤ memoryEnd L m N at hend
        omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
