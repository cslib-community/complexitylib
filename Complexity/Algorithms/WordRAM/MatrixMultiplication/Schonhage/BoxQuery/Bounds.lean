/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.InputLayout
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.State
import Mathlib.Data.Nat.Log

/-!
# Original-input admission for complete sparse box queries

The ordinary headers and two signed arrays determine all address and magnitude
envelopes. Shared table preparation and query traversal remain separate charged terms.
The native fixed program never reads the physical width or an admission certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The complete allocation contains the computed shared geometry/table and native stack. -/
@[expose] def memoryEnd (L m t : ℕ) : ℕ := stackBase L m t + 5 * stackCapacity L

/-- Original headers derive the reusable query's scalar/address budget. -/
theorem query_address_le (L m t : ℕ) (hm : m ≤ L) :
    queryAddressBound L t 5 (5 + 10 ^ L) (directoryBase L) (valueBase L m t)
      (boxes L m t).card ≤ originalAddressBound L m t := by
  have hB := Nat.count_le (BoxTable.Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [BoxTable.count_eligible_eq_card_boxes] at hB
  have hS := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  unfold queryAddressBound originalAddressBound valueBase recordBase directoryBase
  omega

/-- All native stack addresses fit the original scalar envelope, without clearing that space. -/
theorem memoryEnd_le (L m t : ℕ) (hm : m ≤ L) : memoryEnd L m t ≤ originalAddressBound L m t := by
  have hB := Nat.count_le (BoxTable.Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [BoxTable.count_eligible_eq_card_boxes] at hB
  have hS := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  unfold memoryEnd stackBase valueBase recordBase directoryBase stackCapacity originalAddressBound
  omega

/-- Positive physical admission determined by original header and signed-array bounds. -/
@[expose] def admissionWidth (L m t A B : ℕ) : ℕ :=
  Nat.clog 2 (magnitudeBound L A B + originalAddressBound L m t + 1) + 3

theorem admissionWidth_pos (L m t A B : ℕ) : 0 < admissionWidth L m t A B := by
  unfold admissionWidth
  omega

/-- Every sufficiently wide physical machine admits all original signed and scalar bounds. -/
theorem admission_bounds {W L m t A B : ℕ} (hW : admissionWidth L m t A B ≤ W) :
    0 < W - 2 ∧ Fits W (originalAddressBound L m t) ∧
      GenericRAM.Signed.Fits (W - 2) (magnitudeBound L A B : ℕ) := by
  have hlog := Nat.le_pow_clog (by decide : 1 < (2 : ℕ))
    (magnitudeBound L A B + originalAddressBound L m t + 1)
  have hs : Nat.clog 2 (magnitudeBound L A B + originalAddressBound L m t + 1) ≤ (W - 2) - 1 := by
    unfold admissionWidth at hW
    omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hs
  have hmag : magnitudeBound L A B < 2 ^ ((W - 2) - 1) := by omega
  have hw : 0 < W - 2 := by unfold admissionWidth at hW; omega
  refine ⟨hw, ?_, hw, ?_, ?_⟩
  · change originalAddressBound L m t < 2 ^ W
    have hp' := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega :
      Nat.clog 2 (magnitudeBound L A B + originalAddressBound L m t + 1) ≤ W)
    omega
  · have hn : 0 ≤ (magnitudeBound L A B : ℤ) := Int.natCast_nonneg _
    have hp0 : 0 ≤ (2 : ℤ) ^ ((W - 2) - 1) := by positivity
    omega
  · exact_mod_cast hmag

/-- A fixed original-input word/support envelope, independent of larger physical widths. -/
@[expose] def wordBound (L m t A B : ℕ) : ℕ :=
  16 * (magnitudeBound L A B + originalAddressBound L m t + 1)

/-- Minimum-width data are strictly below the same original polynomial envelope. -/
theorem pow_admissionWidth_lt_wordBound (L m t A B : ℕ) :
    2 ^ admissionWidth L m t A B < wordBound L m t A B := by
  let N := magnitudeBound L A B + originalAddressBound L m t + 1
  have hN : 1 < N := by dsimp only [N]; unfold originalAddressBound; omega
  have hl : 0 < Nat.clog 2 N := Nat.clog_pos (by decide) hN
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hN
  have he : Nat.clog 2 N = (Nat.clog 2 N).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hl).symm
  change 2 ^ (Nat.clog 2 N + 3) < 16 * N
  rw [he, show (Nat.clog 2 N).pred + 1 + 3 = (Nat.clog 2 N).pred + 4 by omega,
    pow_add]
  norm_num only [pow_succ, pow_zero, Nat.reduceMul] at *
  omega

/-- The complete fixed program, including its final halt, has a uniform constant code size. -/
theorem program_size_le : program.size + 1 ≤ 4096 := by decide

/-- All composed code is independent of physical width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
