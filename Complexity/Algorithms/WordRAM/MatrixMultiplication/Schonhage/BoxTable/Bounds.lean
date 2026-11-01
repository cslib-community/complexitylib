/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.InputLayout
import Mathlib.Data.Nat.Log

/-!
# Original-input bounds for native compact box tables

The actual shared geometry and one tile have separate charged terms. A positive
logarithmic width threshold follows from the original depth, scalar headers, and
leaf magnitude envelopes. Neither the program nor its input reads a width certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Shared scalar/directory/descriptor setup; this cost is paid once across tiles. -/
@[expose] def geometryTime (L m t : ℕ) : ℕ :=
  4 * L + 20 + (11 * L + 28) * ((m - t + 1) * 10 ^ L)

/-- One compact value-table construction, with dirty-memory-safe scalar setup. -/
@[expose] def tileTime (L m t : ℕ) : ℕ := 328 * (boxes L m t).card + 8

/-- Original input adaptation, shared setup, one tile, and the final halt are charged. -/
@[expose] def timeBound (L m t : ℕ) : ℕ := 4 * L + 19 + geometryTime L m t + tileTime L m t + 1

/-- The physical width threshold uses only original scalar and magnitude parameters. -/
@[expose] def admissionWidth (L m t A B : ℕ) : ℕ :=
  Nat.clog 2 (magnitudeBound L A B + addressBound L m t + 1) + 3

/-- Width admission remains positive at zero depth and zero operands. -/
theorem admissionWidth_pos (L m t A B : ℕ) : 0 < admissionWidth L m t A B := by
  unfold admissionWidth
  omega

/-- The same original-input threshold derives unsigned addresses and signed operand bounds. -/
theorem admission_bounds {W L m t A B : ℕ} (hW : admissionWidth L m t A B ≤ W) :
    0 < W - 2 ∧ Fits W (addressBound L m t) ∧
      GenericRAM.Signed.Fits (W - 2) (magnitudeBound L A B : ℕ) := by
  have hlog := Nat.le_pow_clog (by decide : 1 < (2 : ℕ))
    (magnitudeBound L A B + addressBound L m t + 1)
  have hs : Nat.clog 2 (magnitudeBound L A B + addressBound L m t + 1) ≤ (W - 2) - 1 := by
    unfold admissionWidth at hW
    omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hs
  have hmag : magnitudeBound L A B < 2 ^ ((W - 2) - 1) := by omega
  have hw : 0 < W - 2 := by unfold admissionWidth at hW; omega
  refine ⟨hw, ?_, hw, ?_, ?_⟩
  · change addressBound L m t < 2 ^ W
    have hp' := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega :
      Nat.clog 2 (magnitudeBound L A B + addressBound L m t + 1) ≤ W)
    omega
  · have hnonneg : 0 ≤ (magnitudeBound L A B : ℤ) := Int.natCast_nonneg _
    have hpow : 0 ≤ (2 : ℤ) ^ ((W - 2) - 1) := by positivity
    omega
  · exact_mod_cast hmag

/-- The existing finite cardinality law controls the per-tile memoization cost. -/
theorem tileTime_le (L m t : ℕ) (hm : m ≤ L) (ht : t ≤ m) :
    tileTime L m t ≤ 328 * (m + 1) * ∑ d ∈ Finset.Icc t m, beta L m d + 8 := by
  have hb := card_boxes_le L m t hm ht
  unfold tileTime
  nlinarith only [hb]

/-- Under the usual depth bound, shared geometry is polynomial-depth times the existing
encoding-array length. This setup is independent of the number of tiles. -/
theorem geometryTime_le (L m t : ℕ) (hm : m ≤ L) :
    geometryTime L m t ≤ 64 * (L + 1) ^ 2 * 10 ^ L := by
  have hp : 1 ≤ 10 ^ L := Nat.one_le_pow L _ (by decide)
  have hh : m - t + 1 ≤ L + 1 := by omega
  have hs := Nat.mul_le_mul_right (10 ^ L) hh
  have hc := Nat.mul_le_mul_left (11 * L + 28) hs
  have hsmall : 4 * L + 20 ≤ (4 * L + 20) * 10 ^ L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * L + 20) hp
  calc
    geometryTime L m t ≤ (4 * L + 20) * 10 ^ L +
        (11 * L + 28) * ((L + 1) * 10 ^ L) := Nat.add_le_add hsmall hc
    _ = (4 * L + 20 + (11 * L + 28) * (L + 1)) * 10 ^ L := by ring
    _ ≤ 64 * (L + 1) ^ 2 * 10 ^ L := Nat.mul_le_mul_right _ (by nlinarith)

/-- The directory and descriptors are shared; a retained tile adds exactly one word per box. -/
theorem allocation_le (L m t : ℕ) :
    memoryEnd L m t - directoryBase L ≤ 5 * ((m - t + 1) * 10 ^ L) := by
  have hk := Nat.count_le (Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [count_eligible_eq_card_boxes] at hk
  unfold memoryEnd valueBase recordBase
  omega

/-- A fixed constructor bank and constant flat code bound, including its final halt. -/
theorem program_size_le : program.size + 1 ≤ 1024 := by decide

/-- Lookup uses the same fixed bank and bounded code, independently of the depth. -/
theorem lookup_size_le : lookup.size + 1 ≤ 256 := by decide

/-- Construction never inspects the physical width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

/-- Lookup never inspects the physical width. -/
theorem lookup_not_readsWidth : ¬lookup.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
