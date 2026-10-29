/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram

/-!
# Concrete disjoint memory regions and derived native fits

## Main results

* `BandPreparation.workspace_le_snapshot`: protected data are above the complete encoder.
* `BandPreparation.memory_fits`: the actual allocation end fits the explicit input budget.
* `BandPreparation.tables_fit`, `BandPreparation.split_fits`, `BandPreparation.encoder_fits`:
  component inequalities derived from the same budget, without an intermediate-state oracle.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The native input prefix is disjoint from its protected copy. -/
theorem input_le_snapshot (L m N : ℕ) : inputEnd m N ≤ snapshotBase L m N := by
  unfold snapshotBase
  exact (Nat.le_add_right (inputEnd m N) (Encoding.scratchBase L)).trans
    (Nat.le_add_right _ (10 ^ L))

/-- The encoder's complete low workspace is below the protected original input. -/
theorem workspace_le_snapshot (L m N : ℕ) :
    Encoding.scratchBase L + 10 ^ L ≤ snapshotBase L m N := by
  unfold snapshotBase
  omega

/-- The protected original-input copy ends exactly at the inverse table. -/
theorem snapshot_end (L m N : ℕ) :
    snapshotBase L m N + inputEnd m N = inverseBase L m N := rfl

/-- The inverse table ends exactly at the selected-mask table. -/
theorem inverse_end (L m N : ℕ) : inverseBase L m N + 2 ^ L = tableBase L m N := rfl

/-- The selected-mask table ends exactly at the shared output catalogue. -/
theorem table_end (L m N : ℕ) : tableBase L m N + 2 ^ L = catalogueBase L m N := rfl

/-- The catalogue base is below the complete allocation end, including an empty catalogue. -/
theorem catalogue_le_memoryEnd (L m N : ℕ) : catalogueBase L m N ≤ memoryEnd L m N :=
  Nat.le_add_right _ _

/-- Each table block precedes the complete allocation end. -/
theorem table_le_memoryEnd (L m N : ℕ) : tableBase L m N ≤ memoryEnd L m N :=
  (Nat.le_add_right _ _ : tableBase L m N ≤ tableBase L m N + 2 ^ L).trans
    (catalogue_le_memoryEnd L m N)

/-- The protected prefix ends below every table/output allocation. -/
theorem inverse_le_memoryEnd (L m N : ℕ) : inverseBase L m N ≤ memoryEnd L m N :=
  (Nat.le_add_right _ _ : inverseBase L m N ≤ inverseBase L m N + 2 ^ L).trans
    (table_le_memoryEnd L m N)

/-- The snapshot base is within the complete allocation. -/
theorem snapshot_le_memoryEnd (L m N : ℕ) : snapshotBase L m N ≤ memoryEnd L m N :=
  (Nat.le_add_right _ _ : snapshotBase L m N ≤ snapshotBase L m N + inputEnd m N).trans
    (inverse_le_memoryEnd L m N)

/-- Every original input address also fits the complete allocation. -/
theorem input_le_memoryEnd (L m N : ℕ) : inputEnd m N ≤ memoryEnd L m N :=
  (input_le_snapshot L m N).trans (snapshot_le_memoryEnd L m N)

/-- The constant margin in the original budget covers all fixed program constants. -/
theorem small_fits {w L m N v : ℕ} (hfit : Fits w (wordBudget L m N)) (hv : v ≤ 256) :
    Fits w v :=
  hfit.of_le (hv.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

/-- The entire real allocation, including both catalogue halves, fits the original numerical
word-budget inequality. The sizes of unreachable padded row-major products are irrelevant. -/
theorem memory_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N)) :
    Fits w (memoryEnd L m N) := by
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  apply hfit.of_le
  unfold memoryEnd catalogueBase tableBase inverseBase snapshotBase inputEnd
    Encoding.scratchBase Encoding.outputBase wordBudget
  nlinarith only [h7, Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- Both table-store addresses and all population/count arithmetic fit before table execution. -/
theorem tables_fit {w L m N : ℕ} (hfit : Fits w (wordBudget L m N)) :
    Fits w (inverseBase L m N + tableBase L m N + 2 ^ L + L + 4) := by
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  apply hfit.of_le
  unfold tableBase inverseBase snapshotBase inputEnd Encoding.scratchBase Encoding.outputBase
    wordBudget
  nlinarith only [h7, Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- Every original band index admits the already proved native digit-loop fits. -/
theorem split_fits {w L m N a : ℕ} (hfit : Fits w (wordBudget L m N)) (ha : a < 7 ^ L) :
    Fits w (a + L + 16 * 10 ^ L + 16) := by
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  apply hfit.of_le
  unfold wordBudget
  nlinarith only [ha, h7, Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- The unchanged native encoder's arithmetic/address premise follows from this client's
explicit original-parameter bound. Its signed magnitude premise remains separate. -/
theorem encoder_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N)) :
    Fits w (Encoding.addressBound L) := by
  apply hfit.of_le
  unfold Encoding.addressBound wordBudget
  have hpos : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  nlinarith only [hpos, Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (2 * numBands L m N * 10 ^ L)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
