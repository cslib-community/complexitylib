/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Program
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Admission

/-!
# Persistent routed box-product geometry

The high scalar protocol contains only original parameters and actual computed addresses.
The geometry predicate records the four readonly families of directory/descriptor words.
It is independent of the changing per-tile values, query stack and temporary results.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual high-register contents retained between all tile calls. -/
structure Parameters (L m t N Q : ℕ) (x : Data 160) : Prop where
  /-- Original threshold. -/
  threshold : x.regs Reg.threshold = t
  /-- Shared directory. -/
  directory : x.regs Reg.directory = directoryBase L m N Q
  /-- Computed compact descriptors. -/
  records : x.regs Reg.records = recordBase L m t N Q
  /-- Reusable compact signed values. -/
  values : x.regs Reg.values = valueBase L m t N Q
  /-- Actual compact count. -/
  count : x.regs Reg.count = (boxes L m t).card
  /-- Reusable actual temporary results. -/
  results : x.regs Reg.results = resultBase L m t N Q

/-- Pure directory/descriptor readback, with no execution, frame or cost certificate. -/
structure Geometry (L m t N Q : ℕ) (μ : ℕ → ℕ) : Prop where
  /-- Actual directory ranks, including invalid zero words. -/
  directory : ∀ s < (m - t + 1) * 10 ^ L,
    μ (directoryBase L m N Q + s) = BoxTable.directoryWord L (m - t) s
  /-- Actual completed leaf codes. -/
  code : ∀ s < (m - t + 1) * 10 ^ L, BoxTable.Eligible L (m - t) s →
    μ (recordBase L m t N Q + 3 * Nat.count (BoxTable.Eligible L (m - t)) s) =
      BoxTable.recordCode L s
  /-- Actual star counts. -/
  stars : ∀ s < (m - t + 1) * 10 ^ L, BoxTable.Eligible L (m - t) s →
    μ (recordBase L m t N Q + 3 * Nat.count (BoxTable.Eligible L (m - t)) s + 1) =
      BoxTable.recordStars L s
  /-- Actual highest-star place values. -/
  stride : ∀ s < (m - t + 1) * 10 ^ L, BoxTable.Eligible L (m - t) s →
    μ (recordBase L m t N Q + 3 * Nat.count (BoxTable.Eligible L (m - t)) s + 2) =
      BoxTable.recordStride L s

/-- The current geometry supplies the constructor's readonly catalogue without tying its
outside frame to a previous tile's values. -/
theorem Geometry.catalogue {L m t N Q : ℕ} {μ : ℕ → ℕ} (h : Geometry L m t N Q μ) :
    BoxTable.CataloguePrefix L (m - t) (directoryBase L m N Q) (recordBase L m t N Q)
      ((m - t + 1) * 10 ^ L) μ μ :=
  ⟨h.directory, h.code, h.stars, h.stride, fun _ _ _ => rfl⟩

/-- Writes outside the directory and compact descriptors preserve the actual shared geometry. -/
theorem Geometry.reframe {L m t N Q : ℕ} {μ ν : ℕ → ℕ} (h : Geometry L m t N Q μ)
    (hf : ∀ p, directoryBase L m N Q ≤ p → p < valueBase L m t N Q → ν p = μ p) :
    Geometry L m t N Q ν := by
  constructor
  · intro s hs
    rw [hf _ (by omega) (by unfold valueBase recordBase; omega)]
    exact h.directory s hs
  · intro s hs hv
    have hk := BoxTable.count_lt_card_boxes hs hv
    rw [hf _ (by unfold recordBase; omega) (by unfold valueBase; omega)]
    exact h.code s hs hv
  · intro s hs hv
    have hk := BoxTable.count_lt_card_boxes hs hv
    rw [hf _ (by unfold recordBase; omega) (by unfold valueBase; omega)]
    exact h.stars s hs hv
  · intro s hs hv
    have hk := BoxTable.count_lt_card_boxes hs hv
    rw [hf _ (by unfold recordBase; omega) (by unfold valueBase; omega)]
    exact h.stride s hs hv

/-- Extending a low-bank execution leaves every higher caller register untouched. -/
theorem boxBank_extend_high (z : Data 64) (x : Data 160) (i : Fin 160) (hi : 64 ≤ i.val) :
    (z.extend boxBank x).regs i = x.regs i := by
  have hnot : ¬∃ j, boxBank j = i := by
    rintro ⟨j, hj⟩
    have hv := congrArg (fun r : Fin 160 => r.val) hj
    change j.val = i.val at hv
    omega
  exact Function.extend_apply' _ _ _ hnot

/-- The scalar protocol survives any low-bank native execution. -/
theorem Parameters.extend {L m t N Q : ℕ} {x : Data 160}
    (h : Parameters L m t N Q x) (z : Data 64) :
    Parameters L m t N Q (z.extend boxBank x) :=
  ⟨(boxBank_extend_high z x _ (by decide)).trans h.threshold,
    (boxBank_extend_high z x _ (by decide)).trans h.directory,
    (boxBank_extend_high z x _ (by decide)).trans h.records,
    (boxBank_extend_high z x _ (by decide)).trans h.values,
    (boxBank_extend_high z x _ (by decide)).trans h.count,
    (boxBank_extend_high z x _ (by decide)).trans h.results⟩

/-- The full allocation and one-past-end cursor values fit the original envelope. -/
theorem allocated_fits {w L m t N Q n : ℕ} (hfit : Fits w (wordBudget L m t N Q))
    (hn : n ≤ memoryEnd L m t N Q) : Fits w n :=
  hfit.of_le (by unfold wordBudget; omega)

/-- Every old producer/group buffer precedes the shared box geometry, followed in order
by compact records, retained values, query stack and temporary answers. -/
theorem allocation_order (L m t N Q : ℕ) :
    BandPreparation.memoryEnd L m N ≤ directoryBase L m N Q ∧
    QueriedProduct.groupedBase L m N Q + Q ≤ directoryBase L m N Q ∧
    QueriedProduct.codeBase L m N Q + Q ≤ directoryBase L m N Q ∧
    directoryBase L m N Q ≤ recordBase L m t N Q ∧
    recordBase L m t N Q ≤ valueBase L m t N Q ∧
    valueBase L m t N Q + (boxes L m t).card ≤ resultBase L m t N Q := by
  have hs := (QueriedProduct.producers_le_snapshot L m N Q).1
  have hT := Nat.zero_le (10 ^ L)
  simp only [directoryBase, recordBase, valueBase, resultBase, stackBase,
    QueriedProduct.memoryEnd, QueriedProduct.stampBase, QueriedProduct.scratchBase,
    QueriedProduct.outputBase, QueriedProduct.groupedBase, QueriedProduct.originalBase,
    QueriedProduct.codeBase, QueriedProduct.offsetBase]
  omega

/-- Original admission covers one retained-value constructor on any actual producer pointers. -/
theorem tile_fits {W L m t N Q AA BB : ℕ} (hfit : Fits W (wordBudget L m t N Q))
    (hA : AA ≤ directoryBase L m N Q) (hB : BB ≤ directoryBase L m N Q) :
    Fits W (directoryBase L m N Q + recordBase L m t N Q + valueBase L m t N Q + AA + BB +
      20 * ((m - t + 1) * 10 ^ L) + 20 * 10 ^ L + 30) := by
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  apply hfit.of_le
  unfold wordBudget
  omega

/-- Original admission covers the sparse batch and every one-past-end cursor. -/
theorem batch_fits {W L m t N Q AA BB C n : ℕ} (hfit : Fits W (wordBudget L m t N Q))
    (hA : AA ≤ directoryBase L m N Q) (hB : BB ≤ directoryBase L m N Q)
    (hC : C ≤ directoryBase L m N Q) (hn : n ≤ Q) :
    Fits W (BoxBatch.addressBound L t AA BB (directoryBase L m N Q)
      (valueBase L m t N Q) (boxes L m t).card C (resultBase L m t N Q) n) := by
  have hK : (boxes L m t).card ≤ valueBase L m t N Q := by unfold valueBase; omega
  have hO : resultBase L m t N Q ≤ memoryEnd L m t N Q := by unfold memoryEnd; omega
  apply hfit.of_le
  unfold wordBudget BoxBatch.addressBound BoxQuery.queryAddressBound
  omega

/-- The shared encodings precede every protected group and answer word. -/
theorem band_before_grouped (L m N Q : ℕ) :
    BandPreparation.memoryEnd L m N ≤ QueriedProduct.groupedBase L m N Q := by
  have h := (QueriedProduct.producers_le_snapshot L m N Q).1
  simp only [QueriedProduct.groupedBase, QueriedProduct.originalBase, QueriedProduct.codeBase,
    QueriedProduct.offsetBase]
  omega

/-- Every increment of the actual bounded tile index fits the original input envelope. -/
theorem index_fits {W L m t N Q j : ℕ} (hfit : Fits W (wordBudget L m t N Q))
    (hj : j < numBands L m N ^ 2) : Fits W (j + 1) := by
  have ho := allocation_order L m t N Q
  have hc : numBands L m N ^ 2 ≤ QueriedProduct.codeBase L m N Q := by
    unfold QueriedProduct.codeBase
    omega
  have hcd : QueriedProduct.codeBase L m N Q ≤ directoryBase L m N Q :=
    (Nat.le_add_right _ Q).trans ho.2.2.1
  have hde : directoryBase L m N Q ≤ memoryEnd L m t N Q := by
    have h := ho.2.2.2
    unfold memoryEnd
    omega
  exact allocated_fits hfit ((Nat.succ_le_of_lt hj).trans (hc.trans (hcd.trans hde)))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
