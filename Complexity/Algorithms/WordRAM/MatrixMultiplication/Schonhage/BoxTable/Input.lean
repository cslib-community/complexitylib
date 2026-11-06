/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Initialize
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Tile
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Bounds

/-!
# Complete initialized native box-table constructor

The actual fixed program constructs its shared geometry and one compact signed value
table from ordinary headers and encoded leaf arrays. Computed directory ranks, descriptors,
values, frame and charged time refer to the same final data witness. The geometry charge
remains separate from the linear-in-box-count cost of another tile.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual initialized construction, with all geometry and value work discharged. -/
theorem exec_input {w L m t A B : ℕ} (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (addressBound L m t))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input L m t a b) ∧
    ∃ y, ExecWithin (w + 2) program (State.init (input L m t a b)).data y
        (timeBound L m t - 1) ∧ y.Bounded (w + 2) ∧
      y.regs Reg.levels = L ∧ y.regs Reg.height = m - t ∧
      y.regs Reg.span = 10 ^ L ∧ y.regs Reg.directory = directoryBase L ∧
      y.regs Reg.values = valueBase L m t ∧
      y.regs Reg.count = (boxes L m t).card ∧
      (∀ s < (m - t + 1) * 10 ^ L,
        y.mem (directoryBase L + s) = directoryWord L (m - t) s) ∧
      (∀ s < (m - t + 1) * 10 ^ L, Eligible L (m - t) s →
        y.mem (valueBase L m t + Nat.count (Eligible L (m - t)) s) =
          Signed.encode (slotValue (fun τ => a (Encoding.leafIndex τ))
            (fun τ => b (Encoding.leafIndex τ)) s)) ∧
      (∀ q, ¬(directoryBase L ≤ q ∧ q < memoryEnd L m t) →
        y.mem q = (State.init (input L m t a b) : State registers).data.mem q) := by
  have hi := input_fits a b ha hb haddr hmag
  let x : Data registers := (State.init (input L m t a b)).data
  let S := (m - t + 1) * 10 ^ L
  let K := (boxes L m t).card
  have hK : K = Nat.count (Eligible L (m - t)) S :=
    (count_eligible_eq_card_boxes L m t).symm
  have hKS : K ≤ S := hK ▸ Nat.count_le _
  have hT : 10 ^ L ≤ S := Nat.le_mul_of_pos_left _ (by omega)
  have hA : 4 + 10 ^ L ≤ directoryBase L := by unfold directoryBase; omega
  have hB : 4 + 10 ^ L + 10 ^ L = directoryBase L := by unfold directoryBase; omega
  obtain ⟨xL, xm, xt, xA, xB⟩ := input_readback L m t a b
  obtain ⟨u, hu, uL, um, ut, uA, uB, uD, uμ⟩ := exec_loadInput (L := L) (m := m) (t := t) x xL xm xt
    (haddr.of_le (by unfold addressBound; dsimp only [S] at hT; omega))
  obtain ⟨v, hv, vp, vK, vV, vcat⟩ := exec_geometry
    (L := L) (m := m) (t := t) (D := directoryBase L) u uL um ut uD
    (haddr.of_le (by unfold addressBound directoryBase; dsimp only [S] at hKS hT; omega))
  have vA : v.regs Reg.arrayA = 4 :=
    (hv.regs_eq (by decide : geometry.Preserves Reg.arrayA)).trans uA
  have vB : v.regs Reg.arrayB = 4 + 10 ^ L :=
    (hv.regs_eq (by decide : geometry.Preserves Reg.arrayB)).trans uB
  have vV' : v.regs Reg.values = valueBase L m t := vV
  have vleft (i : Fin (10 ^ L)) : v.mem (4 + i.val) = Signed.encode (a i) := by
    rw [vcat.frame _ (by have := i.isLt; omega) (by
      unfold directoryBase; have := i.isLt; omega), uμ]
    exact xA i
  have vright (i : Fin (10 ^ L)) : v.mem (4 + 10 ^ L + i.val) = Signed.encode (b i) := by
    rw [vcat.frame _ (by have := i.isLt; omega) (by
      unfold directoryBase; have := i.isLt; omega), uμ]
    exact xB i
  obtain ⟨y, hy, yvalues, yframe, yregs⟩ := exec_tile v
    (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))
    (fun τ => ha _) (fun τ => hb _) vp vV' vA vB (vK.trans hK)
    vcat (Nat.le_refl _) (by rw [← hK]; exact Nat.le_refl _)
    (by unfold valueBase recordBase; omega)
    (by unfold valueBase recordBase; omega)
    (fun i => by simpa only [leafIndex_leafAt] using vleft i)
    (fun i => by simpa only [leafIndex_leafAt] using vright i)
    (haddr.of_le (by
      unfold addressBound valueBase recordBase directoryBase
      dsimp only [K, S] at hKS hT
      omega)) hmag
  have he : ExecWithin (w + 2) program x y (timeBound L m t - 1) := by
    apply (hu.seq (hv.seq hy)).mono
    simp only [timeBound, geometryTime, tileTime, count_eligible_eq_card_boxes]
    omega
  refine ⟨hi, y, he, he.bounded (Data.Bounded.init hi), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, yvalues, ?_⟩
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.levels)).trans vp.levels
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.height)).trans vp.height
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.span)).trans vp.span
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.directory)).trans vp.directory
  · exact (yregs _ (by decide)).trans vV'
  · exact (yregs _ (by decide)).trans vK
  · intro s hs
    rw [yframe _ (by unfold valueBase recordBase; omega)]
    exact vcat.directory s hs
  · intro q hq
    rw [yframe _ (by unfold memoryEnd at hq; rw [← hK]; omega)]
    rw [vcat.frame _ (by unfold memoryEnd valueBase recordBase at hq; omega)
      (by unfold memoryEnd valueBase recordBase at hq; rw [← hK]; omega), uμ]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
