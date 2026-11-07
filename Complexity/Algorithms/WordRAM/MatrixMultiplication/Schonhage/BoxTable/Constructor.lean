/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Tile
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Bounds

/-!
# Caller-safe shared geometry and compact value construction

The actual geometry and tile code compose on arbitrary caller data. Both original leaf
arrays lie before the caller's directory pointer; they may otherwise overlap. Scratch
contents need not be zero. Directory ranks, catalogue cardinality and every signed table
word are computed from the original scalar parameters and input words, with a complete
outside-allocation frame. Shared setup and per-tile work remain separately charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Complete actual caller construction, with no assumed catalogue or table geometry. -/
theorem exec_constructor {w L m t D AA BB A B : ℕ} (x : Data registers)
    (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hL : x.regs Reg.levels = L) (hm : x.regs Reg.inner = m)
    (ht : x.regs Reg.threshold = t) (hD : x.regs Reg.directory = D)
    (hAA : x.regs Reg.arrayA = AA) (hBB : x.regs Reg.arrayB = BB)
    (hAD : AA + 10 ^ L ≤ D) (hBD : BB + 10 ^ L ≤ D)
    (hleft : ∀ c : Fin (10 ^ L), x.mem (AA + c.val) = Signed.encode (a (leafAt c)))
    (hright : ∀ c : Fin (10 ^ L), x.mem (BB + c.val) = Signed.encode (b (leafAt c)))
    (haddr : Fits (w + 2) (100 * (D + AA + BB + L + m + t +
      (m - t + 1) * 10 ^ L + 10)))
    (hmag : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) (.seq geometry tile) x y
        (geometryTime L m t + 328 * (boxes L m t).card + 8) ∧
      y.regs Reg.levels = L ∧ y.regs Reg.inner = m ∧ y.regs Reg.threshold = t ∧
      y.regs Reg.height = m - t ∧ y.regs Reg.span = 10 ^ L ∧
      y.regs Reg.directory = D ∧
      y.regs Reg.records = D + (m - t + 1) * 10 ^ L ∧
      y.regs Reg.values = D + (m - t + 1) * 10 ^ L + 3 * (boxes L m t).card ∧
      y.regs Reg.count = (boxes L m t).card ∧
      y.regs Reg.arrayA = AA ∧ y.regs Reg.arrayB = BB ∧
      (∀ s < (m - t + 1) * 10 ^ L,
        y.mem (D + s) = directoryWord L (m - t) s) ∧
      (∀ s < (m - t + 1) * 10 ^ L, Eligible L (m - t) s →
        y.mem (D + (m - t + 1) * 10 ^ L + 3 * (boxes L m t).card +
          Nat.count (Eligible L (m - t)) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(D ≤ q ∧ q < D + (m - t + 1) * 10 ^ L + 4 * (boxes L m t).card) →
        y.mem q = x.mem q) := by
  let S := (m - t + 1) * 10 ^ L
  let K := (boxes L m t).card
  let V := D + S + 3 * K
  have hK : K = Nat.count (Eligible L (m - t)) S :=
    (count_eligible_eq_card_boxes L m t).symm
  have hKS : K ≤ S := hK ▸ Nat.count_le _
  have hTS : 10 ^ L ≤ S := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨v, hv, vp, vK, vV, vcat⟩ := exec_geometry x hL hm ht hD
    (haddr.of_le (by dsimp only [S] at hTS; omega))
  have vA : v.regs Reg.arrayA = AA :=
    (hv.regs_eq (by decide : geometry.Preserves Reg.arrayA)).trans hAA
  have vB : v.regs Reg.arrayB = BB :=
    (hv.regs_eq (by decide : geometry.Preserves Reg.arrayB)).trans hBB
  have vV' : v.regs Reg.values = V := vV
  have vleft (c : Fin (10 ^ L)) : v.mem (AA + c.val) = Signed.encode (a (leafAt c)) := by
    rw [vcat.frame _ (by have := c.isLt; omega) (by have := c.isLt; omega)]
    exact hleft c
  have vright (c : Fin (10 ^ L)) : v.mem (BB + c.val) = Signed.encode (b (leafAt c)) := by
    rw [vcat.frame _ (by have := c.isLt; omega) (by have := c.isLt; omega)]
    exact hright c
  obtain ⟨y, hy, yvalues, yframe, yregs⟩ := exec_tile v a b ha hb vp vV' vA vB
    (vK.trans hK) vcat (Nat.le_refl _) (by rw [← hK])
    (by dsimp only [V]; omega) (by dsimp only [V]; omega) vleft vright
    (haddr.of_le (by dsimp only [S, K] at hKS hTS; dsimp only [V, S, K]; omega)) hmag
  have he : ExecWithin (w + 2) (.seq geometry tile) x y
      (geometryTime L m t + 328 * K + 8) := by
    exact (hv.seq hy).mono (by dsimp only [geometryTime]; rw [← hK]; omega)
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, yvalues, ?_⟩
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.levels)).trans vp.levels
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.inner)).trans
      ((hv.regs_eq (by decide : geometry.Preserves Reg.inner)).trans hm)
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.threshold)).trans
      ((hv.regs_eq (by decide : geometry.Preserves Reg.threshold)).trans ht)
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.height)).trans vp.height
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.span)).trans vp.span
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.directory)).trans vp.directory
  · exact (hy.regs_eq (by decide : tile.Preserves Reg.records)).trans vp.records
  · exact (yregs _ (by decide)).trans vV'
  · exact (yregs _ (by decide)).trans vK
  · exact (yregs _ (by decide)).trans vA
  · exact (yregs _ (by decide)).trans vB
  · intro s hs
    rw [yframe _ (by dsimp only [V, S]; omega)]
    exact vcat.directory s hs
  · intro q hq
    change ¬(D ≤ q ∧ q < D + S + 4 * K) at hq
    rw [yframe _ (by rw [← hK]; dsimp only [V]; omega)]
    rw [vcat.frame _ (by change ¬(D ≤ q ∧ q < D + S); omega)
      (by rw [← hK]; change ¬(D + S ≤ q ∧ q < D + S + 3 * K); omega)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
