/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Restore
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Geometry
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Tiles

/-!
# Complete native routed products using one shared box geometry

Original matrix/coordinate/threshold words suffice for the actual full program. Routing,
shared encodings, geometry, retained values, sparse query batches and answer reconstruction
all execute on the same state. The complete original input and outside memory are restored.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

private theorem buffer_order (L m t N Q : ℕ) :
    BandPreparation.memoryEnd L m N ≤ directoryBase L m N Q ∧
    QueriedProduct.snapshotBase L m N Q + QueriedProduct.inputEnd m N Q ≤
      QueriedProduct.groupedBase L m N Q ∧
    QueriedProduct.inputEnd m N Q < QueriedProduct.groupedBase L m N Q ∧
    QueriedProduct.groupedBase L m N Q + Q = QueriedProduct.outputBase L m N Q ∧
    QueriedProduct.outputBase L m N Q + Q ≤ directoryBase L m N Q ∧
    directoryBase L m N Q ≤ valueBase L m t N Q ∧
    valueBase L m t N Q ≤ memoryEnd L m t N Q := by
  have hs := QueriedProduct.producers_le_snapshot L m N Q
  have hT := Nat.zero_le (10 ^ L)
  dsimp only [memoryEnd, resultBase, stackBase, valueBase, recordBase, directoryBase,
    QueriedProduct.memoryEnd, QueriedProduct.stampBase, QueriedProduct.scratchBase,
    QueriedProduct.outputBase, QueriedProduct.groupedBase, QueriedProduct.originalBase,
    QueriedProduct.codeBase, QueriedProduct.offsetBase]
  omega

/-- One fixed native program computes exact original-order signed matrix products from
only original words. Neither routing, encoding, box geometry, execution nor time is supplied. -/
theorem exec {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (ht : t ≤ m) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 160)
    (hinput : ∀ a, 0 < a → a < QueriedProduct.inputEnd m N qs.length → x.mem a =
      (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (QueriedProduct.inputEnd m N qs.length) = t)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    ∃ y, ExecWithin (w + 2) (program bits) x y (timeBound L m t qs) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ y.regs Reg.threshold = t ∧
      (∀ i : Fin qs.length, y.mem (QueriedProduct.outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, ¬(QueriedProduct.inputEnd m N qs.length + 1 ≤ a ∧
        a < memoryEnd L m t N qs.length) → y.mem a = x.mem a) := by
  obtain ⟨hBand, hSnap, hInput, hGroup, hOut, hDV, hEnd⟩ := buffer_order L m t N qs.length
  obtain ⟨r, old, hr, rp, rt, rg, re, rv, ro, rs, rf⟩ :=
    exec_front hw hm bits X Y qs x hinput hthreshold hX hY hbits hmag hfit
  obtain ⟨g, hg, gp, gb, gi, gg, gf⟩ := exec_prepareGeometry r rp rt hfit
  have ggroups : QueriedProduct.SavedGroups L m N qs.length old g.mem :=
    rg.reframe (fun p hp hb => gf p (by omega))
  have genc : QueriedProduct.EncodedBands hm X Y g.mem :=
    re.reframe (fun p hp => gf p (by omega))
  have gs (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      g.mem (QueriedProduct.snapshotBase L m N qs.length + j) = x.mem j := by
    rw [gf _ (by omega)]
    exact rs j hj
  obtain ⟨v, hv, vp, vb, vg, _, _, va, vf⟩ :=
    exec_evaluateTiles hw hm ht X Y qs old g gp gb gi ggroups genc gg
      (fun i => (rv i).1) ro hX hY hmag hfit
  have vs (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      v.mem (QueriedProduct.snapshotBase L m N qs.length + j) = x.mem j := by
    rw [vf _ (by omega) (by omega)]
    exact gs j hj
  obtain ⟨o, ho, op, oa, oframe⟩ := QueriedProduct.exec_reconstruct X Y qs old v vp vg
    (fun i => (rv i).2) va (old_fits hfit)
  have ot : o.regs Reg.threshold = t := (ho.regs_eq (by decide)).trans vb.threshold
  have os (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      o.mem (QueriedProduct.snapshotBase L m N qs.length + j) = x.mem j := by
    rw [oframe _ (Or.inl (by omega))]
    exact vs j hj
  obtain ⟨y, hy, yp, ym⟩ := exec_restoreInput o op ot hfit
  refine ⟨y, ?_, yp, (hy.regs_eq (by decide)).trans ot, ?_, ?_⟩
  · exact (hr.seq (hg.seq (hv.seq (ho.seq hy)))).mono (by unfold timeBound; omega)
  · intro i
    rw [ym, Function.update_of_ne (by omega), ArrayCopy.copyPrefix_outside (by omega)]
    exact oa i
  · intro a ha
    by_cases hi : a < QueriedProduct.inputEnd m N qs.length
    · rw [ym, Function.update_of_ne (by omega)]
      have hread := ArrayCopy.copyPrefix_read (mem := o.mem)
        (src := QueriedProduct.snapshotBase L m N qs.length) (dst := 0) hi
      simpa only [Nat.zero_add] using hread.trans (os a hi)
    · by_cases heq : a = QueriedProduct.inputEnd m N qs.length
      · subst a
        rw [ym, Function.update_self]
        exact hthreshold.symm
      · have habove : memoryEnd L m t N qs.length ≤ a := by omega
        rw [ym, Function.update_of_ne (by omega), ArrayCopy.copyPrefix_outside (by omega),
          oframe _ (Or.inr (by unfold QueriedProduct.scratchBase; omega)),
          vf _ (by omega) (by omega), gf _ (by omega), rf _ (Or.inr (by omega))]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
