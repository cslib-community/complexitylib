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
import Complexity.Computability.WordRAM.Sequence

/-!
# Complete native routed products using one shared box geometry

`exec_fromSnapshot` executes one shared suffix for contiguous and physically gathered inputs:
routing, shared encodings, geometry, retained values, sparse query batches and occurrence
reconstruction. It restores every original snapshot word and the threshold, retaining the
outside-memory frame. `exec` establishes its premises from ordinary original words.
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

/-- Remaining source allowance after layout and the original snapshot copy. -/
@[expose] def snapshotTimeBound (L m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  snapshotFrontTime L m N qs.length + BoxTable.geometryTime L m t + 17 +
    ((∑ j ∈ Finset.range (Cslib.Algorithms.MatrixMultiplication.Schonhage.numBands L m N ^ 2),
      BoxProduct.tileCharge L m t qs j) + 2) + (9 * qs.length + 3) +
    (7 * QueriedProduct.inputEnd m N qs.length + 12)

/-- Execute the unchanged product back end from an actually gathered snapshot. -/
theorem exec_fromSnapshot {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (ht : t ≤ m) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (original : ℕ → ℕ) (x : Data 160)
    (hsource : ∀ a, 0 < a → a < QueriedProduct.inputEnd m N qs.length → original a =
      (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem a)
    (xp : QueriedProduct.Parameters L m N qs.length x)
    (xt : x.regs BoxProduct.Reg.threshold = t)
    (hheader : ∀ a, 0 < a → a < 5 → x.mem a =
      (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem a)
    (hsnapshot : ∀ a < QueriedProduct.inputEnd m N qs.length,
      x.mem (QueriedProduct.snapshotBase L m N qs.length + a) = original a)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    ∃ y, ExecWithin (w + 2) (programFromSnapshot bits) x y (snapshotTimeBound L m t qs) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ y.regs BoxProduct.Reg.threshold = t ∧
      (∀ i : Fin qs.length, y.mem (QueriedProduct.outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length →
        y.mem a = original a) ∧
      y.mem (QueriedProduct.inputEnd m N qs.length) = t ∧
      (∀ a, BoxProduct.memoryEnd L m t N qs.length ≤ a →
        y.mem a = x.mem a) := by
  obtain ⟨hBand, hSnap, hInput, hGroup, hOut, hDV, hEnd⟩ :=
    BoxProduct.buffer_order L m t N qs.length
  obtain ⟨r, old, hr, rp, rt, rg, re, rv, ro, rs, rf⟩ :=
    exec_frontFromSnapshot hw hm bits X Y qs original x hsource xp xt hheader hsnapshot
      hX hY hbits hmag hfit
  obtain ⟨g, hg, gp, gb, gi, gg, gf⟩ := exec_prepareGeometry r rp rt hfit
  have ggroups : QueriedProduct.SavedGroups L m N qs.length old g.mem :=
    rg.reframe (fun p hp hb => gf p (by omega))
  have genc : QueriedProduct.EncodedBands hm X Y g.mem :=
    re.reframe (fun p hp => gf p (by omega))
  have gs (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      g.mem (QueriedProduct.snapshotBase L m N qs.length + j) = original j := by
    rw [gf _ (by omega)]
    exact rs j hj
  obtain ⟨v, hv, vp, vb, vg, _, _, va, vf⟩ :=
    exec_evaluateTiles hw hm ht X Y qs old g gp gb gi ggroups genc gg
      (fun i => (rv i).1) ro hX hY hmag hfit
  have vs (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      v.mem (QueriedProduct.snapshotBase L m N qs.length + j) = original j := by
    rw [vf _ (by omega) (by omega)]
    exact gs j hj
  obtain ⟨o, ho, op, oa, oframe⟩ := QueriedProduct.exec_reconstruct X Y qs old v vp vg
    (fun i => (rv i).2) va (old_fits hfit)
  have ot : o.regs BoxProduct.Reg.threshold = t := (ho.regs_eq (by decide)).trans vb.threshold
  have os (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      o.mem (QueriedProduct.snapshotBase L m N qs.length + j) = original j := by
    rw [oframe _ (Or.inl (by omega))]
    exact vs j hj
  obtain ⟨y, hy, yp, ym⟩ := exec_restoreInput o op ot hfit
  refine ⟨y, ?_, yp, (hy.regs_eq (by decide)).trans ot, ?_, ?_, ?_, ?_⟩
  · exact (hr.seq (hg.seq (hv.seq (ho.seq hy)))).mono (by unfold snapshotTimeBound; omega)
  · intro i
    rw [ym, Function.update_of_ne (by omega), ArrayCopy.copyPrefix_outside (by omega)]
    exact oa i
  · intro a ha
    rw [ym, Function.update_of_ne (by omega)]
    have hread := ArrayCopy.copyPrefix_read (mem := o.mem)
      (src := QueriedProduct.snapshotBase L m N qs.length) (dst := 0) ha
    simpa only [Nat.zero_add] using hread.trans (os a ha)
  · rw [ym, Function.update_self]
  · intro a ha
    rw [ym, Function.update_of_ne (by omega), ArrayCopy.copyPrefix_outside (by omega),
      oframe _ (Or.inr (by unfold QueriedProduct.scratchBase; omega)),
      vf _ (by omega) (by omega), gf _ (by omega), rf _ (Or.inr (by omega))]

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
  obtain ⟨s, hs, sp, st, ss, sf⟩ := exec_snapshot hm bits X Y qs x hinput hthreshold hfit
  have horder := QueriedProduct.producers_le_snapshot L m N qs.length
  obtain ⟨y, hy, yp, yt, ya, yi, ythreshold, yf⟩ :=
    exec_fromSnapshot hw hm ht bits X Y qs x.mem s hinput sp st
      (fun a ha hb => (sf a (Or.inl (by
        unfold QueriedProduct.inputEnd at horder; omega))).trans
          (hinput a ha (by unfold QueriedProduct.inputEnd; omega)))
      ss hX hY hbits hmag hfit
  refine ⟨y, ?_, yp, yt, ya, ?_⟩
  · obtain ⟨u, A, B, hu, hs, hAB⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨p, C, E, hp, hs, hCE⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨l, F, G, hl, hs, hFG⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨r, H, I, hr, hy, hHI⟩ := ExecWithin.seq_iff.mp hy
    obtain ⟨v, J, K, hv, hf, hJK⟩ := ExecWithin.seq_iff.mp hr
    exact ((hu.seq ((hp.seq (hl.seq (hs.seq hv))).seq hf)).seq hy).mono (by
      unfold timeBound snapshotTimeBound frontTime snapshotFrontTime QueriedProduct.routingTimeBound
        QueriedProduct.snapshotTime QueriedProduct.routingFromSnapshotTime at *
      omega)
  · intro a ha
    by_cases hi : a < QueriedProduct.inputEnd m N qs.length
    · exact yi a hi
    · by_cases heq : a = QueriedProduct.inputEnd m N qs.length
      · subst a
        exact ythreshold.trans hthreshold.symm
      · rw [yf a (by omega)]
        exact sf a (Or.inr (by
          have := buffer_order L m t N qs.length
          omega))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
