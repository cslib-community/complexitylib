/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput.Front
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Charges
import all Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Exec

/-!
# Exact original-order products after a physical snapshot gather

This internal continuation uses the unchanged box mathematics and restoration, with actual
snapshot/header readback and computed registers. The native front discharges these premises.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage
open BoxProduct
open scoped BigOperators

/-- Remaining source allowance after layout and the original snapshot copy. -/
@[expose] def continuationTime (L m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  frontTime L m N qs.length + BoxTable.geometryTime L m t + 17 +
    ((∑ j ∈ Finset.range (Cslib.Algorithms.MatrixMultiplication.Schonhage.numBands L m N ^ 2),
      BoxProduct.tileCharge L m t qs j) + 2) + (9 * qs.length + 3) +
    (7 * QueriedProduct.inputEnd m N qs.length + 12)

/-- Execute the unchanged product back end from an actually gathered snapshot. -/
theorem exec {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (ht : t ≤ m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (original : ℕ → ℕ) (x : Data 160)
    (hsource : ∀ a, 0 < a → a < QueriedProduct.inputEnd m N qs.length → original a =
      (State.init (QueriedProduct.input true L X Y qs) : State 160).data.mem a)
    (xp : QueriedProduct.Parameters L m N qs.length x)
    (xt : x.regs BoxProduct.Reg.threshold = t)
    (hheader : ∀ a, 0 < a → a < 5 → x.mem a =
      (State.init (QueriedProduct.input true L X Y qs) : State 160).data.mem a)
    (hsnapshot : ∀ a < QueriedProduct.inputEnd m N qs.length,
      x.mem (QueriedProduct.snapshotBase L m N qs.length + a) = original a)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    ∃ y, ExecWithin (w + 2) continuation x y (continuationTime L m t qs) ∧
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
    exec_front hw hm X Y qs original x hsource xp xt hheader hsnapshot hX hY hbits hmag hfit
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
  · exact (hr.seq (hg.seq (hv.seq (ho.seq hy)))).mono (by unfold continuationTime; omega)
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

/-- Exact identity between the source allowances; only the original snapshot pass is omitted. -/
theorem source_ledger (L m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) :
    prefixTime L + (7 * QueriedProduct.inputEnd m N qs.length + 10) +
      continuationTime L m t qs = BoxProduct.timeBound L m t qs := by
  unfold prefixTime continuationTime frontTime routingTime BoxProduct.timeBound
    BoxProduct.frontTime QueriedProduct.routingTimeBound
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput
