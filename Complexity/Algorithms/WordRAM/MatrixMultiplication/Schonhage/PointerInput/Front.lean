/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput.Routing
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Front
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.MatrixInput

/-!
# Shared bands from physically gathered original words

Actual snapshot readback and the runtime-computed parameter protocol suffice; low matrix and
coordinate payloads may be dirty. All adaptations and shared band construction remain charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage
open BoxProduct

/-- Continue routing and raw-matrix encoding from an actually populated snapshot. -/
theorem exec_front {w L m t N A : ℕ} (hw : 0 < w)
    (hm : m ≤ L) (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
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
    ∃ (y : Data 160) (old : ℕ → ℕ),
      ExecWithin (w + 2) front x y (frontTime L m N qs.length) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ y.regs BoxProduct.Reg.threshold = t ∧
      QueriedProduct.SavedGroups L m N qs.length old y.mem ∧
      QueriedProduct.EncodedBands hm X Y y.mem ∧
      (∀ i : Fin qs.length,
        old (Wanted.codeAddress L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
          (PrunedQuery.queryIndex
            (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val ∧
        old (Wanted.originalAddress L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs)
              qs.length i) = i.val) ∧
      (∀ j ≤ numBands L m N ^ 2,
        old (Wanted.offsetAddress L m N qs.length + j) =
          Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < j) qs.length) ∧
      (∀ j < QueriedProduct.inputEnd m N qs.length,
        y.mem (QueriedProduct.snapshotBase L m N qs.length + j) = original j) ∧
      (∀ p, p < 4 ∨ QueriedProduct.groupedBase L m N qs.length ≤ p → y.mem p = x.mem p) := by
  have hL : x.mem 1 = L := by
    rw [hheader 1 (by decide) (by decide)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hm' : x.mem 2 = m := by
    rw [hheader 2 (by decide) (by decide)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hN : x.mem 3 = N := by
    rw [hheader 3 (by decide) (by decide)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hQ : x.mem 4 = qs.length := by
    rw [hheader 4 (by decide) (by decide)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hqueries (i : ℕ) (hi : i < qs.length) :
      original (QueriedProduct.queryInputBase m N + 2 * i) = (Wanted.inputPairs qs i).1 ∧
      original (QueriedProduct.queryInputBase m N + 2 * i + 1) = (Wanted.inputPairs qs i).2 := by
    have hr := QueriedProduct.input_query_word true L X Y qs ⟨i, hi⟩ 0
    have hc := QueriedProduct.input_query_word true L X Y qs ⟨i, hi⟩ 1
    rw [hsource _ (by unfold QueriedProduct.queryInputBase; omega)
        (by simpa only [Nat.add_zero] using QueriedProduct.query_address_lt hi (by decide : 0 < 2)),
      hsource _ (by unfold QueriedProduct.queryInputBase; omega)
        (QueriedProduct.query_address_lt hi (by decide : 1 < 2)),
      Wanted.inputPairs_get qs ⟨i, hi⟩]
    simpa only [Fin.val_zero, Fin.val_one, Nat.add_zero, ↓reduceIte, Fin.reduceEq] using
      And.intro hr hc
  obtain ⟨r, old, hr, rp, rg, rv, ro, rs, rf⟩ :=
    exec_routing hm qs x xp original
      hsnapshot hL hm' hN hQ hqueries (BoxProduct.old_fits hfit)
  have rt : r.regs BoxProduct.Reg.threshold = t := (hr.regs_eq (by decide)).trans xt
  have hs := QueriedProduct.producers_le_snapshot L m N qs.length
  have hsnapshot : QueriedProduct.snapshotBase L m N qs.length +
      QueriedProduct.inputEnd m N qs.length ≤ QueriedProduct.groupedBase L m N qs.length := by
    unfold QueriedProduct.groupedBase QueriedProduct.originalBase QueriedProduct.codeBase
      QueriedProduct.offsetBase
    omega
  have rsource (j : ℕ) (hj : j < 2 * (N * D m)) :
      r.mem (QueriedProduct.snapshotBase L m N qs.length + 5 + j) =
        (State.init (QueriedProduct.input true L X Y qs) : State 160).data.mem (5 + j) := by
    rw [show QueriedProduct.snapshotBase L m N qs.length + 5 + j =
      QueriedProduct.snapshotBase L m N qs.length + (5 + j) by omega,
      rs _ (by unfold QueriedProduct.inputEnd; omega)]
    exact hsource _ (by omega) (by unfold QueriedProduct.inputEnd; omega)
  obtain ⟨c, hc, cp, cm, cf⟩ := QueriedProduct.exec_prepareInputMatrices hw true X Y qs r rp
    rsource hX hY (fun _ => hbits) (old_magnitude hmag) (old_fits hfit)
  have ct : c.regs BoxProduct.Reg.threshold = t := (hc.regs_eq (by decide)).trans rt
  have cs (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      c.mem (QueriedProduct.snapshotBase L m N qs.length + j) = original j := by
    rw [cf _ (Or.inr (by unfold QueriedProduct.inputEnd at hs; omega)), rs j hj]
  have cg : QueriedProduct.SavedGroups L m N qs.length old c.mem :=
    rg.reframe (fun a ha _ => cf a (Or.inr (by
      unfold QueriedProduct.offsetBase at ha
      unfold QueriedProduct.inputEnd at hs
      omega)))
  obtain ⟨y, hy, yp, yl, yr, yf⟩ := QueriedProduct.exec_bands hw hm X Y c cp
    (by rw [cf 1 (Or.inl (by decide)), rf 1 (Or.inl (by decide))]; exact hL)
    (by rw [cf 2 (Or.inl (by decide)), rf 2 (Or.inl (by decide))]; exact hm')
    (by rw [cf 3 (Or.inl (by decide)), rf 3 (Or.inl (by decide))]; exact hN)
    cm hX hY (old_magnitude hmag) (old_fits hfit)
  have yt : y.regs BoxProduct.Reg.threshold = t := (hy.regs_eq (by decide)).trans ct
  have yg : QueriedProduct.SavedGroups L m N qs.length old y.mem :=
    cg.reframe (fun a ha _ => yf a (Or.inr (by unfold QueriedProduct.offsetBase at ha; omega)))
  refine ⟨y, old, ?_, yp, yt, yg, ⟨yl, yr⟩, rv, ro, ?_, ?_⟩
  · exact (hr.seq (hc.seq hy)).mono (by unfold frontTime; omega)
  · intro j hj
    rw [yf _ (Or.inr (by omega))]
    exact cs j hj
  · intro p hp
    calc
      y.mem p = c.mem p := by
        apply yf
        rcases hp with hp | hp
        · exact Or.inl (by unfold BandPreparation.inputEnd; omega)
        · exact Or.inr (by omega)
      _ = r.mem p := by
        apply cf
        rcases hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr (by unfold QueriedProduct.inputEnd at hs; omega)
      _ = x.mem p := rf p (by rcases hp with hp | hp <;> omega)


end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput
