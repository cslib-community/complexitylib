/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.MatrixInput
import CslibFrontier.Computability.WordRAM.Sequence


/-!
# Correctness of original-input routing and shared band production

`exec_frontFromSnapshot` shares actual routing, matrix adaptation and band production for
contiguous and physically gathered inputs, in both raw unsigned and canonical signed modes.
The snapshot and ordinary header readback are explicit premises; low payloads may be dirty.
`exec_front` establishes them by executing the original threshold and snapshot prefix.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem exec_thresholdLoad {W L m t N Q : ℕ} (x : Data 160)
    (hrows : x.regs (QueriedProduct.bank BandPreparation.rows) = N)
    (hcols : x.regs (QueriedProduct.bank BandPreparation.columns) = D m)
    (hQ : x.mem 4 = Q) (ht : x.mem (QueriedProduct.inputEnd m N Q) = t)
    (hfit : Fits W (wordBudget L m t N Q)) :
    ∃ y, ExecWithin W thresholdLoad x y 9 ∧ y.regs Reg.threshold = t ∧ y.mem = x.mem := by
  have hI : Fits W (QueriedProduct.inputEnd m N Q) :=
    hfit.of_le (by unfold wordBudget QueriedProduct.wordBudget; omega)
  have h4 : Fits W 4 := hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  have h5 : Fits W 5 := hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  have hprod : Fits W (N * D m) := hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  have hdouble : Fits W (N * D m + N * D m) :=
    hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  have hq : Fits W (Q + Q) := hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  have hsum : Fits W ((N * D m + N * D m) + (Q + Q)) :=
    hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  have hsum5 : Fits W ((N * D m + N * D m) + (Q + Q) + 5) :=
    hI.of_le (by unfold QueriedProduct.inputEnd; omega)
  let z0 := (x.set QueriedProduct.Reg.address 4).set QueriedProduct.Reg.queryCount Q
  let z1 := (z0.set QueriedProduct.Reg.address (N * D m)).set QueriedProduct.Reg.address
    (N * D m + N * D m)
  let z2 := (z1.set QueriedProduct.Reg.value (Q + Q)).set QueriedProduct.Reg.address
    ((N * D m + N * D m) + (Q + Q))
  let z3 := (z2.set QueriedProduct.Reg.value 5).set QueriedProduct.Reg.address
    (QueriedProduct.inputEnd m N Q)
  let y := z3.set Reg.threshold t
  have haddr : (N * D m + N * D m) + (Q + Q) + 5 =
      QueriedProduct.inputEnd m N Q := by unfold QueriedProduct.inputEnd; omega
  change x.regs (34 : Fin 160) = N at hrows
  change x.regs (35 : Fin 160) = D m at hcols
  have er : QueriedProduct.bank BandPreparation.rows = (34 : Fin 160) := rfl
  have ec : QueriedProduct.bank BandPreparation.columns = (35 : Fin 160) := rfl
  have he : ExecWithin W thresholdLoad x y 9 := by
    simp only [thresholdLoad, er, ec]
    ram_eval [y, z3, z2, z1, z0, hrows, hcols, hQ, ht, hI,
      h4, h5, hprod, hdouble, hq, hsum, hsum5, haddr,
      QueriedProduct.Reg.queryCount, QueriedProduct.Reg.address, QueriedProduct.Reg.value,
      Reg.threshold, Fin.mk.injEq]
  exact ⟨y, he, by simp [y], rfl⟩

/-- The actual readonly pass locates and retains the original threshold without changing memory. -/
theorem exec_loadThreshold {W L m t N Q : ℕ} (hm : m ≤ L) (x : Data 160)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hQ : x.mem 4 = Q) (ht : x.mem (QueriedProduct.inputEnd m N Q) = t)
    (hfit : Fits W (wordBudget L m t N Q)) :
    ∃ y, ExecWithin W loadThreshold x y (thresholdTime L) ∧
      y.regs Reg.threshold = t ∧ y.mem = x.mem := by
  obtain ⟨u, hu, up, um, _⟩ := QueriedProduct.exec_parameters hm x hL hmemory hN
    (old_fits hfit)
  obtain ⟨y, hy, yt, ym⟩ := exec_thresholdLoad u up.fixed.rows up.columns
    (by rw [um]; exact hQ) (by rw [um]; exact ht) hfit
  exact ⟨y, hu.seq hy, yt, ym.trans um⟩

/-- Execute the original threshold and snapshot prefix from ordinary input words. -/
theorem exec_snapshot {w L m t N : ℕ} (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 160)
    (hinput : ∀ a, 0 < a → a < QueriedProduct.inputEnd m N qs.length → x.mem a =
      (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (QueriedProduct.inputEnd m N qs.length) = t)
    (hfit : Fits w (wordBudget L m t N qs.length)) :
    ∃ y, ExecWithin w (.seq loadThreshold QueriedProduct.prepareSnapshot) x y
        (thresholdTime L + QueriedProduct.snapshotTime L m N qs.length) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ y.regs Reg.threshold = t ∧
      (∀ j < QueriedProduct.inputEnd m N qs.length,
        y.mem (QueriedProduct.snapshotBase L m N qs.length + j) = x.mem j) ∧
      (∀ a, a < QueriedProduct.snapshotBase L m N qs.length ∨
        QueriedProduct.snapshotBase L m N qs.length + QueriedProduct.inputEnd m N qs.length ≤ a →
        y.mem a = x.mem a) := by
  have hh (a : ℕ) (ha : 0 < a) (hb : a < 5) :=
    hinput a ha (by unfold QueriedProduct.inputEnd; omega)
  have hL : x.mem 1 = L := by
    simpa [State.init, Data.init, QueriedProduct.input] using hh 1 (by decide) (by decide)
  have hm' : x.mem 2 = m := by
    simpa [State.init, Data.init, QueriedProduct.input] using hh 2 (by decide) (by decide)
  have hN : x.mem 3 = N := by
    simpa [State.init, Data.init, QueriedProduct.input] using hh 3 (by decide) (by decide)
  have hQ : x.mem 4 = qs.length := by
    simpa [State.init, Data.init, QueriedProduct.input] using hh 4 (by decide) (by decide)
  obtain ⟨u, hu, ut, um⟩ := exec_loadThreshold hm x hL hm' hN hQ hthreshold hfit
  obtain ⟨y, hy, yp, ys, yf⟩ := QueriedProduct.exec_prepareSnapshot hm u
    (by rw [um]; exact hL) (by rw [um]; exact hm') (by rw [um]; exact hN)
    (by rw [um]; exact hQ) (old_fits hfit)
  exact ⟨y, hu.seq hy, yp, (hy.regs_eq (by decide)).trans ut,
    by simpa only [um] using ys, by simpa only [um] using yf⟩

/-- Continue routing and raw-matrix encoding from an actually populated snapshot. -/
theorem exec_frontFromSnapshot {w L m t N A : ℕ} (hw : 0 < w)
    (hm : m ≤ L) (bits : Bool)
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
    ∃ (y : Data 160) (old : ℕ → ℕ),
      ExecWithin (w + 2) (frontFromSnapshot bits) x y (snapshotFrontTime L m N qs.length) ∧
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
    have hr := QueriedProduct.input_query_word bits L X Y qs ⟨i, hi⟩ 0
    have hc := QueriedProduct.input_query_word bits L X Y qs ⟨i, hi⟩ 1
    rw [hsource _ (by unfold QueriedProduct.queryInputBase; omega)
        (by simpa only [Nat.add_zero] using QueriedProduct.query_address_lt hi (by decide : 0 < 2)),
      hsource _ (by unfold QueriedProduct.queryInputBase; omega)
        (QueriedProduct.query_address_lt hi (by decide : 1 < 2)),
      Wanted.inputPairs_get qs ⟨i, hi⟩]
    simpa only [Fin.val_zero, Fin.val_one, Nat.add_zero, ↓reduceIte, Fin.reduceEq] using
      And.intro hr hc
  obtain ⟨r, old, hr, rp, rg, rv, ro, rs, rf⟩ :=
    QueriedProduct.exec_routingFromSnapshot hm qs x xp original
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
        (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem (5 + j) := by
    rw [show QueriedProduct.snapshotBase L m N qs.length + 5 + j =
      QueriedProduct.snapshotBase L m N qs.length + (5 + j) by omega,
      rs _ (by unfold QueriedProduct.inputEnd; omega)]
    exact hsource _ (by omega) (by unfold QueriedProduct.inputEnd; omega)
  obtain ⟨c, hc, cp, cm, cf⟩ := QueriedProduct.exec_prepareInputMatrices hw bits X Y qs r rp
    rsource hX hY hbits (old_magnitude hmag) (old_fits hfit)
  have ct : c.regs BoxProduct.Reg.threshold = t := (hc.regs_eq (by cases bits <;> decide)).trans rt
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
  · exact (hr.seq (hc.seq hy)).mono (by unfold snapshotFrontTime; omega)
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

/-- Actual routing and shared encoding production from ordinary original matrix words.
The returned router memory is an executed proof witness, not an input certificate. -/
theorem exec_front {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 160)
    (hinput : ∀ a, 0 < a → a < QueriedProduct.inputEnd m N qs.length → x.mem a =
      (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (QueriedProduct.inputEnd m N qs.length) = t)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    ∃ (y : Data 160) (old : ℕ → ℕ),
      ExecWithin (w + 2) (front bits) x y (frontTime L m N qs.length) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ y.regs Reg.threshold = t ∧
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
        y.mem (QueriedProduct.snapshotBase L m N qs.length + j) = x.mem j) ∧
      (∀ p, p < 4 ∨ QueriedProduct.groupedBase L m N qs.length ≤ p → y.mem p = x.mem p) := by
  obtain ⟨s, hs, sp, st, ss, sf⟩ := exec_snapshot hm bits X Y qs x hinput hthreshold hfit
  have horder := QueriedProduct.producers_le_snapshot L m N qs.length
  obtain ⟨y, old, hy, yp, yt, yg, ye, yv, yo, ys, yf⟩ :=
    exec_frontFromSnapshot hw hm bits X Y qs x.mem s hinput sp st
      (fun a ha hb => (sf a (Or.inl (by
        unfold QueriedProduct.inputEnd at horder
        omega))).trans (hinput a ha (by unfold QueriedProduct.inputEnd; omega)))
      ss hX hY hbits hmag hfit
  refine ⟨y, old, ?_, yp, yt, yg, ye, yv, yo, ys, ?_⟩
  · obtain ⟨u, A, B, hu, hs, hAB⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨p, C, E, hp, hs, hCE⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨l, F, G, hl, hs, hFG⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨r, H, I, hr, hy, hHI⟩ := ExecWithin.seq_iff.mp hy
    exact (hu.seq ((hp.seq (hl.seq (hs.seq hr))).seq hy)).mono (by
      unfold frontTime snapshotFrontTime QueriedProduct.snapshotTime
        QueriedProduct.routingFromSnapshotTime QueriedProduct.routingTimeBound at *
      omega)
  · intro a ha
    rw [yf a ha]
    exact sf a (by
      rcases ha with ha | ha
      · exact Or.inl (by unfold QueriedProduct.inputEnd at horder; omega)
      · exact Or.inr (by
          unfold QueriedProduct.groupedBase QueriedProduct.originalBase
            QueriedProduct.codeBase QueriedProduct.offsetBase at ha
          omega))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
