/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.MatrixInput


/-!
# Correctness of original-input routing and shared band production

The extra readonly parameter pass locates the original threshold. Actual routing and
matrix adaptation then establish every computed wanted span, stable permutation and
shared encoding from original words, while retaining the protected input snapshot.
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
  have hL : x.mem 1 = L := by
    rw [hinput 1 (by decide) (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hm' : x.mem 2 = m := by
    rw [hinput 2 (by decide) (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hN : x.mem 3 = N := by
    rw [hinput 3 (by decide) (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hQ : x.mem 4 = qs.length := by
    rw [hinput 4 (by decide) (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, QueriedProduct.input]
  have hqueries (i : ℕ) (hi : i < qs.length) :
      x.mem (QueriedProduct.queryInputBase m N + 2 * i) = (Wanted.inputPairs qs i).1 ∧
      x.mem (QueriedProduct.queryInputBase m N + 2 * i + 1) = (Wanted.inputPairs qs i).2 := by
    have hr := QueriedProduct.input_query_word bits L X Y qs ⟨i, hi⟩ 0
    have hc := QueriedProduct.input_query_word bits L X Y qs ⟨i, hi⟩ 1
    rw [hinput _ (by unfold QueriedProduct.queryInputBase; omega) (by
        simpa only [Nat.add_zero] using QueriedProduct.query_address_lt hi (by decide : 0 < 2)),
      hinput _ (by unfold QueriedProduct.queryInputBase; omega)
        (QueriedProduct.query_address_lt hi (by decide : 1 < 2))]
    rw [Wanted.inputPairs_get qs ⟨i, hi⟩]
    simpa only [Fin.val_zero, Fin.val_one, Nat.add_zero, ↓reduceIte, Fin.reduceEq] using
      And.intro hr hc
  obtain ⟨u, hu, ut, um⟩ := exec_loadThreshold hm x hL hm' hN hQ hthreshold hfit
  obtain ⟨r, old, hr, rp, rg, rv, ro, rs, rf⟩ :=
    QueriedProduct.exec_prepareRouting hm qs u (by rw [um]; exact hL)
      (by rw [um]; exact hm') (by rw [um]; exact hN) (by rw [um]; exact hQ)
      (by intro i hi; rw [um]; exact hqueries i hi) (old_fits hfit)
  have rt : r.regs Reg.threshold = t := (hr.regs_eq (by decide)).trans ut
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
      rs _ (by unfold QueriedProduct.inputEnd; omega), um]
    exact hinput _ (by omega) (by unfold QueriedProduct.inputEnd; omega)
  obtain ⟨c, hc, cp, cm, cf⟩ := QueriedProduct.exec_prepareInputMatrices hw bits X Y qs r rp
    rsource hX hY hbits (old_magnitude hmag) (old_fits hfit)
  have ct : c.regs Reg.threshold = t := (hc.regs_eq (by cases bits <;> decide)).trans rt
  have cs (j : ℕ) (hj : j < QueriedProduct.inputEnd m N qs.length) :
      c.mem (QueriedProduct.snapshotBase L m N qs.length + j) = x.mem j := by
    rw [cf _ (Or.inr (by unfold QueriedProduct.inputEnd at hs; omega)), rs j hj, um]
  have cg : QueriedProduct.SavedGroups L m N qs.length old c.mem :=
    rg.reframe (fun a ha _ => cf a (Or.inr (by
      unfold QueriedProduct.offsetBase at ha
      unfold QueriedProduct.inputEnd at hs
      omega)))
  obtain ⟨y, hy, yp, yl, yr, yf⟩ := QueriedProduct.exec_bands hw hm X Y c cp
    (by rw [cf 1 (Or.inl (by decide)), rf 1 (Or.inl (by decide)), um]; exact hL)
    (by rw [cf 2 (Or.inl (by decide)), rf 2 (Or.inl (by decide)), um]; exact hm')
    (by rw [cf 3 (Or.inl (by decide)), rf 3 (Or.inl (by decide)), um]; exact hN)
    cm hX hY (old_magnitude hmag) (old_fits hfit)
  have yt : y.regs Reg.threshold = t := (hy.regs_eq (by decide)).trans ct
  have yg : QueriedProduct.SavedGroups L m N qs.length old y.mem :=
    cg.reframe (fun a ha _ => yf a (Or.inr (by unfold QueriedProduct.offsetBase at ha; omega)))
  refine ⟨y, old, ?_, yp, yt, yg, ⟨yl, yr⟩, rv, ro, ?_, ?_⟩
  · exact (hu.seq (hr.seq (hc.seq hy))).mono (by unfold frontTime; omega)
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
      _ = u.mem p := rf p (by rcases hp with hp | hp <;> omega)
      _ = x.mem p := congrFun um p

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
