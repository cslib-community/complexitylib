/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.State

/-!
# Actual span capture and complete box-ABI restoration

The existing checked native span arithmetic is reused. Its computed low pointers are
captured before those registers are repurposed, and every scalar read by the retained
box constructor is restored. Scratch values from earlier queries may be arbitrary.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem exec_batchArguments {w Q O n R : ℕ} (x : Data 160)
    (hq : x.regs (QueriedProduct.bank PrunedQuery.queries) = Q)
    (hn : x.regs (QueriedProduct.bank PrunedQuery.queryCount) = n)
    (ho : x.regs (QueriedProduct.bank PrunedQuery.output) = O)
    (hr : x.regs Reg.results = R) (hfit : Fits w (Q + n)) :
    ∃ y, ExecWithin w batchArguments x y 5 ∧
      (y.comap boxBank).regs BoxBatch.Reg.next = Q ∧
      (y.comap boxBank).regs BoxBatch.Reg.stop = Q + n ∧
      (y.comap boxBank).regs BoxBatch.Reg.output = R ∧
      y.regs QueriedProduct.Reg.destination = O ∧ y.regs QueriedProduct.Reg.length = n ∧
      y.mem = x.mem := by
  change x.regs (13 : Fin 160) = Q at hq
  change x.regs (14 : Fin 160) = n at hn
  change x.regs (15 : Fin 160) = O at ho
  let y := ((((x.set (boxBank BoxBatch.Reg.next) Q).set (boxBank BoxBatch.Reg.stop)
    (Q + n)).set (boxBank BoxBatch.Reg.output) R).set QueriedProduct.Reg.destination O).set
      QueriedProduct.Reg.length n
  have eq : QueriedProduct.bank PrunedQuery.queries = (13 : Fin 160) := rfl
  have en : QueriedProduct.bank PrunedQuery.queryCount = (14 : Fin 160) := rfl
  have eo : QueriedProduct.bank PrunedQuery.output = (15 : Fin 160) := rfl
  have eNext : boxBank BoxBatch.Reg.next = (43 : Fin 160) := rfl
  have eStop : boxBank BoxBatch.Reg.stop = (44 : Fin 160) := rfl
  have eOut : boxBank BoxBatch.Reg.output = (45 : Fin 160) := rfl
  have he : ExecWithin w batchArguments x y 5 := by
    simp only [batchArguments, eq, en, eo, eNext, eStop, eOut]
    ram_eval [y, eNext, eStop, eOut, hq, hn, ho, hr, hfit, Reg.results,
      QueriedProduct.Reg.destination, QueriedProduct.Reg.length, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals simp [y, Data.comap_regs, boxBank, BoxBatch.Reg.next, BoxBatch.Reg.stop,
    BoxBatch.Reg.output, QueriedProduct.Reg.destination, QueriedProduct.Reg.length]

private theorem exec_restoreBoxArguments {w L m t N Q AA BB : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (hb : Parameters L m t N Q x)
    (hA : (x.comap QueriedProduct.bank).regs PrunedQuery.arrayA = AA)
    (hB : (x.comap QueriedProduct.bank).regs PrunedQuery.arrayB = BB)
    (hfit : Fits w (wordBudget L m t N Q)) :
    ∃ y, ExecWithin w restoreBoxArguments x y 18 ∧ y.mem = x.mem ∧
      BoxTable.CatalogueParameters L (m - t) (directoryBase L m N Q)
        (recordBase L m t N Q) (y.comap boxBank) ∧
      (y.comap boxBank).regs BoxTable.Reg.inner = m ∧
      (y.comap boxBank).regs BoxTable.Reg.threshold = t ∧
      (y.comap boxBank).regs BoxTable.Reg.values = valueBase L m t N Q ∧
      (y.comap boxBank).regs BoxTable.Reg.count = (boxes L m t).card ∧
      (y.comap boxBank).regs BoxTable.Reg.arrayA = AA ∧
      (y.comap boxBank).regs BoxTable.Reg.arrayB = BB := by
  obtain ⟨c, hc, c0, c1, c10, c9, c3, cm, _⟩ := BoxTable.exec_constants (x.comap boxBank)
    (hfit.of_le (by unfold wordBudget; omega))
  let u := c.extend boxBank x
  have hu := hc.rename boxBank_injective
  have up : QueriedProduct.Parameters L m N Q u := hp.reframe
    (fun i hi => boxBank_extend_high c x i (by omega))
  have ub : Parameters L m t N Q u := hb.extend c
  have uA : u.regs (QueriedProduct.bank PrunedQuery.arrayA) = AA :=
    (hu.regs_eq (by decide)).trans hA
  have uB : u.regs (QueriedProduct.bank PrunedQuery.arrayB) = BB :=
    (hu.regs_eq (by decide)).trans hB
  have fH : Fits w (m - t) := hfit.of_le (by unfold wordBudget; omega)
  have fS : Fits w (m - t + 1) := hfit.of_le (by unfold wordBudget; omega)
  have fST : Fits w ((m - t + 1) * 10 ^ L) := hfit.of_le (by unfold wordBudget; omega)
  let v := (((((u.set (boxBank BoxTable.Reg.arrayA) AA).set (boxBank BoxTable.Reg.arrayB) BB).set
    (boxBank BoxTable.Reg.levels) L).set (boxBank BoxTable.Reg.inner) m).set
      (boxBank BoxTable.Reg.threshold) t).set (boxBank BoxTable.Reg.height) (m - t)
  let v₁ := ((((v.set (boxBank BoxTable.Reg.span) (10 ^ L)).set
    (boxBank BoxTable.Reg.directory) (directoryBase L m N Q)).set
    (boxBank BoxTable.Reg.records) (recordBase L m t N Q)).set
    (boxBank BoxTable.Reg.values) (valueBase L m t N Q)).set
    (boxBank BoxTable.Reg.count) (boxes L m t).card
  let y := (v₁.set (boxBank BoxTable.Reg.slots) (m - t + 1)).set
    (boxBank BoxTable.Reg.slots) ((m - t + 1) * 10 ^ L)
  have eA : boxBank BoxTable.Reg.arrayA = (17 : Fin 160) := rfl
  have eB : boxBank BoxTable.Reg.arrayB = (18 : Fin 160) := rfl
  have eL : boxBank BoxTable.Reg.levels = (9 : Fin 160) := rfl
  have eM : boxBank BoxTable.Reg.inner = (10 : Fin 160) := rfl
  have eT : boxBank BoxTable.Reg.threshold = (11 : Fin 160) := rfl
  have eH : boxBank BoxTable.Reg.height = (12 : Fin 160) := rfl
  have eSpan : boxBank BoxTable.Reg.span = (13 : Fin 160) := rfl
  have eD : boxBank BoxTable.Reg.directory = (14 : Fin 160) := rfl
  have eR : boxBank BoxTable.Reg.records = (15 : Fin 160) := rfl
  have eV : boxBank BoxTable.Reg.values = (16 : Fin 160) := rfl
  have eK : boxBank BoxTable.Reg.count = (21 : Fin 160) := rfl
  have eS : boxBank BoxTable.Reg.slots = (19 : Fin 160) := rfl
  have eOldA : QueriedProduct.bank PrunedQuery.arrayA = (11 : Fin 160) := rfl
  have eOldB : QueriedProduct.bank PrunedQuery.arrayB = (12 : Fin 160) := rfl
  change u.regs (11 : Fin 160) = AA at uA
  change u.regs (12 : Fin 160) = BB at uB
  have hy : ExecWithin w restoreBoxArguments x y 18 := by
    simp only [restoreBoxArguments, eA, eB, eL, eM, eT, eH, eSpan, eD, eR, eV, eK, eS, eOldA, eOldB]
    refine (hu.seq (T₂ := 13) ?_).mono (by omega)
    change ExecWithin w _ u y 13
    ram_eval [y, v₁, v, eA, eB, eL, eM, eT, eH, eSpan, eD, eR, eV, eK, eS,
      up.depth, up.inner, up.leaves, up.one, ub.threshold, ub.directory, ub.records,
      ub.values, ub.count, uA, uB, fH, fS, fST, Reg.threshold, Reg.directory,
      Reg.records, Reg.values, Reg.count, QueriedProduct.Reg.depth, QueriedProduct.Reg.inner,
      QueriedProduct.Reg.leaves, QueriedProduct.Reg.one, Fin.mk.injEq]
  have eOne : boxBank BoxTable.Reg.one = (32 : Fin 160) := rfl
  have eTen : boxBank BoxTable.Reg.ten = (33 : Fin 160) := rfl
  have eNine : boxBank BoxTable.Reg.nine = (34 : Fin 160) := rfl
  have eThree : boxBank BoxTable.Reg.three = (35 : Fin 160) := rfl
  have eNil : boxBank BoxTable.Reg.nil = (42 : Fin 160) := rfl
  have hc0 : u.regs (42 : Fin 160) = 0 := (boxBank_injective.extend_apply _ _ _).trans c0
  have hc1 : u.regs (32 : Fin 160) = 1 := (boxBank_injective.extend_apply _ _ _).trans c1
  have hc10 : u.regs (33 : Fin 160) = 10 := (boxBank_injective.extend_apply _ _ _).trans c10
  have hc9 : u.regs (34 : Fin 160) = 9 := (boxBank_injective.extend_apply _ _ _).trans c9
  have hc3 : u.regs (35 : Fin 160) = 3 := (boxBank_injective.extend_apply _ _ _).trans c3
  refine ⟨y, hy, cm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    all_goals simp [y, v₁, v, Data.comap_regs, eA, eB, eL, eM, eT, eH, eSpan,
      eD, eR, eV, eK, eS, eOne, eTen, eNine, eThree, eNil, hc0, hc1, hc10, hc9, hc3]
  all_goals simp [y, v₁, v, Data.comap_regs, eA, eB, eL, eM, eT, eH, eSpan,
    eD, eR, eV, eK, eS]

set_option maxRecDepth 4096 in
-- The fixed caller frame check unfolds the existing 32-member 160-register protocol.
/-- Actual checked span arithmetic and complete box argument restoration, including the
saved query cursors and real temporary-to-grouped copy arguments. -/
theorem exec_tileArguments {w L m t N Q j a b : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (hb : Parameters L m t N Q x)
    (hx : x.regs QueriedProduct.Reg.index = j) (hj : j < numBands L m N ^ 2)
    (ha : x.mem (QueriedProduct.offsetBase L m N Q + j) = a)
    (hstop : x.mem (QueriedProduct.offsetBase L m N Q + j + 1) = b)
    (hab : a ≤ b) (hbQ : b ≤ Q) (hfit : Fits w (wordBudget L m t N Q)) :
    ∃ y, ExecWithin w tileArguments x y 44 ∧
      QueriedProduct.Parameters L m N Q y ∧ Parameters L m t N Q y ∧ y.mem = x.mem ∧
      y.regs QueriedProduct.Reg.index = j ∧
      BoxTable.CatalogueParameters L (m - t) (directoryBase L m N Q)
        (recordBase L m t N Q) (y.comap boxBank) ∧
      (y.comap boxBank).regs BoxTable.Reg.inner = m ∧
      (y.comap boxBank).regs BoxTable.Reg.threshold = t ∧
      (y.comap boxBank).regs BoxTable.Reg.values = valueBase L m t N Q ∧
      (y.comap boxBank).regs BoxTable.Reg.count = (boxes L m t).card ∧
      (y.comap boxBank).regs BoxTable.Reg.arrayA =
        BandPreparation.catalogueBase L m N + j / numBands L m N * 10 ^ L ∧
      (y.comap boxBank).regs BoxTable.Reg.arrayB =
        BandPreparation.catalogueBase L m N +
          (numBands L m N + j % numBands L m N) * 10 ^ L ∧
      (y.comap boxBank).regs BoxBatch.Reg.next = QueriedProduct.codeBase L m N Q + a ∧
      (y.comap boxBank).regs BoxBatch.Reg.stop = QueriedProduct.codeBase L m N Q + b ∧
      (y.comap boxBank).regs BoxBatch.Reg.output = resultBase L m t N Q ∧
      y.regs QueriedProduct.Reg.destination = QueriedProduct.groupedBase L m N Q + a ∧
      y.regs QueriedProduct.Reg.length = b - a := by
  obtain ⟨u, hu, up, um, ui, _, uL, uA, uB, uq, un, uo, _⟩ :=
    QueriedProduct.exec_tileArguments x hp hx hj ha hstop hab hbQ (old_fits hfit)
  have ub : Parameters L m t N Q u := by
    exact ⟨(hu.regs_eq (by decide)).trans hb.threshold,
      (hu.regs_eq (by decide)).trans hb.directory, (hu.regs_eq (by decide)).trans hb.records,
      (hu.regs_eq (by decide)).trans hb.values, (hu.regs_eq (by decide)).trans hb.count,
      (hu.regs_eq (by decide)).trans hb.results⟩
  have fq : Fits w (QueriedProduct.codeBase L m N Q + a + (b - a)) := by
    apply allocated_fits hfit
    have h10 := Nat.zero_le (10 ^ L)
    unfold memoryEnd resultBase stackBase valueBase recordBase directoryBase
      QueriedProduct.memoryEnd QueriedProduct.stampBase QueriedProduct.scratchBase
      QueriedProduct.outputBase QueriedProduct.groupedBase QueriedProduct.originalBase
    omega
  obtain ⟨v, hv, vn, vs, vo, vd, vl, vm⟩ := exec_batchArguments u uq un uo ub.results fq
  have vp : QueriedProduct.Parameters L m N Q v := up.of_frame (by
    intro i hi
    exact hv.regs_eq (by decide +revert))
  have vb : Parameters L m t N Q v := by
    exact ⟨(hv.regs_eq (by decide)).trans ub.threshold,
      (hv.regs_eq (by decide)).trans ub.directory, (hv.regs_eq (by decide)).trans ub.records,
      (hv.regs_eq (by decide)).trans ub.values, (hv.regs_eq (by decide)).trans ub.count,
      (hv.regs_eq (by decide)).trans ub.results⟩
  have vA : (v.comap QueriedProduct.bank).regs PrunedQuery.arrayA = _ :=
    (hv.regs_eq (by decide)).trans uA
  have vB : (v.comap QueriedProduct.bank).regs PrunedQuery.arrayB = _ :=
    (hv.regs_eq (by decide)).trans uB
  obtain ⟨y, hy, ym, yc, yi, yt, yV, yK, yA, yB⟩ :=
    exec_restoreBoxArguments v vp vb vA vB hfit
  have he : ExecWithin w tileArguments x y 44 := hu.seq (hv.seq hy)
  refine ⟨y, he, hp.of_frame (by intro i hi; exact he.regs_eq (by decide +revert)),
    ?_, ym.trans (vm.trans um), ?_, yc, yi, yt, yV, yK, yA, yB, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(he.regs_eq (by decide)).trans hb.threshold,
      (he.regs_eq (by decide)).trans hb.directory, (he.regs_eq (by decide)).trans hb.records,
      (he.regs_eq (by decide)).trans hb.values, (he.regs_eq (by decide)).trans hb.count,
      (he.regs_eq (by decide)).trans hb.results⟩
  · exact (hy.regs_eq (by decide)).trans ((hv.regs_eq (by decide)).trans ui)
  · exact (hy.regs_eq (by decide)).trans vn
  · have hs := (hy.regs_eq (by decide)).trans vs
    simpa only [Data.comap_regs, Nat.add_assoc, Nat.add_sub_of_le hab] using hs
  · exact (hy.regs_eq (by decide)).trans vo
  · exact (hy.regs_eq (by decide)).trans vd
  · exact (hy.regs_eq (by decide)).trans vl

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
