/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

/-!
# Computing each tile's actual kernel arguments

## Main results

* `QueriedProduct.exec_tileArguments`: load real group endpoints, divide the tile index,
  compute shared catalogue/query/output pointers and populate the existing native kernel ABI.

The span values in this internal interface describe the actual saved offset words. The full
caller establishes their bounds from its executed counting/prefix/scatter passes.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

set_option maxRecDepth 4096 in
-- The fixed 160-register footprint check simplifies a 32-member persistent register set.
/-- Actual tile-index arithmetic and kernel-argument setup cost twenty-one instructions.
Only the two real offset words are read. Every unsigned arithmetic fit follows from the
original allocation bound and the computed span bounds. -/
public theorem exec_tileArguments {w L m N Q t a b : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hx : x.regs index = t) (ht : t < numBands L m N ^ 2)
    (ha : x.mem (offsetBase L m N Q + t) = a)
    (hb : x.mem (offsetBase L m N Q + t + 1) = b) (hab : a ≤ b) (hbQ : b ≤ Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w tileArguments x y 21 ∧ Parameters L m N Q y ∧ y.mem = x.mem ∧
      y.regs index = t ∧ y.regs epoch = x.regs epoch ∧
      (y.comap bank).regs PrunedQuery.inputDepth = L ∧
      (y.comap bank).regs PrunedQuery.arrayA =
        BandPreparation.catalogueBase L m N + t / numBands L m N * 10 ^ L ∧
      (y.comap bank).regs PrunedQuery.arrayB =
        BandPreparation.catalogueBase L m N +
          (numBands L m N + t % numBands L m N) * 10 ^ L ∧
      (y.comap bank).regs PrunedQuery.queries = codeBase L m N Q + a ∧
      (y.comap bank).regs PrunedQuery.queryCount = b - a ∧
      (y.comap bank).regs PrunedQuery.output = groupedBase L m N Q + a ∧
      (y.comap bank).regs PrunedQuery.scratch = scratchBase L m N Q ∧
      (y.comap bank).regs PrunedQuery.epoch = x.regs epoch := by
  let B := numBands L m N
  let H := 10 ^ L
  let C := BandPreparation.catalogueBase L m N
  have hB : 0 < B := by dsimp [B] at *; nlinarith only [ht, Nat.zero_le t]
  have hH : 1 ≤ H := Nat.one_le_pow L _ (by decide)
  have hr : t / B < B := (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [B, pow_two] using ht)
  have hc : t % B < B := Nat.mod_lt t hB
  have hrH : t / B * H ≤ B * H := Nat.mul_le_mul_right H hr.le
  have hcH : (t % B + B) * H ≤ 2 * B * H := Nat.mul_le_mul_right H (by omega)
  have horder : C + 2 * B * H ≤ memoryEnd L m N Q := by
    have h := (producers_le_snapshot L m N Q).1
    have h' := (transfer_bounds L m N Q).2.1
    dsimp only [C, B, H, BandPreparation.memoryEnd] at *
    omega
  have hcodes : codeBase L m N Q + Q ≤ memoryEnd L m N Q := by
    have h10 := Nat.zero_le H
    unfold memoryEnd stampBase scratchBase outputBase groupedBase originalBase
    omega
  have hgroups : groupedBase L m N Q + Q ≤ memoryEnd L m N Q := by
    unfold memoryEnd stampBase scratchBase outputBase
    have h10 := Nat.zero_le (10 ^ L)
    omega
  have htiles : offsetBase L m N Q + B ^ 2 + 1 ≤ memoryEnd L m N Q := by
    dsimp only [B]
    unfold codeBase at hcodes
    omega
  have foffset : Fits w (offsetBase L m N Q + t) := allocated_fits hfit (by
    dsimp only [B] at *
    omega)
  have fnext : Fits w (offsetBase L m N Q + t + 1) := allocated_fits hfit (by
    dsimp only [B] at *
    omega)
  have frow : Fits w (t / B) := allocated_fits hfit (by nlinarith only [hr, hH, horder])
  have fcol : Fits w (t % B) := allocated_fits hfit (by nlinarith only [hc, hH, horder])
  have frowH : Fits w (t / B * H) := allocated_fits hfit (by nlinarith only [hrH, horder])
  have fleft : Fits w (t / B * H + C) := allocated_fits hfit (by nlinarith only [hrH, horder])
  have fcb : Fits w (t % B + B) := allocated_fits hfit (by
    nlinarith only [hcH, hH, horder, Nat.zero_le (t % B + B)])
  have fcbH : Fits w ((t % B + B) * H) := allocated_fits hfit (by omega)
  have fright : Fits w ((t % B + B) * H + C) := allocated_fits hfit (by omega)
  have fq : Fits w (codeBase L m N Q + a) := allocated_fits hfit (by omega)
  have fo : Fits w (groupedBase L m N Q + a) := allocated_fits hfit (by omega)
  have fn : Fits w (b - a) := allocated_fits hfit (by omega)
  let y := (((((((((((((((((((((x.set address (offsetBase L m N Q + t)).set first a).set
    address (offsetBase L m N Q + t + 1)).set stop b).set rowBand (t / B)).set colBand
    (t % B)).set leftPointer (t / B * H)).set leftPointer (t / B * H + C)).set
    rightPointer (t % B + B)).set rightPointer ((t % B + B) * H)).set rightPointer
    ((t % B + B) * H + C)).set queryPointer (codeBase L m N Q + a)).set answerPointer
    (groupedBase L m N Q + a)).set (bank PrunedQuery.inputDepth) L).set
    (bank PrunedQuery.arrayA) (t / B * H + C)).set (bank PrunedQuery.arrayB)
    ((t % B + B) * H + C)).set (bank PrunedQuery.queries) (codeBase L m N Q + a)).set
    (bank PrunedQuery.queryCount) (b - a)).set (bank PrunedQuery.output)
    (groupedBase L m N Q + a)).set (bank PrunedQuery.scratch) (scratchBase L m N Q)).set
    (bank PrunedQuery.epoch) (x.regs epoch))
  have he : ExecWithin w tileArguments x y 21 := by
    ram_eval [tileArguments, y, hp.offsets, hp.one, hp.bands, hp.leaves, hp.catalogue,
      hp.codes, hp.grouped, hp.depth, hp.scratch, hx, ha, hb, foffset, fnext, frow, fcol,
      frowH, fleft, fcb, fcbH, fright, fq, fo, fn, B, H, C, bank, Fin.val_ofNat,
      PrunedQuery.inputDepth, PrunedQuery.arrayA, PrunedQuery.arrayB, PrunedQuery.queries,
      PrunedQuery.queryCount, PrunedQuery.output, PrunedQuery.scratch, PrunedQuery.epoch,
      address, offsets, index, first, stop, one, rowBand, colBand, bands, leftPointer,
      rightPointer, leaves, catalogue, queryPointer, answerPointer, codes, grouped, depth,
      scratch, epoch, Fin.mk.injEq]
  have yp : Parameters L m N Q y := hp.of_frame (by
    intro i hi
    apply he.regs_eq
    have h : ∀ i ∈ parameterRegisters, tileArguments.Preserves i := by decide
    exact h i hi)
  refine ⟨y, he, yp, rfl, ?_⟩
  simp +decide [y, Data.comap_regs, hx, B, H, C, bank,
    PrunedQuery.inputDepth, PrunedQuery.arrayA, PrunedQuery.arrayB, PrunedQuery.queries,
    PrunedQuery.queryCount, PrunedQuery.output, PrunedQuery.scratch, PrunedQuery.epoch,
    address, first, stop, rowBand, colBand, leftPointer, rightPointer, queryPointer,
    answerPointer, index, epoch, Nat.add_comm]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
