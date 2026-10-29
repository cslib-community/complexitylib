/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Memory
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup

/-!
# Charged protected-buffer calculation

## Main results

* `QueriedProduct.exec_layout`: calculate every persistent scalar from the actual producer
  header and original request count, with all intermediate fits derived from original inputs.

This is an internal execution API. It receives ordinary header equalities and a numerical
input bound, not a supplied layout or intermediate-state certificate.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

set_option maxHeartbeats 2000000 in
-- The straight-line proof symbolically checks fifty register updates and their fits.
/-- Actual native layout calculation, preserving all original memory. -/
public theorem exec_layout {w L m N Q : ℕ} (x : Data 160)
    (hp : BandPreparation.BandParameters L m N (x.comap bank)) (hQ : x.mem 4 = Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w layout x y 50 ∧ Parameters L m N Q y ∧ y.mem = x.mem := by
  have hl := caller_fits hfit
  have h2 : 2 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hsmall (v : ℕ) (hv : v ≤ 16 * (L + N + Q + memoryEnd L m N Q + 16)) :
      Fits w v := hl.of_le hv
  have hb0 : x.regs (bank BandPreparation.levels) = L := hp.fixed.levels
  have hb1 : x.regs (bank BandPreparation.inner) = m := hp.fixed.inner
  have hb2 : x.regs (bank BandPreparation.rows) = N := hp.fixed.rows
  have hb3 : x.regs (bank BandPreparation.columns) = D m := hp.columns
  have hb4 : x.regs (bank BandPreparation.masks) = 2 ^ L := hp.masks
  have hb5 : x.regs (bank BandPreparation.cells) = 7 ^ L := hp.cells
  have hb6 : x.regs (bank BandPreparation.leaves) = 10 ^ L := hp.leaves
  have hb7 : x.regs (bank BandPreparation.bands) = numBands L m N := hp.bands
  have hb8 : x.regs (bank BandPreparation.catalogue) = BandPreparation.catalogueBase L m N :=
      hp.catalogue
  have hf0 : Fits w (4) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf1 : Fits w (0) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf2 : Fits w (1) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf3 : Fits w (2) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf4 : Fits w (3) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf5 : Fits w (5) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf6 : Fits w (6) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf7 : Fits w ((numBands L m N) * (numBands L m N)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf8 : Fits w ((N) * (D m)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf9 : Fits w (((N) * (D m)) * (2)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf10 : Fits w ((((N) * (D m)) * (2)) + (5)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf11 : Fits w ((Q) * (2)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf12 : Fits w (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf13 : Fits w ((numBands L m N) * (10 ^ L)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf14 : Fits w (((numBands L m N) * (10 ^ L)) * (2)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf15 : Fits w ((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m
      N)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf16 : Fits w ((Q) * (4)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf17 : Fits w (((Q) * (4)) + (6)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf18 : Fits w ((2 ^ L) * (2)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf19 : Fits w ((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf20 : Fits w (((numBands L m N) * (numBands L m N)) * (3)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf21 : Fits w (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m
      N)) * (3))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf22 : Fits w (((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m
      N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf23 : Fits w ((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m
      N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf24 : Fits w (((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L
      m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf25 : Fits w ((((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L
      m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + ((numBands L m N) * (numBands L m N))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf26 : Fits w (((((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase
      L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N))
      * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + ((numBands L m N) * (numBands L m N))) + (1)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf27 : Fits w ((((((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase
      L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N))
      * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + ((numBands L m N) * (numBands L m N))) + (1)) + (Q)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf28 : Fits w (((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf29 : Fits w ((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf30 : Fits w (((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf31 : Fits w ((L) + (1)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf32 : Fits w (((L) + (1)) * (4)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf33 : Fits w ((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf34 : Fits w (((L) + (1)) * (10 ^ L)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf35 : Fits w ((((L) + (1)) * (10 ^ L)) * (2)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf36 : Fits w (((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2))) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  have hf37 : Fits w ((((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2))) + (10 ^ L)) := hsmall _ (by
    simp only [memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
      originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq]
    ring_nf
    omega)
  let y := ((((((((((((((((((((((((((((((((((((((((((((((((((x.set depth (L)).set inner (m)).set
      rows (N)).set address (4)).set queryCount (Q)).set columns (D m)).set masks (2 ^ L)).set
      cells (7 ^ L)).set leaves (10 ^ L)).set bands (numBands L m N)).set catalogue
      (BandPreparation.catalogueBase L m N)).set zero (0)).set one (1)).set two (2)).set three
      (3)).set four (4)).set five (5)).set six (6)).set tiles ((numBands L m N) * (numBands L m
      N))).set matrixWords ((N) * (D m))).set matrixWords (((N) * (D m)) * (2))).set queryOffset
      ((((N) * (D m)) * (2)) + (5))).set inputSize ((Q) * (2))).set inputSize (((Q) * (2)) +
      ((((N) * (D m)) * (2)) + (5)))).set bandEnd ((numBands L m N) * (10 ^ L))).set bandEnd
      (((numBands L m N) * (10 ^ L)) * (2))).set bandEnd ((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N))).set wantedEnd ((Q) * (4))).set wantedEnd (((Q) *
      (4)) + (6))).set temporary ((2 ^ L) * (2))).set wantedEnd ((((Q) * (4)) + (6)) + ((2 ^ L) *
      (2)))).set temporary (((numBands L m N) * (numBands L m N)) * (3))).set wantedEnd (((((Q) *
      (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) * (3)))).set
      snapshot (((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m N)) +
      (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3))))).set snapshot ((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5))))).set offsets (((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5))))).set codes ((((((((numBands L m N) *
      (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L)
      * (2))) + (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) *
      (numBands L m N)))).set codes (((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1))).set originals ((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q))).set grouped (((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q))).set output ((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q))).set scratch (((((((((((((numBands L m N) * (10 ^ L)) *
      (2)) + (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q))).set temporary ((L) + (1))).set temporary (((L) +
      (1)) * (4))).set stamps ((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4)))).set temporary ((L) +
      (1))).set temporary (((L) + (1)) * (10 ^ L))).set temporary ((((L) + (1)) * (10 ^ L)) *
      (2))).set stamps (((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2)))).set memoryLimit ((((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2))) + (10 ^ L)))
  have he : ExecWithin w layout x y 50 := by
    ram_eval [layout, y, hQ, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12,
      hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf23, hf24, hf25, hf26, hf27,
      hf28, hf29, hf30, hf31, hf32, hf33, hf34, hf35, hf36, hf37, depth, inner, rows, address,
      queryCount, columns, masks, cells, leaves, bands, catalogue, zero, one, two, three, four,
      five, six, tiles, matrixWords, queryOffset, inputSize, bandEnd, wantedEnd, temporary,
      snapshot, offsets, codes, originals, grouped, output, scratch, stamps, memoryLimit, hb0,
      hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]
  refine ⟨y, he, ?_, rfl⟩
  constructor <;>
    simp +decide only [y, Data.set_regs, Function.update_apply, depth, inner, rows, address,
      queryCount, columns, masks, cells, leaves, bands, catalogue, zero, one, two, three, four,
      five, six, tiles, matrixWords, queryOffset, inputSize, bandEnd, wantedEnd, temporary,
      snapshot, offsets, codes, originals, grouped, output, scratch, stamps, memoryLimit,
      ↓reduceIte] <;>
    (try simp only [inputEnd, queryInputBase, snapshotBase, offsetBase, codeBase,
      originalBase, groupedBase, outputBase, scratchBase, stampBase, memoryEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq, pow_two]) <;> ring

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
