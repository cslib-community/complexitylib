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

-- Name the fifty-update state once; separating execution from admission keeps each proof
-- within the default heartbeat limit without changing the actual header code.
private def layoutState (x : Data 160) (L m N Q : ℕ) : Data 160 :=
  ((((((((((((((((((((((((((((((((((((((((((((((((((x.set Reg.depth (L)).set Reg.inner (m)).set
      Reg.rows (N)).set Reg.address (4)).set Reg.queryCount (Q)).set Reg.columns (D m)).set
      Reg.masks (2 ^ L)).set Reg.cells (7 ^ L)).set Reg.leaves (10 ^ L)).set Reg.bands
      (numBands L m N)).set Reg.catalogue (BandPreparation.catalogueBase L m N)).set Reg.zero
      (0)).set Reg.one (1)).set Reg.two (2)).set Reg.three (3)).set Reg.four (4)).set Reg.five
      (5)).set Reg.six (6)).set Reg.tiles ((numBands L m N) * (numBands L m N))).set
      Reg.matrixWords ((N) * (D m))).set Reg.matrixWords (((N) * (D m)) * (2))).set Reg.queryOffset
      ((((N) * (D m)) * (2)) + (5))).set Reg.inputSize ((Q) * (2))).set Reg.inputSize (((Q) * (2)) +
      ((((N) * (D m)) * (2)) + (5)))).set Reg.bandEnd ((numBands L m N) * (10 ^ L))).set
      Reg.bandEnd (((numBands L m N) * (10 ^ L)) * (2))).set Reg.bandEnd ((((numBands L m N) *
      (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m N))).set Reg.wantedEnd ((Q) * (4))).set
      Reg.wantedEnd (((Q) * (4)) + (6))).set Reg.temporary ((2 ^ L) * (2))).set Reg.wantedEnd
      ((((Q) * (4)) + (6)) + ((2 ^ L) * (2)))).set Reg.temporary (((numBands L m N) *
      (numBands L m N)) * (3))).set Reg.wantedEnd (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))).set Reg.snapshot (((((numBands L m N) *
      (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) +
      ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) * (3))))).set Reg.snapshot
      ((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m N)) +
      (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) * (3)))) +
      (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5))))).set Reg.offsets (((((((numBands L m N) *
      (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) +
      ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) +
      ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5))))).set
      Reg.codes ((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) *
      (numBands L m N)))).set Reg.codes (((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1))).set Reg.originals ((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q))).set Reg.grouped (((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q))).set Reg.output ((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q))).set Reg.scratch (((((((((((((numBands L m N) * (10 ^ L)) *
      (2)) + (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q))).set Reg.temporary ((L) + (1))).set Reg.temporary
      (((L) + (1)) * (4))).set Reg.stamps ((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4)))).set Reg.temporary ((L) +
      (1))).set Reg.temporary (((L) + (1)) * (10 ^ L))).set Reg.temporary ((((L) + (1)) *
      (10 ^ L)) * (2))).set Reg.stamps (((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2)))).set Reg.memoryLimit ((((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2))) + (10 ^ L)))

private theorem exec_layout_raw {w L m N Q : ℕ} (x : Data 160)
    (hp : BandPreparation.BandParameters L m N (x.comap bank)) (hQ : x.mem 4 = Q)
    (hf0 : Fits w (4))
    (hf1 : Fits w (0))
    (hf2 : Fits w (1))
    (hf3 : Fits w (2))
    (hf4 : Fits w (3))
    (hf5 : Fits w (5))
    (hf6 : Fits w (6))
    (hf7 : Fits w ((numBands L m N) * (numBands L m N)))
    (hf8 : Fits w ((N) * (D m)))
    (hf9 : Fits w (((N) * (D m)) * (2)))
    (hf10 : Fits w ((((N) * (D m)) * (2)) + (5)))
    (hf11 : Fits w ((Q) * (2)))
    (hf12 : Fits w (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5))))
    (hf13 : Fits w ((numBands L m N) * (10 ^ L)))
    (hf14 : Fits w (((numBands L m N) * (10 ^ L)) * (2)))
    (hf15 : Fits w ((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m
      N)))
    (hf16 : Fits w ((Q) * (4)))
    (hf17 : Fits w (((Q) * (4)) + (6)))
    (hf18 : Fits w ((2 ^ L) * (2)))
    (hf19 : Fits w ((((Q) * (4)) + (6)) + ((2 ^ L) * (2))))
    (hf20 : Fits w (((numBands L m N) * (numBands L m N)) * (3)))
    (hf21 : Fits w (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m
      N)) * (3))))
    (hf22 : Fits w (((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m
      N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))))
    (hf23 : Fits w ((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L m
      N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))))
    (hf24 : Fits w (((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L
      m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))))
    (hf25 : Fits w ((((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase L
      m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N)) *
      (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + ((numBands L m N) * (numBands L m N))))
    (hf26 : Fits w (((((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase
      L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N))
      * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + ((numBands L m N) * (numBands L m N))) + (1)))
    (hf27 : Fits w ((((((((((numBands L m N) * (10 ^ L)) * (2)) + (BandPreparation.catalogueBase
      L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) + (((numBands L m N) * (numBands L m N))
      * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + (((Q) * (2)) + ((((N) * (D m)) *
      (2)) + (5)))) + ((numBands L m N) * (numBands L m N))) + (1)) + (Q)))
    (hf28 : Fits w (((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)))
    (hf29 : Fits w ((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)))
    (hf30 : Fits w (((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)))
    (hf31 : Fits w ((L) + (1)))
    (hf32 : Fits w (((L) + (1)) * (4)))
    (hf33 : Fits w ((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))))
    (hf34 : Fits w (((L) + (1)) * (10 ^ L)))
    (hf35 : Fits w ((((L) + (1)) * (10 ^ L)) * (2)))
    (hf36 : Fits w (((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2))))
    (hf37 : Fits w ((((((((((((((((numBands L m N) * (10 ^ L)) * (2)) +
      (BandPreparation.catalogueBase L m N)) + (((((Q) * (4)) + (6)) + ((2 ^ L) * (2))) +
      (((numBands L m N) * (numBands L m N)) * (3)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) +
      (5)))) + (((Q) * (2)) + ((((N) * (D m)) * (2)) + (5)))) + ((numBands L m N) * (numBands L m
      N))) + (1)) + (Q)) + (Q)) + (Q)) + (Q)) + (((L) + (1)) * (4))) + ((((L) + (1)) * (10 ^ L)) *
      (2))) + (10 ^ L))) :
    ExecWithin w layout x (layoutState x L m N Q) 50 := by
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
  ram_eval [layout, layoutState, hQ, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11,
    hf12,
      hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf23, hf24, hf25, hf26, hf27,
      hf28, hf29, hf30, hf31, hf32, hf33, hf34, hf35, hf36, hf37, Reg.depth, Reg.inner, Reg.rows,
      Reg.address, Reg.queryCount, Reg.columns, Reg.masks, Reg.cells, Reg.leaves, Reg.bands,
      Reg.catalogue, Reg.zero, Reg.one, Reg.two, Reg.three, Reg.four, Reg.five, Reg.six, Reg.tiles,
      Reg.matrixWords, Reg.queryOffset, Reg.inputSize, Reg.bandEnd, Reg.wantedEnd, Reg.temporary,
      Reg.snapshot, Reg.offsets, Reg.codes, Reg.originals, Reg.grouped, Reg.output, Reg.scratch,
      Reg.stamps, Reg.memoryLimit, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]

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
  let y := layoutState x L m N Q
  have he : ExecWithin w layout x y 50 :=
    exec_layout_raw x hp hQ hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hf10 hf11 hf12 hf13 hf14 hf15
      hf16 hf17 hf18 hf19 hf20 hf21 hf22 hf23 hf24 hf25 hf26 hf27 hf28 hf29 hf30 hf31 hf32 hf33
      hf34 hf35 hf36 hf37
  refine ⟨y, he, ?_, rfl⟩
  constructor <;>
    simp +decide only [y, layoutState, Data.set_regs, Function.update_apply, Reg.depth, Reg.inner,
      Reg.rows, Reg.address, Reg.queryCount, Reg.columns, Reg.masks, Reg.cells, Reg.leaves,
      Reg.bands, Reg.catalogue, Reg.zero, Reg.one, Reg.two, Reg.three, Reg.four, Reg.five, Reg.six,
      Reg.tiles, Reg.matrixWords, Reg.queryOffset, Reg.inputSize, Reg.bandEnd, Reg.wantedEnd,
      Reg.temporary, Reg.snapshot, Reg.offsets, Reg.codes, Reg.originals, Reg.grouped, Reg.output,
      Reg.scratch, Reg.stamps, Reg.memoryLimit, ↓reduceIte] <;>
    (try simp only [inputEnd, queryInputBase, snapshotBase, offsetBase, codeBase,
      originalBase, groupedBase, outputBase, scratchBase, stampBase, memoryEnd,
      BandPreparation.memoryEnd, Wanted.memoryLimit_eq, pow_two]) <;> ring

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
