/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Layout
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup

/-!
# Thin-regime layout envelopes for queried products

In the source regime `D m ^ 18 ≤ N`, the queried product's protected-buffer layout
(`QueriedProduct.wordBudget`, `QueriedProduct.memoryEnd`) has polynomial magnitude, word-budget
and memory-end envelopes at every level `m ≤ L ≤ 21 * m`.
The queried product (level `19 * m`) and the routed box product (level `21 * m`) both take their
logarithmic admission widths from this one bound.

## Main results

* `QueriedProduct.thin_envelopes_of_le`: in the source regime `D m ^ 18 ≤ N`, at every level
  `m ≤ L ≤ 21 * m`, polynomial magnitude, word-budget and memory-end envelopes.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- **Thin-regime envelopes at any level up to `21 * m`.** In the source regime
`D m ^ 18 ≤ N`, at every level `L` with `m ≤ L ≤ 21 * m`, the layout's magnitude, word budget
and memory end are bounded by explicit polynomials in `N + Q + A + 2`. The deliberately loose
integer constants leave a uniform logarithmic-width margin. -/
public theorem thin_envelopes_of_le (L m N Q A : ℕ) (hm : m ≤ L) (hL21 : L ≤ 21 * m)
    (hN : D m ^ 18 ≤ N) :
    magnitudeBound L A + wordBudget L m N Q + 1 ≤ 2 ^ 40 * (N + Q + A + 2) ^ 10 ∧
      memoryEnd L m N Q ≤ 128 * (N + Q + A + 2) ^ 4 := by
  let S := N + Q + A + 2
  let Z := S ^ 2
  have hs : 2 ≤ S := by dsimp only [S]; omega
  have hz : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hsz : S ≤ Z := Nat.le_self_pow (by decide) _
  have hNN : N ≤ S := by dsimp only [S]; omega
  have hN0 : N ≤ Z := hNN.trans hsz
  have hQ0 : Q ≤ Z := (show Q ≤ S by dsimp only [S]; omega).trans hsz
  have hA0 : A ≤ Z := (show A ≤ S by dsimp only [S]; omega).trans hsz
  have hp : 10 ^ L ≤ N ^ 2 := by
    calc 10 ^ L ≤ 10 ^ (21 * m) := Nat.pow_le_pow_right (by decide) hL21
      _ = (10 ^ 21) ^ m := by rw [pow_mul]
      _ ≤ (4 ^ 36) ^ m := Nat.pow_le_pow_left (by decide) m
      _ = (D m ^ 18) ^ 2 := by
        simp only [D, ← pow_mul]
        congr 1
        omega
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h10 : 10 ^ L ≤ Z := hp.trans (Nat.pow_le_pow_left hNN 2)
  have h2 : 2 ^ L ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 10) _).trans h10
  have h7 : 7 ^ L ≤ Z := (Nat.pow_le_pow_left (by decide : 7 ≤ 10) _).trans h10
  have hL : L ≤ Z := (Nat.lt_pow_self (by decide : 1 < 10)).le.trans h10
  have hD : D m ≤ Z := ((Nat.le_self_pow (by decide : 18 ≠ 0) _).trans hN).trans hN0
  have hbandpos : 0 < bandSize L m := Nat.mul_pos (K0_pos hm) (N0_pos _ _)
  have hbands : numBands L m N ≤ N := by
    apply Nat.le_of_lt_succ
    change (N + bandSize L m - 1) / bandSize L m < N + 1
    apply (Nat.div_lt_iff_lt_mul hbandpos).mpr
    have hmul := Nat.le_mul_of_pos_right N hbandpos
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hB : numBands L m N ≤ Z := hbands.trans hN0
  have hall : PrunedQuery.epochAllowance L ≤ 2 * Z := by
    unfold PrunedQuery.epochAllowance
    omega
  let bi := 4 + 2 * (Z * Z)
  let bc := (bi + (2 + Z + Z) + Z) + bi + Z + Z
  let be := bc + 2 * Z * Z
  let we := 6 + 4 * Z + 2 * Z + 3 * Z ^ 2
  let ii := 5 + 2 * (Z * Z) + 2 * Z
  let ss := be + we + ii
  let oo := ss + ii
  let cc := oo + Z ^ 2 + 1
  let ou := cc + Z + Z + Z
  let ff := ou + Z
  let ee := ff + 4 * (Z + 1) + 2 * (Z + 1) * Z + Z
  let ep := Z ^ 2 * (1 + 2 * Z)
  have hbc : BandPreparation.catalogueBase L m N ≤ bc := by
    dsimp only [bc, bi]
    simp only [BandPreparation.catalogueBase, BandPreparation.tableBase,
      BandPreparation.inverseBase, BandPreparation.snapshotBase, BandPreparation.inputEnd,
      Encoding.scratchBase, Encoding.outputBase]
    gcongr
  have hbe : BandPreparation.memoryEnd L m N ≤ be := by
    dsimp only [be]
    unfold BandPreparation.memoryEnd
    gcongr
  have hwe : Wanted.memoryLimit L m N Q ≤ we := by
    dsimp only [we]
    rw [Wanted.memoryLimit_eq]
    gcongr
  have hii : inputEnd m N Q ≤ ii := by dsimp only [ii, inputEnd]; gcongr
  have hss : snapshotBase L m N Q ≤ ss := by
    dsimp only [ss, snapshotBase]
    gcongr
  have hoo : offsetBase L m N Q ≤ oo := by
    dsimp only [oo, offsetBase]
    gcongr
  have hcc : codeBase L m N Q ≤ cc := by
    dsimp only [cc, codeBase]
    gcongr
  have hou : outputBase L m N Q ≤ ou := by
    dsimp only [ou, outputBase, groupedBase, originalBase]
    gcongr
  have hff : scratchBase L m N Q ≤ ff := by
    dsimp only [ff, scratchBase]
    gcongr
  have hee : memoryEnd L m N Q ≤ ee := by
    dsimp only [ee, memoryEnd, stampBase]
    gcongr
  have hep : epochBound L m N ≤ ep := by
    dsimp only [ep, epochBound]
    gcongr
  let bb := 256 * (Z + Z + Z * Z + Z + Z + 2 * Z * Z + 1)
  let tab := Z * 2 + 5 + Z
  let rb := 64 * (Z + Z + tab + Z ^ 2 + Z + Z + 1)
  let wb := 256 * (bb + rb + we + Z + Z + Z + Z ^ 2 + Z + Z + 16)
  let kb := (256 * (Z + 1) * Z + 32 * Z + 512) +
    ((8 * ff + 64 * (Z + 1) * Z + be + be + 2 * Z + (ep + 1) + 2 * Z + 128) +
      4 * (cc + ou + Z + 1))
  let ab := 1024 * (bb + wb + kb + ee + ii + Z + Z + Z + 16)
  let mg := Z * Z + Z * Z + Z * ((Z * Z) * (Z * Z)) + Z
  have hbb : BandPreparation.wordBudget L m N ≤ bb := by
    dsimp only [bb, BandPreparation.wordBudget]
    gcongr
  have htab : Wanted.tableAddress L Q ≤ tab := by
    dsimp only [tab, Wanted.tableAddress, Wanted.inputLimit]
    gcongr
  have hrb : Wanted.routeBudget L m N (Wanted.tableAddress L Q) ≤ rb := by
    dsimp only [rb, Wanted.routeBudget]
    gcongr
  have hwb : Wanted.wordBudget L m N Q ≤ wb := by
    dsimp only [wb, Wanted.wordBudget]
    gcongr
  have hkb : PrunedQuery.kernelBudget L (scratchBase L m N Q)
      (BandPreparation.memoryEnd L m N) (BandPreparation.memoryEnd L m N)
      (codeBase L m N Q) (outputBase L m N Q) Q (epochBound L m N) ≤ kb := by
    dsimp only [kb, PrunedQuery.kernelBudget, PrunedQuery.addressBound,
      PrunedQuery.evaluationBudget, PrunedQuery.nodeBudget]
    gcongr
  have hab : wordBudget L m N Q ≤ ab := by
    dsimp only [ab, wordBudget]
    gcongr
  have hmg : magnitudeBound L A ≤ mg := by
    dsimp only [mg, magnitudeBound, PrunedQuery.magnitudeBound]
    gcongr
  have h0 : 1 ≤ Z ^ 5 := Nat.one_le_pow _ _ hz
  have h1 : Z ≤ Z ^ 5 := Nat.le_self_pow (by decide) _
  have h2' : Z ^ 2 ≤ Z ^ 5 := Nat.pow_le_pow_right hz (by decide)
  have h3 : Z ^ 3 ≤ Z ^ 5 := Nat.pow_le_pow_right hz (by decide)
  have htotal : mg + ab + 1 ≤ 2 ^ 40 * Z ^ 5 := by
    dsimp only [mg, ab, wb, bb, rb, tab, kb, ee, ff, ou, cc, oo, ss, be, bc, bi, we, ii, ep]
    nlinarith only [h0, h1, h2', h3]
  have hmem : ee ≤ 128 * Z ^ 2 := by
    have hz2 := Nat.le_self_pow (by decide : 2 ≠ 0) Z
    have h02 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hz
    dsimp only [ee, ff, ou, cc, oo, ss, be, bc, bi, we, ii]
    nlinarith only [hz2, h02]
  constructor
  · have h := (Nat.add_le_add_right (Nat.add_le_add hmg hab) 1).trans htotal
    simpa only [Z, S, ← pow_mul, Nat.reduceMul] using h
  · have h := hee.trans hmem
    simpa only [Z, S, ← pow_mul, Nat.reduceMul] using h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
