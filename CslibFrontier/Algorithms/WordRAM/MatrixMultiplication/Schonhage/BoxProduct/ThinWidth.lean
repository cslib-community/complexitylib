/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Original-data logarithmic width for routed box products

At level `21*m`, the thin-dimension condition bounds every actual address and signed
magnitude by a polynomial in original dimensions, occurrence count and entry bound.
The threshold may be any original integer at most `m`. Neither intermediate-state
fits nor a space/runtime certificate is assumed.

## Main results

* `BoxProduct.thin_envelopes`: polynomial magnitude, address and allocation envelopes.
* `BoxProduct.thin_admissionWidth_le`: a fixed logarithmic width suffices.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
/-- The source regime controls every original power, computed band count and address term.
The deliberately loose integer constants leave a uniform logarithmic-width margin. -/
private theorem old_envelopes_twentyone (m N Q A : ℕ) (hN : D m ^ 18 ≤ N) :
    magnitudeBound (21 * m) A + wordBudget (21 * m) m N Q + 1 ≤
        2 ^ 40 * (N + Q + A + 2) ^ 10 ∧
      memoryEnd (21 * m) m N Q ≤ 128 * (N + Q + A + 2) ^ 4 := by
  let S := N + Q + A + 2
  let Z := S ^ 2
  have hs : 2 ≤ S := by dsimp only [S]; omega
  have hz : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hsz : S ≤ Z := Nat.le_self_pow (by decide) _
  have hNN : N ≤ S := by dsimp only [S]; omega
  have hN0 : N ≤ Z := hNN.trans hsz
  have hQ0 : Q ≤ Z := (show Q ≤ S by dsimp only [S]; omega).trans hsz
  have hA0 : A ≤ Z := (show A ≤ S by dsimp only [S]; omega).trans hsz
  have hp : 10 ^ (21 * m) ≤ N ^ 2 := by
    calc 10 ^ (21 * m) = (10 ^ 21) ^ m := by rw [pow_mul]
      _ ≤ (4 ^ 36) ^ m := Nat.pow_le_pow_left (by decide) m
      _ = (D m ^ 18) ^ 2 := by
        simp only [D, ← pow_mul]
        congr 1
        omega
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h10 : 10 ^ (21 * m) ≤ Z := hp.trans (Nat.pow_le_pow_left hNN 2)
  have h2 : 2 ^ (21 * m) ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 10) _).trans h10
  have h7 : 7 ^ (21 * m) ≤ Z := (Nat.pow_le_pow_left (by decide : 7 ≤ 10) _).trans h10
  have hL : 21 * m ≤ Z := (Nat.lt_pow_self (by decide : 1 < 10)).le.trans h10
  have hD : D m ≤ Z := ((Nat.le_self_pow (by decide : 18 ≠ 0) _).trans hN).trans hN0
  have hm : m ≤ 21 * m := by omega
  have hbandpos : 0 < bandSize (21 * m) m := Nat.mul_pos (K0_pos hm) (N0_pos _ _)
  have hbands : numBands (21 * m) m N ≤ N := by
    apply Nat.le_of_lt_succ
    change (N + bandSize (21 * m) m - 1) / bandSize (21 * m) m < N + 1
    apply (Nat.div_lt_iff_lt_mul hbandpos).mpr
    have hmul := Nat.le_mul_of_pos_right N hbandpos
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hB : numBands (21 * m) m N ≤ Z := hbands.trans hN0
  have hall : PrunedQuery.epochAllowance (21 * m) ≤ 2 * Z := by
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
  have hbc : BandPreparation.catalogueBase (21 * m) m N ≤ bc := by
    dsimp only [bc, bi]
    simp only [BandPreparation.catalogueBase, BandPreparation.tableBase,
      BandPreparation.inverseBase, BandPreparation.snapshotBase, BandPreparation.inputEnd,
      Encoding.scratchBase, Encoding.outputBase]
    gcongr
  have hbe : BandPreparation.memoryEnd (21 * m) m N ≤ be := by
    dsimp only [be]
    unfold BandPreparation.memoryEnd
    gcongr
  have hwe : Wanted.memoryLimit (21 * m) m N Q ≤ we := by
    dsimp only [we]
    rw [Wanted.memoryLimit_eq]
    gcongr
  have hii : inputEnd m N Q ≤ ii := by dsimp only [ii, inputEnd]; gcongr
  have hss : snapshotBase (21 * m) m N Q ≤ ss := by
    dsimp only [ss, snapshotBase]
    gcongr
  have hoo : offsetBase (21 * m) m N Q ≤ oo := by
    dsimp only [oo, offsetBase]
    gcongr
  have hcc : codeBase (21 * m) m N Q ≤ cc := by
    dsimp only [cc, codeBase]
    gcongr
  have hou : outputBase (21 * m) m N Q ≤ ou := by
    dsimp only [ou, outputBase, groupedBase, originalBase]
    gcongr
  have hff : scratchBase (21 * m) m N Q ≤ ff := by
    dsimp only [ff, scratchBase]
    gcongr
  have hee : memoryEnd (21 * m) m N Q ≤ ee := by
    dsimp only [ee, memoryEnd, stampBase]
    gcongr
  have hep : epochBound (21 * m) m N ≤ ep := by
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
  have hbb : BandPreparation.wordBudget (21 * m) m N ≤ bb := by
    dsimp only [bb, BandPreparation.wordBudget]
    gcongr
  have htab : Wanted.tableAddress (21 * m) Q ≤ tab := by
    dsimp only [tab, Wanted.tableAddress, Wanted.inputLimit]
    gcongr
  have hrb : Wanted.routeBudget (21 * m) m N (Wanted.tableAddress (21 * m) Q) ≤ rb := by
    dsimp only [rb, Wanted.routeBudget]
    gcongr
  have hwb : Wanted.wordBudget (21 * m) m N Q ≤ wb := by
    dsimp only [wb, Wanted.wordBudget]
    gcongr
  have hkb : PrunedQuery.kernelBudget (21 * m) (scratchBase (21 * m) m N Q)
      (BandPreparation.memoryEnd (21 * m) m N) (BandPreparation.memoryEnd (21 * m) m N)
      (codeBase (21 * m) m N Q) (outputBase (21 * m) m N Q) Q (epochBound (21 * m) m N) ≤ kb := by
    dsimp only [kb, PrunedQuery.kernelBudget, PrunedQuery.addressBound,
      PrunedQuery.evaluationBudget, PrunedQuery.nodeBudget]
    gcongr
  have hab : wordBudget (21 * m) m N Q ≤ ab := by
    dsimp only [ab, wordBudget]
    gcongr
  have hmg : magnitudeBound (21 * m) A ≤ mg := by
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

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Polynomial magnitude/address envelopes at total depth21m. -/
public theorem thin_envelopes (m t N Q A : ℕ) (ht : t ≤ m) (hN : D m ^ 18 ≤ N) :
    magnitudeBound (21 * m) A + wordBudget (21 * m) m t N Q + 1 ≤
      2 ^ 60 * (N + Q + A + 2) ^ 12 ∧
    memoryEnd (21 * m) m t N Q ≤ 256 * (N + Q + A + 2) ^ 4 := by
  let S := N + Q + A + 2
  let Z := S ^ 2
  have hs : 2 ≤ S := by dsimp only [S]; omega
  have hz : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hsz : S ≤ Z := Nat.le_self_pow (by decide) _
  have hNN : N ≤ S := by dsimp only [S]; omega
  have hN0 : N ≤ Z := hNN.trans hsz
  have hQ0 : Q ≤ Z := (show Q ≤ S by dsimp only [S]; omega).trans hsz
  have hA0 : A ≤ Z := (show A ≤ S by dsimp only [S]; omega).trans hsz
  have hp : 10 ^ (21 * m) ≤ N ^ 2 := by
    calc 10 ^ (21 * m) = (10 ^ 21) ^ m := by rw [pow_mul]
      _ ≤ (4 ^ 36) ^ m := Nat.pow_le_pow_left (by decide) m
      _ = (D m ^ 18) ^ 2 := by
        simp only [D, ← pow_mul]
        congr 1
        omega
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h10 : 10 ^ (21 * m) ≤ Z := hp.trans (Nat.pow_le_pow_left hNN 2)
  have h7 : 7 ^ (21 * m) ≤ Z := (Nat.pow_le_pow_left (by decide : 7 ≤ 10) _).trans h10
  have hL : 21 * m ≤ Z := (Nat.lt_pow_self (by decide : 1 < 10)).le.trans h10
  have h0 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hz
  have h1 : Z ≤ Z ^ 2 := Nat.le_self_pow (by decide) _
  have h5 : Z ^ 5 ≤ Z ^ 6 := Nat.pow_le_pow_right hz (by decide)
  have h2 : Z ^ 2 ≤ Z ^ 6 := Nat.pow_le_pow_right hz (by decide)
  have hOld := QueriedProduct.old_envelopes_twentyone m N Q A hN
  have hOldTotal : QueriedProduct.magnitudeBound (21 * m) A +
      QueriedProduct.wordBudget (21 * m) m N Q + 1 ≤ 2 ^ 40 * Z ^ 5 := by
    simpa only [Z, S, ← pow_mul, Nat.reduceMul] using hOld.1
  have hOldEnd : QueriedProduct.memoryEnd (21 * m) m N Q ≤ 128 * Z ^ 2 := by
    simpa only [Z, S, ← pow_mul, Nat.reduceMul] using hOld.2
  have hSlot : (m - t + 1) * 10 ^ (21 * m) ≤ (Z + 1) * Z :=
    Nat.mul_le_mul (by omega) h10
  have hLC : (21 * m + 1) * 10 ^ (21 * m) ≤ (Z + 1) * Z :=
    Nat.mul_le_mul (by omega) h10
  have hK := Nat.count_le (BoxTable.Eligible (21 * m) (m - t))
    (n := (m - t + 1) * 10 ^ (21 * m))
  rw [BoxTable.count_eligible_eq_card_boxes] at hK
  have hDir : directoryBase (21 * m) m N Q ≤ 128 * Z ^ 2 := hOldEnd
  have hRec : recordBase (21 * m) m t N Q ≤ 128 * Z ^ 2 + (Z + 1) * Z :=
    Nat.add_le_add hDir hSlot
  have hVal : valueBase (21 * m) m t N Q ≤ 128 * Z ^ 2 + 4 * ((Z + 1) * Z) := by
    unfold valueBase
    nlinarith only [hRec, hK.trans hSlot]
  have hEnd : memoryEnd (21 * m) m t N Q ≤ 256 * Z ^ 2 := by
    unfold memoryEnd resultBase stackBase BoxQuery.stackCapacity
    nlinarith only [hVal, hK.trans hSlot, hLC, hQ0, h0, h1]
  have hBudget : wordBudget (21 * m) m t N Q ≤
      10000 * (QueriedProduct.wordBudget (21 * m) m N Q + 1024 * Z ^ 2) := by
    unfold wordBudget
    nlinarith only [hEnd, hDir, hRec, hVal, hSlot, hLC, hL, ht, hN0, hQ0, h0, h1]
  have hEnc : encodedBound (21 * m) A ≤ Z * Z := by
    unfold encodedBound
    exact Nat.mul_le_mul h7 hA0
  have h10twice : 10 ^ (2 * (21 * m)) ≤ Z * Z := by
    rw [show 2 * (21 * m) = 21 * m + 21 * m by omega, pow_add]
    exact Nat.mul_le_mul h10 h10
  have hMag : magnitudeBound (21 * m) A ≤
      QueriedProduct.magnitudeBound (21 * m) A + 2 * Z ^ 2 + Z ^ 6 := by
    have hBox : BoxQuery.magnitudeBound (21 * m) (encodedBound (21 * m) A)
        (encodedBound (21 * m) A) ≤ Z * Z + Z * Z +
          (Z * Z) * ((Z * Z) * (Z * Z)) := by
      exact Nat.add_le_add (Nat.add_le_add hEnc hEnc)
        (Nat.mul_le_mul h10twice (Nat.mul_le_mul hEnc hEnc))
    unfold magnitudeBound
    nlinarith only [hBox]
  constructor
  · have hTotal : magnitudeBound (21 * m) A + wordBudget (21 * m) m t N Q + 1 ≤
        2 ^ 60 * Z ^ 6 := by
      nlinarith only [hOldTotal, hMag, hBudget, h5, h2]
    simpa only [Z, S, ← pow_mul, Nat.reduceMul] using hTotal
  · simpa only [Z, S, ← pow_mul, Nat.reduceMul] using hEnd

/-- Original-data logarithmic width suffices in the `21*m` box-product regime. -/
public theorem thin_admissionWidth_le (m t N Q A : ℕ) (ht : t ≤ m)
    (hN : D m ^ 18 ≤ N) :
    admissionWidth (21 * m) m t N Q A ≤ 128 * Nat.clog 2 (N + Q + A + 2) := by
  let S := N + Q + A + 2
  have hs : 1 < S := by dsimp only [S]; omega
  have hl := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hs
  have hp := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) S
  have he := (thin_envelopes m t N Q A ht hN).1
  have hpow : magnitudeBound (21 * m) A + wordBudget (21 * m) m t N Q + 1 ≤
      2 ^ (60 + 12 * Nat.clog 2 S) := by
    calc _ ≤ 2 ^ 60 * S ^ 12 := he
      _ ≤ 2 ^ 60 * (2 ^ Nat.clog 2 S) ^ 12 := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left hp 12)
      _ = _ := by rw [pow_add, ← pow_mul, Nat.mul_comm (Nat.clog 2 S) 12]
  have hc := (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr hpow
  unfold admissionWidth
  dsimp only [S] at hc hl
  omega
end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
