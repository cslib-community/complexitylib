/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Thin

/-!
# Source-regime logarithmic width for actual queried products

## Main results

* `QueriedProduct.thin_envelopes`: original dimensions give polynomial magnitude/address
  envelopes and an explicit polynomial allocation bound.
* `QueriedProduct.thin_admissionWidth_le`: a positive constant times the logarithm of original
  dimension, request count and entry magnitude suffices in the source's thin regime.

These bounds concern the real native program and its actual allocation formulas. They assume
neither intermediate-state fits nor a polynomial-space certificate.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The source regime controls every original power, computed band count and address term.
The deliberately loose integer constants leave a uniform logarithmic-width margin. -/
public theorem thin_envelopes (m N Q A : ℕ) (hN : D m ^ 18 ≤ N) :
    magnitudeBound (19 * m) A + wordBudget (19 * m) m N Q + 1 ≤
        2 ^ 40 * (N + Q + A + 2) ^ 10 ∧
      memoryEnd (19 * m) m N Q ≤ 128 * (N + Q + A + 2) ^ 4 := by
  let S := N + Q + A + 2
  let Z := S ^ 2
  have hs : 2 ≤ S := by dsimp only [S]; omega
  have hz : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hsz : S ≤ Z := Nat.le_self_pow (by decide) _
  have hNN : N ≤ S := by dsimp only [S]; omega
  have hN0 : N ≤ Z := hNN.trans hsz
  have hQ0 : Q ≤ Z := (show Q ≤ S by dsimp only [S]; omega).trans hsz
  have hA0 : A ≤ Z := (show A ≤ S by dsimp only [S]; omega).trans hsz
  have hp : 10 ^ (19 * m) ≤ N ^ 2 := by
    calc 10 ^ (19 * m) = (10 ^ 19) ^ m := by rw [pow_mul]
      _ ≤ (4 ^ 36) ^ m := Nat.pow_le_pow_left (by decide) m
      _ = (D m ^ 18) ^ 2 := by
        simp only [D, ← pow_mul]
        congr 1
        omega
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h10 : 10 ^ (19 * m) ≤ Z := hp.trans (Nat.pow_le_pow_left hNN 2)
  have h2 : 2 ^ (19 * m) ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 10) _).trans h10
  have h7 : 7 ^ (19 * m) ≤ Z := (Nat.pow_le_pow_left (by decide : 7 ≤ 10) _).trans h10
  have hL : 19 * m ≤ Z := (Nat.lt_pow_self (by decide : 1 < 10)).le.trans h10
  have hD : D m ≤ Z := ((Nat.le_self_pow (by decide : 18 ≠ 0) _).trans hN).trans hN0
  have hm : m ≤ 19 * m := by omega
  have hbandpos : 0 < bandSize (19 * m) m := Nat.mul_pos (K0_pos hm) (N0_pos _ _)
  have hbands : numBands (19 * m) m N ≤ N := by
    apply Nat.le_of_lt_succ
    change (N + bandSize (19 * m) m - 1) / bandSize (19 * m) m < N + 1
    apply (Nat.div_lt_iff_lt_mul hbandpos).mpr
    have hmul := Nat.le_mul_of_pos_right N hbandpos
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hB : numBands (19 * m) m N ≤ Z := hbands.trans hN0
  have hall : PrunedQuery.epochAllowance (19 * m) ≤ 2 * Z := by
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
  have hbc : BandPreparation.catalogueBase (19 * m) m N ≤ bc := by
    dsimp only [bc, bi]
    simp only [BandPreparation.catalogueBase, BandPreparation.tableBase,
      BandPreparation.inverseBase, BandPreparation.snapshotBase, BandPreparation.inputEnd,
      Encoding.scratchBase, Encoding.outputBase]
    gcongr
  have hbe : BandPreparation.memoryEnd (19 * m) m N ≤ be := by
    dsimp only [be]
    unfold BandPreparation.memoryEnd
    gcongr
  have hwe : Wanted.memoryLimit (19 * m) m N Q ≤ we := by
    dsimp only [we]
    rw [Wanted.memoryLimit_eq]
    gcongr
  have hii : inputEnd m N Q ≤ ii := by dsimp only [ii, inputEnd]; gcongr
  have hss : snapshotBase (19 * m) m N Q ≤ ss := by
    dsimp only [ss, snapshotBase]
    gcongr
  have hoo : offsetBase (19 * m) m N Q ≤ oo := by
    dsimp only [oo, offsetBase]
    gcongr
  have hcc : codeBase (19 * m) m N Q ≤ cc := by
    dsimp only [cc, codeBase]
    gcongr
  have hou : outputBase (19 * m) m N Q ≤ ou := by
    dsimp only [ou, outputBase, groupedBase, originalBase]
    gcongr
  have hff : scratchBase (19 * m) m N Q ≤ ff := by
    dsimp only [ff, scratchBase]
    gcongr
  have hee : memoryEnd (19 * m) m N Q ≤ ee := by
    dsimp only [ee, memoryEnd, stampBase]
    gcongr
  have hep : epochBound (19 * m) m N ≤ ep := by
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
  have hbb : BandPreparation.wordBudget (19 * m) m N ≤ bb := by
    dsimp only [bb, BandPreparation.wordBudget]
    gcongr
  have htab : Wanted.tableAddress (19 * m) Q ≤ tab := by
    dsimp only [tab, Wanted.tableAddress, Wanted.inputLimit]
    gcongr
  have hrb : Wanted.routeBudget (19 * m) m N (Wanted.tableAddress (19 * m) Q) ≤ rb := by
    dsimp only [rb, Wanted.routeBudget]
    gcongr
  have hwb : Wanted.wordBudget (19 * m) m N Q ≤ wb := by
    dsimp only [wb, Wanted.wordBudget]
    gcongr
  have hkb : PrunedQuery.kernelBudget (19 * m) (scratchBase (19 * m) m N Q)
      (BandPreparation.memoryEnd (19 * m) m N) (BandPreparation.memoryEnd (19 * m) m N)
      (codeBase (19 * m) m N Q) (outputBase (19 * m) m N Q) Q (epochBound (19 * m) m N) ≤ kb := by
    dsimp only [kb, PrunedQuery.kernelBudget, PrunedQuery.addressBound,
      PrunedQuery.evaluationBudget, PrunedQuery.nodeBudget]
    gcongr
  have hab : wordBudget (19 * m) m N Q ≤ ab := by
    dsimp only [ab, wordBudget]
    gcongr
  have hmg : magnitudeBound (19 * m) A ≤ mg := by
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

/-- A fixed positive logarithmic-width coefficient suffices throughout the thin regime. -/
public theorem thin_admissionWidth_le (m N Q A : ℕ) (hN : D m ^ 18 ≤ N) :
    admissionWidth (19 * m) m N Q A ≤ 128 * Nat.clog 2 (N + Q + A + 2) := by
  let S := N + Q + A + 2
  have hs : 1 < S := by dsimp only [S]; omega
  have hl := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hs
  have hp := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) S
  have he := (thin_envelopes m N Q A hN).1
  have hpow : magnitudeBound (19 * m) A + wordBudget (19 * m) m N Q + 1 ≤
      2 ^ (40 + 10 * Nat.clog 2 S) := by
    calc _ ≤ 2 ^ 40 * S ^ 10 := he
      _ ≤ 2 ^ 40 * (2 ^ Nat.clog 2 S) ^ 10 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 10)
      _ = _ := by rw [pow_add, ← pow_mul, Nat.mul_comm (Nat.clog 2 S) 10]
  have hc := (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr hpow
  unfold admissionWidth
  dsimp only [S] at hc hl
  omega

/-- Complete initialized native thin-product execution at a fixed positive logarithmic-width
threshold. Every original occurrence is answered, including duplicates, and halt is charged.
The occurrence-count condition is stated explicitly rather than replaced by set cardinality. -/
public theorem runs_thin {W m N A : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N) (hQ : qs.length * 2 ^ m ≤ N ^ 2)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hW : 128 * Nat.clog 2 (N + qs.length + A + 2) ≤ W) :
    InputFits W (input bits (19 * m) X Y qs) ∧
    ∃ y n,
      Runs W ((program bits).program output) (State.init (input bits (19 * m) X Y qs))
        ⟨(program bits).size, y⟩ n ∧
      Executes W ((program bits).program output) (State.init (input bits (19 * m) X Y qs))
        (outputBase (19 * m) m N qs.length) (n + 1) ∧
      ((n + 1 : ℕ) : ℝ) ≤ 4325376 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 /
        (D m : ℝ) ^ (1 / 18 : ℝ) ∧ y.Bounded W ∧
      (∀ i : Fin qs.length, y.mem (outputBase (19 * m) m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, ¬(inputEnd m N qs.length ≤ a ∧ a < memoryEnd (19 * m) m N qs.length) →
        y.mem a = (State.init (input bits (19 * m) X Y qs) : State 160).data.mem a) := by
  obtain ⟨hi, y, n, hn, hr, he, hy, hv, hf⟩ := runs_wide (show m ≤ 19 * m by omega)
    bits X Y qs hX hY hbits ((thin_admissionWidth_le m N qs.length A hN).trans hW)
  have hnR : ((n + 1 : ℕ) : ℝ) ≤ (timeBound (show m ≤ 19 * m by omega) qs + 1 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  exact ⟨hi, y, n, hr, he, hnR.trans (thin_timeBound_sparse m N qs hN hQ), hy, hv, hf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
