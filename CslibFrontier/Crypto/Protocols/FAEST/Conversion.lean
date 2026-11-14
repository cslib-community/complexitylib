/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Basic
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Init

/-!
# FAEST seed expansion and conversion to VOLE

FAEST v3 expands the leaves of a depth-`d` all-but-one vector commitment to `2 ^ d` rows in
`F₂^hatℓ`, then Figure 5.6 recursively xors adjacent pairs.  At level `j`, the xor of every odd
row is output as column `v_j`; the paired rows continue to the next level.  Proposition 5.2 states
that hiding leaf `Delta`, substituting the zero row, and permuting the remaining rows by
`i ↦ i xor Delta` produces verifier columns `q_j = v_j xor delta_j * u`, where `delta_j` is the
`j`-th little-endian bit of `Delta`.

This module starts after deterministic seed expansion: its input is the family of expanded rows.
It formalizes the exact divide-and-conquer conversion and packages Proposition 5.2 as the existing
`Cslib.Crypto.Protocols.VOLE.VOLECorrelation Bool` invariant.  It does not formalize BAVC
commitments or their abort behavior, pseudorandomness of the expansion, VOLECommit /
VOLEReconstruct, CRT masks, QuickSilver verification, the complete FAEST protocol, or ROM/QROM
security.

## Main definitions

* `Cslib.Crypto.FAEST.Conversion`: the source output `(u, v₀, ..., v_{d-1})`.
* `Cslib.Crypto.FAEST.convertExpandedRows`: Figure 5.6 on already-expanded rows.
* `Cslib.Crypto.FAEST.verifierRows`: the missing-row and xor-permutation convention.
* `Cslib.Crypto.FAEST.conversionCorrelation`: a converted column in the shared ideal-VOLE API.

## Main results

* `Cslib.Crypto.FAEST.convertExpandedRows_correlation`: Proposition 5.2.
* `Cslib.Crypto.FAEST.conversionCorrelation_valid`: every converted column satisfies the shared
  binary VOLE invariant.

## References

* [C. Baum et al., *FAEST v3: Algorithm Specifications*][BaumEtAl2026FAEST], Section 5.4,
  Figure 5.6 and Proposition 5.2.
-/

public section

namespace Cslib.Crypto.FAEST

open Cslib
open Cslib.Crypto.Protocols.VOLE

/-- Output `(u, v₀, ..., v_{d-1})` of FAEST v3 `ConvertToVOLE` after seed expansion. -/
structure Conversion (d outputLength : Nat) where
  /-- The xor of all expanded rows. -/
  u : BitString outputLength
  /-- One binary VOLE mask column per tree level. -/
  columns : Fin d → BitString outputLength

/-- The index with high part `i` and least-significant bit `b`. -/
@[expose] def pairIndex {d : Nat} (i : Fin (2 ^ d)) (b : Bool) : Fin (2 ^ (d + 1)) :=
  ⟨Nat.bit b i, Nat.bit_lt_two_pow_succ_iff.mpr i.isLt⟩

/-- Split a `(d + 1)`-bit index into its `d` high bits and least-significant bit. -/
private def pairEquiv (d : Nat) : Fin (2 ^ d) × Bool ≃ Fin (2 ^ (d + 1)) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans <|
    finProdFinEquiv.trans <| finCongr (by simp [pow_succ])

private theorem pairEquiv_apply {d : Nat} (i : Fin (2 ^ d)) (b : Bool) :
    pairEquiv d (i, b) = pairIndex i b := by
  apply Fin.ext
  cases b <;>
    simp [pairIndex, pairEquiv, finProdFinEquiv, finTwoEquiv, Nat.bit_val, Nat.add_comm]

private theorem pairIndex_val {d : Nat} (i : Fin (2 ^ d)) (b : Bool) :
    (pairIndex i b : Nat) = Nat.bit b i := rfl

private theorem testBit_pairIndex_zero {d : Nat} (i : Fin (2 ^ d)) (b : Bool) :
    (pairIndex i b : Nat).testBit 0 = b := by
  rw [pairIndex_val, Nat.testBit_bit_zero]

private theorem testBit_pairIndex_succ {d : Nat} (i : Fin (2 ^ d)) (b : Bool) (j : Nat) :
    (pairIndex i b : Nat).testBit (j + 1) = (i : Nat).testBit j := by
  rw [pairIndex_val, show j + 1 = Nat.succ j by omega, Nat.testBit_bit_succ]

/-- Pair adjacent rows as in line 9 of Figure 5.6. -/
@[expose] def pairRows {d outputLength : Nat}
    (rows : Fin (2 ^ (d + 1)) → BitString outputLength) :
    Fin (2 ^ d) → BitString outputLength :=
  fun i => rows (pairIndex i false) + rows (pairIndex i true)

/-- Xor all odd rows as in line 8 of Figure 5.6. -/
@[expose] def oddColumn {d outputLength : Nat}
    (rows : Fin (2 ^ (d + 1)) → BitString outputLength) : BitString outputLength :=
  ∑ i, rows (pairIndex i true)

/-- Figure 5.6 on the rows obtained after applying the source PRG to every present seed.

The missing-seed convention is represented separately by `verifierRows`; it maps the absent row
to zero before calling this same conversion. -/
@[expose] def convertExpandedRows {outputLength : Nat} :
    (d : Nat) → (Fin (2 ^ d) → BitString outputLength) → Conversion d outputLength
  | 0, rows =>
      { u := rows 0
        columns := Fin.elim0 }
  | d + 1, rows =>
      let tail := convertExpandedRows d (pairRows rows)
      { u := tail.u
        columns := Fin.cases (oddColumn rows) tail.columns }

/-- Closed-form xor of all rows, used to state the invariant of Figure 5.6. -/
private def allRows {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) : BitString outputLength :=
  ∑ i, rows i

/-- Closed-form `j`-th output: xor the rows whose `j`-th little-endian index bit is one. -/
private def selectedRows {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (j : Fin d) : BitString outputLength :=
  ∑ i : Fin (2 ^ d), if (i : Nat).testBit j then rows i else 0

private theorem sum_pairIndex {d : Nat} {A : Type*} [AddCommMonoid A]
    (f : Fin (2 ^ (d + 1)) → A) :
    (∑ i, f i) = ∑ i : Fin (2 ^ d), (f (pairIndex i false) + f (pairIndex i true)) := by
  calc
    (∑ i, f i) = ∑ p, f (pairEquiv d p) := ((pairEquiv d).sum_comp f).symm
    _ = ∑ i : Fin (2 ^ d), (f (pairIndex i false) + f (pairIndex i true)) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, pairEquiv_apply, add_comm]

private theorem convertExpandedRows_u {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) :
    (convertExpandedRows d rows).u = allRows rows := by
  induction d with
  | zero => simp [convertExpandedRows, allRows]
  | succ d ih =>
    simp only [convertExpandedRows]
    rw [ih]
    exact (sum_pairIndex rows).symm

private theorem convertExpandedRows_column {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (j : Fin d) :
    (convertExpandedRows d rows).columns j = selectedRows rows j := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [convertExpandedRows, Fin.cases_zero]
      unfold oddColumn selectedRows
      rw [← (pairEquiv d).sum_comp, Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, pairEquiv_apply, Fin.val_zero, testBit_pairIndex_zero,
        Bool.false_eq_true, ↓reduceIte, add_zero]
    · simp only [convertExpandedRows, Fin.cases_succ]
      rw [ih]
      unfold selectedRows
      rw [← (pairEquiv d).sum_comp, Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, pairEquiv_apply, Fin.val_succ, testBit_pairIndex_succ]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : (i : Nat).testBit j = true <;> simp [h, pairRows, add_comm]

/-- Bounded bitwise xor of two depth-`d` leaf indices. -/
@[expose] def xorIndex {d : Nat} (i delta : Fin (2 ^ d)) : Fin (2 ^ d) :=
  ⟨i.val ^^^ delta.val, Nat.xor_lt_two_pow i.isLt delta.isLt⟩

private theorem xorIndex_involutive {d : Nat} (delta i : Fin (2 ^ d)) :
    xorIndex (xorIndex i delta) delta = i := by
  apply Fin.ext
  simp only [xorIndex, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Xoring with a fixed bounded index is a permutation. -/
private def xorEquiv {d : Nat} (delta : Fin (2 ^ d)) : Fin (2 ^ d) ≃ Fin (2 ^ d) :=
  { toFun := fun i => xorIndex i delta
    invFun := fun i => xorIndex i delta
    left_inv := xorIndex_involutive delta
    right_inv := xorIndex_involutive delta }

private theorem xorEquiv_apply {d : Nat} (delta i : Fin (2 ^ d)) :
    xorEquiv delta i = xorIndex i delta := rfl

private theorem testBit_xorIndex {d : Nat} (delta i : Fin (2 ^ d)) (j : Nat) :
    (xorIndex i delta : Nat).testBit j =
      bne ((i : Nat).testBit j) ((delta : Nat).testBit j) := by
  exact Nat.testBit_xor i delta j

/-- Verifier rows from Proposition 5.2: row zero is missing and therefore zero, while every
positive input position `i` contains prover row `i xor Delta`. -/
@[expose] def verifierRows {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (delta : Fin (2 ^ d)) :
    Fin (2 ^ d) → BitString outputLength :=
  fun i => if i = 0 then 0 else rows (xorIndex i delta)

/-- The xor of rows whose `j`-th index bit is zero. -/
private def unselectedRows {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (j : Fin d) : BitString outputLength :=
  ∑ i : Fin (2 ^ d), if (i : Nat).testBit j then 0 else rows i

private theorem unselectedRows_eq_selectedRows_add_allRows {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (j : Fin d) :
    unselectedRows rows j = selectedRows rows j + allRows rows := by
  unfold unselectedRows selectedRows allRows
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  cases (i : Nat).testBit j <;> simp

private theorem selectedRows_verifierRows {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (delta : Fin (2 ^ d)) (j : Fin d) :
    selectedRows (verifierRows rows delta) j =
      selectedRows rows j + fun k => (BitString.equivFin d).symm delta j * allRows rows k := by
  unfold selectedRows
  have hremove :
      (∑ i : Fin (2 ^ d),
          if (i : Nat).testBit j then verifierRows rows delta i else 0) =
        ∑ i : Fin (2 ^ d), if (i : Nat).testBit j then rows (xorIndex i delta) else 0 := by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hbit : (i : Nat).testBit j = true
    · have hne : i ≠ 0 := by
        intro hi
        subst i
        simp at hbit
      simp [hbit, verifierRows, hne]
    · simp [hbit]
  rw [hremove, ← (xorEquiv delta).sum_comp]
  simp only [xorEquiv_apply, xorIndex_involutive, testBit_xorIndex]
  cases hdelta : (delta : Nat).testBit j
  · rw [show
        (∑ i : Fin (2 ^ d), if bne ((i : Nat).testBit j) false then rows i else 0) =
            selectedRows rows j by
        unfold selectedRows
        apply Finset.sum_congr rfl
        intro i _hi
        cases (i : Nat).testBit j <;> simp]
    have hmul : (fun k => (BitString.equivFin d).symm delta j * allRows rows k) = 0 := by
      funext k
      rw [BitString.equivFin_symm_apply, hdelta]
      cases allRows rows k <;> rfl
    rw [hmul, add_zero]
    rfl
  · rw [show
        (∑ i : Fin (2 ^ d), if bne ((i : Nat).testBit j) true then rows i else 0) =
            unselectedRows rows j by
        unfold unselectedRows
        apply Finset.sum_congr rfl
        intro i _hi
        cases (i : Nat).testBit j <;> simp]
    rw [unselectedRows_eq_selectedRows_add_allRows]
    have hmul : (fun k => (BitString.equivFin d).symm delta j * allRows rows k) = allRows rows := by
      funext k
      rw [BitString.equivFin_symm_apply, hdelta]
      cases allRows rows k <;> rfl
    rw [hmul]
    rfl

/-- Proposition 5.2 of FAEST v3: consistent prover and missing-row verifier conversions satisfy
`q_j = v_j xor delta_j * u` for every tree level `j`.

The theorem is parameterized by the depth, output length, and expanded rows.  It is deterministic
and introduces no abort or failure event; obtaining consistent rows from BAVC after a non-aborting
opening is a separate prerequisite. -/
theorem convertExpandedRows_correlation {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (delta : Fin (2 ^ d)) (j : Fin d) :
    (convertExpandedRows d (verifierRows rows delta)).columns j =
      (convertExpandedRows d rows).columns j +
        fun k => (BitString.equivFin d).symm delta j * (convertExpandedRows d rows).u k := by
  rw [convertExpandedRows_column, convertExpandedRows_column, convertExpandedRows_u]
  exact selectedRows_verifierRows rows delta j

/-- The `j`-th output of consistent FAEST conversions, expressed through the shared ideal binary
VOLE-correlation type. -/
@[expose] def conversionCorrelation {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (delta : Fin (2 ^ d)) (j : Fin d) :
    VOLECorrelation Bool outputLength where
  u := (convertExpandedRows d rows).u
  v := (convertExpandedRows d rows).columns j
  delta := (BitString.equivFin d).symm delta j
  w := (convertExpandedRows d (verifierRows rows delta)).columns j

/-- Proposition 5.2 is exactly the existing `VOLECorrelation.Valid` invariant over `Bool`. -/
theorem conversionCorrelation_valid {d outputLength : Nat}
    (rows : Fin (2 ^ d) → BitString outputLength) (delta : Fin (2 ^ d)) (j : Fin d) :
    (conversionCorrelation rows delta j).Valid := by
  intro k
  have h := congrFun (convertExpandedRows_correlation rows delta j) k
  simpa only [conversionCorrelation, Pi.add_apply, Pi.zero_apply, mul_comm, add_comm] using h

end Cslib.Crypto.FAEST
