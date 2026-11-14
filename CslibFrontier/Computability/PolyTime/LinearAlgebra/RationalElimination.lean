/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Computability.PolyTime.Int.Table
import Mathlib.Data.List.GetD

/-!
# Polynomial-time Bareiss–Jordan rational linear algebra

Multi-tape Turing machine polynomial-time computability (`Turing.MultiTapeTM.ComputableInPolyTime`)
for exact rational elimination (`rationalElim`, `ratRref`, `ratRank`, `ratRowBasis`,
`ratKernelBasis`) and linear system solving (`ratSolve`).

## Encodings and local adaptations

* Alexander Schrijver, *Theory of Linear and Integer Programming* (Wiley, 1986), Section 3.3,
  Theorem 3.3 (pp. 32–33), Corollary 3.3a (pp. 33–34), and the Gauss–Jordan discussion with
  Equations (28)–(30) (p. 35), together with Section 3.2, Theorem 3.2 (pp. 29–30).
* **Local adaptations:** (1) Instead of Schrijver's normalized rational elimination, the underlying
  algorithm executes row-denominator-cleared fraction-free Bareiss–Jordan integer updates bounded
  by the factorial/Hadamard `stageEntryBound`. (2) To certify native multi-tape Turing machine time
  and workspace bounds (`Turing.MultiTapeTM.ComputableInPolyTime`) unconditionally, all matrix
  dimension counters (`numRows`, `numCols`, `rank`, `pivotRows`, `pivotCols`, `nonPivotCols`) use
  explicit `encUnary` headers inside `enc_structure` codecs alongside framed signed-binary
  (`encIntBin`) and rational (`encRat`) entries, preventing exponential blowup from oversized
  declared dimensions on malformed or zero-entry tables.

## Main definitions

* `Cslib.LinearAlgebra.IntTable.enc`, `Cslib.LinearAlgebra.RatTable.enc`,
  `Cslib.LinearAlgebra.BareissState.enc`, `Cslib.LinearAlgebra.RationalElimResult.enc`,
  `Cslib.LinearAlgebra.LinearSystemInput.enc`, `Cslib.LinearAlgebra.LinearSolveResult.enc`:
  structured multi-tape binary encodings via `enc_structure`.

## Main results

* `Cslib.LinearAlgebra.rationalElim_computableInPolyTime`
* `Cslib.LinearAlgebra.ratRref_computableInPolyTime`
* `Cslib.LinearAlgebra.ratRank_computableInPolyTime`
* `Cslib.LinearAlgebra.ratRowBasis_computableInPolyTime`
* `Cslib.LinearAlgebra.ratKernelBasis_computableInPolyTime`
* `Cslib.LinearAlgebra.ratSolve_computableInPolyTime`
-/

public section

namespace Cslib.LinearAlgebra

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Structured binary encodings (`#4391`) -/

namespace IntTable

/-- Binary encoding of an `IntTable` with unary matrix dimensions and framed signed-binary rows. -/
enc_structure enc : IntTable where
  numRows : encUnary,
  numCols : encUnary,
  rows : (encList (encList encIntBin))

end IntTable

namespace RatTable

/-- Binary encoding of a `RatTable` with unary matrix dimensions and framed rational rows. -/
enc_structure enc : RatTable where
  numRows : encUnary,
  numCols : encUnary,
  rows : (encList (encList encRat))

end RatTable

namespace BareissState

/-- Binary encoding of a `BareissState` with unary pivot row/column index lists. -/
enc_structure enc : BareissState where
  table : IntTable.enc,
  pivotDet : encIntBin,
  pivotRows : (encList encUnary),
  pivotCols : (encList encUnary)

end BareissState

namespace RationalElimResult

/-- Binary encoding of a `RationalElimResult`. -/
enc_structure enc : RationalElimResult where
  rref : RatTable.enc,
  rank : encUnary,
  pivotRows : (encList encUnary),
  pivotCols : (encList encUnary),
  nonPivotCols : (encList encUnary),
  kernelBasis : (encList (encList encRat))

end RationalElimResult

namespace LinearSystemInput

/-- Binary encoding of a `LinearSystemInput`. -/
enc_structure enc : LinearSystemInput where
  matrix : RatTable.enc,
  rhs : (encList encRat)

end LinearSystemInput

namespace LinearSolveResult

/-- Binary encoding of a `LinearSolveResult`. -/
enc_structure enc : LinearSolveResult where
  solution : (encOption (encList encRat)),
  pivotRows : (encList encUnary),
  pivotCols : (encList encUnary)

end LinearSolveResult

open scoped IntTable RatTable BareissState RationalElimResult LinearSystemInput
  LinearSolveResult

/-! ### Encoding length and coefficient magnitude bounds -/

section SizeBounds

private theorem list_getD_rat_bounds {l : List ℚ} {idx L : ℕ}
    (hlen : (encList encRat l).length ≤ L) :
    (l.getD idx 0).num.natAbs ≤ 2 ^ L ∧ (l.getD idx 0).den ≤ 2 ^ L := by
  by_cases hi : idx < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    have hq : (encRat l[idx]).length ≤ L :=
      (length_le_encList_of_mem _ (List.getElem_mem hi)).trans hlen
    exact ⟨(natAbs_num_lt_two_pow_length_encRat _).le.trans (Nat.pow_le_pow_right (by omega) hq),
      (den_lt_two_pow_length_encRat _).le.trans (Nat.pow_le_pow_right (by omega) hq)⟩
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
    exact ⟨Nat.zero_le _, Nat.one_le_two_pow⟩

private theorem ratTable_encoding_bounds (M : RatTable) :
    let L := (RatTable.enc M).length
    M.numRows ≤ L ∧ M.numCols ≤ L ∧
      ∀ i : Fin M.numRows, ∀ j : Fin M.numCols,
        (M.toMatrix i j).num.natAbs ≤ 2 ^ L ∧ (M.toMatrix i j).den ≤ 2 ^ L := by
  intro L
  have hrows : (encUnary M.numRows).length ≤ L := by
    dsimp only [L]
    rw [RatTable.enc_apply]
    exact length_le_encPair_left encUnary (encPair encUnary (encList (encList encRat)))
      (M.numRows, M.numCols, M.rows)
  have hcols : (encUnary M.numCols).length ≤ L := by
    dsimp only [L]
    rw [RatTable.enc_apply]
    have h1 := length_le_encPair_left encUnary (encList (encList encRat)) (M.numCols, M.rows)
    have h2 := length_le_encPair_right encUnary (encPair encUnary (encList (encList encRat)))
      (M.numRows, (M.numCols, M.rows))
    exact h1.trans h2
  have hmat : (encList (encList encRat) M.rows).length ≤ L := by
    dsimp only [L]
    rw [RatTable.enc_apply]
    have h1 := length_le_encPair_right encUnary (encList (encList encRat)) (M.numCols, M.rows)
    have h2 := length_le_encPair_right encUnary (encPair encUnary (encList (encList encRat)))
      (M.numRows, (M.numCols, M.rows))
    exact h1.trans h2
  refine ⟨by simpa only [encUnary_apply, List.length_replicate] using hrows,
    by simpa only [encUnary_apply, List.length_replicate] using hcols, fun i j => ?_⟩
  simp only [RatTable.toMatrix_apply, RatTable.entry]
  by_cases hi : i.val < M.rows.length
  · rw [List.getD_eq_getElem _ _ hi]
    have hrow_len : (encList encRat (M.rows[i.val])).length ≤ L :=
      (length_le_encList_of_mem _ (List.getElem_mem hi)).trans hmat
    exact list_getD_rat_bounds hrow_len
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
    simp only [List.getD_nil]
    exact ⟨Nat.zero_le _, Nat.one_le_two_pow⟩

private theorem linearSystemInput_encoding_bounds (sys : LinearSystemInput) :
    let L := (LinearSystemInput.enc sys).length
    sys.matrix.numRows ≤ L ∧ sys.matrix.numCols ≤ L ∧
      (∀ i : Fin sys.matrix.numRows, ∀ j : Fin sys.matrix.numCols,
        (sys.matrix.toMatrix i j).num.natAbs ≤ 2 ^ L ∧
        (sys.matrix.toMatrix i j).den ≤ 2 ^ L) ∧
      (∀ i : Fin sys.matrix.numRows,
        (sys.rhs.getD i.val 0).num.natAbs ≤ 2 ^ L ∧
        (sys.rhs.getD i.val 0).den ≤ 2 ^ L) := by
  intro L
  have hm : (RatTable.enc sys.matrix).length ≤ L := by
    dsimp only [L]
    rw [LinearSystemInput.enc_apply]
    exact length_le_encPair_left RatTable.enc (encList encRat) (sys.matrix, sys.rhs)
  have hr : (encList encRat sys.rhs).length ≤ L := by
    dsimp only [L]
    rw [LinearSystemInput.enc_apply]
    exact length_le_encPair_right RatTable.enc (encList encRat) (sys.matrix, sys.rhs)
  obtain ⟨hmr, hmc, hment⟩ := ratTable_encoding_bounds sys.matrix
  refine ⟨hmr.trans hm, hmc.trans hm, fun i j => ?_, fun i => list_getD_rat_bounds hr⟩
  have hij := hment i j
  exact ⟨hij.1.trans (Nat.pow_le_pow_right (by omega) hm),
    hij.2.trans (Nat.pow_le_pow_right (by omega) hm)⟩

private theorem length_encIntBin_of_natAbs_le {z : ℤ} {S : ℕ} (hz : |z| ≤ (S : ℤ)) :
    (encIntBin z).length ≤ S.size + 1 := by
  rw [length_encIntBin]
  have hna : z.natAbs ≤ S := Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hz)
  exact Nat.add_le_add_right (Nat.size_le_size hna) 1

private def bareissStateSizeBound (m n sB : ℕ) : ℕ :=
  let sS := (m + 1) * (m + 1 + (sB + 1)) + 2
  2 * (2 * m + 1 + (2 * n + 1 + m * (2 * (n * (2 * (sS + 1) + 1)) + 1))) + 1 +
    (2 * (sS + 1) + 1 + (2 * (m * (2 * m + 1)) + 1 + m * (2 * n + 1)))

private theorem length_encBareissState_le_of_inv {T : IntTable} {c : ℕ} {st : BareissState}
    (hinv : BareissInv T c st) {B : ℕ}
    (hB : ∀ i : Fin T.numRows, ∀ j : Fin T.numCols, |T.toMatrix i j| ≤ (B : ℤ)) :
    (BareissState.enc st).length ≤ bareissStateSizeBound T.numRows T.numCols B.size := by
  set S := stageEntryBound T.numRows T.numCols B
  set sS := (T.numRows + 1) * (T.numRows + 1 + (B.size + 1)) + 2
  have hS_size : S.size ≤ sS := by
    have h1 := size_stageEntryBound_le T.numRows T.numCols B
    have h2 : (min T.numRows T.numCols + 1).size ≤ T.numRows + 1 :=
      (Nat.size_le_self _).trans (Nat.add_le_add_right (Nat.min_le_left _ _) 1)
    have h3 : (B + 1).size ≤ B.size + 1 := by
      refine Nat.size_le.mpr ?_
      have hlt : B < 2 ^ B.size := Nat.lt_size_self B
      have hpow : 1 ≤ 2 ^ B.size := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega
    have h4 : min T.numRows T.numCols + 1 ≤ T.numRows + 1 :=
      Nat.add_le_add_right (Nat.min_le_left _ _) 1
    calc S.size
        ≤ (min T.numRows T.numCols + 1) * ((min T.numRows T.numCols + 1).size + (B + 1).size) + 2 :=
          h1
      _ ≤ (T.numRows + 1) * (T.numRows + 1 + (B.size + 1)) + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul h4 (Nat.add_le_add h2 h3)) 2
  have hbd := bareissInv_entry_bound hinv hB
  have hwf := hinv.wellFormed
  have hrows_len : st.table.rows.length = T.numRows := hwf.1.trans hinv.dims.1
  have hcols_len : ∀ row ∈ st.table.rows, row.length = T.numCols := fun row hr =>
    (hwf.2 row hr).trans hinv.dims.2
  have hrow_enc_le : ∀ row ∈ st.table.rows,
      (encList encIntBin row).length ≤ T.numCols * (2 * (sS + 1) + 1) := by
    intro row hr
    obtain ⟨ri, hri, rfl⟩ := List.getElem_of_mem hr
    have hri' : ri < T.numRows := hrows_len ▸ hri
    have hrow_l : st.table.rows[ri].length = T.numCols := hcols_len _ (List.getElem_mem hri)
    refine (length_encList_le encIntBin st.table.rows[ri] (b := sS + 1) fun z hz => ?_).trans
      (by rw [hrow_l])
    obtain ⟨ci, hci, rfl⟩ := List.getElem_of_mem hz
    have hci' : ci < T.numCols := hrow_l ▸ hci
    have hent : st.table.entry ri ci = st.table.rows[ri][ci] := by
      simp only [IntTable.entry, Cslib.rowEntry, List.getD_eq_getElem _ _ hri,
        List.getD_eq_getElem _ _ hci]
    exact (length_encIntBin_of_natAbs_le (hent ▸ hbd.1 ⟨ri, hri'⟩ ⟨ci, hci'⟩)).trans
      (Nat.add_le_add_right hS_size 1)
  have hrows_enc : (encList (encList encIntBin) st.table.rows).length ≤
      T.numRows * (2 * (T.numCols * (2 * (sS + 1) + 1)) + 1) := by
    refine (length_encList_le (encList encIntBin) st.table.rows
      (b := T.numCols * (2 * (sS + 1) + 1)) hrow_enc_le).trans (by rw [hrows_len])
  have htable_enc : (IntTable.enc st.table).length ≤
      2 * T.numRows + 1 +
        (2 * T.numCols + 1 + T.numRows * (2 * (T.numCols * (2 * (sS + 1) + 1)) + 1)) := by
    rw [IntTable.enc_apply, length_encPair, length_encPair, encUnary_apply, List.length_replicate,
      encUnary_apply, List.length_replicate]
    dsimp only
    rw [hinv.dims.1, hinv.dims.2]
    exact Nat.add_le_add_left (Nat.add_le_add_left hrows_enc _) _
  have hpiv_det : (encIntBin st.pivotDet).length ≤ sS + 1 :=
    (length_encIntBin_of_natAbs_le hbd.2).trans (Nat.add_le_add_right hS_size 1)
  have hk_le : st.pivotRows.length ≤ T.numRows :=
    (bareissInv_pivotRows_length_le hinv).trans (Nat.min_le_left _ _)
  have hpiv_rows : (encList encUnary st.pivotRows).length ≤ T.numRows * (2 * T.numRows + 1) := by
    refine (length_encList_le encUnary st.pivotRows (b := T.numRows) fun r hr => ?_).trans
      (Nat.mul_le_mul_right _ hk_le)
    simp only [encUnary_apply, List.length_replicate]
    exact (hinv.row_lt r hr).le
  have hpiv_cols : (encList encUnary st.pivotCols).length ≤ T.numRows * (2 * T.numCols + 1) := by
    refine (length_encList_le encUnary st.pivotCols (b := T.numCols) fun c hc => ?_).trans
      (Nat.mul_le_mul_right _ (by rw [← hinv.len_eq]; exact hk_le))
    simp only [encUnary_apply, List.length_replicate]
    exact (hinv.col_dim c hc).le
  rw [BareissState.enc_apply, length_encPair, length_encPair, length_encPair]
  dsimp only [bareissStateSizeBound, sS] at *
  gcongr

end SizeBounds

/-! ### Polynomial-time component certificates and public theorems -/

section PolyTimeImpl

attribute [local irreducible] encRat encIntBin encNat IntTable.enc RatTable.enc
  BareissState.enc RationalElimResult.enc LinearSystemInput.enc LinearSolveResult.enc

@[local fun_prop]
private theorem ratTable_entry_poly {α : Type} {encIn : α ↪ List Bool}
    {M : α → RatTable} {i j : α → ℕ}
    (hM : ComputableInPolyTime M encIn RatTable.enc)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => (M a).entry (i a) (j a)) encIn encRat := by
  have hbase : ComputableInPolyTime (fun p : (RatTable × ℕ) × ℕ => p.1.1.entry p.1.2 p.2)
      (encPair (encPair RatTable.enc encUnary) encUnary) encRat := by
    unfold RatTable.entry
    fun_prop
  exact hbase.comp ((hM.prod hi).prod hj)

@[local fun_prop]
private theorem normalizedRatRow_poly {α : Type} {encIn : α ↪ List Bool}
    {M : α → RatTable} {r : α → ℕ}
    (hM : ComputableInPolyTime M encIn RatTable.enc)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun a => normalizedRatRow (M a) (r a)) encIn (encList encRat) := by
  have hbase : ComputableInPolyTime (fun p : RatTable × ℕ => normalizedRatRow p.1 p.2)
      (encPair RatTable.enc encUnary) (encList encRat) := by
    unfold normalizedRatRow
    exact mapWithInput (unary_range' (by fun_prop)) (by fun_prop)
  exact hbase.comp (hM.prod hr)

@[local fun_prop]
private theorem rowDenomProd_poly {α : Type} {encIn : α ↪ List Bool} {r : α → List ℚ}
    (hr : ComputableInPolyTime r encIn (encList encRat)) :
    ComputableInPolyTime (fun a => rowDenomProd (r a)) encIn encNat := by
  have hbase : ComputableInPolyTime rowDenomProd (encList encRat) encNat := by
    unfold rowDenomProd
    refine (ComputableInPolyTime.foldlWith_spec
      (encP := encBool) (encA := encRat) (encB := encNat)
      (par := fun _ => false) (list := fun row => row) (init := fun _ => 1)
      (step := fun _ acc q => acc * q.den)
      (.const false) (.id') (.const 1) ?_
      (fun _ consumed acc => acc ≤ 2 ^ (encList encRat consumed).length)
      (fun _ => Nat.one_le_two_pow)
      (fun _ consumed state value _ hinv => ?_)
      (size := fun row => (encList encRat row).length + 1)
      (PolyBounded.self.add (.const 1))
      (fun row consumed state hpre hinv => ?_)).1
    · exact binary_mul' ((snd _ _).comp (fst _ _)) (rat_den.comp (snd _ _))
    · have hval : value.den ≤ 2 ^ (encRat value).length :=
        (den_lt_two_pow_length_encRat value).le
      have hlen : (encList encRat (consumed ++ [value])).length =
          (encList encRat consumed).length + (2 * (encRat value).length + 1) := by
        rw [encList_append, List.length_append, encList_cons, encList_nil,
          List.append_nil, length_frame]
      rw [hlen]
      have hpow : 2 ^ ((encList encRat consumed).length + (encRat value).length) ≤
          2 ^ ((encList encRat consumed).length + (2 * (encRat value).length + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact (Nat.mul_le_mul hinv hval).trans (by rw [← Nat.pow_add]; exact hpow)
    · have hpre_len : (encList encRat consumed).length ≤ (encList encRat row).length := by
        obtain ⟨rest, rfl⟩ := hpre
        simp only [encList_append, List.length_append, Nat.le_add_right]
      have hlt : state < 2 ^ ((encList encRat row).length + 1) :=
        (hinv.trans (Nat.pow_le_pow_right (by omega) hpre_len)).trans_lt
          (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
      have hsize : state.size ≤ (encList encRat row).length + 1 := Nat.size_le.mpr hlt
      simpa only [encNat_apply, Nat.size_eq_bits_len] using hsize
  exact hbase.comp hr

@[local fun_prop]
private theorem clearRow_poly {α : Type} {encIn : α ↪ List Bool} {r : α → List ℚ}
    (hr : ComputableInPolyTime r encIn (encList encRat)) :
    ComputableInPolyTime (fun a => clearRow (r a)) encIn (encList encIntBin) := by
  have hbase : ComputableInPolyTime clearRow (encList encRat) (encList encIntBin) := by
    unfold clearRow
    have hdiv : ComputableInPolyTime (fun p : List ℚ × ℚ => rowDenomProd p.1 / p.2.den)
        (encPair (encList encRat) encRat) encNat :=
      binary_div' (rowDenomProd_poly (fst (encList encRat) encRat))
        (rat_den.comp (snd _ _))
    have hcast : ComputableInPolyTime Int.ofNat encNat encIntBin := intBin_natCast
    have hmul : ComputableInPolyTime
        (fun p : List ℚ × ℚ => p.2.num * Int.ofNat (rowDenomProd p.1 / p.2.den))
        (encPair (encList encRat) encRat) encIntBin :=
      intBin_mul' (rat_num.comp (snd _ _)) (hcast.comp hdiv)
    exact mapWithInput (.id') hmul
  exact hbase.comp hr

@[local fun_prop]
private theorem clearDenoms_poly {α : Type} {encIn : α ↪ List Bool} {M : α → RatTable}
    (hM : ComputableInPolyTime M encIn RatTable.enc) :
    ComputableInPolyTime (fun a => clearDenoms (M a)) encIn IntTable.enc := by
  have hbase : ComputableInPolyTime clearDenoms RatTable.enc IntTable.enc := by
    unfold clearDenoms
    have hrows : ComputableInPolyTime
        (fun M : RatTable => (List.range M.numRows).map fun r => clearRow (normalizedRatRow M r))
        RatTable.enc (encList (encList encIntBin)) :=
      mapWithInput (unary_range' (by fun_prop)) (by fun_prop)
    fun_prop
  exact hbase.comp hM

private theorem findPivotRow_base :
    ComputableInPolyTime (fun p : BareissState × ℕ => findPivotRow p.1 p.2)
      (encPair BareissState.enc encUnary) (encOption encUnary) := by
  unfold findPivotRow IntTable.entry
  have hr : ComputableInPolyTime (fun p : BareissState × ℕ => List.range p.1.table.numRows)
      (encPair BareissState.enc encUnary) (encList encUnary) :=
    unary_range' (by fun_prop)
  have ht : ComputableInPolyTime
      (fun p : (BareissState × ℕ) × ℕ =>
        !p.1.1.pivotRows.contains p.2 &&
          decide (Cslib.rowEntry p.1.1.table.rows p.2 p.1.2 ≠ 0))
      (encPair (encPair BareissState.enc encUnary) encUnary) encBool := by
    fun_prop
  exact findWithInput hr ht

private theorem findPivotRow_poly {α : Type} {encIn : α ↪ List Bool}
    {st : α → BareissState} {c : α → ℕ}
    (hst : ComputableInPolyTime st encIn BareissState.enc)
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun a => findPivotRow (st a) (c a)) encIn (encOption encUnary) :=
  @ComputableInPolyTime.comp α (BareissState × ℕ) (Option ℕ) encIn
    (encPair BareissState.enc encUnary) (encOption encUnary)
    (fun p => findPivotRow p.1 p.2) (fun a => (st a, c a))
    findPivotRow_base (hst.prod hc)

private theorem bareissStep_base :
    ComputableInPolyTime (fun p : BareissState × ℕ => bareissStep p.1 p.2)
      (encPair BareissState.enc encUnary) BareissState.enc := by
  have heq : (fun p : BareissState × ℕ => bareissStep p.1 p.2) = fun p =>
      (findPivotRow p.1 p.2).elim p.1 fun r =>
        BareissState.mk
          (IntTable.mk p.1.table.numRows p.1.table.numCols
            (Cslib.tabulateTable p.1.table.numRows p.1.table.numCols fun i j =>
              if i = r then Cslib.rowEntry p.1.table.rows r j
              else
                (Cslib.rowEntry p.1.table.rows r p.2 * Cslib.rowEntry p.1.table.rows i j -
                  Cslib.rowEntry p.1.table.rows i p.2 * Cslib.rowEntry p.1.table.rows r j) /
                    p.1.pivotDet))
          (Cslib.rowEntry p.1.table.rows r p.2) (p.1.pivotRows ++ [r])
          (p.1.pivotCols ++ [p.2]) := by
    funext p
    unfold bareissStep IntTable.entry
    cases findPivotRow p.1 p.2 <;> rfl
  rw [heq]
  exact ComputableInPolyTime.optionElimWithInput findPivotRow_base
    (fst BareissState.enc encUnary) (by fun_prop)

private theorem bareissStep_poly {α : Type} {encIn : α ↪ List Bool}
    {st : α → BareissState} {c : α → ℕ}
    (hst : ComputableInPolyTime st encIn BareissState.enc)
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun a => bareissStep (st a) (c a)) encIn BareissState.enc :=
  @ComputableInPolyTime.comp α (BareissState × ℕ) BareissState encIn
    (encPair BareissState.enc encUnary) BareissState.enc
    (fun p => bareissStep p.1 p.2) (fun a => (st a, c a))
    bareissStep_base (hst.prod hc)

private theorem bareissElimCols_poly_of_bound {γ : Type} {encIn : γ ↪ List Bool}
    {toTable : γ → IntTable} {colLimit : γ → ℕ} {B : γ → ℕ}
    (htoTable : ComputableInPolyTime toTable encIn IntTable.enc)
    (hcolLimit : ComputableInPolyTime colLimit encIn encUnary)
    (hwf : ∀ x, (toTable x).WellFormed)
    (hlim : ∀ x, colLimit x ≤ (toTable x).numCols)
    (hrows : PolyBounded (fun x => (encIn x).length) (fun x => (toTable x).numRows))
    (hcols : PolyBounded (fun x => (encIn x).length) (fun x => (toTable x).numCols))
    (hsizeB : PolyBounded (fun x => (encIn x).length) (fun x => (B x).size))
    (hB : ∀ x, ∀ i : Fin (toTable x).numRows, ∀ j : Fin (toTable x).numCols,
      |(toTable x).toMatrix i j| ≤ (B x : ℤ)) :
    ComputableInPolyTime (fun x => bareissElimCols (toTable x) (colLimit x))
      encIn BareissState.enc := by
  unfold bareissElimCols bareissInit
  have hpoly_bound : PolyBounded (fun x => (encIn x).length)
      (fun x => bareissStateSizeBound (toTable x).numRows (toTable x).numCols (B x).size) := by
    unfold bareissStateSizeBound
    have hsS : PolyBounded (fun x => (encIn x).length)
        (fun x => ((toTable x).numRows + 1) *
          ((toTable x).numRows + 1 + ((B x).size + 1)) + 2) :=
      ((hrows.add (.const 1)).mul ((hrows.add (.const 1)).add (hsizeB.add (.const 1)))).add
        (.const 2)
    have hinner := (PolyBounded.const 2).mul (hsS.add (.const 1))
    have hrow := ((PolyBounded.const 2).mul (hcols.mul (hinner.add (.const 1)))).add (.const 1)
    have htable := (PolyBounded.const 2).mul
      ((((((PolyBounded.const 2).mul hrows).add (.const 1))).add
        ((((((PolyBounded.const 2).mul hcols).add (.const 1))).add (hrows.mul hrow)))))
    have hpivDet := ((PolyBounded.const 2).mul (hsS.add (.const 1))).add (.const 1)
    have hpivRows :=
      ((PolyBounded.const 2).mul
        (hrows.mul (((PolyBounded.const 2).mul hrows).add (.const 1)))).add (.const 1)
    have hpivCols := hrows.mul (((PolyBounded.const 2).mul hcols).add (.const 1))
    exact (htable.add (.const 1)).add (hpivDet.add (hpivRows.add hpivCols))
  refine (ComputableInPolyTime.foldlWith_spec
    (encP := encBool) (encA := encUnary) (encB := BareissState.enc)
    (par := fun _ => false) (list := fun x => List.range (colLimit x))
    (init := fun x => ⟨toTable x, 1, [], []⟩)
    (step := fun _ st c => bareissStep st c)
    (.const false) (unary_range' hcolLimit)
    (by fun_prop)
    (bareissStep_poly
      ((ComputableInPolyTime.snd encBool BareissState.enc).comp
        (ComputableInPolyTime.fst (encPair encBool BareissState.enc) encUnary))
      (ComputableInPolyTime.snd (encPair encBool BareissState.enc) encUnary))
    (fun x consumed st =>
      ∃ k ≤ colLimit x, consumed = List.range k ∧ BareissInv (toTable x) k st)
    (fun x => ⟨0, Nat.zero_le _, rfl, bareissInv_init (hwf x)⟩)
    (fun x consumed st c hpre ⟨k, hk, hcon, hinv⟩ => ?_)
    hpoly_bound
    (fun x consumed st _ ⟨_, _, _, hinv⟩ =>
      length_encBareissState_le_of_inv hinv (hB x))).1
  obtain ⟨rest, hrest⟩ := hpre
  have hlen : (consumed ++ [c]).length ≤ (List.range (colLimit x)).length :=
    calc (consumed ++ [c]).length
        ≤ (consumed ++ [c]).length + rest.length := Nat.le_add_right _ _
      _ = ((consumed ++ [c]) ++ rest).length := (List.length_append).symm
      _ = (List.range (colLimit x)).length := by rw [hrest]
  simp only [hcon, List.length_append, List.length_range, List.length_singleton] at hlen
  have hk' : k < colLimit x := by omega
  have hc_eq : c = k := by
    have hk_rest : k < ((consumed ++ [c]) ++ rest).length := by
      rw [hrest, List.length_range]
      exact hk'
    have hget : (List.range (colLimit x))[k]'(by rw [List.length_range]; exact hk') =
        ((consumed ++ [c]) ++ rest)[k]'hk_rest := by
      simp only [hrest]
    have hleft : k < (consumed ++ [c]).length := by
      simp only [hcon, List.length_append, List.length_range, List.length_singleton]
      omega
    have hright : consumed.length ≤ k := by simp only [hcon, List.length_range, le_refl]
    rw [List.getElem_range, List.getElem_append_left hleft,
      List.getElem_append_right hright] at hget
    simp only [hcon, List.length_range, Nat.sub_self, List.getElem_singleton] at hget
    exact hget.symm
  rw [hc_eq]
  exact ⟨k + 1, hk', by simp only [hcon, List.range_succ],
    bareissInv_step (hk'.trans_le (hlim x)) hinv⟩

@[local fun_prop]
private theorem bareissElim_clearDenoms_poly {α : Type} {encIn : α ↪ List Bool}
    {M : α → RatTable} (hM : ComputableInPolyTime M encIn RatTable.enc) :
    ComputableInPolyTime (fun a => bareissElim (clearDenoms (M a))) encIn BareissState.enc := by
  have hbase : ComputableInPolyTime (fun M => bareissElim (clearDenoms M))
      RatTable.enc BareissState.enc := by
    unfold bareissElim
    have hrows : PolyBounded (fun M => (RatTable.enc M).length)
        (fun M => (clearDenoms M).numRows) :=
      PolyBounded.self.mono fun M => (ratTable_encoding_bounds M).1
    have hcols : PolyBounded (fun M => (RatTable.enc M).length)
        (fun M => (clearDenoms M).numCols) :=
      PolyBounded.self.mono fun M => (ratTable_encoding_bounds M).2.1
    have hsizeB : PolyBounded (fun M => (RatTable.enc M).length)
        (fun M => (2 ^ ((M.numCols + 1) * (RatTable.enc M).length)).size) := by
      have hle : ∀ M : RatTable, (2 ^ ((M.numCols + 1) * (RatTable.enc M).length)).size ≤
          ((RatTable.enc M).length + 1) * (RatTable.enc M).length + 1 := by
        intro M
        have hsize : (2 ^ ((M.numCols + 1) * (RatTable.enc M).length)).size ≤
            (M.numCols + 1) * (RatTable.enc M).length + 1 :=
          Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
        have hmc := (ratTable_encoding_bounds M).2.1
        exact hsize.trans
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right hmc 1)) 1)
      exact (((PolyBounded.self.add (.const 1)).mul .self).add (.const 1)).mono hle
    exact bareissElimCols_poly_of_bound (by fun_prop) (by fun_prop) clearDenoms_wellFormed
      (fun _ => le_refl _) hrows hcols hsizeB
      fun M i j => clearDenoms_abs_le M (ratTable_encoding_bounds M).2.2 i j
  exact hbase.comp hM

@[local fun_prop]
private theorem augmentRatTable_poly {α : Type} {encIn : α ↪ List Bool}
    {A : α → RatTable} {b : α → List ℚ}
    (hA : ComputableInPolyTime A encIn RatTable.enc)
    (hb : ComputableInPolyTime b encIn (encList encRat)) :
    ComputableInPolyTime (fun a => augmentRatTable (A a) (b a)) encIn RatTable.enc := by
  have hbase : ComputableInPolyTime (fun p : RatTable × List ℚ => augmentRatTable p.1 p.2)
      (encPair RatTable.enc (encList encRat)) RatTable.enc := by
    unfold augmentRatTable
    have hrows : ComputableInPolyTime
        (fun p : RatTable × List ℚ =>
          (List.range p.1.numRows).map fun i => normalizedRatRow p.1 i ++ [p.2.getD i 0])
        (encPair RatTable.enc (encList encRat)) (encList (encList encRat)) :=
      mapWithInput (unary_range' (by fun_prop)) (by fun_prop)
    fun_prop
  exact hbase.comp (hA.prod hb)

@[local fun_prop]
private theorem bareissElimCols_aug_poly :
    ComputableInPolyTime
      (fun sys => bareissElimCols (clearDenoms (augmentRatTable sys.matrix sys.rhs))
        sys.matrix.numCols)
      LinearSystemInput.enc BareissState.enc := by
  let toT : LinearSystemInput → IntTable :=
    fun sys => clearDenoms (augmentRatTable sys.matrix sys.rhs)
  let Bfn : LinearSystemInput → ℕ :=
    fun sys => 2 ^ ((sys.matrix.numCols + 2) * (LinearSystemInput.enc sys).length)
  have hrows : PolyBounded (fun sys => (LinearSystemInput.enc sys).length)
      (fun sys => (toT sys).numRows) :=
    PolyBounded.self.mono fun sys => (linearSystemInput_encoding_bounds sys).1
  have hcols : PolyBounded (fun sys => (LinearSystemInput.enc sys).length)
      (fun sys => (toT sys).numCols) :=
    (PolyBounded.self.add (.const 1)).mono fun sys => by
      change sys.matrix.numCols + 1 ≤ (LinearSystemInput.enc sys).length + 1
      exact Nat.add_le_add_right (linearSystemInput_encoding_bounds sys).2.1 1
  have hsizeB : PolyBounded (fun sys => (LinearSystemInput.enc sys).length)
      (fun sys => (Bfn sys).size) := by
    have hle : ∀ sys : LinearSystemInput, (Bfn sys).size ≤
        ((LinearSystemInput.enc sys).length + 2) * (LinearSystemInput.enc sys).length + 1 := by
      intro sys
      dsimp only [Bfn]
      have hsize : (2 ^ ((sys.matrix.numCols + 2) * (LinearSystemInput.enc sys).length)).size ≤
          (sys.matrix.numCols + 2) * (LinearSystemInput.enc sys).length + 1 :=
        Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
      have hmc := (linearSystemInput_encoding_bounds sys).2.1
      exact hsize.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right hmc 2)) 1)
    exact (((PolyBounded.self.add (.const 2)).mul .self).add (.const 1)).mono hle
  refine bareissElimCols_poly_of_bound (by fun_prop) (by fun_prop)
    (fun sys => clearDenoms_wellFormed _)
    (fun sys => by simp only [clearDenoms, augmentRatTable]; omega)
    hrows hcols hsizeB fun sys i j => ?_
  refine clearDenoms_abs_le (augmentRatTable sys.matrix sys.rhs) (fun i' j' => ?_) i j
  have hb := linearSystemInput_encoding_bounds sys
  rw [augmentRatTable_toMatrix_apply]
  split_ifs with hj
  · exact hb.2.2.1 ⟨i'.val, i'.isLt⟩ ⟨j'.val, hj⟩
  · exact hb.2.2.2 ⟨i'.val, i'.isLt⟩

@[local fun_prop]
private theorem scaledIntRow_poly {α : Type} {encIn : α ↪ List Bool}
    {T : α → IntTable} {Δ : α → ℤ} {r : α → ℕ}
    (hT : ComputableInPolyTime T encIn IntTable.enc)
    (hΔ : ComputableInPolyTime Δ encIn encIntBin)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun a => scaledIntRow (T a) (Δ a) (r a)) encIn (encList encRat) := by
  have hbase : ComputableInPolyTime (fun p : (IntTable × ℤ) × ℕ => scaledIntRow p.1.1 p.1.2 p.2)
      (encPair (encPair IntTable.enc encIntBin) encUnary) (encList encRat) := by
    unfold scaledIntRow IntTable.entry
    exact mapWithInput (unary_range' (by fun_prop)) (by fun_prop)
  exact hbase.comp ((hT.prod hΔ).prod hr)

@[local fun_prop]
private theorem selectRatRows_poly {α : Type} {encIn : α ↪ List Bool}
    {M : α → RatTable} {idxs : α → List ℕ}
    (hM : ComputableInPolyTime M encIn RatTable.enc)
    (hidxs : ComputableInPolyTime idxs encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => selectRatRows (M a) (idxs a))
      encIn (encList (encList encRat)) := by
  have hbase : ComputableInPolyTime (fun p : RatTable × List ℕ => selectRatRows p.1 p.2)
      (encPair RatTable.enc (encList encUnary)) (encList (encList encRat)) := by
    unfold selectRatRows
    exact mapWithInput (snd _ _) (by fun_prop)
  exact hbase.comp (hM.prod hidxs)

@[local fun_prop]
private theorem computeNonPivotCols_poly {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {cols : α → List ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hcols : ComputableInPolyTime cols encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => computeNonPivotCols (n a) (cols a))
      encIn (encList encUnary) := by
  have hbase : ComputableInPolyTime (fun p : ℕ × List ℕ => computeNonPivotCols p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
    unfold computeNonPivotCols
    exact filterWithInput (unary_range' (fst _ _)) (by fun_prop)
  exact hbase.comp (hn.prod hcols)

@[local fun_prop]
private theorem buildKernelVec_poly {α : Type} {encIn : α ↪ List Bool}
    {st : α → BareissState} {j : α → ℕ}
    (hst : ComputableInPolyTime st encIn BareissState.enc)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => buildKernelVec (st a) (j a)) encIn (encList encRat) := by
  have hbase : ComputableInPolyTime (fun p : BareissState × ℕ => buildKernelVec p.1 p.2)
      (encPair BareissState.enc encUnary) (encList encRat) := by
    have heq : (fun p : BareissState × ℕ => buildKernelVec p.1 p.2) = fun p =>
        (List.range p.1.table.numCols).map fun c =>
          ((p.1.pivotRows.zip p.1.pivotCols).find? fun pc => pc.2 == c).elim
            (if c = p.2 then 1 else 0)
            (fun pc => Rat.divInt (-Cslib.rowEntry p.1.table.rows pc.1 p.2) p.1.pivotDet) := by
      funext p
      unfold buildKernelVec IntTable.entry
      dsimp only
      refine congrArg (fun f => List.map f (List.range p.1.table.numCols)) ?_
      funext c
      cases (p.1.pivotRows.zip p.1.pivotCols).find? fun pc => pc.2 == c <;> rfl
    rw [heq]
    refine mapWithInput (unary_range' (by fun_prop)) ?_
    exact ComputableInPolyTime.optionElimWithInput
      (findWithInput (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)
  exact hbase.comp (hst.prod hj)

/-- `rationalElim` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem rationalElim_computableInPolyTime :
    ComputableInPolyTime rationalElim RatTable.enc RationalElimResult.enc := by
  let stOf : RatTable → BareissState := fun M => bareissElim (clearDenoms M)
  let pivRowsOf : RatTable → List (List ℚ) := fun M =>
    (stOf M).pivotRows.map (scaledIntRow (stOf M).table (stOf M).pivotDet)
  let zeroRowsOf : RatTable → List (List ℚ) := fun M =>
    List.replicate (M.numRows - (stOf M).pivotRows.length) (List.replicate M.numCols (0 : ℚ))
  let nonPivOf : RatTable → List ℕ := fun M =>
    computeNonPivotCols M.numCols (stOf M).pivotCols
  let kernelOf : RatTable → List (List ℚ) := fun M =>
    (nonPivOf M).map (buildKernelVec (stOf M))
  have heq : rationalElim = fun M =>
      RationalElimResult.mk ⟨M.numRows, M.numCols, pivRowsOf M ++ zeroRowsOf M⟩
        (stOf M).pivotRows.length (stOf M).pivotRows (stOf M).pivotCols
        (nonPivOf M) (kernelOf M) := by
    funext M
    rfl
  rw [heq]
  have hpiv : ComputableInPolyTime pivRowsOf RatTable.enc (encList (encList encRat)) :=
    mapWithInput (by fun_prop) (by fun_prop)
  have hker : ComputableInPolyTime kernelOf RatTable.enc (encList (encList encRat)) :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

/-- `ratRref` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem ratRref_computableInPolyTime :
    ComputableInPolyTime ratRref RatTable.enc RatTable.enc := by
  unfold ratRref
  fun_prop

/-- `ratRank` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem ratRank_computableInPolyTime :
    ComputableInPolyTime ratRank RatTable.enc encUnary := by
  unfold ratRank
  fun_prop

/-- `ratRowBasis` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem ratRowBasis_computableInPolyTime :
    ComputableInPolyTime ratRowBasis RatTable.enc (encList (encList encRat)) := by
  unfold ratRowBasis
  fun_prop

/-- `ratKernelBasis` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem ratKernelBasis_computableInPolyTime :
    ComputableInPolyTime ratKernelBasis RatTable.enc (encList (encList encRat)) := by
  unfold ratKernelBasis
  fun_prop

/-- `ratSolve` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem ratSolve_computableInPolyTime :
    ComputableInPolyTime ratSolve LinearSystemInput.enc LinearSolveResult.enc := by
  let stOf : LinearSystemInput → BareissState := fun sys =>
    bareissElimCols (clearDenoms (augmentRatTable sys.matrix sys.rhs)) sys.matrix.numCols
  let consOf : LinearSystemInput → Bool := fun sys =>
    (List.range sys.matrix.numRows).all fun r =>
      (stOf sys).pivotRows.contains r ||
        decide (Cslib.rowEntry (stOf sys).table.rows r sys.matrix.numCols = 0)
  let solOf : LinearSystemInput → List ℚ := fun sys =>
    (List.range sys.matrix.numCols).map fun c =>
      (((stOf sys).pivotRows.zip (stOf sys).pivotCols).find? fun pc => pc.2 == c).elim 0
        fun pc =>
          Rat.divInt (Cslib.rowEntry (stOf sys).table.rows pc.1 sys.matrix.numCols)
            (stOf sys).pivotDet
  have heq : ratSolve = fun sys =>
      if consOf sys = true then
        LinearSolveResult.mk (some (solOf sys)) (stOf sys).pivotRows (stOf sys).pivotCols
      else
        LinearSolveResult.mk none (stOf sys).pivotRows (stOf sys).pivotCols := by
    funext sys
    unfold ratSolve IntTable.entry
    by_cases hcons : consOf sys = true
    · have hc := hcons
      dsimp only [consOf, stOf] at hc
      simp only [hcons, hc, ↓reduceIte]
      dsimp only [solOf, stOf]
      refine congrArg (fun s => LinearSolveResult.mk (some s) _ _) ?_
      refine congrArg (fun f => List.map f (List.range sys.matrix.numCols)) ?_
      funext c
      cases ((bareissElimCols (clearDenoms (augmentRatTable sys.matrix sys.rhs))
          sys.matrix.numCols).pivotRows.zip
          (bareissElimCols (clearDenoms (augmentRatTable sys.matrix sys.rhs))
            sys.matrix.numCols).pivotCols).find?
          (fun pc => pc.2 == c) <;> rfl
    · have hc := Bool.eq_false_iff.mpr hcons
      dsimp only [consOf, stOf] at hc
      simp only [hcons, hc, Bool.false_eq_true, ↓reduceIte]
      rfl
  rw [heq]
  have hst : ComputableInPolyTime stOf LinearSystemInput.enc BareissState.enc :=
    bareissElimCols_aug_poly
  have hcons : ComputableInPolyTime consOf LinearSystemInput.enc encBool :=
    allWithInput (unary_range' (by fun_prop)) (by fun_prop)
  have hsol : ComputableInPolyTime solOf LinearSystemInput.enc (encList encRat) :=
    mapWithInput (unary_range' (by fun_prop))
      (ComputableInPolyTime.optionElimWithInput
        (findWithInput (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop))
  have hyes : ComputableInPolyTime
      (fun sys => LinearSolveResult.mk (some (solOf sys))
        (stOf sys).pivotRows (stOf sys).pivotCols)
      LinearSystemInput.enc LinearSolveResult.enc := by fun_prop
  have hno : ComputableInPolyTime
      (fun sys => LinearSolveResult.mk none (stOf sys).pivotRows (stOf sys).pivotCols)
      LinearSystemInput.enc LinearSolveResult.enc := by fun_prop
  exact hcons.ite hyes hno

end PolyTimeImpl

end Cslib.LinearAlgebra
