/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.List.BoundedEnumeration
public import CslibFrontier.Computability.PolyTime.CNF.WeightedNormalization
import all CslibFrontier.Logics.Propositional.CNF.WeightedAffine
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Binary weighted query construction

Certified bounded subset traversal, signed-clause filtering, global deduplication
and ordinary CNF boundary writing for [ChenJiangZhu2027], Section 7.1,
Theorem 7.1, equations (24)–(25), PDF pp. 23–24. The demand cap is fixed;
indices are unary, weights and demands signed binary integers. This certifies the
selected-query branch, not the complete encoded counting-plan dispatch.
-/

public section

namespace Cslib.Logic.PL.WeightedRow.BinaryQuery

open Turing.MultiTapeTM

/-- Normalized distinct signed variables with binary weights, paired with binary demand. -/
abbrev RowData := BinaryNormalization.Input
/-- Framed encoding of normalized row data. -/
@[expose] def encRow : RowData ↪ List Bool := BinaryNormalization.encInput
/-- Unary variable / polarity literal encoding. -/
@[expose] def encLiteral : Literal ℕ ↪ List Bool := encPair encUnary encBool
/-- Ordinary CNF as actual framed lists of framed clauses. -/
@[expose] def encCNF : CNF ℕ ↪ List Bool := encList (encList encLiteral)

/-- Select a bounded enumeration using a binary length parameter. Out-of-range values
fall back to length zero. The cap is fixed independently of the input. -/
@[expose] def boundedAt {α : Type} (D : ℕ) (b : ℤ) (l : List α) : List (List α) :=
  match D with
  | 0 => boundedLists l 0
  | D + 1 => if b = (D + 1 : ℕ) then boundedLists l (D + 1) else boundedAt D b l

/-- The fixed-cap dispatch returns the exact existing bounded enumeration. -/
theorem boundedAt_eq {α : Type} (l : List α) (D b : ℕ) (hb : b ≤ D) :
    boundedAt D b l = boundedLists l b := by
  induction D with
  | zero =>
    have : b = 0 := by omega
    subst b
    rfl
  | succ D ih =>
    by_cases he : b = D + 1
    · subst b; simp [boundedAt]
    · have hb' : b ≤ D := by omega
      have he' : (b : ℤ) ≠ (D : ℤ) + 1 := by omega
      simp [boundedAt, he', ih hb']

/-- Fixed-cap binary dispatch and every selected sublist traversal are certified. -/
theorem boundedAt_polytime {α : Type} (enc : α ↪ List Bool) (fallback : α) (D : ℕ) :
    ComputableInPolyTime (fun p : ℤ × List α => boundedAt D p.1 p.2)
      (encPair encIntBin (encList enc)) (encList (encList enc)) := by
  have hbound (k : ℕ) : ComputableInPolyTime
      (fun p : ℤ × List α => boundedLists p.2 k)
      (encPair encIntBin (encList enc)) (encList (encList enc)) := by
    unfold boundedLists
    apply ComputableInPolyTime.flatMapConst
    intro j _
    exact (Cslib.sublistsLen_polytime enc fallback j).comp (by fun_prop)
  induction D with
  | zero => exact hbound 0
  | succ D ih =>
    unfold boundedAt
    have he : ComputableInPolyTime (fun p : ℤ × List α => decide (p.1 = (D + 1 : ℕ)))
        (encPair encIntBin (encList enc)) encBool := by fun_prop
    simpa only [decide_eq_true_eq] using he.ite' (hbound (D + 1)) ih

/-- Sum binary coefficients of a candidate subset. -/
@[expose] def weightSum (t : List BinaryNormalization.Entry) : ℤ :=
  (t.map fun (_, (_, w)) => w).sum

/-- Actual upper-clause writing, at most demand+1 selected variables. -/
@[expose] def upper (d : ℕ) (p : RowData) : CNF ℕ :=
  ((boundedAt (d + 1) (p.2 + 1) p.1).filter fun t => decide (p.2 < weightSum t)).map
    fun t => t.map fun (i, (s, _)) => (i, !s)

/-- Actual attainment-term writing, at most fixed d selected variables. -/
@[expose] def attainment (d : ℕ) (p : RowData) : DNF ℕ :=
  ((boundedAt d d p.1).filter fun t => decide (weightSum t = p.2)).map
    fun t => t.map fun (i, (s, _)) => (i, s)

/-- All-row deduplication uses ordinary encoded literal-list equality. -/
@[expose] def base (d : ℕ) (rows : List RowData) : CNF ℕ :=
  (rows.flatMap (upper d)).dedup

/-- Boundary writing after constant substitution. Original variables remain below n;
auxiliary path variables start at n. All branch tests are unary index/Boolean tests. -/
@[expose] def termClauses (n h : ℕ) (β : Bool) (j : ℕ) (t : Term ℕ) : CNF ℕ :=
  let neg := t.map fun (i, s) => (i, !s)
  if j = 0 then
    if h = 0 then if β then [neg] else [] else [neg ++ [(n, false)]]
  else if j = h then [neg ++ [(n + j - 1, β)]]
  else [neg ++ [(n + j - 1, false), (n + j, true)],
    neg ++ [(n + j - 1, true), (n + j, false)]]

/-- Compile the ordinary query, including every literal and clause write. -/
@[expose] def query (d n : ℕ) (rows : List RowData) (β : Bool) : CNF ℕ :=
  base d rows ++ (List.range rows.length).flatMap fun j =>
    (attainment d (rows.getD j ([], 0))).flatMap
      (termClauses n (rows.length - 1) β j)

section Runtime

@[fun_prop] private theorem weightSum_polytime :
    ComputableInPolyTime weightSum (encList BinaryNormalization.encEntry) encIntBin := by
  unfold weightSum
  fun_prop

private theorem literalMap_polytime (neg : Bool) :
    ComputableInPolyTime (fun t : List BinaryNormalization.Entry =>
      t.map fun (i, (s, _)) => (i, if neg then !s else s))
      (encList BinaryNormalization.encEntry) (encList encLiteral) := by
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  fun_prop

/-- Binary upper-clause enumeration, weight tests and literal writing have polynomial resources. -/
@[fun_prop] theorem upper_polytime (d : ℕ) :
    ComputableInPolyTime (upper d) encRow encCNF := by
  have ht : ComputableInPolyTime (fun p : RowData => p.1) encRow
      (encList BinaryNormalization.encEntry) := by fun_prop
  have hb : ComputableInPolyTime (fun p : RowData => p.2) encRow encIntBin := by fun_prop
  have ha := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_add).comp
    (hb.prod (ComputableInPolyTime.const 1))
  have he := (boundedAt_polytime BinaryNormalization.encEntry (0, false, 0) (d + 1)).comp
    (ha.prod ht)
  have htest : ComputableInPolyTime
      (fun p : RowData × List BinaryNormalization.Entry => decide (p.1.2 < weightSum p.2))
      (encPair encRow (encList BinaryNormalization.encEntry)) encBool :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_lt).comp
      ((hb.comp (ComputableInPolyTime.fst _ _)).prod
        (weightSum_polytime.comp (ComputableInPolyTime.snd _ _)))
  have hf := ComputableInPolyTime.filterWithInput
    (test := fun p t => decide (p.2 < weightSum t)) he htest
  exact ComputableInPolyTime.mapWithInput hf
      ((literalMap_polytime true).comp (ComputableInPolyTime.snd _ _))

/-- Binary attainment tests and term writing are certified for fixed demand cap. -/
@[fun_prop] theorem attainment_polytime (d : ℕ) :
    ComputableInPolyTime (attainment d) encRow encCNF := by
  have ht : ComputableInPolyTime (fun p : RowData => p.1) encRow
      (encList BinaryNormalization.encEntry) := by fun_prop
  have he := (boundedAt_polytime BinaryNormalization.encEntry (0, false, 0) d).comp
    ((ComputableInPolyTime.const (d : ℤ)).prod ht)
  have htest : ComputableInPolyTime
      (fun p : RowData × List BinaryNormalization.Entry => decide (weightSum p.2 = p.1.2))
      (encPair encRow (encList BinaryNormalization.encEntry)) encBool := by
    fun_prop
  have hf := ComputableInPolyTime.filterWithInput
    (test := fun p t => decide (weightSum t = p.2)) he htest
  exact ComputableInPolyTime.mapWithInput hf
      ((literalMap_polytime false).comp (ComputableInPolyTime.snd _ _))

/-- Deduplication is charged after actual all-row upper-clause construction. -/
@[fun_prop] theorem base_polytime (d : ℕ) :
    ComputableInPolyTime (base d) (encList encRow) encCNF := by
  unfold base
  exact (Cslib.dedup_polytime (encList encLiteral) []).comp
    (ComputableInPolyTime.flatMapWithInput (by fun_prop) (by fun_prop))

/-- Constant-substituted boundary clause writing has uniform polynomial resources. -/
@[fun_prop] theorem termClauses_polytime {α : Type} {enc : α ↪ List Bool}
    {n h j : α → ℕ} {β : α → Bool} {t : α → Term ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hh : ComputableInPolyTime h enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) (hβ : ComputableInPolyTime β enc encBool)
    (ht : ComputableInPolyTime t enc (encList encLiteral)) :
    ComputableInPolyTime (fun x => termClauses (n x) (h x) (β x) (j x) (t x)) enc encCNF := by
  have hneg : ComputableInPolyTime
      (fun x => (t x).map fun (i, s) => (i, !s)) enc (encList encLiteral) := by fun_prop
  have hz : ComputableInPolyTime (fun x => decide (j x = 0)) enc encBool := by fun_prop
  have hh0 : ComputableInPolyTime (fun x => decide (h x = 0)) enc encBool := by fun_prop
  have heq : ComputableInPolyTime (fun x => decide (j x = h x)) enc encBool := by fun_prop
  have hfirst : ComputableInPolyTime
      (fun x => [(t x).map (fun (i, s) => (i, !s)) ++ [(n x, false)]]) enc encCNF := by
    fun_prop
  have hlast : ComputableInPolyTime
      (fun x => [(t x).map (fun (i, s) => (i, !s)) ++ [(n x + j x - 1, β x)]])
      enc encCNF := by fun_prop
  have hinner : ComputableInPolyTime (fun x =>
      [(t x).map (fun (i, s) => (i, !s)) ++ [(n x + j x - 1, false), (n x + j x, true)],
        (t x).map (fun (i, s) => (i, !s)) ++ [(n x + j x - 1, true), (n x + j x, false)]])
      enc encCNF := by fun_prop
  have hone : ComputableInPolyTime
      (fun x => [(t x).map fun (i, s) => (i, !s)]) enc encCNF := by fun_prop
  simpa only [termClauses, decide_eq_true_eq] using
    hz.ite' (hh0.ite' (hβ.ite' hone (ComputableInPolyTime.const [])) hfirst)
      (heq.ite' hlast hinner)

/-- Uniform polynomial binary time and stage space for complete query output at each fixed d. -/
@[fun_prop] theorem query_polytime (d : ℕ) :
    ComputableInPolyTime (fun p : (ℕ × List RowData) × Bool =>
      let ((n, rows), β) := p
      query d n rows β)
      (encPair (encPair encUnary (encList encRow)) encBool) encCNF := by
  let encI := encPair (encPair encUnary (encList encRow)) encBool
  have hn : ComputableInPolyTime (fun p : (ℕ × List RowData) × Bool => p.1.1)
      encI encUnary := by fun_prop
  have hr : ComputableInPolyTime (fun p : (ℕ × List RowData) × Bool => p.1.2)
      encI (encList encRow) := by fun_prop
  have hb : ComputableInPolyTime (fun p : (ℕ × List RowData) × Bool => p.2)
      encI encBool := by fun_prop
  have hl : ComputableInPolyTime (fun p : (ℕ × List RowData) × Bool => p.1.2.length)
      encI encUnary := by fun_prop
  have ht : ComputableInPolyTime
      (fun p : ((ℕ × List RowData) × Bool) × ℕ => attainment d (p.1.1.2.getD p.2 ([], 0)))
      (encPair encI encUnary) encCNF := by
    apply (attainment_polytime d).comp
    exact ComputableInPolyTime.listGetDWithInput (hr.comp (ComputableInPolyTime.fst _ _))
      (by fun_prop) ([], 0)
  have hm : ComputableInPolyTime
      (fun p : (ℕ × List RowData) × Bool => p.1.2.length - 1) encI encUnary := by fun_prop
  have hpar := ComputableInPolyTime.fst (encPair encI encUnary) (encList encLiteral)
  have hctx := (ComputableInPolyTime.fst encI encUnary).comp hpar
  have hw := termClauses_polytime (hn.comp hctx) (hm.comp hctx)
    ((ComputableInPolyTime.snd encI encUnary).comp hpar) (hb.comp hctx)
    (ComputableInPolyTime.snd (encPair encI encUnary) (encList encLiteral))
  have h : ComputableInPolyTime
      (fun p : (ℕ × List RowData) × Bool => query d p.1.1 p.1.2 p.2) encI encCNF := by
    unfold query
    exact ComputableInPolyTime.listAppend' ((base_polytime d).comp hr)
      (ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hl)
        (ComputableInPolyTime.flatMapWithInput ht hw))
  exact h.of_enc_eq fun _ => rfl

end Runtime

/-- Serialize an actual capped row in its canonical support order. -/
@[expose] def ofRow {n d : ℕ} (R : Row (Fin n) d) : RowData :=
  ((supportList R).map fun (i : Fin n) => ((i : ℕ), (R.sign i, (R.weight i : ℤ))), R.demand)

private theorem sublistsLen_map {α β : Type} (f : α → β) (l : List α) (k : ℕ) :
    (l.map f).sublistsLen k = (l.sublistsLen k).map (List.map f) := by
  induction l generalizing k with
  | nil => cases k <;> simp
  | cons a l ih =>
    cases k <;> simp [List.sublistsLen_succ_cons, ih, List.map_map, Function.comp_def]

private theorem boundedLists_map {α β : Type} (f : α → β) (l : List α) (k : ℕ) :
    boundedLists (l.map f) k = (boundedLists l k).map (List.map f) := by
  simp [boundedLists, sublistsLen_map, List.map_flatMap]

private theorem weight_cast {n d : ℕ} (R : Row (Fin n) d) (t : List (Fin n)) :
    (t.map fun i => (R.weight i : ℤ)).sum = (((t.map R.weight).sum : ℕ) : ℤ) := by
  simpa only [List.map_map, Function.comp_def] using
    (Nat.cast_list_sum (R := ℤ) (t.map R.weight)).symm

/-- The binary upper writer emits the exact reviewed clauses with natural variable indices. -/
theorem upper_ofRow {n d : ℕ} (R : Row (Fin n) d) :
    upper d (ofRow R) = (upperList R).relabel Fin.val := by
  have he := boundedAt_eq
    ((supportList R).map fun (i : Fin n) => ((i : ℕ), (R.sign i, (R.weight i : ℤ))))
    (d + 1) (R.demand + 1) (by have := R.bounded; omega)
  simp only [Nat.cast_add, Nat.cast_one] at he
  simp only [upper, ofRow, he, boundedLists_map, List.filter_map, List.map_map,
    Function.comp_def, weightSum, upperList, CNF.relabel, Clause.relabel]
  congr 1
  simp only [weight_cast, Int.ofNat_lt]

/-- Attainment writing agrees with the reviewed DNF, including the empty true term. -/
theorem attainment_ofRow {n d : ℕ} (R : Row (Fin n) d) :
    attainment d (ofRow R) = (attainmentList R).map (Clause.relabel Fin.val) := by
  simp only [attainment, ofRow, boundedAt_eq _ d d (by omega), boundedLists_map,
    List.filter_map, List.map_map, Function.comp_def, weightSum, attainmentList, Clause.relabel]
  congr 1
  simp only [weight_cast, Int.natCast_inj]

/-- Global deduplication preserves the exact reviewed base after injective index erasure. -/
theorem base_ofRows {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) :
    base d ((List.finRange (h + 1)).map fun j => ofRow (R j)) =
      (executableBase R).relabel Fin.val := by
  have hi : Function.Injective (Clause.relabel (Fin.val : Fin n → ℕ)) := by
    apply List.map_injective_iff.mpr
    intro a b he
    exact Prod.ext (Fin.ext (congrArg (fun p : ℕ × Bool => p.1) he))
      (congrArg (fun p : ℕ × Bool => p.2) he)
  simp only [base, executableBase, List.flatMap_map, upper_ofRow,
    CNF.relabel, ← List.map_flatMap]
  exact List.dedup_map_of_injective hi _

/-- Original and auxiliary variables occupy disjoint declared index intervals. -/
@[expose] def flattenVar {n h : ℕ} : Fin n ⊕ Fin h → ℕ :=
  Sum.elim Fin.val (fun j => n + j)

/-- Constant-substituted binary boundary writing is the reviewed ordinary clause writer. -/
theorem termClauses_eq {n h : ℕ} (β : Bool) (j : Fin (h + 1)) (t : Term (Fin n)) :
    termClauses n h β j (Clause.relabel Fin.val t) =
      (TwoBoundary.termClauses h β j t).relabel (flattenVar (n := n)) := by
  have hj := j.isLt
  have hn : (j : ℕ) ≠ h + 1 := by omega
  by_cases hz : h = 0
  · subst h
    have he : j = 0 := Fin.ext (by omega)
    subst j
    cases β <;> simp [termClauses, TwoBoundary.termClauses, TwoBoundary.lowerClause,
      TwoBoundary.port, flattenVar, CNF.relabel, Clause.relabel, List.filterMap_map]
  · by_cases hf : (j : ℕ) = 0
    · cases β <;> simp [termClauses, TwoBoundary.termClauses, TwoBoundary.lowerClause,
        TwoBoundary.port, flattenVar, CNF.relabel, Clause.relabel, List.filterMap_map, hf, hz]
    · by_cases hl : (j : ℕ) = h
      · have he : n + h - 1 = n + (h - 1) := by omega
        cases β <;> simp [termClauses, TwoBoundary.termClauses, TwoBoundary.lowerClause,
          TwoBoundary.port, flattenVar, CNF.relabel, Clause.relabel, List.filterMap_map,
          hl, hz, he]
      · have he : n + (j : ℕ) - 1 = n + ((j : ℕ) - 1) := by omega
        simp [termClauses, TwoBoundary.termClauses, TwoBoundary.lowerClause,
          TwoBoundary.port, flattenVar, CNF.relabel, Clause.relabel, List.filterMap_map,
          hf, hl, hn, he, Function.comp_def]

/-- The certified binary writer emits precisely the reviewed ordinary query, with injectively
flattened original/auxiliary variable indices. No oracle answer is supplied. -/
theorem query_ofRows {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) (β : Bool) :
    query d n ((List.finRange (h + 1)).map fun j => ofRow (R j)) β =
      (executableQuery R β).relabel (flattenVar (n := n)) := by
  have hg (j : Fin (h + 1)) :
      ((List.finRange (h + 1)).map fun i => ofRow (R i)).getD j ([], 0) = ofRow (R j) := by
    simp [List.getD_eq_getElem?_getD, j.isLt]
  simp only [query, List.length_map, List.length_finRange, Nat.add_sub_cancel, base_ofRows]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, hg, attainment_ofRow, termClauses_eq]
  simp [executableQuery, TwoBoundary.query, CNF.relabel, Clause.relabel, List.map_append,
    List.map_flatMap, List.map_map, Function.comp_def, flattenVar]

/-- Convert an original binary occurrence row to canonical normalized/capped signed row data. -/
@[expose] def normalizedData (n : ℕ) (p : BinaryNormalization.Input) : RowData :=
  (((List.range n).filter fun i => decide (0 < BinaryNormalization.difference p i)).map
    (fun i => (i, (BinaryNormalization.sign n p i, BinaryNormalization.weight n p i))),
      BinaryNormalization.demand n p)

/-- Retained normalized data in original order; the backend tracks invalid rows separately. -/
@[expose] def preparedRows (n : ℕ) (rows : List BinaryNormalization.Input) : List RowData :=
  (rows.filter (BinaryNormalization.retained n)).map (normalizedData n)

/-- Select the actual original capped rows using the certified computed Gram basis. -/
@[expose] def selectedRows (n : ℕ) (rows : List BinaryNormalization.Input) : List RowData :=
  let A := (BinaryNormalization.materialize n rows).1
  let ids := LinearSystem.gramRowBasis n A
  let prepared := preparedRows n rows
  ids.map fun i => prepared.getD i ([], 0)

/-- Actual original-input selected-row query writing, without supplied normalized rows or basis. -/
@[expose] def selectedQuery (d n : ℕ) (rows : List BinaryNormalization.Input)
    (β : Bool) : CNF ℕ :=
  query d n (selectedRows n rows) β

/-- Canonical normalization data writing is uniformly binary polynomial time/space. -/
@[fun_prop] theorem normalizedData_polytime {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {p : α → BinaryNormalization.Input}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc BinaryNormalization.encInput) :
    ComputableInPolyTime (fun x => normalizedData (n x) (p x)) enc encRow := by
  have hpos : ComputableInPolyTime
      (fun z : α × ℕ => decide (0 < BinaryNormalization.difference (p z.1) z.2))
      (encPair enc encUnary) encBool :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_isPos).comp
      (BinaryNormalization.difference_polytime (hp.comp (ComputableInPolyTime.fst _ _))
        (by fun_prop))
  have hs := ComputableInPolyTime.filterWithInput
    (test := fun x i => decide (0 < BinaryNormalization.difference (p x) i))
    (ComputableInPolyTime.range.comp hn) hpos
  unfold normalizedData
  exact (ComputableInPolyTime.mapWithInput hs (by fun_prop)).prod
    (BinaryNormalization.demand_polytime hn hp)

/-- Original-row filtering and normalized-data writing include their encoded output costs. -/
@[fun_prop] theorem preparedRows_polytime :
    ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => preparedRows p.1 p.2)
      (encPair encUnary (encList BinaryNormalization.encInput)) (encList encRow) := by
  unfold preparedRows
  fun_prop

/-- Original-row selection is composed with actual binary normalization and lookup. -/
@[fun_prop] theorem selectedRows_polytime :
    ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => selectedRows p.1 p.2)
      (encPair encUnary (encList BinaryNormalization.encInput)) (encList encRow) := by
  have hn : ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => p.1)
      (encPair encUnary (encList BinaryNormalization.encInput)) encUnary := by fun_prop
  have hA := BinaryNormalization.materialize_polytime.fst'
  have hi := LinearSystem.gramRowBasis_polytime.comp (hn.prod hA)
  unfold selectedRows
  exact ComputableInPolyTime.mapWithInput hi
    (ComputableInPolyTime.listGetDWithInput
      (preparedRows_polytime.comp (ComputableInPolyTime.fst _ _)) (by fun_prop) ([], 0))

/-- Fixed-d polynomial binary resources through original normalization, Gram selection,
bounded subset enumeration, global deduplication and all ordinary query writes. -/
@[fun_prop] theorem selectedQuery_polytime (d : ℕ) :
    ComputableInPolyTime (fun p : (ℕ × List BinaryNormalization.Input) × Bool =>
      let ((n, rows), β) := p
      selectedQuery d n rows β)
      (encPair (encPair encUnary (encList BinaryNormalization.encInput)) encBool) encCNF := by
  have hrows := selectedRows_polytime.comp
    (ComputableInPolyTime.fst (encPair encUnary (encList BinaryNormalization.encInput)) encBool)
  have hn : ComputableInPolyTime
      (fun p : (ℕ × List BinaryNormalization.Input) × Bool => p.1.1)
      (encPair (encPair encUnary (encList BinaryNormalization.encInput)) encBool) encUnary := by
    fun_prop
  exact (query_polytime d).comp ((hn.prod hrows).prod (by fun_prop))

/-- Compute the dispatcher diagnostics and both query branches together. Direct-answer
serialization is deliberately separate; these queries are interpreted only in the query case. -/
@[expose] def originalQueryStage (d n : ℕ) (rows : List BinaryNormalization.Input) :
    (Bool × (List ℕ × (Bool × Bool))) × (CNF ℕ × CNF ℕ) :=
  (BinaryNormalization.analyze n rows,
    (selectedQuery d n rows false, selectedQuery d n rows true))

/-- One composed machine charges the simultaneous diagnostics and both CNF outputs,
including peak workspace and output writes, with no supplied resource advice. -/
@[fun_prop] theorem originalQueryStage_polytime (d : ℕ) :
    ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input =>
      originalQueryStage d p.1 p.2)
      (encPair encUnary (encList BinaryNormalization.encInput))
      (encPair (encPair encBool (encPair (encList encUnary) (encPair encBool encBool)))
        (encPair encCNF encCNF)) := by
  have hf := (selectedQuery_polytime d).comp
    ((ComputableInPolyTime.id').prod (ComputableInPolyTime.const false))
  have ht := (selectedQuery_polytime d).comp
    ((ComputableInPolyTime.id').prod (ComputableInPolyTime.const true))
  exact BinaryNormalization.analyze_polytime.prod (hf.prod ht)

/-- The serialized normalized data is the actual reviewed capped row. -/
theorem normalizedData_ofOccurrences {n m d : ℕ} (R : Occurrences n m)
    (hd : R.demand ≤ d) (hv : 0 ≤ R.shifted ∧ R.shifted ≤ (R.total : ℤ)) :
    normalizedData n (BinaryNormalization.ofOccurrences R) = ofRow (R.toRow d hd) := by
  simp [normalizedData, ← List.map_coe_finRange_eq_range, List.filter_map, List.map_map,
    BinaryNormalization.difference_ofOccurrences, BinaryNormalization.sign_ofOccurrences,
    BinaryNormalization.weight_ofOccurrences R hv, BinaryNormalization.demand_ofOccurrences R hv,
    ofRow, supportList, Occurrences.toRow, Function.comp_def]

private theorem preparedRows_original {n t d : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) (js : List (Fin t)) :
    preparedRows n (js.map fun j => BinaryNormalization.ofOccurrences (R j)) =
      (cappedRows (js.map fun j => (R j).normalize d (hd j))).map ofRow := by
  induction js with
  | nil => simp [preparedRows, cappedRows]
  | cons j js ih =>
    by_cases hv : 0 ≤ (R j).shifted ∧ (R j).shifted ≤ ((R j).total : ℤ)
    · by_cases hz : (R j).total = 0
      · have hshift : (R j).shifted = 0 := by rw [hz] at hv; omega
        simpa [preparedRows, BinaryNormalization.retained,
          BinaryNormalization.valid_ofOccurrences, BinaryNormalization.total_ofOccurrences,
          Occurrences.normalize, hz, hshift, cappedRows] using ih
      · simpa [preparedRows, BinaryNormalization.retained,
          BinaryNormalization.valid_ofOccurrences, BinaryNormalization.total_ofOccurrences,
          Occurrences.normalize, hv, hz, cappedRows,
          normalizedData_ofOccurrences (R j) (hd j) hv] using congrArg
            (List.cons (ofRow ((R j).toRow d (hd j)))) ih
    · simpa [preparedRows, BinaryNormalization.retained,
        BinaryNormalization.valid_ofOccurrences, Occurrences.normalize, hv, cappedRows] using ih

/-- Exact normalized original-row list correspondence before computed basis lookup. -/
theorem preparedRows_ofOccurrences {n t d : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    preparedRows n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
      (cappedRows ((List.finRange t).map fun j => (R j).normalize d (hd j))).map ofRow :=
  preparedRows_original R hd _

/-- Every emitted selected row is the actual row chosen by the reviewed computed basis. -/
theorem selectedRows_ofOccurrences {n t d : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d) :
    let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
    selectedRows n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
      (List.finRange (cappedBasis ns).length).map fun i => ofRow (selectedCappedRow ns i) := by
  dsimp only
  simp only [selectedRows, BinaryNormalization.materialize_ofOccurrences R hd,
    preparedRows_ofOccurrences R hd]
  let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
  change ((cappedBasis ns).map fun i => ((cappedRows ns).map ofRow).getD i ([], 0)) =
    (List.finRange (cappedBasis ns).length).map fun i => ofRow (selectedCappedRow ns i)
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hi' : i < (cappedBasis ns).length := by simpa using hi
  have hb := (cappedIndex ns ⟨i, hi'⟩).isLt
  simp only [cappedIndex, List.getD_eq_getElem _ _ hi'] at hb
  simp [List.getD_eq_getElem?_getD, hb, selectedCappedRow, cappedIndex]

/-- Original and path indices remain within the full declared variable interval. -/
theorem flattenVar_lt {n h : ℕ} (v : Fin n ⊕ Fin h) :
    flattenVar v < n + h := by
  cases v with
  | inl i => simp only [flattenVar, Sum.elim_inl]; omega
  | inr i => simp only [flattenVar, Sum.elim_inr]; omega

/-- Flattening does not identify original or auxiliary variables. -/
theorem flattenVar_injective {n h : ℕ} :
    Function.Injective (flattenVar : Fin n ⊕ Fin h → ℕ) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext he)
    | inr b => have := a.isLt; simp only [flattenVar, Sum.elim_inl, Sum.elim_inr] at he; omega
  | inr a =>
    cases b with
    | inl b => have := b.isLt; simp only [flattenVar, Sum.elim_inl, Sum.elim_inr] at he; omega
    | inr b =>
      simp only [flattenVar, Sum.elim_inr] at he
      exact congrArg Sum.inr (Fin.ext (by omega))

/-- Actual ordinary-query output preserves the established literal-width bound. -/
theorem query_ofRows_width {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) (β : Bool)
    (c : Clause ℕ) (hc : c ∈ query d n ((List.finRange (h + 1)).map fun j => ofRow (R j)) β) :
    c.length ≤ d + 2 := by
  rw [query_ofRows] at hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  simpa only [Clause.relabel, List.length_map] using executableQuery_width R β a ha

/-- Every variable actually written fits the declared original-plus-path index range. -/
theorem query_ofRows_index {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) (β : Bool)
    (c : Clause ℕ) (hc : c ∈ query d n ((List.finRange (h + 1)).map fun j => ofRow (R j)) β)
    (l : Literal ℕ) (hl : l ∈ c) : l.1 < n + h := by
  rw [query_ofRows] at hc
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
  exact flattenVar_lt v.1

/-- Global deduplication retains the sharp per-query polynomial clause budget. -/
theorem query_ofRows_polynomial {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) (β : Bool) :
    (query d n ((List.finRange (h + 1)).map fun j => ofRow (R j)) β).length ≤
      (d + 2) * (2 * n + 1) ^ (d + 1) + 2 * ((h + 1) * ((d + 1) * (n + 1) ^ d)) := by
  rw [query_ofRows]
  simpa only [CNF.relabel, List.length_map] using executableQuery_polynomial R β

/-- Query-branch correspondence for the computed original-row basis. The shape equality is
used only to state the finite index type; the certified program computes the basis itself. -/
theorem selectedQuery_ofOccurrences {n t d k : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j))
    (hd : ∀ j, (R j).demand ≤ d)
    (hk : k + 1 = (cappedBasis ((List.finRange t).map fun j => (R j).normalize d (hd j))).length)
    (β : Bool) :
    let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
    selectedQuery d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) β =
      (executableQuery (fun i : Fin (k + 1) => selectedCappedRow ns (Fin.cast hk i)) β).relabel
        (flattenVar (n := n)) := by
  dsimp only
  let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
  have hs : selectedRows n
      ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
        (List.finRange (k + 1)).map fun i => ofRow (selectedCappedRow ns (Fin.cast hk i)) := by
    calc
      _ = List.ofFn (fun i => ofRow (selectedCappedRow ns i)) := by
        simpa only [List.ofFn_eq_map] using selectedRows_ofOccurrences R hd
      _ = List.ofFn (fun i : Fin (k + 1) => ofRow (selectedCappedRow ns (Fin.cast hk i))) :=
        List.ofFn_congr hk.symm _
      _ = _ := List.ofFn_eq_map
  rw [selectedQuery, hs, query_ofRows]

private theorem boundedAt_sublist {α : Type} (D : ℕ) (b : ℤ) (l t : List α)
    (ht : t ∈ boundedAt D b l) : t.Sublist l := by
  induction D with
  | zero => exact (mem_boundedLists.mp ht).1
  | succ D ih =>
    unfold boundedAt at ht
    split_ifs at ht
    · exact (mem_boundedLists.mp ht).1
    · exact ih ht

/-- Every candidate-weight partial sum has bit growth controlled by its actual framed row input. -/
theorem candidate_prefix_bits (p : RowData) (D : ℕ) (b : ℤ)
    (t : List BinaryNormalization.Entry) (ht : t ∈ boundedAt D b p.1) (k : ℕ) :
    (((t.map fun (e : BinaryNormalization.Entry) =>
      let (_, (_, w)) := e; w).take k).sum).natAbs.size ≤
      (encRow p).length + p.1.length := by
  have hsub := boundedAt_sublist D b p.1 t ht
  have he := Int.size_natAbs_sum_le (b := (encRow p).length)
    (l := (t.map fun (e : BinaryNormalization.Entry) =>
      let (_, (_, w)) := e; w).take k) (by
      intro z hz
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hz)
      rcases e with ⟨j, s, w⟩
      exact BinaryNormalization.entry_bits_le_input p j s w (hsub.subset he))
  have hl : ((t.map fun (e : BinaryNormalization.Entry) =>
      let (_, (_, w)) := e; w).take k).length ≤ p.1.length :=
    (List.length_take_le' _ _).trans (by simpa only [List.length_map] using hsub.length_le)
  exact he.trans (Nat.add_le_add_left ((Nat.size_le_self _).trans hl) _)

/-- The established exact candidate budget applies to the certified bounded traversal. -/
theorem upper_candidate_bound {n d : ℕ} (R : Row (Fin n) d) :
    (boundedAt (d + 1) ((ofRow R).2 + 1) (ofRow R).1).length ≤
      (R.demand + 2) * ((supportList R).length + 1) ^ (R.demand + 1) := by
  have h := boundedAt_eq (ofRow R).1 (d + 1) (R.demand + 1)
    (by have := R.bounded; omega)
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [show (ofRow R).2 = (R.demand : ℤ) from rfl, h]
  simpa only [ofRow, List.length_map] using boundedLists_polynomial (ofRow R).1 (R.demand + 1)

/-- Output storage follows from the constructed machine certificate, not conversely. -/
theorem selectedQuery_output_polyBounded (d : ℕ) :
    PolyBounded
      (fun p : (ℕ × List BinaryNormalization.Input) × Bool =>
        (encPair (encPair encUnary (encList BinaryNormalization.encInput)) encBool p).length)
      (fun p => let ((n, rows), β) := p; (encCNF (selectedQuery d n rows β)).length) :=
  ((ComputableInPolyTime.encoding_length _).comp (selectedQuery_polytime d)).polyBounded

end Cslib.Logic.PL.WeightedRow.BinaryQuery
