/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.Rectangular
public import CslibFrontier.Computability.PolyTime.Int.ExactDiv
public import CslibFrontier.Computability.GenericRAM.Native.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Int.Cast.Field
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Binary rational original-row selection

An entry is an explicit signed binary numerator/denominator pair. The actual admission test
rejects zero denominators; reduction and positive denominators are unnecessary. One computed
common denominator clears the complete augmented table. The integer backend selects coefficient
rows on consistent inputs and augmented rows otherwise, without basis/rank/solution advice.
Source: [ChenJiangZhu2027], Lemma 3.1 (PDF pp.10–11), crediting Jansen–Pieterse.

The declared coefficient width is unary. Each row has its RHS at that width; missing entries are
zero (0/1), excess columns are ignored. This is an explicit nonsuccinct typed binary frame, not
an untrusted-byte parser or a transfer to a different machine model.

## Main definitions

* `admit`, `denominator`, `clear`: actual validation and integer compilation.
* `select`: tagged original indices, or rejection of an invalid rational frame.

## Main results

* `select_ofData`: all rational systems, exact original solutions, rank and row budgets.
* `basis_selected_iff`, `basis_rank_of_consistent`: actual raw-frame branch semantics.
* `boolean_count`: exact multiplicity on all declared Boolean variables.
* `select_polytime`, `exists_certificate`: complete binary machine time and workspace.

## References

* [ChenJiangZhu2027], Lemma 3.1, PDF pp.10–11.
* Bart M. P. Jansen and Astrid Pieterse, *Optimal sparsification for some binary CSPs
  using low-degree polynomials*, MFCS 2016, article 71,
  DOI: 10.4230/LIPIcs.MFCS.2016.71; journal version, ACM TOCT 11(4), article 28 (2019),
  DOI: 10.1145/3349618. Row-selection attribution follows the cited lemma.
-/

public section

namespace Cslib.LinearSystem.RationalFrontend

open Turing.MultiTapeTM Matrix Circuits.Rational

/-- Signed numerator followed by nonzero signed denominator on admitted inputs. -/
abbrev Fraction := ℤ × ℤ
/-- Framed binary signed numerator, then binary signed denominator. -/
abbrev encFraction : Fraction ↪ List Bool := encPair encIntBin encIntBin
/-- A framed list of explicit rational entries. -/
abbrev encRow : List Fraction ↪ List Bool := encList encFraction
/-- A framed list of framed rational rows. -/
abbrev encTable : List (List Fraction) ↪ List Bool := encList encRow
/-- Unary declared coefficient width and original augmented rows, RHS at column width. -/
abbrev Input := ℕ × List (List Fraction)
/-- Framed unary width followed by the doubly framed binary fraction table. -/
abbrev encInput : Input ↪ List Bool := encPair encUnary encTable
/-- An absence tag rejects an invalid frame; present original indices are unary and list-framed. -/
abbrev encSelection : Option (List ℕ) ↪ List Bool := encOption (encList encUnary)
/-- Original coefficient width, retaining unused variables. -/
@[expose] def width (x : Input) : ℕ := x.1
/-- Original rows, without replacing them by scaled equations. -/
@[expose] def rows (x : Input) : List (List Fraction) := x.2
/-- Missing rational entries have the valid zero representation. -/
@[expose] def entry (x : Input) (i j : ℕ) : Fraction := ((rows x).getD i []).getD j (0, 1)
/-- Materialize only declared augmented columns, including the actual RHS. -/
@[expose] def entries (x : Input) : List Fraction :=
  (List.range (rows x).length).flatMap fun i =>
    (List.range (width x + 1)).map fun j => entry x i j
/-- All actual denominator factors of the augmented table, in original row order. -/
@[expose] def denominators (x : Input) : List ℤ := (entries x).map Prod.snd
/-- Actual binary validity check; the empty table is valid. -/
@[expose] def admit (x : Input) : Bool := (denominators x).all fun z => decide (z ≠ 0)
/-- One computed common denominator, including the RHS and repeated factors. -/
@[expose] def denominator (x : Input) : ℤ := (denominators x).prod
/-- Materialize the complete augmented integer table by exact signed binary division. -/
@[expose] def clear (x : Input) : List (List ℤ) :=
  tabulateTable (rows x).length (width x + 1) fun i j =>
    (entry x i j).1 * (denominator x / (entry x i j).2)
/-- Actual compiled right-hand sides, aligned with the unchanged original row order. -/
@[expose] def rhs (x : Input) : List ℤ := (clear x).map fun row => row.getD (width x) 0
/-- The integer backend tests its computed rational point against every original row. -/
@[expose] def consistent (x : Input) : Bool := rectangularConsistent (width x) (clear x) (rhs x)
/-- The selected indices are original; the inconsistent branch also includes the RHS column. -/
@[expose] def basis (x : Input) : List ℕ :=
  if consistent x then gramRowBasis (width x) (clear x)
  else gramRowBasis (width x + 1) (clear x)
/-- Actual validation, compilation, consistency test and original-row selection. -/
@[expose] def select (x : Input) : Option (List ℕ) := if admit x then some (basis x) else none

/-- A rational entry lookup includes the actual framed-list traversals and unary indices. -/
@[fun_prop] theorem entry_polytime {α : Type} {enc : α ↪ List Bool}
    {x : α → Input} {i j : α → ℕ} (hx : ComputableInPolyTime x enc encInput)
    (hi : ComputableInPolyTime i enc encUnary) (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => entry (x a) (i a) (j a)) enc encFraction := by
  unfold entry rows encInput encTable encRow encFraction at *
  fun_prop

/-- The complete declared augmented table is written by polynomial-time list traversals. -/
@[fun_prop] theorem entries_polytime :
    ComputableInPolyTime entries encInput (encList encFraction) := by
  unfold entries
  apply ComputableInPolyTime.flatMapWithInput (encA := encUnary)
  · unfold rows encInput encTable
    fun_prop
  · apply ComputableInPolyTime.mapWithInput (encA := encUnary)
    · unfold width encInput
      fun_prop
    · apply entry_polytime <;> fun_prop

/-- Denominator materialization and validation include all binary entry reads. -/
@[fun_prop] theorem denominators_polytime :
    ComputableInPolyTime denominators encInput (encList encIntBin) := by
  unfold denominators
  exact (ComputableInPolyTime.map (ComputableInPolyTime.snd encIntBin encIntBin)).comp
    entries_polytime

/-- The admission test is polynomial in actual binary input length. -/
@[fun_prop] theorem admit_polytime : ComputableInPolyTime admit encInput encBool := by
  unfold admit
  fun_prop

/-- Every intermediate binary product is charged by the existing integer product machine. -/
@[fun_prop] theorem denominator_polytime : ComputableInPolyTime denominator encInput encIntBin :=
  ComputableInPolyTime.intBin_prod.comp denominators_polytime

/-- Clearing is polynomial binary time, including products, division and all cell writes. -/
@[fun_prop] theorem clear_polytime : ComputableInPolyTime clear encInput encIntTable := by
  unfold clear
  apply computableInPolyTime_tabulateTable
  · unfold rows encInput encTable
    fun_prop
  · unfold width encInput
    fun_prop
  · dsimp only [TableIndex.ctx, TableIndex.row, TableIndex.col, TableIndex.rowCtx]
    fun_prop

/-- Reading the actual RHS column preserves binary polynomial time. -/
@[fun_prop] theorem rhs_polytime : ComputableInPolyTime rhs encInput (encList encIntBin) := by
  unfold rhs
  apply ComputableInPolyTime.mapWithInput clear_polytime
  unfold width encInput
  fun_prop

/-- The actual compiled consistency test has no supplied solution or rank input. -/
@[fun_prop] theorem consistent_polytime : ComputableInPolyTime consistent encInput encBool := by
  unfold consistent
  have hp := ((show ComputableInPolyTime width encInput encUnary from by
    unfold width encInput; fun_prop).prod clear_polytime).prod rhs_polytime
  exact rectangularConsistent_polytime.comp hp

/-- Both actual row scans, dispatch and tagged original-index output are polynomial binary time. -/
@[fun_prop] theorem select_polytime : ComputableInPolyTime select encInput encSelection := by
  have hn : ComputableInPolyTime width encInput encUnary := by unfold width encInput; fun_prop
  have ha := gramRowBasis_polytime.comp (hn.prod clear_polytime)
  have hn1 := ComputableInPolyTime.unary_add.comp (hn.prod (.const 1))
  have hb := gramRowBasis_polytime.comp (hn1.prod clear_polytime)
  have hbasis : ComputableInPolyTime basis encInput (encList encUnary) :=
    consistent_polytime.ite ha hb
  exact admit_polytime.ite ((ComputableInPolyTime.optionSome _).comp hbasis) (.const none)

/-- A declaration-only width is preserved even when there are no input rows. -/
theorem clear_length (x : Input) : (clear x).length = (rows x).length := by simp [clear]

/-- The actual denominator magnitude has at most the sum of its binary factor widths plus one. -/
theorem denominator_bits_le (x : Input) : (denominator x).natAbs.size ≤
    ((denominators x).map fun z => z.natAbs.size).sum + 1 :=
  Int.size_natAbs_prod_le _

/-- Every admitted rational frame has a nonzero computed common denominator. -/
theorem denominator_ne_zero (x : Input) (hx : admit x = true) : denominator x ≠ 0 := by
  have h := List.all_eq_true.mp hx
  apply List.prod_ne_zero
  intro hz
  exact (of_decide_eq_true (h 0 hz)) rfl

/-- The total interpreted augmented rational row, independently of the integer compiler. -/
@[expose] def rationalRow (x : Input) (i : ℕ) (j : Fin (width x + 1)) : ℚ :=
  ((entry x i j.val).1 : ℚ) / ((entry x i j.val).2 : ℚ)

private theorem denominator_mem (x : Input) (i : Fin (rows x).length)
    (j : Fin (width x + 1)) : (entry x i.val j.val).2 ∈ denominators x := by
  apply List.mem_map.mpr
  refine ⟨entry x i.val j.val, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  exact ⟨i.val, List.mem_range.mpr i.isLt,
    List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩⟩

/-- Each emitted integer entry is the same computed nonzero scalar times its original rational. -/
theorem clear_entry (x : Input) (hx : admit x = true) (i : Fin (rows x).length)
    (j : Fin (width x + 1)) : (rowEntry (clear x) i.val j.val : ℚ) =
      (denominator x : ℚ) * rationalRow x i.val j := by
  have hm := denominator_mem x i j
  have hden : ((entry x i.val j.val).2 : ℚ) ≠ 0 := by
    exact_mod_cast of_decide_eq_true (List.all_eq_true.mp hx _ hm)
  have hd : (entry x i.val j.val).2 ∣ denominator x := List.dvd_prod hm
  simp only [clear, rowEntry_tabulateTable, i.isLt, j.isLt, and_self, ↓reduceIte, Int.cast_mul,
    Int.cast_div hd hden, rationalRow]
  ring

/-- Original rational coefficient row, before the RHS column. -/
@[expose] def coefficientRow (x : Input) (i : ℕ) : Fin (width x) → ℚ :=
  fun j => rationalRow x i j.castSucc
/-- Original rational right-hand side, at the declared augmented last column. -/
@[expose] def rightHandSide (x : Input) (i : ℕ) : ℚ := rationalRow x i (Fin.last (width x))
/-- Satisfying one original equation means its ordinary rational dot-product equality. -/
@[expose] def Satisfies (x : Input) (y : Fin (width x) → ℚ) (i : ℕ) : Prop :=
  coefficientRow x i ⬝ᵥ y = rightHandSide x i

private theorem rhs_entry (x : Input) (i : Fin (rows x).length) :
    (rhs x).getD i.val 0 = rowEntry (clear x) i.val (width x) := by
  simp [rhs, rowEntry, clear_length, i.isLt]

private theorem coefficient_scaled (x : Input) (hx : admit x = true)
    (i : Fin (rows x).length) :
    (fun j : Fin (width x) => (rowEntry (clear x) i.val j.val : ℚ)) =
      (denominator x : ℚ) • coefficientRow x i.val := by
  funext j
  exact clear_entry x hx i j.castSucc

private theorem augmented_scaled (x : Input) (hx : admit x = true)
    (i : Fin (rows x).length) :
    (fun j : Fin (width x + 1) => (rowEntry (clear x) i.val j.val : ℚ)) =
      (denominator x : ℚ) • rationalRow x i.val := by
  funext j
  exact clear_entry x hx i j

private theorem integerEquation_iff (x : Input) (hx : admit x = true)
    (i : Fin (rows x).length) (y : Fin (width x) → ℚ) :
    (fun j : Fin (width x) => (rowEntry (clear x) i.val j.val : ℚ)) ⬝ᵥ y =
      (rhs x).getD i.val 0 ↔ Satisfies x y i.val := by
  have hd : (denominator x : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero x hx
  have hb := clear_entry x hx i (Fin.last (width x))
  simp only [Fin.val_last] at hb
  rw [coefficient_scaled x hx i, rhs_entry x i, hb, smul_dotProduct]
  change (denominator x : ℚ) * (coefficientRow x i.val ⬝ᵥ y) =
    (denominator x : ℚ) * rightHandSide x i.val ↔ _
  exact mul_right_inj' hd

private theorem augmentedEquation_iff (x : Input) (hx : admit x = true)
    (i : Fin (rows x).length) (y : Fin (width x) → ℚ) :
    (fun j : Fin (width x + 1) => (rowEntry (clear x) i.val j.val : ℚ)) ⬝ᵥ
      Fin.snoc y (-1) = 0 ↔ Satisfies x y i.val := by
  have hd : (denominator x : ℚ) ≠ 0 := by exact_mod_cast denominator_ne_zero x hx
  rw [augmented_scaled x hx i, smul_dotProduct, smul_eq_mul, mul_eq_zero]
  simp only [hd, false_or]
  simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    mul_neg_one, ← sub_eq_add_neg]
  exact sub_eq_zero

private theorem integerAll_iff (x : Input) (hx : admit x = true)
    (y : Fin (width x) → ℚ) :
    (∀ i : Fin (clear x).length,
      (fun j : Fin (width x) => (rowEntry (clear x) i.val j.val : ℚ)) ⬝ᵥ y =
        (rhs x).getD i.val 0) ↔ ∀ i : Fin (rows x).length, Satisfies x y i.val := by
  constructor
  · intro h i
    exact (integerEquation_iff x hx i y).mp
      (h ⟨i.val, by simpa only [clear_length] using i.isLt⟩)
  · intro h i
    let j : Fin (rows x).length := ⟨i.val, by simpa only [clear_length] using i.isLt⟩
    exact (integerEquation_iff x hx j y).mpr (h j)

/-- The computed consistency branch is equivalent to existence of an original rational solution. -/
theorem consistent_correct (x : Input) (hx : admit x = true) :
    consistent x = true ↔ ∃ y : Fin (width x) → ℚ,
      ∀ i : Fin (rows x).length, Satisfies x y i.val := by
  have hh := rectangularConsistent_correct (width x) (clear x) (rhs x)
  exact hh.trans (exists_congr fun y => integerAll_iff x hx y)

/-- Every output index names an original row, including in the inconsistent branch. -/
theorem basis_mem (x : Input) (i : ℕ) (hi : i ∈ basis x) : i < (rows x).length := by
  unfold basis at hi
  split_ifs at hi <;> simpa only [clear_length] using gramRowBasis_mem _ (clear x) i hi

/-- All cases retain at most r+1 original rows, without assuming consistency. -/
theorem basis_length (x : Input) : (basis x).length ≤ width x + 1 := by
  unfold basis
  split_ifs
  · exact (gramRowBasis_length _ _).trans (Nat.le_succ _)
  · exact gramRowBasis_length _ _

private theorem basis_getD_mem (x : Input) (i : Fin (basis x).length) :
    (basis x).getD i.val 0 ∈ basis x := by
  rw [List.getD_eq_getElem _ _ i.isLt]
  exact List.getElem_mem _

/-- The actual returned original subsystem has exactly the same rational solutions, even when
inconsistent. Boolean solutions are the restriction to Boolean coordinate words. -/
theorem basis_selected_iff (x : Input) (hx : admit x = true) (y : Fin (width x) → ℚ) :
    (∀ i ∈ basis x, Satisfies x y i) ↔
      ∀ i : Fin (rows x).length, Satisfies x y i.val := by
  constructor
  · intro hy
    by_cases hc : consistent x = true
    · obtain ⟨y₀, hy₀⟩ := (consistent_correct x hx).mp hc
      have hzero : ∀ i : Fin (clear x).length,
          (fun j : Fin (width x) => (rowEntry (clear x) i.val j.val : ℚ)) ⬝ᵥ y₀ =
            (rhs x).getD i.val 0 := by
        exact (integerAll_iff x hx y₀).mpr hy₀
      have hsel : ∀ i : Fin (gramRowBasis (width x) (clear x)).length,
          (indexedRows (width x) (clear x) (gramRowBasis (width x) (clear x))).row i ⬝ᵥ y =
            (rhs x).getD ((gramRowBasis (width x) (clear x)).getD i.val 0) 0 := by
        intro i
        have hi : (gramRowBasis (width x) (clear x)).getD i.val 0 ∈ basis x := by
          simpa only [basis, hc, Bool.false_eq_true, ↓reduceIte] using basis_getD_mem x
            ⟨i.val, by simpa only [basis, hc, Bool.false_eq_true, ↓reduceIte] using i.isLt⟩
        exact (integerEquation_iff x hx ⟨_, basis_mem x _ hi⟩ y).mpr (hy _ hi)
      have hh := (gramRowBasis_selected_iff (width x) (clear x) (rhs x) y₀ hzero y).mp hsel
      exact (integerAll_iff x hx y).mp hh
    · have hzero : ∀ i : Fin (clear x).length,
          (fun j : Fin (width x + 1) => (rowEntry (clear x) i.val j.val : ℚ)) ⬝ᵥ
            (0 : Fin (width x + 1) → ℚ) = (([] : List ℤ).getD i.val 0 : ℚ) := by
        intro i
        simp
      have hsel : ∀ i : Fin (gramRowBasis (width x + 1) (clear x)).length,
          (indexedRows (width x + 1) (clear x) (gramRowBasis (width x + 1) (clear x))).row i
            ⬝ᵥ Fin.snoc y (-1) = (([] : List ℤ).getD
              ((gramRowBasis (width x + 1) (clear x)).getD i.val 0) 0 : ℚ) := by
        intro i
        have hi : (gramRowBasis (width x + 1) (clear x)).getD i.val 0 ∈ basis x := by
          simpa only [basis, hc, Bool.false_eq_true, ↓reduceIte] using basis_getD_mem x
            ⟨i.val, by simpa only [basis, hc, Bool.false_eq_true, ↓reduceIte] using i.isLt⟩
        exact (augmentedEquation_iff x hx ⟨_, basis_mem x _ hi⟩ y).mpr (hy _ hi)
      have hh := (gramRowBasis_selected_iff (width x + 1) (clear x) [] 0 hzero
        (Fin.snoc y (-1))).mp hsel
      intro i
      apply (augmentedEquation_iff x hx i y).mp
      exact hh ⟨i.val, by simpa only [clear_length] using i.isLt⟩
  · intro hy i hi
    exact hy ⟨i, basis_mem x i hi⟩

/-- Consistent inputs retain exactly the ordinary rational coefficient-row rank. The branch is
computed, and no consistency or basis witness is an argument of the executable selector. -/
theorem basis_rank_of_consistent (x : Input) (hx : admit x = true) (hc : consistent x = true) :
    (basis x).length = Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun i : Fin (rows x).length => coefficientRow x i.val))) := by
  have hr := gramRowBasis_rank (width x) (clear x)
  rw [clear_length] at hr
  have hscale : (fun i : Fin (rows x).length =>
      fun j : Fin (width x) => (rowEntry (clear x) i.val j.val : ℚ)) =
        fun i : Fin (rows x).length => (denominator x : ℚ) • coefficientRow x i.val := by
    funext i
    exact coefficient_scaled x hx i
  rw [hscale, Set.range_smul] at hr
  have hd : IsUnit (denominator x : ℚ) := isUnit_iff_ne_zero.mpr (by
    exact_mod_cast denominator_ne_zero x hx)
  rw [Submodule.span_smul_eq_of_isUnit _ _ hd] at hr
  simpa only [basis, hc, ↓reduceIte] using hr

/-- Actual tagged output, original indices, r+1 bound and rational solution equivalence. -/
theorem select_correct (x : Input) (hx : admit x = true) :
    ∃ ids, select x = some ids ∧ ids.length ≤ width x + 1 ∧
      (∀ i ∈ ids, i < (rows x).length) ∧
      ∀ y : Fin (width x) → ℚ, (∀ i ∈ ids, Satisfies x y i) ↔
        ∀ i : Fin (rows x).length, Satisfies x y i.val :=
  ⟨basis x, by simp [select, hx], basis_length x, basis_mem x, basis_selected_iff x hx⟩

open Classical in
/-- Boolean words keep the entire declared dimension and their exact original multiplicity. -/
theorem boolean_count (x : Input) (hx : admit x = true) :
    Fintype.card {z : Fin (width x) → Bool //
      ∀ i ∈ basis x, Satisfies x (fun j => if z j then 1 else 0) i} =
    Fintype.card {z : Fin (width x) → Bool //
      ∀ i : Fin (rows x).length, Satisfies x (fun j => if z j then 1 else 0) i.val} :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun z => basis_selected_iff x hx
    (fun j => if z j then 1 else 0))

/-- Canonical explicit fraction representation of an arbitrary rational. -/
@[expose] def ofRational (q : ℚ) : Fraction := (q.num, q.den)
/-- Every finite rational system has an explicit augmented input in the binary frame. -/
@[expose] def ofData {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) : Input :=
  (n, List.ofFn fun i : Fin m => List.ofFn fun j : Fin (n + 1) =>
    ofRational (Fin.snoc (α := fun _ => ℚ) (A i) (b i) j))

/-- The original semantics accepts every rational, not just integer or common-denominator data. -/
theorem ofRational_value (q : ℚ) : ((ofRational q).1 : ℚ) / ((ofRational q).2 : ℚ) = q := by
  simpa only [ofRational, Int.cast_natCast] using q.num_div_den

private theorem entry_ofData {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (i : Fin m) (j : Fin (n + 1)) : entry (ofData A b) i.val j.val =
      ofRational (Fin.snoc (α := fun _ => ℚ) (A i) (b i) j) := by
  simp only [entry, rows, ofData, List.getD_eq_getElem, List.length_ofFn,
    List.getElem_ofFn, i.isLt, j.isLt]

/-- The canonical encoded augmented row interprets exactly the original rational equation. -/
theorem rationalRow_ofData {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (i : Fin m) (j : Fin (n + 1)) : rationalRow (ofData A b) i.val j =
      Fin.snoc (α := fun _ => ℚ) (A i) (b i) j := by
  change ((entry (ofData A b) i.val j.val).1 : ℚ) /
    ((entry (ofData A b) i.val j.val).2 : ℚ) = _
  rw [entry_ofData, ofRational_value]

/-- Every explicit original rational system passes the actual denominator admission test. -/
theorem admit_ofData {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) :
    admit (ofData A b) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hi' : i < m := by simpa [rows, ofData] using List.mem_range.mp hi
  have hj' : j < n + 1 := by simpa [width, ofData] using List.mem_range.mp hj
  rw [entry_ofData A b ⟨i, hi'⟩ ⟨j, hj'⟩]
  apply decide_eq_true
  change ((Fin.snoc (α := fun _ => ℚ) (A ⟨i, hi'⟩) (b ⟨i, hi'⟩) ⟨j, hj'⟩).den : ℤ) ≠ 0
  exact_mod_cast (Fin.snoc (α := fun _ => ℚ) (A ⟨i, hi'⟩) (b ⟨i, hi'⟩) ⟨j, hj'⟩).den_ne_zero

/-- The rational-input predicate specializes to the original matrix equation, entry for entry. -/
theorem satisfies_ofData {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (y : Fin n → ℚ) (i : Fin m) : Satisfies (ofData A b) y i.val ↔ A i ⬝ᵥ y = b i := by
  have ha : coefficientRow (ofData A b) i.val = A i := by
    funext j
    exact (rationalRow_ofData A b i j.castSucc).trans (Fin.snoc_castSucc _ _ j)
  have hb : rightHandSide (ofData A b) i.val = b i := by
    exact (rationalRow_ofData A b i (Fin.last n)).trans (Fin.snoc_last _ _)
  change (coefficientRow (ofData A b) i.val ⬝ᵥ y = rightHandSide (ofData A b) i.val) ↔ _
  rw [ha, hb]
  exact Iff.rfl

/-- Lemma 3.1 on every original rational matrix/RHS: actual original-row output, at most r+1
rows, exact solution equivalence even for inconsistent systems, and exact coefficient rank
on consistent systems. No selected row, rank or solver advice is supplied. -/
theorem select_ofData {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) :
    ∃ ids, select (ofData A b) = some ids ∧ ids.length ≤ n + 1 ∧
      (∀ i ∈ ids, i < m) ∧
      (∀ y : Fin n → ℚ, (∀ i : Fin m, i.val ∈ ids → A i ⬝ᵥ y = b i) ↔
        ∀ i : Fin m, A i ⬝ᵥ y = b i) ∧
      ((∃ y : Fin n → ℚ, ∀ i : Fin m, A i ⬝ᵥ y = b i) →
        ids.length = Module.finrank ℚ (Submodule.span ℚ (Set.range A))) := by
  let x := ofData A b
  have hx : admit x = true := admit_ofData A b
  have hm : (rows x).length = m := by simp only [x, rows, ofData, List.length_ofFn]
  refine ⟨basis x, ?_, basis_length x, ?_, ?_, ?_⟩
  · change select x = some (basis x)
    simp only [select, hx, ↓reduceIte]
  · intro i hi
    exact (basis_mem x i hi).trans_eq hm
  · intro y
    constructor
    · intro hy
      have hh : ∀ j ∈ basis x, Satisfies x y j := by
        intro j hj
        let j' : Fin m := ⟨j, (basis_mem x j hj).trans_eq hm⟩
        exact (satisfies_ofData A b y j').mpr (hy j' hj)
      have hall := (basis_selected_iff x hx y).mp hh
      intro i
      exact (satisfies_ofData A b y i).mp
        (hall ⟨i.val, by simpa only [hm] using i.isLt⟩)
    · intro hy i _
      exact hy i
  · rintro ⟨y, hy⟩
    have hc : consistent x = true := (consistent_correct x hx).mpr ⟨y, fun i =>
      (satisfies_ofData A b y ⟨i.val, by simpa only [hm] using i.isLt⟩).mpr (hy _)⟩
    have hr := basis_rank_of_consistent x hx hc
    rw [hm] at hr
    have hf : (fun i : Fin m => coefficientRow x i.val) = A := by
      funext i j
      exact (rationalRow_ofData A b i j.castSucc).trans (Fin.snoc_castSucc _ _ j)
    rw [hf] at hr
    exact hr

/-- The whole actual validated selector has an independent polynomial time/workspace certificate,
including binary arithmetic, intermediate tables, all original index writes and rejection tags. -/
theorem exists_certificate : ∃ cs : Cslib.GenericRAM.NativeCertificate select encInput encSelection,
    ∃ C e : ℕ, ∀ x,
      cs.time x ≤ C * ((encInput x).length + 1) ^ e ∧
      cs.space x ≤ C * ((encInput x).length + 1) ^ e := by
  obtain ⟨cs, ht, hs⟩ := Cslib.GenericRAM.NativeCertificate.exists_polynomial select_polytime
  obtain ⟨C, e, h⟩ := (ht.add hs).exists_le
  exact ⟨cs, C, e, fun x => ⟨(Nat.le_add_right _ _).trans (h x),
    (Nat.le_add_left _ _).trans (h x)⟩⟩

end Cslib.LinearSystem.RationalFrontend
