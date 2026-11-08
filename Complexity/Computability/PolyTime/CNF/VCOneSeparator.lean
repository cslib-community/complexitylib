/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.VCOneClosure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup

/-!
# Certified greedy VC-one separator extraction

Delete each coordinate once, keeping it exactly when the reduced projection occurs in the
explicit table. This is the actual algorithm of [ChenJiangZhu2027], Lemma 6.2 (PDF pp. 19–20).
The certificate charges scanning all rows and retained coordinates at every deletion. It supplies
no separator, affine coefficients or runtime as advice. The semantic theorem reuses the existing
signed exact-one separation proof. Closures and all missing rows are computed by `BinaryClosure`.
## Main results

* `greedy_polytime`, `equations_polytime`: actual greedy deletion and complete equation writing.
* `equation_rows_perm`: correspondence with the reviewed original signed clause.
* `equation_separator`, `equations_length`: semantic separation and sharp equation count.

-/

public section

namespace Cslib.Logic.PL.VCOne.BinarySeparator

open Turing.MultiTapeTM

/-- Projection agreement, tested by scanning listed rows and retained coordinates. -/
@[expose] def agrees (rows : List (List Bool)) (y : List Bool) (s : List ℕ) : Bool :=
  rows.any fun x => s.all fun i => x.getD i false == y.getD i false

/-- Try deleting a coordinate and retain it exactly when deletion restores agreement. -/
@[expose] def delete (rows : List (List Bool)) (y : List Bool) (s : List ℕ) (i : ℕ) : List ℕ :=
  let reduced := s.filter fun j => j != i
  if agrees rows y reduced then s else reduced

/-- Visit each explicit coordinate once, updating the actual retained index list. -/
@[expose] def trim (rows : List (List Bool)) (y : List Bool) (todo s : List ℕ) : List ℕ :=
  todo.foldl (delete rows y) s

/-- Full greedy deletion on a unary declared local width. -/
@[expose] def greedy (p : BinaryClosure.Input) (y : List Bool) : List ℕ :=
  trim p.2 y (List.range p.1) (List.range p.1)

/-- Framed local table together with the unwanted candidate bit string. -/
@[expose] def encInput := encPair BinaryClosure.encInput encBits

private theorem agrees_polytime : ComputableInPolyTime
    (fun p : (List (List Bool) × List Bool) × List ℕ => agrees p.1.1 p.1.2 p.2)
    (encPair (encPair (encList encBits) encBits) (encList encUnary)) encBool := by
  unfold agrees
  apply ComputableInPolyTime.anyWithInput (by fun_prop)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  fun_prop

private theorem delete_polytime : ComputableInPolyTime
    (fun p : ((BinaryClosure.Input × List Bool) × List ℕ) × ℕ =>
      delete p.1.1.1.2 p.1.1.2 p.1.2 p.2)
    (encPair (encPair encInput (encList encUnary)) encUnary) (encList encUnary) := by
  have hr : ComputableInPolyTime
      (fun p : ((BinaryClosure.Input × List Bool) × List ℕ) × ℕ =>
        p.1.2.filter fun j => j != p.2)
      (encPair (encPair encInput (encList encUnary)) encUnary) (encList encUnary) := by
    apply ComputableInPolyTime.filterWithInput (by fun_prop)
    fun_prop
  have ht := agrees_polytime.comp (show ComputableInPolyTime
    (fun p : ((BinaryClosure.Input × List Bool) × List ℕ) × ℕ =>
      ((p.1.1.1.2, p.1.1.2), p.1.2.filter fun j => j != p.2)) _ _ from
      ((show ComputableInPolyTime
        (fun p : ((BinaryClosure.Input × List Bool) × List ℕ) × ℕ =>
          (p.1.1.1.2, p.1.1.2)) _ _ from by
            unfold encInput BinaryClosure.encInput; fun_prop).prod hr))
  unfold delete
  exact ht.ite' (by fun_prop) hr

/-- Every deletion preserves order and shrinks the stored index list, on arbitrary input. -/
theorem delete_sublist (rows : List (List Bool)) (y : List Bool) (s : List ℕ) (i : ℕ) :
    List.Sublist (delete rows y s i) s := by
  dsimp only [delete]
  split_ifs
  · exact List.Sublist.refl _
  · exact List.filter_sublist

/-- Uniform actual polynomial binary resources for the whole greedy pass, including its scans. -/
@[fun_prop] theorem greedy_polytime :
    ComputableInPolyTime (fun p : BinaryClosure.Input × List Bool => greedy p.1 p.2)
      encInput (encList encUnary) := by
  have hr : ComputableTidilyInPolyTime
      (fun p : BinaryClosure.Input × List Bool => List.range p.1.1)
      encInput (encList encUnary) := by unfold encInput BinaryClosure.encInput; fun_prop
  exact ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
      (encA := encUnary) (encL := encList encUnary) (encB := encList encUnary)
      ComputableTidilyInPolyTime.id' hr hr delete_polytime.tidy (.const 0)
      (fun p s i _ => by
        simpa only [Nat.add_zero] using
          length_encList_sublist encUnary (delete_sublist p.1.2 p.2 s i)))

private theorem agrees_rows {n : ℕ} (R : Finset (Fin n → Bool))
    (y : Fin n → Bool) (s : List (Fin n)) :
    agrees (BinaryClosure.rows R) (List.ofFn y) (s.map Fin.val) =
      decide (∃ x ∈ R, Set.EqOn x y s.toFinset) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [agrees, BinaryClosure.rows, List.any_eq_true, List.all_eq_true,
    Finset.mem_sort, Finset.mem_image, List.mem_map, beq_iff_eq,
    Set.EqOn, Finset.mem_coe, List.mem_toFinset]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    exact ⟨x, hx, fun i hi => by simpa only [List.getD_ofFn] using h i.val ⟨i, hi, rfl⟩⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨List.ofFn x, ⟨x, hx, rfl⟩, ?_⟩
    rintro i ⟨j, hj, rfl⟩
    simpa only [List.getD_ofFn] using h hj

/-- Greedy list deletion is exactly the reviewed finite-set deletion algorithm. -/
theorem trim_rows {n : ℕ} (R : Finset (Fin n → Bool)) (y : Fin n → Bool)
    (todo s : List (Fin n)) :
    (trim (BinaryClosure.rows R) (List.ofFn y) (todo.map Fin.val) (s.map Fin.val)).toFinset =
      (VCOne.trim R y todo s.toFinset).image Fin.val := by
  induction todo generalizing s with
  | nil => simp only [trim, List.map_nil, List.foldl_nil, VCOne.trim]; ext j; simp
  | cons i todo ih =>
    have hfilter : (s.map Fin.val).filter (fun j => j != i.val) =
        (s.filter fun j => j != i).map Fin.val := by
      rw [List.filter_map]
      congr 1
    have hset : (s.filter fun j => j != i).toFinset = s.toFinset.erase i := by
      ext j
      simp [and_comm]
    simp only [trim, List.map_cons, List.foldl_cons, delete, hfilter]
    rw [agrees_rows, hset]
    by_cases h : ∃ x ∈ R, Set.EqOn x y (s.toFinset.erase i)
    · simpa only [VCOne.trim, h, decide_true, ↓reduceIte, trim] using ih s
    · simpa only [VCOne.trim, h, decide_false, Bool.false_eq_true, ↓reduceIte, hset, trim] using
        ih (s.filter fun j => j != i)

/-- The actual extracted separator uses precisely the original table's greedy scope. -/
theorem greedy_rows {n : ℕ} (R : Finset (Fin n → Bool)) (y : Fin n → Bool) :
    (greedy (n, BinaryClosure.rows R) (List.ofFn y)).toFinset =
      (greedyScope R y).image Fin.val := by
  unfold greedy
  change (trim _ _ (List.range n) (List.range n)).toFinset = _
  have hm : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hm, trim_rows]
  simp [greedyScope, Fin.sort_univ]

private theorem trim_sublist (rows : List (List Bool)) (y : List Bool) (todo s : List ℕ) :
    List.Sublist (trim rows y todo s) s := by
  induction todo generalizing s with
  | nil => exact List.Sublist.refl _
  | cons i todo ih => exact (ih (delete rows y s i)).trans (delete_sublist rows y s i)

/-- Actual separator coordinates remain distinct original coordinates in their original order. -/
theorem greedy_sublist (p : BinaryClosure.Input) (y : List Bool) :
    List.Sublist (greedy p y) (List.range p.1) := trim_sublist _ _ _ _

/-- Write the signed exact-one row, in the original local columns. -/
@[expose] def equation (p : BinaryClosure.Input) (y : List Bool) : Clause ℕ :=
  (greedy p y).map fun i => (i, !y.getD i false)

/-- Each actual equation is written with unary local columns and literal signs. -/
@[fun_prop] theorem equation_polytime : ComputableInPolyTime
    (fun p : BinaryClosure.Input × List Bool => equation p.1 p.2) encInput
    (encList (encPair encUnary encBool)) := by
  unfold equation
  apply ComputableInPolyTime.mapWithInput greedy_polytime
  unfold encInput
  fun_prop

/-- Compute all unwanted closure tuples and write one actual separator for each. -/
@[expose] def equations (p : BinaryClosure.Input) : CNF ℕ :=
  (BinaryClosure.missing p).map (equation p)

/-- The complete closure-to-separator list computation has uniform polynomial binary resources. -/
@[fun_prop] theorem equations_polytime : ComputableInPolyTime equations BinaryClosure.encInput
    (encList (encList (encPair encUnary encBool))) := by
  unfold equations
  exact ComputableInPolyTime.mapWithInput BinaryClosure.missing_polytime equation_polytime

/-- Original literal order is immaterial: the actual row is a permutation of the reviewed signed
clause, after erasing only the bounded index type. Coefficients and polarities are unchanged. -/
theorem equation_rows_perm {n : ℕ} (R : Finset (Fin n → Bool)) (y : Fin n → Bool) :
    (equation (n, BinaryClosure.rows R) (List.ofFn y)).Perm
      ((ExactOne.signedClause (greedyScope R y) (fun i => !y i)).relabel Fin.val) := by
  have hs : (greedy (n, BinaryClosure.rows R) (List.ofFn y)).Perm
      ((greedyScope R y).sort (· ≤ ·) |>.map Fin.val) := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_range (n := n)).sublist (greedy_sublist _ _))
      ((Finset.sort_nodup _ _).map Fin.val_injective)).mpr
    intro i
    rw [← List.mem_toFinset, greedy_rows]
    simp
  have hm := hs.map (fun i => (i, !(List.ofFn y).getD i false))
  simpa only [equation, ExactOne.signedClause, Clause.relabel, List.map_map,
    Function.comp_def, List.getD_ofFn, Prod.map_apply, id_eq] using hm

/-- Exact semantic separator correspondence on all original local assignments. -/
theorem equation_rows_eval {n : ℕ} (R : Finset (Fin n → Bool)) (y : Fin n → Bool)
    (σ : ℕ → Bool) :
    (equation (n, BinaryClosure.rows R) (List.ofFn y)).evalOne σ = true ↔
      ExactOne.Holds (greedyScope R y) (fun i => !y i) (σ ∘ Fin.val) := by
  have hp := equation_rows_perm R y
  have he : (equation (n, BinaryClosure.rows R) (List.ofFn y)).evalOne σ =
      ((ExactOne.signedClause (greedyScope R y) (fun i => !y i)).relabel Fin.val).evalOne σ := by
    unfold Clause.evalOne
    rw [hp.countP_eq]
  rw [he, Clause.evalOne_relabel, ← ExactOne.holds_iff_evalOne]

/-- Each written equation excludes its unwanted point and includes every allowed row. -/
theorem equation_separator {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R)
    (y : Fin n → Bool) (hy : y ∈ closure R \ R) :
    3 ≤ (equation (n, BinaryClosure.rows R) (List.ofFn y)).length ∧
      (∀ x ∈ R, (equation (n, BinaryClosure.rows R) (List.ofFn y)).evalOne
        (fun i => (List.ofFn x).getD i false) = true) ∧
      (equation (n, BinaryClosure.rows R) (List.ofFn y)).evalOne
        (fun i => (List.ofFn y).getD i false) ≠ true := by
  obtain ⟨hs, hin, hout⟩ := greedy_separator R hR y
    (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  have heq (x : Fin n → Bool) :
      ((fun i => (List.ofFn x).getD i false) ∘ Fin.val) = x := by
    funext i
    exact List.getD_ofFn x i false
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · have hp := (equation_rows_perm R y).length_eq
    simp only [Clause.relabel, List.length_map, ExactOne.signedClause,
      Finset.length_sort] at hp
    exact hs.trans_eq hp.symm
  · rw [equation_rows_eval, heq]
    exact hin x hx
  · change ¬ (equation (n, BinaryClosure.rows R) (List.ofFn y)).evalOne _ = true
    rw [equation_rows_eval, heq]
    exact hout

/-- The actual equation count has the sharp width-plus-one-minus-input-table-size bound. -/
theorem equations_length {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R) :
    (equations (n, BinaryClosure.rows R)).length ≤ n + 1 - R.card := by
  simpa only [equations, List.length_map] using BinaryClosure.missing_length R hR

end Cslib.Logic.PL.VCOne.BinarySeparator
