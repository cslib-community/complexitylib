/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOnePathPlan
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Sort

/-!
# Executable indexed Exact Cover transposition

[ChenJiangZhu2027], Corollary 5.4, PDF p.18, uses the number of indexed candidate sets,
not the universe size, as its exponential parameter. The actual incidence-list transpose scans
candidate indices once per declared universe element. Membership ignores repeated incidences;
equal or empty candidates retain distinct original bits. An uncovered element writes an empty
exact-one row. No rank, selected subsystem or count is supplied.

The universe is explicitly declared in unary. Candidate elements are binary indices; source
inputs use indices below the declaration. The total program intersects arbitrary raw lists with
the declared universe, and `admit` recognizes that source promise. This is an encoded-value API,
not a parser for malformed bit strings.

## Main results

* `backend_polytime`, `compile_polytime`: actual transpose and complete dispatcher resources.
* `backend_eq`: exact finite equation correspondence, retaining candidate indices.
* `compile_count`, `compile_withinBudget`: original counts and actual query bounds.
-/

public section

namespace Cslib.Logic.PL.ExactCover

open Turing.MultiTapeTM

/-- Unary universe declaration and indexed candidate lists with binary element labels. -/
abbrev Input := ℕ × List (List ℕ)
/-- Number of explicitly declared universe elements. -/
@[expose] def universeSize (x : Input) : ℕ := x.1
/-- Original candidate lists in their original index order, including empty/repeated sets. -/
@[expose] def candidates (x : Input) : List (List ℕ) := x.2
/-- Number of original selection bits; it is computed from the actual candidate list. -/
abbrev size (x : Input) : ℕ := (candidates x).length
/-- Pair encoding: frame the unary universe declaration, then concatenate framed candidate
lists, each of which concatenates framed binary natural element indices. -/
abbrev encInput : Input ↪ List Bool := encPair encUnary (encList (encList encNat))
/-- One transpose request: candidate lists followed by one binary universe element. -/
abbrev RowRequest := List (List ℕ) × ℕ
/-- Frame the concatenation of framed binary candidate lists, followed by the binary element. -/
abbrev encRowRequest : RowRequest ↪ List Bool := encPair (encList (encList encNat)) encNat
/-- Actually test incidence by scanning the original candidate at index i. -/
@[expose] def member (p : RowRequest × ℕ) : Bool :=
  let ((sets, element), i) := p
  (sets.getD i []).any fun a => decide (a = element)
/-- Actual transposed positive exact-one row; each candidate index occurs at most once. -/
@[expose] def row (p : RowRequest) : Clause ℕ :=
  let (sets, element) := p
  ((List.range sets.length).filter fun i => member ((sets, element), i)).map fun i => (i, true)
/-- Materialize all original equations, without enumerating assignments or subsets. -/
@[expose] def transpose (x : Input) : CNF ℕ :=
  (List.range (universeSize x)).map fun v => row (candidates x, v)
/-- Source admission: every listed incidence belongs to the explicitly declared universe. -/
@[expose] def admit (x : Input) : Bool :=
  (candidates x).all fun a => a.all fun v => decide (v < universeSize x)
/-- Actual exact-one backend input, with one variable per original candidate index. -/
@[expose] def backend (x : Input) : ExactOne.BinaryPlan.Input :=
  (size x, [], transpose x)
/-- Actual original-input direct/rank/candidate/two-query dispatcher. -/
@[expose] def compile (x : Input) : ExactOne.BinaryPlan.Output :=
  ExactOne.BinaryPlan.compile (backend x)

private theorem member_polytime :
    ComputableInPolyTime member (encPair encRowRequest encUnary) encBool := by
  have hget : ComputableInPolyTime
      (fun p : RowRequest × ℕ => p.1.1.getD p.2 [])
      (encPair encRowRequest encUnary) (encList encNat) := by
    unfold encRowRequest
    fun_prop
  have he : ComputableInPolyTime
      (fun p : (RowRequest × ℕ) × ℕ => decide (p.2 = p.1.1.2))
      (encPair (encPair encRowRequest encUnary) encNat) encBool := by
    have hleft : ComputableTidilyInPolyTime (fun p : (RowRequest × ℕ) × ℕ => p.2)
        (encPair (encPair encRowRequest encUnary) encNat) encNat := by fun_prop
    have hright : ComputableTidilyInPolyTime (fun p : (RowRequest × ℕ) × ℕ => p.1.1.2)
        (encPair (encPair encRowRequest encUnary) encNat) encNat := by
      unfold encRowRequest
      fun_prop
    exact .of_tidy ((ComputableTidilyInPolyTime.decide_eq encNat).comp (hleft.prod hright))
  exact ComputableInPolyTime.anyWithInput hget he

private theorem row_polytime :
    ComputableInPolyTime row encRowRequest (encList (encPair encNat encBool)) := by
  have hr : ComputableInPolyTime (fun p : RowRequest => List.range p.1.length)
      encRowRequest (encList encUnary) := by
    unfold encRowRequest
    fun_prop
  have hf := ComputableInPolyTime.filterWithInput
    (test := fun q i => member (q, i)) hr member_polytime
  have hm : ComputableInPolyTime (fun i : ℕ => (i, true)) encUnary (encPair encNat encBool) := by
    fun_prop
  exact hm.map.comp hf

/-- Every incidence lookup, element comparison and output row/literal write has polynomial
binary time in the actual original encoding; there is no restriction on incidence density. -/
@[fun_prop] theorem backend_polytime :
    ComputableInPolyTime backend encInput ExactOne.BinaryPlan.encInput := by
  have hu : ComputableInPolyTime universeSize encInput encUnary := by
    unfold universeSize encInput
    fun_prop
  have hc : ComputableInPolyTime candidates encInput (encList (encList encNat)) := by
    unfold candidates encInput
    fun_prop
  have ht : ComputableInPolyTime transpose encInput VCOne.encSignedCNF := by
    unfold transpose
    apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hu)
    exact row_polytime.comp (hc.comp (ComputableInPolyTime.fst encInput encUnary) |>.prod
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd encInput encUnary)))
  have hs := (ComputableInPolyTime.length_list (encList encNat)).comp hc
  exact hs.prod ((ComputableInPolyTime.const []).prod ht)

/-- Whole original-input compilation includes normalization, Gram/basis diagnostics and actual
query writing; its resource proof composes implementations, not output-volume bounds. -/
@[fun_prop] theorem compile_polytime : ComputableInPolyTime compile encInput
    ExactOne.BinaryPlan.encOutput := ExactOne.BinaryPlan.compile_polytime.comp backend_polytime

/-- Actual admission also has polynomial binary cost, without coefficient/index expansion. -/
@[fun_prop] theorem admit_polytime : ComputableInPolyTime admit encInput encBool := by
  unfold admit candidates universeSize encInput
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  have hu : ComputableInPolyTime (fun p : (Input × List ℕ) × ℕ => p.1.1.1)
      (encPair (encPair encInput (encList encNat)) encNat) encNat := by
    apply ComputableInPolyTime.unary_to_binary.comp
    unfold encInput
    fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.binary_lt.comp
    ((ComputableTidilyInPolyTime.snd (encPair encInput (encList encNat)) encNat).prod hu.tidy))

/-- Exact checked source-admission condition. Out-of-universe labels are not silently claimed
as an admitted source instance, even though the total constructor has intersection semantics. -/
theorem admit_eq_true_iff (x : Input) : admit x = true ↔
    ∀ a ∈ candidates x, ∀ v ∈ a, v < universeSize x := by
  simp [admit]

/-- The original candidate sets as subsets of the declared finite universe. -/
@[expose] def sets (x : Input) (i : Fin (size x)) : Finset (Fin (universeSize x)) :=
  Finset.univ.filter fun v => v.val ∈ (candidates x).get i
/-- Conventional indexed Exact Cover predicate on the original selection bits. -/
@[expose] def IsCover (x : Input) (σ : Fin (size x) → Bool) : Prop :=
  ∀ v : Fin (universeSize x), ∃ i, v.val ∈ (candidates x).get i ∧ σ i = true ∧
    ∀ j, v.val ∈ (candidates x).get j → σ j = true → j = i
/-- Original-object count, used only as the specification. -/
@[expose] noncomputable def count (x : Input) : ℕ :=
  Nat.card {σ : Fin (size x) → Bool // IsCover x σ}
/-- Finite equations for correspondence, with the original candidate bits shared by every row. -/
@[expose] def finiteRows (x : Input) : CNF (Fin (size x)) :=
  List.ofFn fun v : Fin (universeSize x) =>
    ((List.finRange (size x)).filter fun i => v.val ∈ (candidates x).get i).map fun i => (i, true)

private theorem finite_row_perm (x : Input) (v : Fin (universeSize x)) :
    (((List.finRange (size x)).filter fun i => v.val ∈ (candidates x).get i).map
      fun i => (i, true)).Perm
      (ExactOne.signedClause (ExactOne.coverScopes (sets x) v) (fun _ => true)) := by
  apply List.Perm.map
  apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _ |>.filter _)
    (Finset.sort_nodup _ _)).mpr
  intro i
  simp [ExactOne.coverScopes, sets]

/-- The original incidence membership characterization agrees with the existing parsimonious
Exact Cover transposition theorem, without identifying equal candidate indices. -/
theorem isCover_iff (x : Input) (σ : Fin (size x) → Bool) :
    IsCover x σ ↔ ∀ v, ExactOne.Holds (ExactOne.coverScopes (sets x) v) (fun _ => true) σ := by
  rw [ExactOne.coverScopes_iff]
  simp only [IsCover, sets, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The executed binary transpose erases only finite labels, not candidate positions. -/
theorem backend_eq (x : Input) : backend x =
    (size x, (CNF.relabel Fin.val ([] : CNF (Fin (size x))),
      CNF.relabel Fin.val (finiteRows x))) := by
  unfold backend finiteRows transpose
  simp only [CNF.relabel, List.map_ofFn, List.map_nil]
  congr 2
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro v _
  dsimp only [row, Clause.relabel]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.filter_map, List.map_map, Function.comp_def, member]
  congr 1
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

/-- Each transposed equation has at most one literal per original candidate index. -/
theorem finiteRows_width (x : Input) : ∀ c ∈ finiteRows x, c.length ≤ size x := by
  intro c hc
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hc
  exact (by simpa only [List.length_map, List.length_finRange] using
    List.length_filter_le (fun i => decide (v.val ∈ (candidates x).get i)) (List.finRange (size x)))

/-- Scope of an actual finite transposed row, indexed by its written row position. -/
@[expose] def scopes (x : Input) (i : Fin (finiteRows x).length) : Finset (Fin (size x)) :=
  ExactOne.coverScopes (sets x) (Fin.cast (List.length_ofFn) i)

/-- Each actual finite equation is precisely the existing distinct-variable scope encoding. -/
theorem finiteRows_perm (x : Input) (i : Fin (finiteRows x).length) :
    ((finiteRows x).get i).Perm (ExactOne.signedClause (scopes x i) (fun _ => true)) := by
  have he : (finiteRows x).get i =
      (((List.finRange (size x)).filter fun j =>
        (Fin.cast (show (finiteRows x).length = universeSize x from List.length_ofFn) i).val ∈
          (candidates x).get j).map fun j => (j, true)) := List.get_ofFn _ i
  rw [he]
  exact finite_row_perm x _

/-- The reused exact-one source count counts original indexed covers, with no extra certificates. -/
theorem sourceCount_eq_count (x : Input) :
    ExactOne.sourceCount ([] : CNF (Fin (size x))) (scopes x) (fun _ _ => true) = count x := by
  classical
  have hcard : Nat.card {σ : Fin (size x) → Bool //
      CNF.eval σ ([] : CNF (Fin (size x))) = true ∧
        ∀ i, ExactOne.Holds (scopes x i) (fun _ => true) σ} = count x := by
    unfold count
    apply Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp only [CNF.eval_nil, true_and]
    rw [isCover_iff]
    exact Equiv.forall_congr (finCongr (show (finiteRows x).length = universeSize x from
      List.length_ofFn)) (fun _ => Iff.rfl)
  simpa only [ExactOne.sourceCount, ← Nat.card_eq_fintype_card] using hcard

/-- The actual dispatched count is exactly the number of original indexed covers. -/
theorem compile_count (x : Input) : WeightedRow.BinaryPlan.Output.count (compile x) = count x := by
  have h := ExactOne.BinaryPlan.compile_count_of_perm ([] : CNF (Fin (size x)))
    (finiteRows x) (scopes x) (fun _ _ => true) (finiteRows_perm x)
  rw [← backend_eq x] at h
  exact h.trans (sourceCount_eq_count x)

/-- At most two width-three queries, with at most 2s-2 variables and a quadratic clause budget,
independent of the universe size/incidence count; direct branches write no query. -/
theorem compile_withinBudget (x : Input) : WeightedRow.BinaryPlan.WithinBudget (size x) 1
    (compile x) := by
  unfold compile
  rw [backend_eq]
  exact ExactOne.BinaryPlan.compile_withinBudget _ _ (by simp) (finiteRows_width x)

/-- The ordinary query trace actually emitted by the direct-or-two-query dispatcher. -/
@[expose] def queries (x : Input) : List (ℕ × CNF ℕ) :=
  match compile x with
  | .inl _ => []
  | .inr (n, qfalse, qtrue) => [(n, qfalse), (n, qtrue)]

/-- Direct branches emit no query, and every other branch emits exactly a pair. -/
theorem query_count_le (x : Input) : (queries x).length ≤ 2 := by
  unfold queries
  split <;> simp

/-- Explicit source query resources: at most 2s-2 variables, width three and
16s²+16s+3 clauses. These concern the actual emitted queries and valid literal indices. -/
theorem query_bounds (x : Input) (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ queries x) :
    N ≤ 2 * size x - 2 ∧ q.length ≤ 16 * size x ^ 2 + 16 * size x + 3 ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  have h := compile_withinBudget x
  unfold queries at hq
  split at hq
  · simp at hq
  · rename_i n qf qt he
    rw [he] at h
    obtain ⟨hN, hrest⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      obtain ⟨hc, hw⟩ := hrest q (by simp)
      refine ⟨hN, ?_, hw⟩
      unfold WeightedRow.countingBudget at hc
      norm_num only [Nat.reduceAdd, pow_one] at hc
      nlinarith

end Cslib.Logic.PL.ExactCover
