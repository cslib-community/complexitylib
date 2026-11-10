/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.ExactOnePlan
import all CslibFrontier.Computability.PolyTime.CNF.WeightedPlan
import all CslibFrontier.Logics.Propositional.CNF.ExactOneBinary
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.OfFn

/-!
# Correctness of the binary signed-row path dispatcher

Reuse occurrence-sensitive exact-one encoding, two-boundary cancellation and the integer
original-row selection theorem. These bridges concern the actual dispatcher, not a supplied
answer/counter contract. This is the side-CNF form needed by [ChenJiangZhu2027], Theorem 6.3.
-/

public section

namespace Cslib.Logic.PL.ExactOne.BinaryPlan

open Matrix Cslib.LinearSystem
open WeightedRow

/-- Ordinary finite-variable query corresponding to the actual raw binary writer. -/
@[expose] def finiteQuery {n h : ℕ} (B : CNF (Fin n))
    (E : Fin (h + 1) → Clause (Fin n)) (β : Bool) : CNF (Fin n ⊕ Fin h) :=
  TwoBoundary.query ((B ++ (List.ofFn E).flatMap Clause.atMostOneOccurrences).dedup)
    h (fun j => (E j).map fun l => [l]) β

private theorem pairs_width {n : ℕ} (c : Clause (Fin n)) :
    ∀ a ∈ c.atMostOneOccurrences, a.length ≤ 2 := by
  induction c with
  | nil => simp [Clause.atMostOneOccurrences]
  | cons l c ih =>
    intro a ha
    simp only [Clause.atMostOneOccurrences, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨x, _, rfl⟩ | ha
    · simp
    · exact ih a ha

/-- Global deduplication bounds the side/pair part; one path edge per literal adds at most
`2 * n²` clauses. This is a bound on the actual finite query, independent of table count. -/
theorem finiteQuery_budget {n h : ℕ} (B : CNF (Fin n))
    (E : Fin (h + 1) → Clause (Fin n)) (β : Bool)
    (hb : ∀ c ∈ B, c.length ≤ 2) (he : ∀ j, (E j).length ≤ n)
    (hh : h + 1 ≤ n) :
    (finiteQuery B E β).length ≤ 1 + 2 * n + 6 * n ^ 2 ∧
      ∀ c ∈ finiteQuery B E β, c.length ≤ 3 := by
  classical
  let base := B ++ (List.ofFn E).flatMap Clause.atMostOneOccurrences
  have hw : ∀ c ∈ base, c.length ≤ 2 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hb c hc
    · obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hc
      exact pairs_width a c ha
  have hd := dedup_binary_length base hw
  simp only [Fintype.card_fin] at hd
  constructor
  · have hs : (∑ j : Fin (h + 1), ((E j).map fun l => [l]).length) ≤ n * n := by
      calc
        _ ≤ ∑ _j : Fin (h + 1), n := Finset.sum_le_sum fun j _ => by
          simpa only [List.length_map] using he j
        _ = (h + 1) * n := by simp
        _ ≤ n * n := Nat.mul_le_mul_right n hh
    have hl := TwoBoundary.query_length base.dedup (fun j => (E j).map fun l => [l]) β
    change (TwoBoundary.query base.dedup h _ β).length ≤ _
    nlinarith
  · intro c hc
    exact TwoBoundary.query_width base.dedup (fun j => (E j).map fun l => [l])
      2 1 (fun a ha => hw a (List.mem_dedup.mp ha))
      (by intro j t ht; obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; simp) β c hc

/-- The actual binary clause lists are exactly the reviewed path construction, with only the
original/auxiliary index type erased. No source assignment or count is supplied. -/
theorem query_relabel {n h : ℕ} (B : CNF (Fin n))
    (E : Fin (h + 1) → Clause (Fin n)) (β : Bool) :
    query n (B.relabel Fin.val) (CNF.relabel Fin.val (List.ofFn E)) β =
      (finiteQuery B E β).relabel (BinaryQuery.flattenVar (n := n)) := by
  have he (j : Fin (h + 1)) :
      (CNF.relabel Fin.val (List.ofFn E)).getD j.val [] = (E j).relabel Fin.val := by
    simp only [CNF.relabel, List.map_ofFn]
    exact List.getD_ofFn _ j []
  have hb : ((B.relabel Fin.val) ++
      (CNF.relabel Fin.val (List.ofFn E)).flatMap pairs).dedup =
      CNF.relabel Fin.val (B ++ (List.ofFn E).flatMap Clause.atMostOneOccurrences).dedup := by
    simp only [pairs_eq, CNF.relabel, List.flatMap_map, Clause.atMostOneOccurrences_relabel,
      ← List.map_flatMap, ← List.map_append]
    exact List.dedup_map_of_injective
      (List.map_injective_iff.mpr (Fin.val_injective.prodMap Function.injective_id)) _
  rw [query, hb]
  simp only [CNF.relabel, List.length_map, List.length_ofFn, Nat.add_sub_cancel]
  simp only [CNF.relabel] at he
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, he, Clause.relabel]
  have ht (j : Fin (h + 1)) (l : Literal (Fin n)) :
      BinaryQuery.termClauses n h β j.val [(l.1.val, l.2)] =
        (TwoBoundary.termClauses h β j [l]).relabel (BinaryQuery.flattenVar (n := n)) :=
    BinaryQuery.termClauses_eq β j [l]
  simp only [finiteQuery, TwoBoundary.query, CNF.relabel, List.map_append,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
  congr 1
  · congr 1
    funext c
    simp only [Clause.relabel, List.map_map, Function.comp_def]
    rfl
  · congr 1
    funext j
    congr 1
    funext l
    rcases l with ⟨i, b⟩
    exact ht j (i, b)

/-- Existing path cancellation counts the original side formula and exact-one rows, including
occurrence repetitions. The binary writer uses no marking or weighted counting oracle. -/
theorem finiteQuery_count {n h : ℕ} (B : CNF (Fin n))
    (E : Fin (h + 1) → Clause (Fin n)) :
    Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ ∀ j, (E j).evalOne σ = true} =
      Fintype.card {σ // (finiteQuery B E false).eval σ = true} -
        Fintype.card {σ // (finiteQuery B E true).eval σ = true} := by
  classical
  unfold finiteQuery
  rw [← TwoBoundary.counting_identity]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  have hb (F : CNF (Fin n)) : CNF.eval σ F.dedup = F.eval σ := by
    apply Bool.eq_iff_iff.mpr
    simp [CNF.eval_eq_true_iff]
  have hc (c : Clause (Fin n)) :
      DNF.eval σ (c.map fun l => [l]) = c.eval σ := by
    simp only [DNF.eval, List.any_map, Function.comp_def, Term.eval, List.all_cons,
      List.all_nil, Bool.and_true]
    rfl
  have hp (c : Clause (Fin n)) : c.eval σ = true ↔ 0 < c.countP (Literal.eval σ) := by
    simp [Clause.eval, List.countP_pos_iff]
  simp only [hb, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff,
    List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    Clause.eval_atMostOneOccurrences, hc, Clause.evalOne_eq_true_iff, hp]
  constructor
  · rintro ⟨hb, he⟩
    exact ⟨⟨hb, fun j => by rw [he j]⟩, fun j => by rw [he j]; omega⟩
  · rintro ⟨⟨hb, ha⟩, hc⟩
    exact ⟨hb, fun j => by have := ha j; have := hc j; omega⟩

/-- Semantic counting correspondence for the actual raw query writer. -/
theorem query_count {n h : ℕ} (B : CNF (Fin n))
    (E : Fin (h + 1) → Clause (Fin n)) :
    WeightedRow.BinaryPlan.Output.count
      (Sum.inr (n + h, (query n (B.relabel Fin.val) (CNF.relabel Fin.val (List.ofFn E)) false,
      query n (B.relabel Fin.val) (CNF.relabel Fin.val (List.ofFn E)) true)) : Output) =
      Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ ∀ j, (E j).evalOne σ = true} := by
  rw [WeightedRow.BinaryPlan.Output.count, query_relabel, query_relabel,
    WeightedRow.BinaryPlan.queryCount_relabel, WeightedRow.BinaryPlan.queryCount_relabel]
  exact (finiteQuery_count B E).symm

/-- Tests on stored bits agree with finite signed-equation semantics. -/
theorem test_relabel {n : ℕ} (B E : CNF (Fin n)) (bits : List Bool) (σ : Fin n → Bool)
    (hbits : ∀ j, bits.getD j.val false = σ j) :
    test (B.relabel Fin.val) (E.relabel Fin.val) bits =
      (B.eval σ && E.evalOne σ) := by
  have hl (l : Literal (Fin n)) :
      (bits.getD (Prod.map Fin.val id l).1 false == (Prod.map Fin.val id l).2) =
        Literal.eval σ l := by
    change (bits.getD l.1.val false == l.2) = Literal.eval σ l
    rw [hbits]
    rfl
  simp only [test, eval, CNF.relabel, Clause.relabel, List.all_map, List.any_map,
    List.countP_map, Function.comp_def, hl]
  rfl

/-- Permuting a row does not change its occurrence-sensitive equation. -/
theorem row_eval_of_perm {n : ℕ} (c : Clause (Fin n)) (S : Finset (Fin n))
    (p σ : Fin n → Bool) (hc : c.Perm (signedClause S p)) :
    c.evalOne σ = true ↔ Holds S p σ := by
  simp only [holds_iff_evalOne, Clause.evalOne_eq_true_iff]
  rw [hc.countP_eq]

/-- Materialization is invariant under the actual within-row ordering. Thus the binary backend
receives exactly the original signed system, not a separately supplied coefficient matrix. -/
theorem materialize_of_perm {n : ℕ} (E : CNF (Fin n))
    (S : Fin E.length → Finset (Fin n)) (p : Fin E.length → Fin n → Bool)
    (h : ∀ i, (E.get i).Perm (signedClause (S i) (p i))) :
    VCOne.payloadRows n (E.relabel Fin.val) = integerRows S p ∧
      VCOne.payloadRhs (E.relabel Fin.val) = integerRhs S p := by
  constructor
  · apply List.ext_getElem
    · simp [VCOne.payloadRows, CNF.relabel, integerRows]
    · intro i hi hj
      simp only [VCOne.payloadRows, CNF.relabel, List.length_map] at hi
      have hp := (h ⟨i, hi⟩).map (Prod.map Fin.val id)
      simp only [List.get_eq_getElem] at hp
      have hc := VCOne.payloadRows_scoped (S ⟨i, hi⟩) (p ⟨i, hi⟩)
      simp only [VCOne.payloadRows, List.map_singleton, List.singleton_inj] at hc
      simp only [VCOne.payloadRows, CNF.relabel, List.getElem_map, integerRows,
        List.getElem_ofFn]
      change (List.range n).map (fun c =>
        if (Clause.relabel Fin.val E[i]).any (fun l => l.1 == c && l.2) then (1 : ℤ)
        else if (Clause.relabel Fin.val E[i]).any (fun l => l.1 == c && !l.2) then -1 else 0) = _
      have he : (List.range n).map (fun c =>
          if (Clause.relabel Fin.val E[i]).any (fun l => l.1 == c && l.2) then (1 : ℤ)
          else if (Clause.relabel Fin.val E[i]).any (fun l => l.1 == c && !l.2) then -1 else 0) =
          (VCOne.payloadRows n
            [(signedClause (S ⟨i, hi⟩) (p ⟨i, hi⟩)).relabel Fin.val]).headD [] := by
        simp only [VCOne.payloadRows, List.map_singleton, List.headD_cons]
        apply List.map_congr_left
        intro c _
        change (Clause.relabel Fin.val E[i]).Perm
          (Clause.relabel Fin.val (signedClause (S ⟨i, hi⟩) (p ⟨i, hi⟩))) at hp
        simp only [hp.any_eq]
      rw [he]
      simpa only [VCOne.payloadRows, List.map_singleton, List.headD_cons, signedClause,
        Clause.relabel, List.map_map, Function.comp_def, Prod.map_apply, id_eq] using hc
  · apply List.ext_getElem
    · simp [VCOne.payloadRhs, CNF.relabel, integerRhs]
    · intro i hi hj
      simp only [VCOne.payloadRhs, CNF.relabel, List.length_map] at hi
      have hp := (h ⟨i, hi⟩).map (Prod.map Fin.val id)
      simp only [List.get_eq_getElem] at hp
      have hs := (hp.map (fun l => if l.2 then (0 : ℤ) else 1)).sum_eq
      have hc := VCOne.payloadRhs_scoped (S ⟨i, hi⟩) (p ⟨i, hi⟩)
      simp only [VCOne.payloadRhs, List.map_singleton, List.singleton_inj] at hc
      simp only [VCOne.payloadRhs, CNF.relabel, List.getElem_map, integerRhs,
        List.getElem_ofFn]
      simp only [Clause.relabel]
      rw [hs]
      simpa only [signedClause, Clause.relabel, List.map_map, Function.comp_def,
        Prod.map_apply, id_eq] using hc

/-- Integer equality reads the very same candidate as the reviewed rational interpretation. -/
theorem candidate_getD (n : ℕ) (E : CNF ℕ) (j : Fin n) :
    (candidate n E).getD j.val false =
      candidateBits (rectangularPoint n (VCOne.payloadRows n E) (VCOne.payloadRhs E)) j := by
  let A := VCOne.payloadRows n E
  let b := VCOne.payloadRhs E
  let cert := rectangularCertificate n A b
  have hd : cert.1 ≠ 0 := rectangularCertificate_den_ne_zero n A b
  have hzero : ((0 : ℤ) == cert.1) = false := by simp [Ne.symm hd]
  have hb : (candidate n E).getD j.val false = (cert.2.getD j.val 0 == cert.1) := by
    change (cert.2.map fun z => z == cert.1).getD j.val false = _
    rw [← hzero, List.getD_map]
  have hq (z : ℤ) : (z == cert.1) = decide ((z : ℚ) / cert.1 = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [div_eq_iff (by exact_mod_cast hd : (cert.1 : ℚ) ≠ 0)]
    simp only [one_mul]
    norm_cast
  exact hb.trans (hq _)

/-- Tests of the computed candidate equal the reviewed candidate checker, without carrying
rational arithmetic in the actual program. -/
theorem candidate_test_of_perm {n : ℕ} (B E : CNF (Fin n))
    (S : Fin E.length → Finset (Fin n)) (p : Fin E.length → Fin n → Bool)
    (h : ∀ i, (E.get i).Perm (signedClause (S i) (p i))) :
    (if test (B.relabel Fin.val) (E.relabel Fin.val)
      (candidate n (E.relabel Fin.val)) then (1 : ℕ) else 0) =
        checkCandidate B S p (rectangularPoint n (integerRows S p) (integerRhs S p)) := by
  have ht := test_relabel B E _ _ (candidate_getD n (E.relabel Fin.val))
  obtain ⟨hA, hb⟩ := materialize_of_perm E S p h
  rw [hA, hb] at ht
  have he (σ : Fin n → Bool) : E.evalOne σ = true ↔ ∀ i, Holds (S i) (p i) σ := by
    rw [CNF.evalOne_eq_true_iff]
    constructor
    · intro hx i
      exact (row_eval_of_perm _ _ _ _ (h i)).mp (hx _ (E.get_mem i))
    · intro hx c hc
      obtain ⟨i, rfl⟩ := List.get_of_mem hc
      exact (row_eval_of_perm _ _ _ _ (h i)).mpr (hx i)
  simp only [ht, Bool.and_eq_true, he, checkCandidate]
  split_ifs <;> rfl

/-- The executable small branch checks exactly the one or two original assignments. -/
theorem small_count_relabel {n : ℕ} (B E : CNF (Fin n)) (hn : n ≤ 1) :
    small n (B.relabel Fin.val) (E.relabel Fin.val) =
      Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ E.evalOne σ = true} := by
  classical
  interval_cases n
  · have ht := test_relabel B E [] (fun _ => false) (fun i => Fin.elim0 i)
    simp only [small, List.replicate_zero, ht, Bool.and_eq_true, ↓reduceIte, Nat.add_zero]
    rw [Fintype.card_subtype]
    have he (σ : Fin 0 → Bool) : σ = fun _ => false := Subsingleton.elim _ _
    simp only [Finset.univ_unique, Finset.filter_singleton, he]
    split_ifs <;> simp
  · have ht (b : Bool) := test_relabel B E [b] (fun _ => b) (fun i => by
      have hi : i.val = 0 := by omega
      simp only [hi, List.getD_cons_zero])
    have hc : Fintype.card {σ : Fin 1 → Bool // B.eval σ = true ∧ E.evalOne σ = true} =
        Fintype.card {b : Bool // B.eval (fun _ => b) = true ∧ E.evalOne (fun _ => b) = true} := by
      symm
      exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.funUnique (Fin 1) Bool).symm
        (fun _ => Iff.rfl))
    rw [hc, Fintype.card_subtype]
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [hu]
    simp only [small, List.replicate_succ, List.replicate_zero, ht, Bool.and_eq_true,
      Nat.one_ne_zero, ↓reduceIte]
    simp only [Finset.filter_insert, Finset.filter_singleton]
    split_ifs <;> simp_all

/-- Erasing finite labels preserves the actual query's clause, width and declaration budgets. -/
theorem query_budget {n h : ℕ} (B : CNF (Fin n))
    (E : Fin (h + 1) → Clause (Fin n)) (β : Bool)
    (hb : ∀ c ∈ B, c.length ≤ 2) (he : ∀ j, (E j).length ≤ n)
    (hh : h + 1 ≤ n) :
    let Q := query n (B.relabel Fin.val) (CNF.relabel Fin.val (List.ofFn E)) β
    Q.length ≤ WeightedRow.countingBudget n 1 ∧
      ∀ c ∈ Q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < n + h := by
  classical
  rw [query_relabel]
  obtain ⟨hl, hw⟩ := finiteQuery_budget B E β hb he hh
  refine ⟨?_, ?_⟩
  · simp only [CNF.relabel, List.length_map]
    unfold WeightedRow.countingBudget
    norm_num only [Nat.reduceAdd, pow_one]
    nlinarith
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    refine ⟨by simpa only [Clause.relabel, List.length_map] using hw a ha, ?_⟩
    intro l hl
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
    exact BinaryQuery.flattenVar_lt v.1

/-- The signed system and occurrence rows express the same source count. -/
theorem sourceCount_of_perm {n : ℕ} (B E : CNF (Fin n))
    (S : Fin E.length → Finset (Fin n)) (p : Fin E.length → Fin n → Bool)
    (h : ∀ i, (E.get i).Perm (signedClause (S i) (p i))) :
    sourceCount B S p =
      Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ E.evalOne σ = true} := by
  classical
  unfold sourceCount
  simp only [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  apply and_congr_right
  intro _
  rw [CNF.evalOne_eq_true_iff]
  constructor
  · intro hx c hc
    obtain ⟨i, rfl⟩ := List.get_of_mem hc
    exact (row_eval_of_perm _ _ _ _ (h i)).mpr (hx i)
  · intro hx i
    exact (row_eval_of_perm _ _ _ _ (h i)).mp (hx _ (E.get_mem i))

private theorem queryCount_fin {n : ℕ} (B : CNF (Fin n)) :
    WeightedRow.BinaryPlan.queryCount n (B.relabel Fin.val) = declaredCount B := by
  classical
  unfold WeightedRow.BinaryPlan.queryCount declaredCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  rw [CNF.eval_relabel]
  have he : WeightedRow.BinaryPlan.assignment σ ∘ Fin.val = σ := by
    funext j
    simp [WeightedRow.BinaryPlan.assignment, j.isLt]
  rw [he]

private theorem getD_relabel {n : ℕ} (E : CNF (Fin n)) (i : ℕ) :
    (E.relabel Fin.val).getD i [] = (E.getD i []).relabel Fin.val := by
  change (E.map (Clause.relabel Fin.val)).getD i
    (Clause.relabel (Fin.val : Fin n → ℕ) ([] : Clause (Fin n))) = _
  rw [List.getD_map]

private theorem selected_count_of_perm {n : ℕ} (B E : CNF (Fin n))
    (S : Fin E.length → Finset (Fin n)) (p : Fin E.length → Fin n → Bool)
    (h : ∀ i, (E.get i).Perm (signedClause (S i) (p i)))
    (hc : rectangularConsistent n (integerRows S p) (integerRhs S p) = true)
    (hn : gramRowBasis n (integerRows S p) ≠ []) :
    let ids := gramRowBasis n (integerRows S p)
    let selected := ids.map fun i => (E.relabel Fin.val).getD i []
    WeightedRow.BinaryPlan.Output.count (.inr (n + ids.length - 1,
      (query n (B.relabel Fin.val) selected false,
        query n (B.relabel Fin.val) selected true))) = sourceCount B S p := by
  classical
  let ids := gramRowBasis n (integerRows S p)
  let L : CNF (Fin n) := ids.map fun i => E.getD i []
  have hl : 0 < L.length := by simpa only [L, List.length_map] using List.length_pos_iff.mpr hn
  let k := L.length - 1
  have hk : k + 1 = L.length := by dsimp only [k]; omega
  let F : Fin (k + 1) → Clause (Fin n) := fun j => L.get (Fin.cast hk j)
  have hF : List.ofFn F = L := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; exact hk
    · intro i hi hj
      simp only [F, List.getElem_ofFn, List.get_eq_getElem]
      rfl
  have hraw : (ids.map fun i => (E.relabel Fin.val).getD i []) = L.relabel Fin.val := by
    calc _ = ids.map (fun i => (E.getD i []).relabel Fin.val) :=
            List.map_congr_left fun i _ => getD_relabel E i
      _ = _ := by simp only [L, CNF.relabel, List.map_map, Function.comp_def]
  have hN : n + ids.length - 1 = n + k := by
    have hk' : k = ids.length - 1 := by
      dsimp only [k, L]
      rw [List.length_map]
    rw [hk']
    have hids : 0 < ids.length := by simpa only [L, List.length_map] using hl
    omega
  change WeightedRow.BinaryPlan.Output.count (.inr (n + ids.length - 1, _)) = _
  rw [hraw, hN, ← hF, query_count]
  unfold sourceCount
  simp only [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  apply and_congr_right
  intro _
  have hf : (∀ j, (F j).evalOne σ = true) ↔ L.evalOne σ = true := by
    rw [← hF, CNF.evalOne_eq_true_iff]
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  rw [hf, CNF.evalOne_eq_true_iff]
  have hb (i : Fin E.length) : i ∈ binaryIndices S p ↔ i.val ∈ ids := by
    simp [binaryIndices, ids, Fin.ext_iff]
  rw [← binaryIndices_selected S p hc σ]
  constructor
  · intro hx i hi
    have hid := (hb i).mp hi
    have hval := hx (E.getD i.val []) (List.mem_map.mpr ⟨i.val, hid, rfl⟩)
    rw [List.getD_eq_getElem _ _ i.isLt] at hval
    exact (row_eval_of_perm _ _ _ _ (h i)).mp hval
  · intro hx c hcL
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcL
    have hib : i < E.length := by
      simpa only [integerRows_length] using gramRowBasis_mem n (integerRows S p) i hi
    rw [List.getD_eq_getElem _ _ hib]
    exact (row_eval_of_perm _ _ _ _ (h ⟨i, hib⟩)).mpr (hx ⟨i, hib⟩ ((hb _).mpr hi))

/-- The complete executable dispatcher preserves the original declared count. Every rank,
candidate, matrix and pair of ordinary queries comes from the original side formula and rows. -/
theorem compile_count_of_perm {n : ℕ} (B E : CNF (Fin n))
    (S : Fin E.length → Finset (Fin n)) (p : Fin E.length → Fin n → Bool)
    (h : ∀ i, (E.get i).Perm (signedClause (S i) (p i))) :
    WeightedRow.BinaryPlan.Output.count (compile (n, (B.relabel Fin.val, E.relabel Fin.val))) =
      sourceCount B S p := by
  classical
  obtain ⟨hA, hrhs⟩ := materialize_of_perm E S p h
  have he : ([] : Clause ℕ) ∈ B.relabel Fin.val ↔ ([] : Clause (Fin n)) ∈ B := by
    simp [CNF.relabel, Clause.relabel]
  unfold compile
  by_cases hs : n ≤ 1
  · simp only [hs, ↓reduceIte, WeightedRow.BinaryPlan.Output.count]
    rw [sourceCount_of_perm B E S p h]
    exact small_count_relabel B E hs
  by_cases hbare : B = [] ∧ E = []
  · rw [sourceCount_of_perm B E S p h, hbare.1, hbare.2]
    simp [hs, CNF.relabel, WeightedRow.BinaryPlan.Output.count, CNF.eval, CNF.evalOne]
  have hb : ((B.relabel Fin.val).isEmpty && (E.relabel Fin.val).isEmpty) = false := by
    simpa [CNF.relabel, Bool.and_eq_true] using hbare
  simp only [hs, ↓reduceIte, hb, Bool.false_eq_true, he]
  by_cases hz : ([] : Clause (Fin n)) ∈ B
  · simp only [hz, ↓reduceIte, WeightedRow.BinaryPlan.Output.count]
    rw [sourceCount_of_perm B E S p h]
    symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x => ?_⟩
    have hf := (CNF.eval_eq_true_iff _ _).mp x.property.1 [] hz
    simp only [Clause.eval, List.any_nil, Bool.false_eq_true] at hf
  simp only [hz, ↓reduceIte, hA, hrhs]
  by_cases hc : rectangularConsistent n (integerRows S p) (integerRhs S p) = true
  · simp only [hc, ↓reduceIte]
    by_cases hf : (gramRowBasis n (integerRows S p)).length = n
    · simp only [hf, ↓reduceIte, WeightedRow.BinaryPlan.Output.count]
      rw [candidate_test_of_perm B E S p h]
      exact binaryCandidate_correct S p B hc (by simpa only [binaryIndices_length] using hf)
    simp only [hf, ↓reduceIte]
    by_cases hn : (gramRowBasis n (integerRows S p)).isEmpty = true
    · simp only [hn, ↓reduceIte, WeightedRow.BinaryPlan.Output.count]
      have hnil : binaryIndices S p = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [binaryIndices_length, List.isEmpty_iff.mp hn]
        rfl
      have hsolve (σ : Fin n → Bool) : ∀ i, Holds (S i) (p i) σ :=
        (binaryIndices_selected S p hc σ).mp (by simp [hnil])
      have hsource : sourceCount B S p = declaredCount B := by
        unfold sourceCount declaredCount
        simp only [← Nat.card_eq_fintype_card]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => by simp [hsolve σ])
      have hfalse : WeightedRow.BinaryPlan.queryCount n ([[]] : CNF ℕ) = 0 := by
        simp [WeightedRow.BinaryPlan.queryCount, CNF.eval, Clause.eval]
      rw [hfalse, Nat.sub_zero, hsource]
      have hdedup : CNF.relabel Fin.val B.dedup = (B.relabel Fin.val).dedup :=
        (List.dedup_map_of_injective
          (List.map_injective_iff.mpr (Fin.val_injective.prodMap Function.injective_id)) _).symm
      rw [← hdedup, queryCount_fin]
      unfold declaredCount
      simp [CNF.eval_eq_true_iff]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      exact selected_count_of_perm B E S p h hc (fun hnil => hn (by simp [hnil]))
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, WeightedRow.BinaryPlan.Output.count]
    symm
    apply count_eq_zero_of_inconsistent
    exact fun hz => hc ((binaryConsistent_iff S p).mpr hz)

/-- The complete dispatcher's actual emitted queries have the required width, variable and
polynomial list budgets. Direct branches require no query. -/
theorem compile_withinBudget {n : ℕ} (B E : CNF (Fin n))
    (hb : ∀ c ∈ B, c.length ≤ 2) (he : ∀ c ∈ E, c.length ≤ n) :
    WeightedRow.BinaryPlan.WithinBudget n 1
      (compile (n, (B.relabel Fin.val, E.relabel Fin.val))) := by
  classical
  dsimp only [compile]
  split_ifs with hs hbare hz hc hf hn
  all_goals try trivial
  · have hn' : 2 ≤ n := by omega
    refine ⟨by omega, ?_⟩
    intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · have hd := dedup_binary_length B hb
      have hm : (B.relabel Fin.val).dedup = CNF.relabel Fin.val B.dedup :=
        List.dedup_map_of_injective
          (List.map_injective_iff.mpr (Fin.val_injective.prodMap Function.injective_id)) B
      rw [hm]
      refine ⟨?_, ?_⟩
      · simp only [CNF.relabel, List.length_map, Fintype.card_fin] at hd ⊢
        unfold WeightedRow.countingBudget
        norm_num only [Nat.reduceAdd, pow_one]
        nlinarith
      · intro c hcm
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hcm
        refine ⟨by simpa only [Clause.relabel, List.length_map] using
          (hb a (List.mem_dedup.mp ha)).trans (by decide : 2 ≤ 1 + 2), ?_⟩
        intro l hl
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
        exact v.1.isLt
    · refine ⟨?_, ?_⟩
      · simp only [List.length_cons, List.length_nil]
        unfold WeightedRow.countingBudget
        norm_num only [Nat.reduceAdd, pow_one]
        nlinarith
      · intro c hcm
        simp only [List.mem_singleton] at hcm
        subst c
        simp
  · rename_i hempty
    let ids := gramRowBasis n (VCOne.payloadRows n (E.relabel Fin.val))
    let L : CNF (Fin n) := ids.map fun i => E.getD i []
    have hl : 0 < L.length := by
      simpa only [L, List.length_map] using
        List.length_pos_iff.mpr (by simpa only [List.isEmpty_iff] using hempty)
    have hi : ids.length ≤ n := gramRowBasis_length _ _
    have hk : (L.length - 1) + 1 = L.length := by omega
    let F : Fin (L.length - 1 + 1) → Clause (Fin n) := fun j => L.get (Fin.cast hk j)
    have hF : List.ofFn F = L := by
      apply List.ext_getElem
      · simp only [List.length_ofFn]; exact hk
      · intro i hi hj
        simp only [F, List.getElem_ofFn, List.get_eq_getElem]
        rfl
    have hraw : (ids.map fun i => (E.relabel Fin.val).getD i []) =
        CNF.relabel Fin.val (List.ofFn F) := by
      rw [hF]
      calc _ = ids.map (fun i => (E.getD i []).relabel Fin.val) :=
              List.map_congr_left fun i _ => getD_relabel E i
        _ = _ := by simp only [L, CNF.relabel, List.map_map, Function.comp_def]
    have hN : n + ids.length - 1 = n + (L.length - 1) := by
      have hlen : L.length = ids.length := List.length_map _
      omega
    have hlen : L.length ≤ n := by simpa only [L, List.length_map] using hi
    have hrow (j : Fin (L.length - 1 + 1)) : (F j).length ≤ n := by
      have hm : F j ∈ L := L.get_mem _
      obtain ⟨i, him, heq⟩ := List.mem_map.mp hm
      rw [← heq]
      have hib : i < E.length := by
        simpa only [VCOne.payloadRows, CNF.relabel, List.length_map] using
          gramRowBasis_mem n (VCOne.payloadRows n (E.relabel Fin.val)) i him
      rw [List.getD_eq_getElem _ _ hib]
      exact he _ (List.getElem_mem hib)
    change WeightedRow.BinaryPlan.WithinBudget n 1
      (.inr (n + ids.length - 1, (query _ _ _ false, query _ _ _ true)))
    rw [hraw, hN]
    have hlenids : L.length = ids.length := List.length_map _
    change ids.length ≠ n at hf
    refine ⟨by omega, ?_⟩
    intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact query_budget B F false hb hrow (by omega)
    · exact query_budget B F true hb hrow (by omega)

end Cslib.Logic.PL.ExactOne.BinaryPlan
