/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.WeightedGlobal
public import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Executable bounded subset enumeration

List enumeration for [ChenJiangZhu2027], Section 7.1, equations (24)–(25).
Only lengths at most the requested bound are visited. No full powerset is built.
The candidate budget is polynomial for fixed bound. This is not a binary-machine
runtime or space certificate for the normalization and all-cases pipeline.
-/

public section

namespace Cslib.Logic.PL.WeightedRow

open scoped BigOperators

/-- Enumerate sublists of each permitted length, retaining their canonical input order. -/
@[expose] def boundedLists {α : Type*} (l : List α) (k : ℕ) : List (List α) :=
  (List.range (k + 1)).flatMap fun j => l.sublistsLen j

/-- Exact candidate count, before weight tests. -/
theorem boundedLists_length {α : Type*} (l : List α) (k : ℕ) :
    (boundedLists l k).length = ∑ j ∈ Finset.range (k + 1), l.length.choose j := by
  have aux (m : ℕ) : ((List.range m).map fun j => l.length.choose j).sum =
      ∑ j ∈ Finset.range m, l.length.choose j := by
    induction m with
    | zero => simp
    | succ m ih => simpa only [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, Finset.sum_range_succ] using
        (congrArg (fun x => x + l.length.choose m) ih)
  simpa [boundedLists, List.length_flatMap, List.length_sublistsLen] using aux (k + 1)

/-- Fixed-bound polynomial domination, including empty inputs. -/
theorem boundedLists_polynomial {α : Type*} (l : List α) (k : ℕ) :
    (boundedLists l k).length ≤ (k + 1) * (l.length + 1) ^ k := by
  rw [boundedLists_length]
  calc
    _ ≤ ∑ _j ∈ Finset.range (k + 1), (l.length + 1) ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (by omega : l.length ≤ l.length + 1) j).trans
          (Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hj; omega)))
    _ = _ := by simp

/-- Membership exposes both the input ordering and the size bound. -/
theorem mem_boundedLists {α : Type*} {l t : List α} {k : ℕ} :
    t ∈ boundedLists l k ↔ t.Sublist l ∧ t.length ≤ k := by
  simp only [boundedLists, List.mem_flatMap, List.mem_range, List.mem_sublistsLen]
  constructor
  · rintro ⟨j, hj, hs, rfl⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hk⟩
    exact ⟨t.length, by omega, hs, rfl⟩

/-- Every bounded subset is represented, without requiring its external list ordering. -/
theorem boundedLists_finsets {α : Type*} [DecidableEq α] (l : List α)
    (hl : l.Nodup) (k : ℕ) (s : Finset α) :
    s ∈ (boundedLists l k).map List.toFinset ↔ s ⊆ l.toFinset ∧ s.card ≤ k := by
  constructor
  · rintro hm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ht, hk⟩ := mem_boundedLists.mp ht
    exact ⟨fun i hi => List.mem_toFinset.mpr (ht.subset (List.mem_toFinset.mp hi)),
      (List.toFinset_card_of_nodup (ht.nodup hl)).le.trans hk⟩
  · rintro ⟨hs, hk⟩
    let t := l.filter fun i => i ∈ s
    have he : t.toFinset = s := by
      ext i
      simp only [t, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hs h), h⟩⟩
    apply List.mem_map.mpr
    refine ⟨t, mem_boundedLists.mpr ⟨List.filter_sublist, ?_⟩, he⟩
    rw [← List.toFinset_card_of_nodup (hl.filter _), he]
    exact hk

/-- Canonical support list for a finite declared variable type; no type powerset is visited. -/
@[expose] def supportList {n d : ℕ} (R : Row (Fin n) d) : List (Fin n) :=
  (List.finRange n).filter fun i => i ∈ R.support

/-- Executable equation (24) clause writer. -/
@[expose] def upperList {n d : ℕ} (R : Row (Fin n) d) : CNF (Fin n) :=
  ((boundedLists (supportList R) (R.demand + 1)).filter
    fun t => R.demand < (t.map R.weight).sum).map
      fun t => (t.map fun i => (i, !(R.sign i)))

/-- Executable equation (25) term writer. -/
@[expose] def attainmentList {n d : ℕ} (R : Row (Fin n) d) : DNF (Fin n) :=
  ((boundedLists (supportList R) d).filter
    fun t => (t.map R.weight).sum = R.demand).map
      fun t => (t.map fun i => (i, R.sign i))

/-- Filtering and writing cannot increase the number of upper candidates. -/
theorem upperList_length {n d : ℕ} (R : Row (Fin n) d) :
    (upperList R).length ≤
      (R.demand + 2) * ((supportList R).length + 1) ^ (R.demand + 1) := by
  simp only [upperList, List.length_map]
  exact (List.length_filter_le _ _).trans (boundedLists_polynomial _ _)

/-- Filtering and writing cannot increase the number of attainment candidates. -/
theorem attainmentList_length {n d : ℕ} (R : Row (Fin n) d) :
    (attainmentList R).length ≤ (d + 1) * ((supportList R).length + 1) ^ d := by
  simp only [attainmentList, List.length_map]
  exact (List.length_filter_le _ _).trans (boundedLists_polynomial _ _)

/-- Upper clauses use at most `d + 1` literals. -/
theorem upperList_width {n d : ℕ} (R : Row (Fin n) d) (c : Clause (Fin n))
    (hc : c ∈ upperList R) : c.length ≤ d + 1 := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  have h := (mem_boundedLists.mp (List.mem_filter.mp ht).1).2
  simpa only [List.length_map] using h.trans (Nat.add_le_add_right R.bounded 1)

/-- Attainment terms use at most `d` literals. -/
theorem attainmentList_width {n d : ℕ} (R : Row (Fin n) d) (t : Term (Fin n))
    (ht : t ∈ attainmentList R) : t.length ≤ d := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  simpa only [List.length_map] using
    (mem_boundedLists.mp (List.mem_filter.mp hs).1).2

private theorem supportList_nodup {n d : ℕ} (R : Row (Fin n) d) :
    (supportList R).Nodup := (List.nodup_finRange n).filter _

private theorem supportList_set {n d : ℕ} (R : Row (Fin n) d) :
    (supportList R).toFinset = R.support := by
  ext i
  simp [supportList]

private theorem bounded_exists {n d : ℕ} (R : Row (Fin n) d) (k : ℕ)
    (P : Finset (Fin n) → Prop) :
    (∃ t ∈ boundedLists (supportList R) k, P t.toFinset) ↔
      ∃ s ⊆ R.support, s.card ≤ k ∧ P s := by
  constructor
  · rintro ⟨t, ht, hp⟩
    have hs := (boundedLists_finsets (supportList R) (supportList_nodup R) k t.toFinset).mp
      (List.mem_map.mpr ⟨t, ht, rfl⟩)
    exact ⟨t.toFinset, by simpa only [supportList_set] using hs.1, hs.2, hp⟩
  · rintro ⟨s, hs, hk, hp⟩
    have hm := (boundedLists_finsets (supportList R) (supportList_nodup R) k s).mpr
      ⟨by simpa only [supportList_set] using hs, hk⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    exact ⟨t, ht, hp⟩

/-- The executable attainment writer agrees with the reviewed finite-set formula. -/
theorem attainmentList_eval {n d : ℕ} (R : Row (Fin n) d) (σ : Fin n → Bool) :
    (attainmentList R).eval σ = R.attainment.eval σ := by
  apply Bool.eq_iff_iff.mpr
  have hterm (t : List (Fin n)) :
      Term.eval σ (t.map fun i => (i, R.sign i)) = true ↔
        ∀ i ∈ t.toFinset, σ i = R.sign i := by
    simp [Term.eval_eq_true_iff]
  have hsum (t : List (Fin n)) (ht : t ∈ boundedLists (supportList R) d) :
      (t.map R.weight).sum = ∑ i ∈ t.toFinset, R.weight i :=
    (List.sum_toFinset R.weight
      ((mem_boundedLists.mp ht).1.nodup (supportList_nodup R))).symm
  have hr (s : Finset (Fin n)) : Term.eval σ (R.term s) = true ↔
      ∀ i ∈ s, σ i = R.sign i := by
    simp [Row.term, Term.eval_eq_true_iff]
  simp only [attainmentList, DNF.eval_eq_true_iff, List.mem_map, List.mem_filter,
    decide_eq_true_eq, exists_exists_and_eq_and, hterm, Row.attainment,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_powerset, hr]
  constructor
  · rintro ⟨t, ⟨ht, hw⟩, hp⟩
    obtain ⟨s, hs, hk, hw, hp⟩ := (bounded_exists R d
      (fun s => (∑ i ∈ s, R.weight i) = R.demand ∧ ∀ i ∈ s, σ i = R.sign i)).mp
      ⟨t, ht, (hsum t ht).symm.trans hw, hp⟩
    exact ⟨s, ⟨hs, hk, hw⟩, hp⟩
  · rintro ⟨s, ⟨hs, hk, hw⟩, hp⟩
    obtain ⟨t, ht, hw, hp⟩ := (bounded_exists R d
      (fun s => (∑ i ∈ s, R.weight i) = R.demand ∧ ∀ i ∈ s, σ i = R.sign i)).mpr ⟨s, hs, hk, hw, hp⟩
    exact ⟨t, ⟨ht, (hsum t ht).trans hw⟩, hp⟩


/-- The executable upper writer agrees with the reviewed finite-set formula. -/
theorem upperList_eval {n d : ℕ} (R : Row (Fin n) d) (σ : Fin n → Bool) :
    (upperList R).eval σ = R.upper.eval σ := by
  classical
  apply Bool.eq_iff_iff.mpr
  apply not_iff_not.mp
  have hr (s : Finset (Fin n)) : Clause.eval σ ((R.term s).negate) = true ↔
      ¬ (∀ i ∈ s, σ i = R.sign i) := by
    simp [Row.term, Term.eval_negate, Bool.eq_false_iff, Term.eval_eq_true_iff]
  have ht (t : List (Fin n)) : Clause.eval σ (t.map fun i => (i, !(R.sign i))) = true ↔
      ¬ (∀ i ∈ t.toFinset, σ i = R.sign i) := by
    simp [Clause.eval_eq_true_iff, Bool.eq_not_iff, not_forall]
  have hsum (t : List (Fin n)) (ht : t ∈ boundedLists (supportList R) (R.demand + 1)) :
      (t.map R.weight).sum = ∑ i ∈ t.toFinset, R.weight i :=
    (List.sum_toFinset R.weight
      ((mem_boundedLists.mp ht).1.nodup (supportList_nodup R))).symm
  simp only [upperList, Row.upper, CNF.eval_eq_true_iff, List.forall_mem_map,
    List.mem_filter, decide_eq_true_eq, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_powerset, and_imp, hr, ht, not_forall, not_exists, not_not]
  constructor
  · rintro ⟨t, ht, hw, hp⟩
    obtain ⟨s, hs, hk, hw, hp⟩ := (bounded_exists R (R.demand + 1)
      (fun s => R.demand < (∑ i ∈ s, R.weight i) ∧ ∀ i ∈ s, σ i = R.sign i)).mp
        ⟨t, ht, by simpa only [hsum t ht] using hw, hp⟩
    exact ⟨s, hs, hk, hw, hp⟩
  · rintro ⟨s, hs, hk, hw, hp⟩
    obtain ⟨t, ht, hw, hp⟩ := (bounded_exists R (R.demand + 1)
      (fun s => R.demand < (∑ i ∈ s, R.weight i) ∧ ∀ i ∈ s, σ i = R.sign i)).mpr
        ⟨s, hs, hk, hw, hp⟩
    exact ⟨t, ht, by simpa only [hsum t ht] using hw, hp⟩

/-- Canonical signed clauses remove permutations before global list deduplication. -/
@[expose] def executableBase {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) :
    CNF (Fin n) :=
  ((List.finRange (h + 1)).flatMap fun j => upperList (R j)).dedup

/-- Actual boundary query writing, including constant substitution. -/
@[expose] def executableQuery {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (β : Bool) : CNF (Fin n ⊕ Fin h) :=
  TwoBoundary.query (executableBase R) h (fun j => attainmentList (R j)) β

/-- Deduplication preserves the conjunction of the generated upper clauses. -/
theorem executableBase_eval {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (σ : Fin n → Bool) :
    (executableBase R).eval σ = true ↔ ∀ j, (upperList (R j)).eval σ = true := by
  simp only [executableBase, CNF.eval_eq_true_iff, List.mem_dedup, List.mem_flatMap,
    List.mem_finRange, true_and, forall_exists_index]
  exact forall_comm

/-- A concrete output budget before exploiting cross-row clause coincidences. -/
theorem executableQuery_length {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (β : Bool) :
    (executableQuery R β).length ≤
      ((List.finRange (h + 1)).map fun j => (upperList (R j)).length).sum +
        2 * ∑ j, (attainmentList (R j)).length := by
  apply (TwoBoundary.query_length (executableBase R)
    (fun j => attainmentList (R j)) β).trans
  apply Nat.add_le_add_right
  exact (List.dedup_sublist _).length_le.trans_eq List.length_flatMap

/-- Query writing agrees pointwise with the reviewed globally deduplicated query. -/
theorem executableQuery_eval {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (β : Bool) (σ : Fin n ⊕ Fin h → Bool) :
    (executableQuery R β).eval σ = (globalQuery R β).eval σ := by
  apply Bool.eq_iff_iff.mpr
  simp only [executableQuery, globalQuery, TwoBoundary.query_eval,
    executableBase_eval, upperList_eval, upper_eval, globalBase_upper_eval,
    attainmentList_eval]

/-- Exact counting transfers without an assumed oracle output. -/
theorem executable_counting_identity {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d) :
    Fintype.card {σ : Fin n → Bool // ∀ j, (R j).value σ = (R j).demand} =
      Fintype.card {σ : Fin n ⊕ Fin h → Bool // (executableQuery R false).eval σ = true} -
      Fintype.card {σ : Fin n ⊕ Fin h → Bool // (executableQuery R true).eval σ = true} := by
  simp only [executableQuery_eval]
  exact global_counting_identity R

/-- The executable query retains the advertised width. -/
theorem executableQuery_width {n d h : ℕ} (R : Fin (h + 1) → Row (Fin n) d)
    (β : Bool) (c : Clause (Fin n ⊕ Fin h))
    (hc : c ∈ executableQuery R β) :
    c.length ≤ d + 2 := by
  have hb : ∀ c ∈ executableBase R, c.length ≤ d + 1 := by
    intro c hc
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hc)
    exact upperList_width (R j) c hj
  simpa only [executableQuery, Nat.max_eq_right (by omega : d + 1 ≤ d + 2)] using
    TwoBoundary.query_width (executableBase R)
    (fun j => attainmentList (R j)) (d + 1) d hb
    (fun j t ht => attainmentList_width (R j) t ht) β c hc

end Cslib.Logic.PL.WeightedRow
