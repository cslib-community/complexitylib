/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Tree
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.Ring

/-!
# Sparsification on formulas

The branching step of the sparsification procedure on formulas in conjunctive normal form, as
list operations: reduction (`CNF.Sparsification.reduce`), flowers and petals, the children
(`CNF.Sparsification.child`) and a computed heavy-heart choice (`CNF.Sparsification.choice`).

Formulas are kept in a normal form (`CNF.Sparsification.Normalized`): no clause repeats a literal or
has more than `k` literals, no two clauses have the same literals, and no clause strictly contains
another. Then a formula and its clause set have the same number of clauses, and the list operations
compute the clause-set operations of `Cslib.Logic.PL.ClauseSet.Sparsification`
(`CNF.Sparsification.toClauseSet_child`). Any formula of width `k` is brought into normal form by
`CNF.Sparsification.normalize`.

The candidate hearts of a clause `C` are its sublists selected by the subsets of the first `k`
positions (`CNF.Sparsification.hearts`); for clauses of width `k` these are all of its subclauses,
so every heavy heart is a candidate. The choice takes a heavy candidate of least *rank*
`c (k + 1) + (k - |H|)`, which has the smallest clause size `c` and then the largest heart: a
valid choice (`CNF.Sparsification.choice_spec`). So the list-level step is a branching rule
(`CNF.Sparsification.rule`) on the formulas in normal form, to which the analysis of the branching
tree applies.

## Main definitions

* `Cslib.Logic.PL.CNF.Sparsification.subclause`, `Cslib.Logic.PL.CNF.Sparsification.reduce`,
  `Cslib.Logic.PL.CNF.Sparsification.flower`, `Cslib.Logic.PL.CNF.Sparsification.petals`,
  `Cslib.Logic.PL.CNF.Sparsification.intro`, `Cslib.Logic.PL.CNF.Sparsification.child`,
  `Cslib.Logic.PL.CNF.Sparsification.heavy`, `Cslib.Logic.PL.CNF.Sparsification.hearts`,
  `Cslib.Logic.PL.CNF.Sparsification.candidates`, `Cslib.Logic.PL.CNF.Sparsification.rank`,
  `Cslib.Logic.PL.CNF.Sparsification.choice`, `Cslib.Logic.PL.CNF.Sparsification.next`: the
  list-level step.
* `Cslib.Logic.PL.CNF.Sparsification.isSparse`: the list-level test for sparseness.
* `Cslib.Logic.PL.CNF.Sparsification.dedup`, `Cslib.Logic.PL.CNF.Sparsification.dedupClauses`,
  `Cslib.Logic.PL.CNF.Sparsification.normalize`, `Cslib.Logic.PL.CNF.Sparsification.Normalized`:
  the normal form.
* `Cslib.Logic.PL.CNF.Sparsification.rule`: the list-level branching rule.

## Main results

* `Cslib.Logic.PL.CNF.Sparsification.toClauseSet_child`: the list-level children compute the
  clause-set children.
* `Cslib.Logic.PL.CNF.Sparsification.choice_spec`: the computed choice is valid.
* `Cslib.Logic.PL.CNF.Sparsification.isSparse_eq_true_iff`: the list-level test decides
  sparseness.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Sparsification

open Finset ClauseSet.Sparsification
open scoped List

variable {V : Type*} [DecidableEq V]

/-! ### The list operations -/

/-- Whether every literal of `D` is a literal of `C`. -/
def subclause (D C : Clause V) : Bool := D.all fun l => C.any (· == l)

/-- Remove every clause whose literals strictly contain those of another clause. -/
def reduce (ψ : CNF V) : CNF V :=
  ψ.filter fun C => ψ.all fun D => !(subclause D C && !subclause C D)

/-- The *flower* of `H` at clause size `c`: the clauses of length `c` containing the literals of
`H`. -/
def flower (ψ : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  ψ.filter fun C => C.length == c && subclause H C

/-- The petals `C \ H` of the flower of `H`. -/
def petals (ψ : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  (flower ψ c H).map fun C => C.filter fun l => !H.any (· == l)

/-- The clauses a branch introduces: the heart (`false`) or the petals (`true`). -/
def intro (ψ : CNF V) (c : ℕ) (H : Clause V) (b : Bool) : CNF V :=
  if b then petals ψ c H else [H]

/-- A child of a branching node: add the introduced clauses and reduce. -/
def child (ψ : CNF V) (c : ℕ) (H : Clause V) (b : Bool) : CNF V :=
  reduce (ψ ++ intro ψ c H b)

/-- Whether `H` is a heavy heart for clause size `c`, for the thresholds `θ`. -/
def heavy (θ : ℕ → ℕ) (ψ : CNF V) (x : ℕ × Clause V) : Bool :=
  decide (1 ≤ x.2.length) && decide (x.2.length < x.1) &&
    decide (θ (x.1 - x.2.length) ≤ (flower ψ x.1 x.2).length)

/-- The candidate hearts of a clause: its sublists selected by subsets of the first `k`
positions. -/
def hearts (k : ℕ) (C : Clause V) : List (Clause V) :=
  (List.range k).sublists.map fun S => (C.zipIdx.filter fun p => S.any (· == p.2)).map Prod.fst

/-- The candidate pairs of a clause size and a heart: each clause with its candidate hearts. -/
def candidates (k : ℕ) (ψ : CNF V) : List (ℕ × Clause V) :=
  ψ.flatMap fun C => (hearts k C).map fun H => (C.length, H)

/-- The rank `c (k + 1) + (k - |H|)` of a clause size `c` and a heart `H`: smaller sizes, and then
larger hearts, have smaller ranks. -/
def rank (k : ℕ) (x : ℕ × Clause V) : ℕ := x.1 * (k + 1) + (k - x.2.length)

/-- The computed choice: a heavy candidate of least rank, or `(0, [])` if there is none. -/
def choice (θ : ℕ → ℕ) (k : ℕ) (ψ : CNF V) : ℕ × Clause V :=
  (((List.range ((k + 1) * (k + 1) + 1)).flatMap fun r =>
    ((candidates k ψ).filter (heavy θ ψ)).filter fun x => rank k x == r).head?).getD (0, [])

/-- Whether no candidate is a heavy heart. -/
def isSparse (θ : ℕ → ℕ) (k : ℕ) (ψ : CNF V) : Bool :=
  !(candidates k ψ).any (heavy θ ψ)

/-- One branching step: the heart (`false`) or petal (`true`) child for the computed choice. -/
def next (θ : ℕ → ℕ) (k : ℕ) (ψ : CNF V) (b : Bool) : CNF V :=
  child ψ (choice θ k ψ).1 (choice θ k ψ).2 b

/-- Remove repeated literals of a clause, keeping first occurrences. -/
def dedup (C : Clause V) : Clause V :=
  (C.zipIdx.filter fun p => C.idxOf p.1 == p.2).map Prod.fst

/-- Remove every clause with the same literals as an earlier clause. -/
def dedupClauses (ψ : CNF V) : CNF V :=
  (ψ.zipIdx.filter fun p => ψ.zipIdx.all fun q =>
    !(decide (q.2 < p.2) && subclause q.1 p.1 && subclause p.1 q.1)).map Prod.fst

/-- The normal form of a formula: repeated literals and clauses removed, and reduced. -/
def normalize (φ : CNF V) : CNF V :=
  reduce (dedupClauses (φ.map dedup))

/-! ### Clause sets of formulas -/

/-- A clause set `C` belongs to `ψ.toClauseSet` if and only if `D.toFinset = C` for some clause
`D ∈ ψ`. -/
theorem mem_toClauseSet {ψ : CNF V} {C : Finset (Literal V)} :
    C ∈ ψ.toClauseSet ↔ ∃ D ∈ ψ, D.toFinset = C := by
  simp [CNF.toClauseSet]

private theorem toClauseSet_append (ψ χ : CNF V) :
    (ψ ++ χ).toClauseSet = ψ.toClauseSet ∪ χ.toClauseSet := by
  simp [CNF.toClauseSet, List.toFinset_append]

private theorem toClauseSet_mono {ψ χ : CNF V} (h : ψ ⊆ χ) : ψ.toClauseSet ⊆ χ.toClauseSet := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := mem_toClauseSet.mp hC
  exact mem_toClauseSet.mpr ⟨D, h hD, rfl⟩

private theorem subclause_eq_true_iff {D C : Clause V} :
    subclause D C = true ↔ D.toFinset ⊆ C.toFinset := by
  simp only [subclause, List.all_eq_true, List.any_eq_true, beq_iff_eq, exists_eq_right]
  constructor
  · intro h l hl
    exact List.mem_toFinset.mpr (h l (List.mem_toFinset.mp hl))
  · intro h l hl
    exact List.mem_toFinset.mp (h (List.mem_toFinset.mpr hl))

/-- `reduce ψ` is a sublist of `ψ`. -/
theorem reduce_sublist (ψ : CNF V) : reduce ψ <+ ψ := List.filter_sublist

private theorem not_and_not_subclause_iff {D C : Clause V} :
    (!(subclause D C && !subclause C D)) = true ↔ ¬ D.toFinset ⊂ C.toFinset := by
  rw [Finset.ssubset_def, ← subclause_eq_true_iff, ← subclause_eq_true_iff]
  cases subclause D C <;> cases subclause C D <;> simp

/-- The list-level reduction computes the reduction of clause sets. -/
private theorem toClauseSet_reduce (ψ : CNF V) :
    (reduce ψ).toClauseSet = ClauseSet.Sparsification.reduce ψ.toClauseSet := by
  have hkeep (C : Clause V) : (ψ.all fun D => !(subclause D C && !subclause C D)) = true ↔
      ∀ D' ∈ ψ.toClauseSet, ¬ D' ⊂ C.toFinset := by
    rw [List.all_eq_true]
    constructor
    · intro h D' hD'
      obtain ⟨D, hD, rfl⟩ := mem_toClauseSet.mp hD'
      exact not_and_not_subclause_iff.mp (h D hD)
    · intro h D hD
      exact not_and_not_subclause_iff.mpr (h _ (mem_toClauseSet.mpr ⟨D, hD, rfl⟩))
  ext C'
  rw [mem_toClauseSet, ClauseSet.Sparsification.mem_reduce]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hCψ, hk⟩ := List.mem_filter.mp hC
    exact ⟨mem_toClauseSet.mpr ⟨C, hCψ, rfl⟩, (hkeep C).mp hk⟩
  · rintro ⟨hC', hk⟩
    obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
    exact ⟨C, List.mem_filter.mpr ⟨hC, (hkeep C).mpr hk⟩, rfl⟩

private theorem toClauseSet_flower {ψ : CNF V} (hnd : ∀ C ∈ ψ, C.Nodup) (c : ℕ) (H : Clause V) :
    (flower ψ c H).toClauseSet = ClauseSet.Sparsification.flower ψ.toClauseSet c H.toFinset := by
  ext C'
  rw [mem_toClauseSet, ClauseSet.Sparsification.mem_flower, mem_toClauseSet]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hCψ, hk⟩ := List.mem_filter.mp hC
    simp only [Bool.and_eq_true, beq_iff_eq, subclause_eq_true_iff] at hk
    exact ⟨⟨C, hCψ, rfl⟩, by rw [List.toFinset_card_of_nodup (hnd C hCψ), hk.1], hk.2⟩
  · rintro ⟨⟨C, hC, rfl⟩, hcard, hH⟩
    refine ⟨C, List.mem_filter.mpr ⟨hC, ?_⟩, rfl⟩
    simp only [Bool.and_eq_true, beq_iff_eq, subclause_eq_true_iff]
    exact ⟨by rw [← List.toFinset_card_of_nodup (hnd C hC), hcard], hH⟩

private theorem toFinset_filter_not_mem (C H : Clause V) :
    (C.filter fun l => !H.any (· == l)).toFinset = C.toFinset \ H.toFinset := by
  ext l
  rw [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff, List.mem_toFinset, List.mem_toFinset]
  refine and_congr_right fun _ => ?_
  rw [Bool.not_eq_true', List.any_eq_false]
  exact ⟨fun h hl => h l hl (beq_self_eq_true l), fun h l' hl' heq => h (beq_iff_eq.mp heq ▸ hl')⟩

private theorem toClauseSet_petals {ψ : CNF V} (hnd : ∀ C ∈ ψ, C.Nodup) (c : ℕ) (H : Clause V) :
    (petals ψ c H).toClauseSet = ClauseSet.Sparsification.petals ψ.toClauseSet c H.toFinset := by
  ext C'
  rw [mem_toClauseSet, ClauseSet.Sparsification.mem_petals, ← toClauseSet_flower hnd]
  simp only [petals, List.mem_map, mem_toClauseSet]
  constructor
  · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨C.toFinset, ⟨C, hC, rfl⟩, (toFinset_filter_not_mem C H).symm⟩
  · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨_, ⟨C, hC, rfl⟩, toFinset_filter_not_mem C H⟩

private theorem toClauseSet_intro {ψ : CNF V} (hnd : ∀ C ∈ ψ, C.Nodup) (c : ℕ) (H : Clause V)
    (b : Bool) :
    (intro ψ c H b).toClauseSet =
      ClauseSet.Sparsification.intro ψ.toClauseSet c H.toFinset b := by
  cases b
  · simp [intro, ClauseSet.Sparsification.intro, CNF.toClauseSet]
  · simp only [intro, ite_true, ClauseSet.Sparsification.intro]
    exact toClauseSet_petals hnd c H

/-- The list-level children compute the clause-set children. -/
theorem toClauseSet_child {ψ : CNF V} (hnd : ∀ C ∈ ψ, C.Nodup) (c : ℕ) (H : Clause V)
    (b : Bool) :
    (child ψ c H b).toClauseSet =
      ClauseSet.Sparsification.child ψ.toClauseSet c H.toFinset b := by
  rw [child, toClauseSet_reduce, toClauseSet_append, toClauseSet_intro hnd]
  rfl

/-! ### The normal form -/

/-- The normal form of the list-level procedure, for width `k`: no clause repeats a literal or
has more than `k` literals, no two clauses have the same literals, and no clause strictly contains
another. -/
structure Normalized (k : ℕ) (ψ : CNF V) : Prop where
  nodup : ∀ C ∈ ψ, C.Nodup
  length_le : ∀ C ∈ ψ, C.length ≤ k
  nodup_toFinset : (ψ.map List.toFinset).Nodup
  reduced : Reduced ψ.toClauseSet

/-- A formula in normal form has as many clauses as its clause set. -/
theorem Normalized.card_toClauseSet {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) :
    ψ.toClauseSet.card = ψ.length := by
  rw [CNF.toClauseSet, List.toFinset_card_of_nodup h.nodup_toFinset, List.length_map]

/-- Every clause in the clause set of a `k`-normalized formula has at most `k` literals. -/
theorem Normalized.card_le {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) :
    ∀ C ∈ ψ.toClauseSet, C.card ≤ k := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := mem_toClauseSet.mp hC
  rw [List.toFinset_card_of_nodup (h.nodup D hD)]
  exact h.length_le D hD

private theorem Normalized.length_flower {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) (c : ℕ)
    (H : Clause V) : (flower ψ c H).length =
      (ClauseSet.Sparsification.flower ψ.toClauseSet c H.toFinset).card := by
  have hsub : flower ψ c H <+ ψ := List.filter_sublist
  rw [← toClauseSet_flower h.nodup, CNF.toClauseSet,
    List.toFinset_card_of_nodup ((hsub.map _).nodup h.nodup_toFinset), List.length_map]

private theorem heavy_eq_true_iff {θ : ℕ → ℕ} {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) {c : ℕ}
    {H : Clause V} (hH : H.Nodup) :
    heavy θ ψ (c, H) = true ↔ Heavy θ ψ.toClauseSet c H.toFinset := by
  simp only [heavy, Bool.and_eq_true, decide_eq_true_eq, Heavy,
    List.toFinset_card_of_nodup hH, h.length_flower, and_assoc]

/-! ### Candidates -/

omit [DecidableEq V] in
private theorem mem_hearts {k : ℕ} {C H : Clause V} (hH : H ∈ hearts k C) : H <+ C := by
  obtain ⟨S, -, rfl⟩ := List.mem_map.mp hH
  conv_rhs => rw [← List.zipIdx_map_fst 0 C]
  exact List.filter_sublist.map _

/-- For a clause of width `k`, every subclause is a candidate heart. -/
private theorem exists_mem_hearts {k : ℕ} {C : Clause V} (hk : C.length ≤ k)
    {H' : Finset (Literal V)} (hH' : H' ⊆ C.toFinset) : ∃ H ∈ hearts k C, H.toFinset = H' := by
  set S := (C.zipIdx.filter fun p => decide (p.1 ∈ H')).map Prod.snd
  have hS : S ∈ (List.range k).sublists := by
    refine List.mem_sublists.mpr (List.Sublist.trans ?_ (List.range_sublist.mpr hk))
    rw [List.range_eq_range', ← List.zipIdx_map_snd]
    exact List.filter_sublist.map _
  -- an entry of the clause is selected exactly when its literal is in `H'`
  have hsel : ∀ p ∈ C.zipIdx, (S.any fun i => i == p.2) = decide (p.1 ∈ H') := by
    intro p hp
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨i, hi, hip⟩
      rw [beq_iff_eq] at hip
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
      obtain ⟨hqz, hqH⟩ := List.mem_filter.mp hq
      have h₁ := List.mem_zipIdx_iff_getElem?.mp hqz
      have h₂ := List.mem_zipIdx_iff_getElem?.mp hp
      rw [hip, h₂, Option.some_inj] at h₁
      rw [h₁]
      exact of_decide_eq_true hqH
    · intro hpH
      exact ⟨p.2, List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true hpH⟩, rfl⟩,
        beq_self_eq_true _⟩
  refine ⟨_, List.mem_map.mpr ⟨S, hS, rfl⟩, ?_⟩
  rw [List.filter_congr hsel]
  ext l
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  · intro hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (hH' hl))
    exact ⟨(C[i], i), List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_eq_getElem hi), decide_eq_true hl⟩, rfl⟩

omit [DecidableEq V] in
private theorem mem_candidates {k : ℕ} {ψ : CNF V} {x : ℕ × Clause V} (hx : x ∈ candidates k ψ) :
    ∃ C ∈ ψ, x.1 = C.length ∧ x.2 <+ C := by
  obtain ⟨C, hC, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hx
  exact ⟨C, hC, rfl, mem_hearts hH⟩

private theorem Normalized.nodup_of_mem_candidates {k : ℕ} {ψ : CNF V} (h : Normalized k ψ)
    {x : ℕ × Clause V} (hx : x ∈ candidates k ψ) : x.2.Nodup := by
  obtain ⟨C, hC, -, hsub⟩ := mem_candidates hx
  exact hsub.nodup (h.nodup C hC)

/-- Every heavy heart of a formula in normal form is a candidate. -/
private theorem Normalized.exists_mem_candidates {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {ψ : CNF V}
    (h : Normalized k ψ) {c : ℕ} {H' : Finset (Literal V)} (hH' : Heavy θ ψ.toClauseSet c H') :
    ∃ H, (c, H) ∈ candidates k ψ ∧ H.toFinset = H' := by
  obtain ⟨C', hC'⟩ := hH'.flower_nonempty hθ
  obtain ⟨hC'ψ, hcard, hsub⟩ := ClauseSet.Sparsification.mem_flower.mp hC'
  obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'ψ
  obtain ⟨H, hH, hHeq⟩ := exists_mem_hearts (h.length_le C hC) hsub
  refine ⟨H, List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨H, hH, ?_⟩⟩, hHeq⟩
  rw [← hcard, List.toFinset_card_of_nodup (h.nodup C hC)]

private theorem rank_lt {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) {x : ℕ × Clause V}
    (hx : x ∈ candidates k ψ) : rank k x < (k + 1) * (k + 1) + 1 := by
  obtain ⟨C, hC, hx1, -⟩ := mem_candidates hx
  have h₁ : C.length * (k + 1) ≤ k * (k + 1) := Nat.mul_le_mul_right _ (h.length_le C hC)
  have h₂ : (k + 1) * (k + 1) = k * (k + 1) + k + 1 := by ring
  unfold rank
  rw [hx1]
  omega

omit [DecidableEq V] in
/-- A smaller rank has a clause size at most as large, and a heart at least as large at the same
clause size. -/
private theorem le_of_rank_le {k : ℕ} {x y : ℕ × Clause V} (hx : x.2.length ≤ k)
    (hy : y.2.length ≤ k) (h : rank k x ≤ rank k y) :
    x.1 ≤ y.1 ∧ (x.1 = y.1 → y.2.length ≤ x.2.length) := by
  unfold rank at h
  constructor
  · by_contra hlt
    have h₁ : (y.1 + 1) * (k + 1) ≤ x.1 * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    have h₂ : (y.1 + 1) * (k + 1) = y.1 * (k + 1) + k + 1 := by ring
    omega
  · intro heq
    rw [heq] at h
    omega

/-- The head of a list of blocks, over ranks below `R`: it lies in the first nonempty block. -/
private theorem exists_of_head?_flatMap_range {α : Type*} (g : ℕ → List α) {R : ℕ} {x : α}
    (hx : ((List.range R).flatMap g).head? = some x) :
    ∃ r < R, x ∈ g r ∧ ∀ r' < r, g r' = [] := by
  induction R with
  | zero => simp at hx
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, List.head?_append] at hx
    rcases hnil : ((List.range R).flatMap g).head? with _ | y
    · rw [hnil, Option.none_or] at hx
      have hg : ∀ r' < R, g r' = [] := fun r' hr' =>
        List.flatMap_eq_nil_iff.mp (List.head?_eq_none_iff.mp hnil) r' (List.mem_range.mpr hr')
      refine ⟨R, Nat.lt_succ_self R, ?_, hg⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
      exact List.mem_of_mem_head? hx
    · rw [hnil, Option.some_or] at hx
      cases hx
      obtain ⟨r, hr, hxr, hmin⟩ := ih hnil
      exact ⟨r, by omega, hxr, hmin⟩

/-- **The computed choice is valid.** At a formula in normal form that is not sparse, the computed
choice is a heavy heart with the smallest clause size, and among those the largest heart. -/
theorem choice_spec {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {ψ : CNF V} (h : Normalized k ψ)
    (hns : ¬ Sparse θ ψ.toClauseSet) :
    Choice θ ψ.toClauseSet (choice θ k ψ).1 (choice θ k ψ).2.toFinset ∧
      (choice θ k ψ).2.Nodup := by
  set hc := (candidates k ψ).filter (heavy θ ψ)
  set g : ℕ → List (ℕ × Clause V) := fun r => hc.filter fun x => rank k x == r
  -- every heavy heart is a heavy candidate in the block of its rank
  have hcand : ∀ c H', Heavy θ ψ.toClauseSet c H' →
      ∃ y ∈ hc, y.1 = c ∧ y.2.toFinset = H' ∧ y ∈ g (rank k y) := by
    intro c H' hH'
    obtain ⟨H, hH, hHeq⟩ := h.exists_mem_candidates hθ hH'
    have hy : (c, H) ∈ hc := List.mem_filter.mpr ⟨hH, (heavy_eq_true_iff h
      (h.nodup_of_mem_candidates hH)).mpr (hHeq ▸ hH')⟩
    exact ⟨(c, H), hy, rfl, hHeq, List.mem_filter.mpr ⟨hy, beq_self_eq_true _⟩⟩
  obtain ⟨c₀, H₀, hH₀⟩ : ∃ c H, Heavy θ ψ.toClauseSet c H := by
    simpa [Sparse] using hns
  obtain ⟨y₀, hy₀, -, -, hy₀g⟩ := hcand c₀ H₀ hH₀
  have hy₀R : rank k y₀ < (k + 1) * (k + 1) + 1 := rank_lt h (List.mem_filter.mp hy₀).1
  -- the head of the blocks
  obtain ⟨x, hx⟩ : ∃ x, ((List.range ((k + 1) * (k + 1) + 1)).flatMap g).head? = some x := by
    rcases hhead : ((List.range ((k + 1) * (k + 1) + 1)).flatMap g).head? with _ | x
    · exfalso
      have := List.flatMap_eq_nil_iff.mp (List.head?_eq_none_iff.mp hhead) (rank k y₀)
        (List.mem_range.mpr hy₀R)
      rw [this] at hy₀g
      simp at hy₀g
    · exact ⟨x, rfl⟩
  have hchoice : choice θ k ψ = x := by
    simp only [choice]
    rw [show (List.range ((k + 1) * (k + 1) + 1)).flatMap g = _ from rfl, hx, Option.getD_some]
  obtain ⟨r, -, hxr, hmin⟩ := exists_of_head?_flatMap_range g hx
  obtain ⟨hxhc, hxr'⟩ := List.mem_filter.mp hxr
  rw [beq_iff_eq] at hxr'
  obtain ⟨hxcand, hxheavy⟩ := List.mem_filter.mp hxhc
  have hxnd := h.nodup_of_mem_candidates hxcand
  -- a heavy candidate `y` has rank at least that of `x`
  have hle : ∀ y ∈ hc, y ∈ g (rank k y) → rank k x ≤ rank k y := by
    intro y _ hyg
    by_contra hlt
    rw [hmin (rank k y) (by omega)] at hyg
    simp at hyg
  have hlen (y : ℕ × Clause V) (hy : y ∈ candidates k ψ) : y.2.length ≤ k := by
    obtain ⟨C, hC, -, hsub⟩ := mem_candidates hy
    exact hsub.length_le.trans (h.length_le C hC)
  rw [hchoice]
  refine ⟨⟨(heavy_eq_true_iff h hxnd).mp hxheavy, fun c' H' hH' => ?_, fun H' hH' => ?_⟩, hxnd⟩
  · obtain ⟨y, hy, rfl, -, hyg⟩ := hcand c' H' hH'
    exact (le_of_rank_le (hlen x hxcand) (hlen y (List.mem_filter.mp hy).1)
      (hle y hy hyg)).1
  · obtain ⟨y, hy, hy1, rfl, hyg⟩ := hcand x.1 H' hH'
    have hynd := h.nodup_of_mem_candidates (List.mem_filter.mp hy).1
    rw [List.toFinset_card_of_nodup hynd, List.toFinset_card_of_nodup hxnd]
    exact (le_of_rank_le (hlen x hxcand) (hlen y (List.mem_filter.mp hy).1)
      (hle y hy hyg)).2 hy1.symm

/-- The list-level test decides sparseness of formulas in normal form. -/
theorem isSparse_eq_true_iff {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {ψ : CNF V}
    (h : Normalized k ψ) : isSparse θ k ψ = true ↔ Sparse θ ψ.toClauseSet := by
  simp only [isSparse, Bool.not_eq_true', List.any_eq_false]
  constructor
  · intro hno c H' hH'
    obtain ⟨H, hH, hHeq⟩ := h.exists_mem_candidates hθ hH'
    exact hno _ hH ((heavy_eq_true_iff h (h.nodup_of_mem_candidates hH)).mpr (hHeq ▸ hH'))
  · intro hs x hx hheavy
    exact hs x.1 x.2.toFinset ((heavy_eq_true_iff h (h.nodup_of_mem_candidates hx)).mp hheavy)

/-! ### The step preserves the normal form -/

private theorem reduce_nodup_toFinset {ψ : CNF V} (h : (ψ.map List.toFinset).Nodup) :
    ((reduce ψ).map List.toFinset).Nodup :=
  ((reduce_sublist ψ).map _).nodup h

/-- **The children are in normal form.** -/
private theorem normalized_child {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {ψ : CNF V}
    (h : Normalized k ψ) {c : ℕ} {H : Clause V} (hH : H.Nodup)
    (hheavy : Heavy θ ψ.toClauseSet c H.toFinset) (b : Bool) : Normalized k (child ψ c H b) := by
  have hsub : child ψ c H b <+ ψ ++ intro ψ c H b := reduce_sublist _
  -- the introduced clauses are new, distinct, without repetitions and narrower
  have hintro : ∀ C ∈ intro ψ c H b, C.Nodup ∧
      ∃ D ∈ ψ, C.toFinset ⊂ D.toFinset := by
    intro C hC
    have hC' : C.toFinset ∈ ClauseSet.Sparsification.intro ψ.toClauseSet c H.toFinset b := by
      rw [← toClauseSet_intro h.nodup]
      exact mem_toClauseSet.mpr ⟨C, hC, rfl⟩
    obtain ⟨D', hD', hlt⟩ := exists_flower_ssuperset hθ hheavy hC'
    obtain ⟨D, hD, rfl⟩ := mem_toClauseSet.mp (flower_subset _ _ _ hD')
    refine ⟨?_, D, hD, hlt⟩
    cases b
    · simp only [intro, Bool.false_eq_true, ite_false, List.mem_singleton] at hC
      exact hC ▸ hH
    · simp only [intro, ite_true, petals, List.mem_map] at hC
      obtain ⟨E, hE, rfl⟩ := hC
      exact (h.nodup E (List.filter_sublist.subset hE)).filter _
  have hnodupIntro : ((intro ψ c H b).map List.toFinset).Nodup := by
    cases b
    · simp [intro]
    · simp only [intro, ite_true, petals, List.map_map]
      refine List.Nodup.map_on ?_ (((List.filter_sublist).map _).nodup h.nodup_toFinset |>.of_map _)
      intro E hE F hF heq
      have hE' := List.mem_filter.mp hE
      have hF' := List.mem_filter.mp hF
      simp only [Bool.and_eq_true, beq_iff_eq, subclause_eq_true_iff] at hE' hF'
      simp only [Function.comp_apply, toFinset_filter_not_mem] at heq
      have hEF : E.toFinset = F.toFinset := by
        rw [← sdiff_union_of_subset hE'.2.2, ← sdiff_union_of_subset hF'.2.2, heq]
      exact List.inj_on_of_nodup_map h.nodup_toFinset hE'.1 hF'.1 hEF
  refine ⟨fun C hC => ?_, fun C hC => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp (hsub.subset hC) with hC | hC
    · exact h.nodup C hC
    · exact (hintro C hC).1
  · rcases List.mem_append.mp (hsub.subset hC) with hC | hC
    · exact h.length_le C hC
    · obtain ⟨hnd, D, hD, hlt⟩ := hintro C hC
      rw [← List.toFinset_card_of_nodup hnd]
      exact (card_lt_card hlt).le.trans (by
        rw [List.toFinset_card_of_nodup (h.nodup D hD)]; exact h.length_le D hD)
  · refine (hsub.map _).nodup ?_
    rw [List.map_append, List.nodup_append]
    refine ⟨h.nodup_toFinset, hnodupIntro, fun A hA B hB hAB => ?_⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hA
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hB
    obtain ⟨-, D, hD, hlt⟩ := hintro E hE
    exact h.reduced _ (mem_toClauseSet.mpr ⟨D, hD, rfl⟩) _ (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
      (hAB ▸ hlt)
  · rw [child, toClauseSet_reduce]
    exact reduced_reduce _

/-- The clause set of `next θ k ψ b` equals the clause-set child for the computed choice. -/
theorem toClauseSet_next {θ : ℕ → ℕ} {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) (b : Bool) :
    (next θ k ψ b).toClauseSet = ClauseSet.Sparsification.child ψ.toClauseSet
      (choice θ k ψ).1 (choice θ k ψ).2.toFinset b :=
  toClauseSet_child h.nodup _ _ b

/-- At a non-sparse `k`-normalized formula, one branching step preserves normal form. -/
theorem normalized_next {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {ψ : CNF V} (h : Normalized k ψ)
    (hns : ¬ Sparse θ ψ.toClauseSet) (b : Bool) : Normalized k (next θ k ψ b) :=
  normalized_child hθ h (choice_spec hθ h hns).2 (choice_spec hθ h hns).1.1 b

/-! ### The branching rule -/

/-- **The list-level branching rule**, on formulas in normal form: the computed choice, and at a
sparse formula no step. -/
def rule {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) (k : ℕ) :
    BranchingRule θ V {ψ : CNF V // Normalized k ψ} where
  toClauseSet ψ := ψ.1.toClauseSet
  next ψ b := if hs : isSparse θ k ψ.1 = true then ψ else
    ⟨next θ k ψ.1 b, normalized_next hθ ψ.2 (fun h => hs ((isSparse_eq_true_iff hθ ψ.2).mpr h)) b⟩
  exists_choice_next ψ hns := by
    have hs : ¬ isSparse θ k ψ.1 = true := fun hs => hns ((isSparse_eq_true_iff hθ ψ.2).mp hs)
    refine ⟨_, _, (choice_spec hθ ψ.2 hns).1, fun b => ?_⟩
    simp only [hs]
    exact toClauseSet_next ψ.2 b

private theorem rule_next_val {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ}
    (ψ : {ψ : CNF V // Normalized k ψ}) (hs : isSparse θ k ψ.1 = false) (b : Bool) :
    ((rule hθ k).next ψ b).1 = next θ k ψ.1 b := by
  simp [rule, hs]

/-! ### Normalization -/

private theorem mem_dedup {C : Clause V} {l : Literal V} : l ∈ dedup C ↔ l ∈ C := by
  simp only [dedup, List.mem_map, List.mem_filter, beq_iff_eq, Prod.exists, exists_and_right,
    exists_eq_right]
  constructor
  · rintro ⟨i, hi, -⟩
    exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hi)
  · intro hl
    refine ⟨C.idxOf l, List.mem_zipIdx_iff_getElem?.mpr ?_, rfl⟩
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hl), List.getElem_idxOf]

private theorem nodup_dedup (C : Clause V) : (dedup C).Nodup := by
  have hzip : C.zipIdx.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    have := congrArg Prod.snd heq
    simp only [List.getElem_zipIdx, Nat.zero_add] at this
    omega
  refine (hzip.filter _).map_on ?_
  rintro ⟨u, i⟩ hu ⟨v, j⟩ hv (rfl : u = v)
  simp only [List.mem_filter, beq_iff_eq] at hu hv
  rw [← hu.2, ← hv.2]

private theorem length_dedup_le (C : Clause V) : (dedup C).length ≤ C.length := by
  rw [← List.toFinset_card_of_nodup (nodup_dedup C)]
  refine (card_le_card fun l hl => ?_).trans (List.toFinset_card_le C)
  exact List.mem_toFinset.mpr (mem_dedup.mp (List.mem_toFinset.mp hl))

/-- Deduplicating a clause preserves its set of literals. -/
theorem toFinset_dedup (C : Clause V) : (dedup C).toFinset = C.toFinset := by
  ext l
  simp [mem_dedup]

/-- `dedupClauses ψ` is a sublist of `ψ`. -/
theorem dedupClauses_sublist (ψ : CNF V) : dedupClauses ψ <+ ψ := by
  conv_rhs => rw [← List.zipIdx_map_fst 0 ψ]
  exact List.filter_sublist.map _

omit [DecidableEq V] in
private theorem pairwise_zipIdx (ψ : CNF V) :
    ψ.zipIdx.Pairwise fun p q => p.2 < q.2 := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_zipIdx, Nat.zero_add]
  exact hij

private theorem nodup_toFinset_dedupClauses (ψ : CNF V) :
    ((dedupClauses ψ).map List.toFinset).Nodup := by
  rw [dedupClauses, List.map_map, List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine ((pairwise_zipIdx ψ).filter _).imp_of_mem fun {p q} _ hq hpq heq => ?_
  obtain ⟨hp, -⟩ := List.mem_filter.mp ‹p ∈ _›
  obtain ⟨-, hkeep⟩ := List.mem_filter.mp hq
  have := List.all_eq_true.mp hkeep p hp
  simp only [Function.comp_apply] at heq
  have h₁ : subclause p.1 q.1 = true := subclause_eq_true_iff.mpr heq.le
  have h₂ : subclause q.1 p.1 = true := subclause_eq_true_iff.mpr heq.ge
  simp [hpq, h₁, h₂] at this

private theorem toClauseSet_dedupClauses (ψ : CNF V) :
    (dedupClauses ψ).toClauseSet = ψ.toClauseSet := by
  refine Finset.Subset.antisymm (toClauseSet_mono (dedupClauses_sublist ψ).subset) ?_
  intro C' hC'
  obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
  -- the first clause with the same literals is kept
  classical
  have hex : ∃ i, ∃ hi : i < ψ.length, ψ[i].toFinset = C.toFinset := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hC
    exact ⟨i, hi, rfl⟩
  set i := Nat.find hex
  obtain ⟨hi, hieq⟩ := Nat.find_spec hex
  refine mem_toClauseSet.mpr ⟨ψ[i], List.mem_map.mpr ⟨(ψ[i], i), List.mem_filter.mpr
    ⟨List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi), ?_⟩, rfl⟩, hieq⟩
  refine List.all_eq_true.mpr fun q hq => ?_
  obtain ⟨j, hj, hjq⟩ : ∃ j, ∃ hj : j < ψ.length, q = (ψ[j], j) := by
    have := List.mem_zipIdx_iff_getElem?.mp hq
    rw [List.getElem?_eq_some_iff] at this
    obtain ⟨hj, hjq⟩ := this
    exact ⟨q.2, hj, by rw [hjq]⟩
  subst hjq
  by_cases hji : j < i
  · have hne : ψ[j].toFinset ≠ ψ[i].toFinset := fun heq =>
      Nat.find_min hex hji ⟨hj, heq.trans hieq⟩
    have hsub : ¬ (subclause ψ[j] ψ[i] = true ∧ subclause ψ[i] ψ[j] = true) := fun ⟨h₁, h₂⟩ =>
      hne (Finset.Subset.antisymm (subclause_eq_true_iff.mp h₁) (subclause_eq_true_iff.mp h₂))
    cases h₁ : subclause ψ[j] ψ[i] <;> cases h₂ : subclause ψ[i] ψ[j] <;> simp_all
  · simp [hji]

private theorem toClauseSet_normalize (φ : CNF V) :
    (normalize φ).toClauseSet = ClauseSet.Sparsification.reduce φ.toClauseSet := by
  rw [normalize, toClauseSet_reduce, toClauseSet_dedupClauses]
  congr 1
  simp [CNF.toClauseSet, List.map_map, Function.comp_def, toFinset_dedup]

/-- **Normalization.** Every formula of width `k` has a normal form with the same solutions. -/
theorem normalized_normalize {k : ℕ} {φ : CNF V} (hφ : ∀ C ∈ φ, C.length ≤ k) :
    Normalized k (normalize φ) := by
  have hsub : normalize φ <+ φ.map dedup :=
    (reduce_sublist _).trans (dedupClauses_sublist _)
  refine ⟨fun C hC => ?_, fun C hC => ?_, ?_, ?_⟩
  · obtain ⟨D, -, rfl⟩ := List.mem_map.mp (hsub.subset hC)
    exact nodup_dedup D
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC)
    exact (length_dedup_le D).trans (hφ D hD)
  · exact reduce_nodup_toFinset (nodup_toFinset_dedupClauses _)
  · rw [toClauseSet_normalize]
    exact reduced_reduce _

/-- The clause set of `normalize φ` has the same solutions as `φ`. -/
theorem sat_toClauseSet_normalize_iff (φ : CNF V) (x : V → Bool) :
    (normalize φ).toClauseSet.Sat x ↔ φ.eval x = true := by
  rw [toClauseSet_normalize, sat_reduce_iff, CNF.sat_toClauseSet_iff]

end Cslib.Logic.PL.CNF.Sparsification
