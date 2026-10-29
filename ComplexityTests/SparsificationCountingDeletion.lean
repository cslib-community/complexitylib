/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingDeletion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingDeletion

-- A negated-heart unit deletes a clause outside the selected flower.
theorem negated_unit_deletes_unselected_pair : {(0, false), (1, true)} ∉ countingChild
    ({{(0, false), (1, true)}, {(0, true), (2, true)}, {(0, true), (3, true)}} :
      ClauseSet (Fin 4)) 2 {(0, true)} true := by decide

private def θ (j : ℕ) := 2 ^ j

private theorem θpos (j : ℕ) : 1 ≤ θ j := by
  induction j with
  | zero => decide
  | succ j ih =>
    change 1 ≤ 2 ^ (j + 1)
    rw [pow_succ]
    change 1 ≤ 2 ^ j at ih
    omega

private theorem θtwo {j : ℕ} (hj : 0 < j) : 2 ≤ θ j := by
  cases j with
  | zero => omega
  | succ j =>
    change 2 ≤ 2 ^ (j + 1)
    rw [pow_succ]
    have := θpos j
    change 1 ≤ 2 ^ j at this
    omega

-- A heavy flower contains two different clauses. Their common width establishes the minimum
-- priority, and the intersection cap establishes the maximum-heart priority.
private theorem choice_of_pairs {V : Type*} [DecidableEq V]
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)} (hh : Heavy θ ψ c H)
    (hw : ∀ C ∈ ψ, ∀ D ∈ ψ, C ≠ D → C.card = D.card → C.card = c)
    (hinter : ∀ C ∈ ψ, ∀ D ∈ ψ, C ≠ D → (C ∩ D).card ≤ H.card) : Choice θ ψ c H := by
  refine ⟨hh, ?_, ?_⟩
  · intro c' H' hh'
    have htwo : 2 ≤ (flower ψ c' H').card := (θtwo (Nat.sub_pos_of_lt hh'.2.1)).trans hh'.2.2
    obtain ⟨C, hC, D, hD, hCD⟩ := one_lt_card.mp (by omega : 1 < (flower ψ c' H').card)
    have hCc := (mem_flower.mp hC).2.1
    have hDc := (mem_flower.mp hD).2.1
    have := hw C (flower_subset _ _ _ hC) D (flower_subset _ _ _ hD) hCD (by omega)
    omega
  · intro H' hh'
    have htwo : 2 ≤ (flower ψ c H').card := (θtwo (Nat.sub_pos_of_lt hh'.2.1)).trans hh'.2.2
    obtain ⟨C, hC, D, hD, hCD⟩ := one_lt_card.mp (by omega : 1 < (flower ψ c H').card)
    exact (card_le_card (subset_inter (mem_flower.mp hC).2.2 (mem_flower.mp hD).2.2)).trans
      (hinter C (flower_subset _ _ _ hC) D (flower_subset _ _ _ hD) hCD)

private def root : ClauseSet (Fin 9) :=
  {{(1, true), (2, true)}, {(0, true), (1, false), (3, true)},
    {(0, true), (1, true), (4, true)}, {(0, true), (5, true), (6, true)},
    {(0, true), (7, true), (8, true)}}

private def first := countingChild root 3 {(0, true)} true
private def nodes (tail : Bool) (i : ℕ) :=
  if i = 0 then root else if i = 1 then first else countingChild first 2 {(1, true)} tail
private def sizes (i : ℕ) := if i = 0 then 3 else 2
private def hearts (i : ℕ) : Finset (Literal (Fin 9)) :=
  if i = 0 then {(0, true)} else {(1, true)}
private def dirs (tail : Bool) (i : ℕ) := if i = 0 then true else tail

private theorem firstChoice : Choice θ root 3 {(0, true)} := by
  apply choice_of_pairs
  · unfold Heavy; decide
  · decide
  · decide

private theorem secondChoice : Choice θ first 2 {(1, true)} := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Heavy; decide
  · intro c H hh
    have := hh.1
    have := hh.2.1
    omega
  · intro H hh
    have := hh.2.1
    change H.card ≤ 1
    omega

private theorem steps (tail : Bool) : ∀ i < 2,
    nodes tail (i + 1) = countingChild (nodes tail i) (sizes i) (hearts i) (dirs tail i) := by
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> rfl

private theorem choices (tail : Bool) : ∀ i < 2,
    Choice θ (nodes tail i) (sizes i) (hearts i) := by
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact firstChoice
  · exact secondChoice

private theorem rootReduced : Reduced root := by unfold Reduced; decide

-- Three width-two clauses disappear, but the initial root pair must not be counted as marked.
example : (first.filter fun C => C.card = 2 ∧ C ∉ nodes true 2).card = 3 := by decide
example : (first.filter fun C => C ∉ root ∧ C.card = 2 ∧ C ∉ nodes true 2).card = 2 := by decide

-- The unselected marked pair has NO petal donor. The added negated-heart unit is indispensable.
example : {(1, false), (3, true)} ∉ flower first 2 {(1, true)} := by decide
example : ¬ ∃ D ∈ petals first 2 {(1, true)}, D ⊆ ({(1, false), (3, true)} :
    Finset (Literal (Fin 9))) := by decide
example : {(1, false)} ∈ countingIntro first 2 {(1, true)} true \ (first ∪ root) ∧
    ({(1, false)} : Finset (Literal (Fin 9))) ⊂ {(1, false), (3, true)} := by decide

private theorem second_true_unit_insertions :
    ((countingIntro first 2 {(1, true)} true \ (first ∪ root)).filter
      fun D => D.card = 1).card = 3 := by decide

private theorem second_false_unit_insertions :
    ((countingIntro first 2 {(1, true)} false \ (first ∪ root)).filter
      fun D => D.card = 1).card = 1 := by decide

-- Combining `card_counting_deleted_marked_le` with the exact unit insertion counts (`3` on the B
-- branch and `1` on the A branch) bounds the marked width-2 deletions at step `m = 1` by `12` and
-- `4`, while the actual deleted counts are `2` and `1`.
example :
    (first.filter fun C => C ∉ root ∧ C.card = 2 ∧ C ∉ nodes true 2).card ≤ 12 ∧
      (first.filter fun C => C ∉ root ∧ C.card = 2 ∧ C ∉ nodes false 2).card = 1 ∧
      (first.filter fun C => C ∉ root ∧ C.card = 2 ∧ C ∉ nodes false 2).card ≤ 4 := by
  have htrue := card_counting_deleted_marked_le θpos 2 (nodes true) sizes hearts (dirs true)
    (steps true) (choices true) rootReduced (m := 1) (by omega) 2
  have hfalse := card_counting_deleted_marked_le θpos 2 (nodes false) sizes hearts (dirs false)
    (steps false) (choices false) rootReduced (m := 1) (by omega) 2
  simp only [Nat.Ico_succ_singleton, sum_singleton] at htrue hfalse
  change _ ≤ 2 * 2 ^ 1 * ((countingIntro first 2 {(1, true)} true \ (first ∪ root)).filter
    fun D => D.card = 1).card at htrue
  change _ ≤ 2 * 2 ^ 1 * ((countingIntro first 2 {(1, true)} false \ (first ∪ root)).filter
    fun D => D.card = 1).card at hfalse
  rw [second_true_unit_insertions] at htrue
  rw [second_false_unit_insertions] at hfalse
  exact ⟨htrue, by decide, hfalse⟩

-- Unit deletions have zero charge (`Ico 1 1` is empty), so `card_counting_deleted_marked_le` at
-- `j = 1` implies that every marked unit clause in `first` survives into `nodes tail 2`.
example (tail : Bool) (C : Finset (Literal (Fin 9)))
    (hfirst : C ∈ first) (hroot : C ∉ root) (hcard : C.card = 1) :
    C ∈ nodes tail 2 := by
  by_contra hgone
  have hle := card_counting_deleted_marked_le θpos 2 (nodes tail) sizes hearts (dirs tail)
    (steps tail) (choices tail) rootReduced (m := 1) (by omega) 1
  have hmem : C ∈ first.filter (fun D => D ∉ root ∧ D.card = 1 ∧ D ∉ nodes tail 2) :=
    mem_filter.mpr ⟨hfirst, hroot, hcard, hgone⟩
  have hpos : 0 < (first.filter fun D => D ∉ root ∧ D.card = 1 ∧ D ∉ nodes tail 2).card :=
    card_pos.mpr ⟨C, hmem⟩
  simp only [Ico_self, sum_empty] at hle
  change (first.filter fun D => D ∉ root ∧ D.card = 1 ∧ D ∉ nodes tail 2).card ≤ 0 at hle
  omega

-- Because `{(0, true), (1, false), (3, true)} ∉ nodes true 2`, the subclause witness provided by
-- `exists_mem_counting_node_subset` must be a strict subclause of width at most `2`.
example : ∃ D ∈ nodes true 2,
    D ⊂ ({(0, true), (1, false), (3, true)} : Finset (Literal (Fin 9))) ∧ D.card ≤ 2 := by
  obtain ⟨D, hD, hsub⟩ :=
    exists_mem_counting_node_subset 2 (nodes true) sizes hearts (dirs true) (steps true)
      (t := 2) le_rfl (C := {(0, true), (1, false), (3, true)}) (by decide)
  have hne : D ≠ {(0, true), (1, false), (3, true)} := by
    rintro rfl
    revert hD; decide
  have hssub : D ⊂ {(0, true), (1, false), (3, true)} := ssubset_of_subset_of_ne hsub hne
  have hlt : D.card < ({(0, true), (1, false), (3, true)} : Finset (Literal (Fin 9))).card :=
    card_lt_card hssub
  have h3 : ({(0, true), (1, false), (3, true)} : Finset (Literal (Fin 9))).card = 3 := by decide
  exact ⟨D, hD, hssub, by omega⟩

-- Empty variables and an empty root clause need no inhabitance at a zero-length prefix.
example : ∃ D ∈ ({∅} : ClauseSet Empty), D = ∅ := by
  obtain ⟨D, hD, hsub⟩ :=
    exists_mem_counting_node_subset 0 (fun _ => ({∅} : ClauseSet Empty)) id
      (fun _ => ∅) (fun _ => false) (by intro i hi; omega) (t := 0) le_rfl
      (C := (∅ : Finset (Literal Empty))) (by decide)
  exact ⟨D, hD, subset_empty.mp hsub⟩

-- The FULL insertion balance still needs nontautology. In this reduced, legal-choice root,
-- one newly introduced width-two petal is immediately removed by the added negated unit.
private def tautRoot : ClauseSet (Fin 8) :=
  {{(0, true), (0, false), (1, true)}, {(0, true), (2, true), (3, true)},
    {(0, true), (4, true), (5, true)}, {(0, true), (6, true), (7, true)}}

example : Reduced tautRoot := by unfold Reduced; decide
example : Choice θ tautRoot 3 {(0, true)} := by
  apply choice_of_pairs
  · unfold Heavy; decide
  · decide
  · decide

example : ((countingIntro tautRoot 3 {(0, true)} true \ tautRoot).filter
    fun C => C.card = 2).card = 4 := by decide
example : ((countingChild tautRoot 3 {(0, true)} true).filter
    fun C => C ∉ tautRoot ∧ C.card = 2).card = 3 := by decide
example : ∃ C ∈ tautRoot, ∃ l ∈ C, Std.Sat.Literal.negate l ∈ C := by decide

end ComplexityTests.SparsificationCountingDeletion
