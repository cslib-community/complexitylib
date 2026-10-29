/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingInsertions
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingInsertions

/-- A two-petal B-step counts both petal units and the negated-heart unit. -/
theorem binary_flower_inserts_three_units :
    let root : ClauseSet (Fin 3) := {{(0, true), (1, true)}, {(0, true), (2, true)}}
    countingInsertionCount 1
      (fun i => if i = 0 then root else countingChild root 2 {(0, true)} true)
      (fun _ => 2) (fun _ => {(0, true)}) (fun _ => true) 1 = 3 := by decide

private def θ (j : ℕ) := 2 ^ j
private theorem θpos (j : ℕ) : 1 ≤ θ j := Nat.one_le_pow j 2 (by decide)

private theorem θtwo {j : ℕ} (hj : 1 ≤ j) : 2 ≤ θ j := by
  change 2 ^ 1 ≤ 2 ^ j
  exact Nat.pow_le_pow_right (by decide) hj

-- The first B-step inserts four pairs. The second B-step deletes two marked pairs, including
-- an unselected pair killed by the negated-heart unit. The root pair is deleted but unmarked.
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
  have hpairs : ∀ C ∈ root, ∀ D ∈ root, C ≠ D → C.card = D.card → C.card = 3 := by decide
  have hinter : ∀ C ∈ root, ∀ D ∈ root, C ≠ D → (C ∩ D).card ≤ 1 := by decide
  refine ⟨by unfold Heavy; decide, ?_, ?_⟩
  · intro c H hh
    have htwo : 2 ≤ (flower root c H).card :=
      (θtwo (by have := hh.2.1; omega)).trans hh.2.2
    obtain ⟨C, hC, D, hD, hCD⟩ := one_lt_card.mp (by omega : 1 < (flower root c H).card)
    have hCc := (mem_flower.mp hC).2.1
    have hDc := (mem_flower.mp hD).2.1
    have := hpairs C (flower_subset _ _ _ hC) D (flower_subset _ _ _ hD) hCD (by omega)
    omega
  · intro H hh
    have htwo : 2 ≤ (flower root 3 H).card :=
      (θtwo (by have := hh.2.1; omega)).trans hh.2.2
    obtain ⟨C, hC, D, hD, hCD⟩ := one_lt_card.mp (by omega : 1 < (flower root 3 H).card)
    have hH : H ⊆ C ∩ D := subset_inter (mem_flower.mp hC).2.2 (mem_flower.mp hD).2.2
    exact (card_le_card hH).trans (hinter C (flower_subset _ _ _ hC) D (flower_subset _ _ _ hD) hCD)

private theorem secondChoice : Choice θ first 2 {(1, true)} := by
  refine ⟨by unfold Heavy; decide, ?_, ?_⟩
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
private theorem rootNontautological :
    ∀ C ∈ root, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by decide

-- Compute the event count THROUGH the proved balance, with both a nonzero final population and
-- nonzero deletions. Looking only at the final node would lose half of the insertions.
private theorem four_pair_insertion_events :
    countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 2 = 4 := by
  have hbalance := countingInsertionCount_eq_present_add_deleted θpos 2 (nodes true)
    sizes hearts (dirs true) (steps true) (fun i hi => (choices true i hi).1)
    rootReduced rootNontautological (j := 2) (by decide)
  have hfinal : ((nodes true 2).filter fun C => C ∉ nodes true 0 ∧ C.card = 2).card = 2 := by decide
  have hdeleted : (∑ m ∈ range 2, ((nodes true m).filter fun C =>
      C ∉ nodes true 0 ∧ C.card = 2 ∧ C ∉ nodes true (m + 1)).card) = 2 := by decide
  rw [hfinal, hdeleted] at hbalance
  exact hbalance

example : countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 2 ≠
    ((nodes true 2).filter fun C => C ∉ root ∧ C.card = 2).card := by
  rw [four_pair_insertion_events]
  decide

example : countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 1 = 4 := by decide
example : countingInsertionCount 1 (nodes true) sizes hearts (dirs true) 1 = 1 := by decide

-- The A-tail deletes one marked pair; the B-tail deletes two. Both prefixes still count the
-- same four earlier pair insertions, and root clauses never enter the event count.
example : countingInsertionCount 2 (nodes false) sizes hearts (dirs false) 2 = 4 := by decide
example : ((nodes false 2).filter fun C => C ∉ root ∧ C.card = 2).card = 3 := by decide
example : ((nodes true 1).filter fun C => C.card = 2 ∧ C ∉ nodes true 2).card = 3 := by decide

-- Combining `countingInsertionCount_le_rec` at `j = 2` with `countingInsertionCount_one_le` on
-- any legal counting path starting from `root` yields `countingInsertionCount N ψ c H b 2 ≤ 144`
-- (`72 + 4 * 18`), sharper than the geometric `countingInsertionCount_le_pow` bound (`216`).
example (N : ℕ) (ψ : ℕ → ClauseSet (Fin 9)) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal (Fin 9))) (b : ℕ → Bool) (hroot : ψ 0 = root)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i)) :
    countingInsertionCount N ψ c H b 1 ≤ 18 ∧
      countingInsertionCount N ψ c H b 2 ≤ 144 ∧
      countingInsertionCount N ψ c H b 2 ≤ 216 := by
  have hred : Reduced (ψ 0) := hroot ▸ rootReduced
  have hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := hroot ▸ rootNontautological
  have hsup : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ (univ : Finset (Fin 9)) := fun _ _ _ _ => mem_univ _
  have h1 : countingInsertionCount N ψ c H b 1 ≤ 18 := by
    simpa using countingInsertionCount_one_le θpos N ψ c H b hstep
      (fun i hi => (hchoice i hi).1) hred univ hsup
  have hrec := countingInsertionCount_le_rec θpos N ψ c H b hstep hchoice hred hnt
    univ hsup (j := 2) (by decide)
  simp only [Nat.Ico_succ_singleton, sum_singleton, Nat.reduceSub, card_univ, Fintype.card_fin]
    at hrec
  change countingInsertionCount N ψ c H b 2 ≤
    4 * 9 * 2 + 2 * (2 * countingInsertionCount N ψ c H b 1) at hrec
  have hpow : countingInsertionCount N ψ c H b 2 ≤ 216 := by
    simpa using countingInsertionCount_le_pow (M := 2) (by decide) N ψ c H b hstep hchoice
      hred hnt univ hsup (j := 2) (by decide)
  exact ⟨h1, by omega, hpow⟩

-- Actual full-Choice clients of the recurrence and the source's unchanged closed constant.
example : countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 2 ≤ 88 := by
  exact countingInsertionCount_le_rec θpos 2 (nodes true) sizes hearts (dirs true)
    (steps true) (choices true) rootReduced rootNontautological univ
    (by intro C hC l hl; exact mem_univ _) (by decide)

-- Declared-variable budget form `countingInsertionCount_le_pow_of_card_le` for any `n ≥ 9`.
example (n : ℕ) (hn : 9 ≤ n) :
    countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 2 ≤ 24 * n := by
  simpa using countingInsertionCount_le_pow_of_card_le (M := 2) (by decide) 2 (nodes true)
    sizes hearts (dirs true) (steps true) (choices true) rootReduced rootNontautological univ
    (by intro C hC l hl; exact mem_univ _) (n := n) (by simpa using hn) (j := 2) (by decide)

-- Empty variables with an empty root clause do not require division by n or an inhabited type:
-- `countingInsertionCount_le_pow_of_card_le` at `n = 0` forces `0` insertion events at every `N`.
example (N : ℕ) (ψ : ℕ → ClauseSet Empty) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal Empty)) (b : ℕ → Bool) (hroot : ψ 0 = {∅})
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i)) (j : ℕ) (hj : 1 ≤ j) :
    countingInsertionCount N ψ c H b j = 0 := by
  have hle := countingInsertionCount_le_pow_of_card_le (M := 2) (by decide) N ψ c H b
    hstep hchoice (by rw [hroot]; unfold Reduced; decide) (by rw [hroot]; simp) ∅
    (by rw [hroot]; simp) (n := 0) le_rfl hj
  simpa using Nat.eq_zero_of_le_zero hle

-- Contradictory root units on one variable are individually nontautological. Neither is an
-- insertion, and `countingInsertionCount_one_le` bounds unit insertions on `{()}` by `2`.
private def oneVariable : ClauseSet Unit := {{((), true)}, {((), false)}}

example : countingInsertionCount 0 (fun _ => oneVariable) (fun _ => 0)
    (fun _ => ∅) (fun _ => false) 1 = 0 := by decide

example (N : ℕ) (ψ : ℕ → ClauseSet Unit) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal Unit)) (b : ℕ → Bool) (hroot : ψ 0 = oneVariable)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) :
    countingInsertionCount N ψ c H b 1 ≤ 2 := by
  have h := countingInsertionCount_one_le θpos N ψ c H b hstep hheavy
    (by rw [hroot]; unfold Reduced; decide) {()}
    (by intro C _ l _; exact mem_singleton.mpr (Subsingleton.elim _ _))
  simpa using h

-- Without nontautology, even the one-step event balance can fail before any OLD marked clause
-- is deleted. This is the full-Choice counterexample retained in SparsificationCountingDeletion.
private def tautRoot : ClauseSet (Fin 8) :=
  {{(0, true), (0, false), (1, true)}, {(0, true), (2, true), (3, true)},
    {(0, true), (4, true), (5, true)}, {(0, true), (6, true), (7, true)}}
private def tautNodes (i : ℕ) :=
  if i = 0 then tautRoot else countingChild tautRoot 3 {(0, true)} true

example : countingInsertionCount 1 tautNodes (fun _ => 3) (fun _ => {(0, true)})
    (fun _ => true) 2 = 4 := by decide
example : ((tautNodes 1).filter fun C => C ∉ tautNodes 0 ∧ C.card = 2).card = 3 := by decide
example : (∑ m ∈ range 1, ((tautNodes m).filter fun C =>
    C ∉ tautNodes 0 ∧ C.card = 2 ∧ C ∉ tautNodes (m + 1)).card) = 0 := by decide

end ComplexityTests.SparsificationCountingInsertions
