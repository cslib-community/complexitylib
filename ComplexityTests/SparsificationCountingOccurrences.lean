/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingOccurrences

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingOccurrences

-- The added unit is real payload data, rather than silently omitted in the occurrence proof.
theorem negated_unit_remains_in_payload : {(0, false)} ∈ countingIntro
    ({{(0, true), (1, true), (2, true)}} : ClauseSet (Fin 3)) 3 {(0, true)} true := by decide

private def threshold (j : ℕ) := 2 ^ j

private theorem threshold_pos (j : ℕ) : 1 ≤ threshold j := by
  induction j with
  | zero => decide
  | succ j ih =>
    change 1 ≤ 2 ^ (j + 1)
    rw [pow_succ]
    change 1 ≤ 2 ^ j at ih
    omega

private theorem threshold_two {j : ℕ} (hj : 0 < j) : 2 ≤ threshold j := by
  cases j with
  | zero => omega
  | succ j =>
    change 2 ≤ 2 ^ (j + 1)
    rw [pow_succ]
    have := threshold_pos j
    change 1 ≤ 2 ^ j at this
    omega

-- A checked uniform-width family supplies the minimum-width priority. Intersections control
-- the maximum heart: any heavy flower has two different clauses containing that heart.
private theorem choice_of_uniform_intersections {V : Type*} [DecidableEq V]
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hheavy : Heavy threshold ψ c H) (hwidth : ∀ C ∈ ψ, C.card = c)
    (hinter : ∀ C ∈ ψ, ∀ D ∈ ψ, C ≠ D → (C ∩ D).card ≤ H.card) :
    Choice threshold ψ c H := by
  refine ⟨hheavy, ?_, ?_⟩
  · intro c' H' hh
    obtain ⟨C, hC⟩ := hh.flower_nonempty threshold_pos
    have hCc := (mem_flower.mp hC).2.1
    have := hwidth C (flower_subset _ _ _ hC)
    omega
  · intro H' hh
    have htwo : 2 ≤ (flower ψ c H').card :=
      (threshold_two (Nat.sub_pos_of_lt hh.2.1)).trans hh.2.2
    obtain ⟨C, hC, D, hD, hCD⟩ := one_lt_card.mp (by omega : 1 < (flower ψ c H').card)
    calc
      H'.card ≤ (C ∩ D).card := card_le_card
        (subset_inter (mem_flower.mp hC).2.2 (mem_flower.mp hD).2.2)
      _ ≤ H.card := hinter C (flower_subset _ _ _ hC) D (flower_subset _ _ _ hD) hCD

private def fan : ClauseSet (Fin 9) :=
  {{(0, true), (1, true), (2, true)}, {(0, true), (3, true), (4, true)},
    {(0, true), (5, true), (6, true)}, {(0, true), (7, true), (8, true)}}

private def fanHeart : Finset (Literal (Fin 9)) := {(0, true)}

private theorem fan_choice : Choice threshold fan 3 fanHeart := by
  apply choice_of_uniform_intersections
  · unfold Heavy
    decide
  · decide
  · decide

private def fanNodes (i : ℕ) := if i = 0 then fan else countingChild fan 3 fanHeart true

-- A genuine maximum-heart B step introduces four width-two petals plus a negated unit.
example : ((fanNodes 1).filter fun C => C.card = 1).card = 1 := by decide

example : ((fanNodes 1).filter fun C => C ∉ fan ∧ C.card = 2 ∧ {(1, true)} ⊆ C).card = 1 := by
  decide

example : ((fanNodes 1).filter fun C => C ∉ fan ∧ C.card = 2 ∧ {(1, true)} ⊆ C).card < 4 := by
  have hstep : ∀ i < 1, fanNodes (i + 1) = countingChild (fanNodes i) 3 fanHeart true := by
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  have hchoice : ∀ i < 1, Choice threshold (fanNodes i) 3 fanHeart := by
    intro i hi
    have : i = 0 := by omega
    subst i
    exact fan_choice
  exact card_counting_newContaining_lt threshold_pos 1 fanNodes (fun _ => 3)
    (fun _ => fanHeart) (fun _ => true) hstep hchoice (by omega) (by decide) (by decide)

-- All root clauses are unmarked, even if the initial root itself has high occurrence:
-- `card_counting_newContaining_lt` bounds marked clauses (`< 4`), while dropping `C ∉ rootPairs`
-- gives `4` clauses, so marked occurrences are strictly fewer than total occurrences.
private def rootPairs : ClauseSet (Fin 5) :=
  {{(0, true), (1, true)}, {(0, true), (2, true)},
    {(0, true), (3, true)}, {(0, true), (4, true)}}

example :
    (rootPairs.filter fun C => C ∉ rootPairs ∧ C.card = 2 ∧ {(0, true)} ⊆ C).card <
      (rootPairs.filter fun C => C.card = 2 ∧ {(0, true)} ⊆ C).card := by
  have hmarked :
      (rootPairs.filter fun C => C ∉ rootPairs ∧ C.card = 2 ∧ {(0, true)} ⊆ C).card < 4 :=
    card_counting_newContaining_lt threshold_pos 0 (fun _ => rootPairs) (fun _ => 0)
      (fun _ => ∅) (fun _ => false) (by intro i hi; omega) (by intro i hi; omega)
      (t := 0) (by omega) (by decide) (by decide)
  have htotal : (rootPairs.filter fun C => C.card = 2 ∧ {(0, true)} ⊆ C).card = 4 := by decide
  omega

-- Dropping maximum-heart priority really breaks the proposed bound, even in one step.
private def star : ClauseSet (Fin 6) :=
  {{(0, true), (1, true), (2, true)}, {(0, true), (1, true), (3, true)},
    {(0, true), (1, true), (4, true)}, {(0, true), (1, true), (5, true)}}

example : Heavy threshold star 3 {(0, true)} := by unfold Heavy; decide

example : ¬ Choice threshold star 3 {(0, true)} := by
  intro h
  have hh : Heavy threshold star 3 {(0, true), (1, true)} := by unfold Heavy; decide
  have hbad := h.2.2 {(0, true), (1, true)} hh
  change 2 ≤ 1 at hbad
  omega

example : ¬ ((countingChild star 3 {(0, true)} true).filter fun C =>
    C ∉ star ∧ C.card = 2 ∧ {(1, true)} ⊆ C).card < 4 := by decide

-- Dropping minimum-width priority also breaks the bound: a second A step ignores an existing
-- width-two heavy clause. Both selected hearts still have maximal possible proper size.
private def minRoot : ClauseSet (Fin 5) :=
  {{(0, true), (1, true), (2, true)}, {(0, true), (3, true), (4, true)}}

private def minFirst := countingChild minRoot 3 {(0, true), (1, true)} false
private def minSecond := countingChild minFirst 3 {(0, true), (3, true)} false

example : Heavy (fun _ => 1) minFirst 3 {(0, true), (3, true)} := by unfold Heavy; decide

example : ∀ H : Finset (Literal (Fin 5)), Heavy (fun _ => 1) minFirst 3 H →
    H.card ≤ ({(0, true), (3, true)} : Finset (Literal (Fin 5))).card := by
  intro H hh
  have := hh.2.1
  change H.card ≤ 2
  omega

example : ¬ Choice (fun _ => 1) minFirst 3 {(0, true), (3, true)} := by
  intro h
  have hh : Heavy (fun _ => 1) minFirst 2 {(0, true)} := by unfold Heavy; decide
  have hbad := h.2.1 2 {(0, true)} hh
  omega

example : ¬ (minSecond.filter fun C => C ∉ minRoot ∧ C.card = 2 ∧ {(0, true)} ⊆ C).card < 2 := by
  decide

end ComplexityTests.SparsificationCountingOccurrences
