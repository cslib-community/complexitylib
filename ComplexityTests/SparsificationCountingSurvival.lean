/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingSurvival

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingSurvival

private def θ (j : ℕ) := 2 ^ j

private theorem θpos (j : ℕ) : 1 ≤ θ j := Nat.one_le_pow j 2 (by decide)

-- Mixed polarities, a two-literal heart, and four disjoint two-literal petals. One of the
-- negated-heart units is already in the root, so payload is not the same as new unit events.
private def root : ClauseSet (Fin 10) :=
  {{(0, false)}, {(0, true), (1, false), (2, true), (3, false)},
    {(0, true), (1, false), (4, true), (5, false)},
    {(0, true), (1, false), (6, true), (7, false)},
    {(0, true), (1, false), (8, true), (9, false)}}

private def heart : Finset (Literal (Fin 10)) := {(0, true), (1, false)}

private theorem rootReduced : Reduced root := by unfold Reduced; decide

private theorem rootNontautological :
    ∀ C ∈ root, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by decide

private theorem rootHeavy : Heavy θ root 4 heart := by unfold Heavy; decide

private def nodes (b : Bool) (i : ℕ) := if i = 0 then root else countingChild root 4 heart b

private theorem steps (b : Bool) : ∀ i < 1,
    nodes b (i + 1) = countingChild (nodes b i) 4 heart b := by
  intro i hi
  have : i = 0 := by omega
  subst i
  rfl

private theorem heavies (b : Bool) : ∀ i < 1, Heavy θ (nodes b i) 4 heart := by
  intro i hi
  have : i = 0 := by omega
  subst i
  exact rootHeavy

-- Apply the path theorem, then count its concrete insertion batch: A inserts one width-two
-- heart; B inserts four width-two petals. This exercises the equality in both directions.
example : ((nodes false 1 \ (nodes false 0 ∪ nodes false 0)).filter (·.card = 2)).card = 1 := by
  rw [← countingIntro_filter_eq_node_sdiff θpos 1 (nodes false) (fun _ => 4)
    (fun _ => heart) (fun _ => false) (steps false) (heavies false)
    rootReduced rootNontautological (m := 0) (by decide) (by decide)]
  decide

example : ((nodes true 1 \ (nodes true 0 ∪ nodes true 0)).filter (·.card = 2)).card = 4 := by
  rw [← countingIntro_filter_eq_node_sdiff θpos 1 (nodes true) (fun _ => 4)
    (fun _ => heart) (fun _ => true) (steps true) (heavies true)
    rootReduced rootNontautological (m := 0) (by decide) (by decide)]
  decide

-- Combining `intro_subset_countingChild` with `nontautological_counting_node` and
-- `nontautological_countingChild` shows that every heart or petal introduced at `root` both
-- survives in `nodes b 1` and is nontautological.
example (b : Bool) (C : Finset (Literal (Fin 10))) (hC : C ∈ intro root 4 heart b) :
    C ∈ nodes b 1 ∧ ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
  have hmem : C ∈ nodes b 1 :=
    intro_subset_countingChild θpos rootReduced rootNontautological rootHeavy b hC
  refine ⟨hmem, ?_⟩
  cases b
  · exact nontautological_counting_node θpos 1 (nodes false) (fun _ => 4)
      (fun _ => heart) (fun _ => false) (steps false) (heavies false)
      rootNontautological (t := 1) le_rfl C hmem
  · exact nontautological_countingChild θpos rootNontautological rootHeavy true C hmem

-- Existing negated units belong to the raw payload but are not new insertions. Extending the
-- event equality from widths at least two to width one would fail in this same legal example.
example : ((countingIntro root 4 heart true).filter (·.card = 1)).card = 2 := by decide
example : ((nodes true 1 \ root).filter (·.card = 1)).card = 1 := by decide
example : {(0, false)} ∈ nodes true 1 ∧ {(0, false)} ∈ root := by decide

-- A one-literal petal is also covered by core survival, even though the event equality above
-- deliberately separates width-one accounting.
theorem unit_petal_survives : {(2, true)} ∈ countingChild
    ({{(0, true), (2, true)}, {(0, true), (3, false)}} : ClauseSet (Fin 4))
    2 {(0, true)} true := by
  apply intro_subset_countingChild θpos (by unfold Reduced; decide)
    (by decide) (by unfold Heavy; decide) true
  decide

-- A later step has a current node different from the root. It removes the remaining old
-- width-three clause and introduces a width-two heart, while the earlier negated unit persists.
private def chainRoot : ClauseSet ℕ := {{(0, true), (1, true), (2, true), (3, true)}}

private def chainFirst := countingChild chainRoot 4 {(0, true)} true

private def chainNodes (i : ℕ) :=
  if i = 0 then chainRoot else if i = 1 then chainFirst
    else countingChild chainFirst 3 {(1, true), (2, true)} false

private def chainSizes (i : ℕ) := if i = 0 then 4 else 3
private def chainHearts (i : ℕ) : Finset (Literal ℕ) :=
  if i = 0 then {(0, true)} else {(1, true), (2, true)}
private def chainDirs (i : ℕ) := i == 0

private theorem chainSteps : ∀ i < 2, chainNodes (i + 1) =
    countingChild (chainNodes i) (chainSizes i) (chainHearts i) (chainDirs i) := by
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> rfl

private theorem chainHeavies : ∀ i < 2,
    Heavy (fun _ => 1) (chainNodes i) (chainSizes i) (chainHearts i) := by
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> unfold Heavy <;> decide

example : ((chainNodes 2 \ (chainNodes 1 ∪ chainNodes 0)).filter (·.card = 2)).card = 1 := by
  rw [← countingIntro_filter_eq_node_sdiff (fun _ => le_rfl) 2 chainNodes chainSizes
    chainHearts chainDirs chainSteps chainHeavies (by unfold Reduced; decide)
    (by decide) (m := 1) (by decide) (by decide)]
  decide

example : {(0, false)} ∈ chainNodes 2 ∧ {(1, true), (2, true)} ∈ chainNodes 2 := by decide

-- Reducedness is essential: a pre-existing unit immediately subsumes the new width-two petal.
private def unreduced : ClauseSet (Fin 3) :=
  {{(1, true)}, {(0, true), (1, true), (2, true)}}

example : ∀ C ∈ unreduced, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by decide
example : Heavy (fun _ => 1) unreduced 3 {(0, true)} := by unfold Heavy; decide
example : ¬ Reduced unreduced := by unfold Reduced; decide
example : {(1, true), (2, true)} ∈ intro unreduced 3 {(0, true)} true ∧
    {(1, true), (2, true)} ∉ countingChild unreduced 3 {(0, true)} true := by decide

-- The independent tautological full-Choice 4-payload/3-survivor counterexample remains in
-- SparsificationCountingDeletion. It is unchanged and checked alongside this module.

-- No ambient variable or nonempty-formula hypothesis at a zero-length prefix.
example : ∀ C ∈ ({∅} : ClauseSet Empty), ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
  exact nontautological_counting_node θpos 0 (fun _ => ({∅} : ClauseSet Empty))
    (fun _ => 0) (fun _ => ∅) (fun _ => false) (by intro i hi; omega)
    (by intro i hi; omega) (by simp) (t := 0) le_rfl

end ComplexityTests.SparsificationCountingSurvival
