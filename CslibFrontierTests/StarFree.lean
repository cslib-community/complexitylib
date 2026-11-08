/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.SecondOrder.WordMSO.StarFree

/-!
# Tests: star-free languages and first-order logic over words

* Libkin's star-free expressions for `Σ*` and `a*b*` over `{a, b} = {false, true}`, with words in
  (including the nonempty `ab` and `aab`) and out of their languages, their regularity, and their
  first-order definability;
* the translated sentence `starFreeSentence` on concrete words, including a concatenation whose
  first factor is empty;
* `{ε}` is star-free over the finite alphabet `Bool` and not over the infinite alphabet `ℕ`, where
  it is first-order definable; finite languages over `Bool` are star-free;
* even length is regular but not star-free over a one-letter alphabet (`(aa)*`).
-/

namespace ComplexityTests.StarFree

open Cslib.Language Cslib.Language.StarFreeExpression Cslib.Logic.WordMSO

/-! ### Libkin's examples -/

/-- `Σ*`, as the complement of `∅`. -/
def all : StarFreeExpression Bool := compl zero

/-- Libkin's `a*b*` over `{a, b} = {false, true}`: no `b` (`true`) immediately before an `a`
(`false`), as the complement of `Σ* · b · a · Σ*`. -/
def aStarBStar : StarFreeExpression Bool :=
  compl (comp (comp (comp all (char true)) (char false)) all)

/-- The words ending in `false`, as `Σ* · a`. -/
def endsFalse : StarFreeExpression Bool := comp all (char false)

example (w : List Bool) : w ∈ all.matches' := Language.notMem_zero w

example : all.matchEpsilon = true := rfl

/-- `ba ∈ Σ* · b · a · Σ*`, so `ba ∉ a*b*`. -/
theorem notMem_aStarBStar : [true, false] ∉ aStarBStar.matches' := fun h =>
  h (Language.mem_mul.2 ⟨[true, false], Language.mem_mul.2 ⟨[true], Language.mem_mul.2
    ⟨[], Language.notMem_zero _, [true], rfl, rfl⟩, [false], rfl, rfl⟩, [], Language.notMem_zero _,
    rfl⟩)

example : [] ∈ aStarBStar.matches' := (matchEpsilon_iff _).1 rfl

/-- A word of `Σ* · b · a · Σ*` has a `b` (`true`) immediately followed by an `a` (`false`). -/
theorem exists_true_false {w : List Bool}
    (h : w ∈ (comp (comp (comp all (char true)) (char false)) all).matches') :
    ∃ u v, w = u ++ true :: false :: v := by
  obtain ⟨x, hx, v, -, rfl⟩ := Language.mem_mul.1 h
  obtain ⟨y, hy, z, hz, rfl⟩ := Language.mem_mul.1 hx
  obtain ⟨u, -, t, ht, rfl⟩ := Language.mem_mul.1 hy
  change t = [true] at ht
  change z = [false] at hz
  subst ht hz
  exact ⟨u, v, by simp⟩

/-- `ab ∈ a*b*`: the nonempty word `[false, true]` has no `b` immediately before an `a`. -/
example : [false, true] ∈ aStarBStar.matches' := by
  intro h
  obtain ⟨u, v, huv⟩ := exists_true_false h
  match u, huv with
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: u, h =>
    have := congrArg List.length h
    simp only [List.length_cons, List.length_append, List.length_nil] at this
    omega

example : aStarBStar.matchEpsilon = true := rfl

example : aStarBStar.matches'.IsRegular := aStarBStar.isRegular_matches'

example : IsStarFree aStarBStar.matches' := ⟨_, rfl⟩

example : FODefinable aStarBStar.matches' := IsStarFree.foDefinable ⟨_, rfl⟩

example : IsStarFree (⊤ : Language Bool) := IsStarFree.top

/-! ### The translated sentences on concrete words -/

example : (starFreeSentence aStarBStar).IsFO := isFO_starFreeSentence _

example : [true, false] ∉ (starFreeSentence aStarBStar).language := by
  rw [starFreeSentence_language]
  exact notMem_aStarBStar

example : [] ∈ (starFreeSentence aStarBStar).language := by
  rw [starFreeSentence_language]
  exact (matchEpsilon_iff _).1 rfl

/-- The translated sentence of `a*b*` accepts the nonempty word `aab`. -/
example : [false, false, true] ∈ (starFreeSentence aStarBStar).language := by
  rw [starFreeSentence_language]
  intro h
  obtain ⟨u, v, huv⟩ := exists_true_false h
  match u, huv with
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | _ :: _ :: _ :: u, h =>
    have := congrArg List.length h
    simp only [List.length_cons, List.length_append, List.length_nil] at this
    omega

/-- `[false] ∈ Σ* · a` through the empty first factor, the case of the translation that does not
guess a split position. -/
example : [false] ∈ (starFreeSentence endsFalse).language := by
  rw [starFreeSentence_language]
  exact Language.mem_mul.2 ⟨[], Language.notMem_zero _, [false], rfl, rfl⟩

example : [true, false] ∈ (starFreeSentence endsFalse).language := by
  rw [starFreeSentence_language]
  exact Language.mem_mul.2 ⟨[true], Language.notMem_zero _, [false], rfl, rfl⟩

example : [] ∉ (starFreeSentence endsFalse).language := by
  rw [starFreeSentence_language, ← matchEpsilon_iff]
  decide

example : ∃ φ : (wordLanguage Bool).Sentence, WordFO.language φ = endsFalse.matches' :=
  IsStarFree.exists_sentence ⟨_, rfl⟩

/-! ### The empty word and the size of the alphabet -/

example : IsStarFree (1 : Language Bool) := IsStarFree.one

example : IsStarFree {w : List Bool | w.length = 1} := IsStarFree.setOf_length_eq_one

example : ¬ IsStarFree (1 : Language ℕ) := not_isStarFree_one

example : FODefinable (1 : Language ℕ) := foDefinable_one

example : ∃ L : Language ℕ, FODefinable L ∧ ¬ IsStarFree L := exists_foDefinable_not_isStarFree

example : IsStarFree (1 : Language (Fin 3)) := isStarFree_one_iff.2 inferInstance

/-- A finite language over a finite alphabet is star-free. -/
example : IsStarFree ({[true, false], []} : Language Bool) :=
  IsStarFree.of_finite ((Set.finite_singleton _).insert _)

/-- Every word gives a star-free one-word language over a finite alphabet, but not over `ℕ`:
`{ε}` is a one-word language. -/
example : IsStarFree ({[true, false, true]} : Language Bool) := IsStarFree.singleton _

example : ¬ IsStarFree ({[]} : Language ℕ) := not_isStarFree_one

/-! ### Even length is regular but not star-free -/

/-- `(aa)*` over the one-letter alphabet `Unit` is not star-free. -/
example : ¬ IsStarFree {w : List Unit | Even w.length} := not_isStarFree_even

example : ∃ L : Language Bool, L.IsRegular ∧ ¬ IsStarFree L := exists_isRegular_not_isStarFree

end ComplexityTests.StarFree
