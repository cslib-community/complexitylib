/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.Arrow
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin

/-!
# Arrow's theorem clients

This is a `module` importing the public surface of `CslibFrontier.GameTheory.SocialChoice.Arrow`,
so it checks that clients can use the exposed definitions.

Dictatorship satisfies weak Pareto and IIA, so the theorem is not vacuous. Three of Arrow's
hypotheses are each checked against a rule that drops it:

* With three voters and only two alternatives, majority rule satisfies weak Pareto and IIA but is
  not dictatorial, so three alternatives are needed.
* With two voters and three alternatives, the Borda count is weakly Pareto and not dictatorial,
  so IIA is needed; by the theorem, the Borda count violates IIA.
* The rule that ranks every alternative equally satisfies IIA but not weak Pareto.

Finiteness of the electorate is also necessary, but the infinite-electorate counterexample is not
formalized.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.SocialChoice

open Cslib.GameTheory.SocialChoice SocialWelfareFunction

/-! ### Dictatorship: Arrow's hypotheses are satisfiable -/

/-- The dictatorship of voter `0` among three voters, on three alternatives, is weakly Pareto
and satisfies IIA, so the hypotheses of Arrow's theorem are not vacuous. -/
example : (dictatorship (V := Fin 3) (A := Fin 3) 0).IsPareto ∧
    (dictatorship (V := Fin 3) (A := Fin 3) 0).IsIIA :=
  ⟨isPareto_dictatorship 0, isIIA_dictatorship 0⟩

/-- The dictator of `dictatorship 0` is voter `0` and nobody else. -/
example (i : Fin 3) : (dictatorship (A := Fin 3) (0 : Fin 3)).IsDictator i ↔ i = 0 :=
  ⟨fun h => h.unique (isDictator_dictatorship 0), by rintro rfl; exact isDictator_dictatorship 0⟩

/-- Arrow's theorem for three voters and three alternatives: the weakly Pareto IIA rules are
the dictatorships. -/
example (F : SocialWelfareFunction (Fin 3) (Fin 3)) (hP : F.IsPareto) (hI : F.IsIIA) :
    ∃ i, F = dictatorship i :=
  (isPareto_and_isIIA_iff (Fintype.two_lt_card_iff.1 (by simp))).1 ⟨hP, hI⟩

/-- Arrow's theorem for a rule with strict social rankings, viewed as weak rankings. -/
example (F : Profile (Fin 5) (Fin 4) → Ranking (Fin 4))
    (hP : SocialWelfareFunction.IsPareto fun P => (F P).toWeakRanking)
    (hI : SocialWelfareFunction.IsIIA fun P => (F P).toWeakRanking) :
    ∃ i, ∀ P a b, (P i).Prefers a b → (F P).Prefers a b := by
  obtain ⟨i, hi⟩ := isDictatorial_of_three_le_card hP hI (by simp)
  exact ⟨i, fun P a b h => (F P).toWeakRanking_prefers.1 (hi P a b h)⟩

/-! ### Majority rule on two alternatives: three alternatives are needed -/

section Majority

open Classical in
/-- The number of the three voters ranking `a` above `b`. -/
noncomputable def support (P : Profile (Fin 3) Bool) (a b : Bool) : ℕ :=
  (Finset.univ.filter fun i => (P i).Prefers a b).card

/-- The voters ranking `a` above `b` and those ranking `b` above `a` split the electorate. -/
theorem support_add_support (P : Profile (Fin 3) Bool) {a b : Bool} (hab : a ≠ b) :
    support P a b + support P b a = 3 := by
  classical
  unfold support
  have : (Finset.univ.filter fun i => (P i).Prefers b a) =
      Finset.univ.filter fun i => ¬ (P i).Prefers a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((P i).not_prefers_iff hab).symm
  rw [this, Finset.card_filter_add_card_filter_not]
  rfl

/-- Pairwise majority rule with three voters and two alternatives: `a` is ranked at least as
high as `b` when `a = b` or at least two voters rank `a` above `b`. -/
noncomputable def majority : SocialWelfareFunction (Fin 3) Bool := fun P =>
  { AtLeast := fun a b => a = b ∨ 2 ≤ support P a b
    total := fun a b => by
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      · have := support_add_support P hab
        omega
    trans := fun a b c hab hbc => by
      by_cases h₁ : a = b
      · subst h₁; exact hbc
      by_cases h₂ : b = c
      · subst h₂; exact hab
      -- With two alternatives, `a ≠ b` and `b ≠ c` force `a = c`.
      exact Or.inl (by revert h₁ h₂; cases a <;> cases b <;> cases c <;> simp) }

theorem majority_isPareto : majority.IsPareto := by
  classical
  intro P a b h hba
  have hab : a ≠ b := (P 0).ne_of_prefers (h 0)
  have h0 : support P b a = 0 := by
    unfold support
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => (P i).asymm (h i)
  rcases hba with hba | hba
  · exact hab hba.symm
  · omega

theorem majority_isIIA : majority.IsIIA := by
  intro P Q a b h
  have : support P a b = support Q a b := by
    classical
    unfold support
    congr 1
    exact Finset.filter_congr fun i _ => h i
  change a = b ∨ 2 ≤ support P a b ↔ a = b ∨ 2 ≤ support Q a b
  rw [this]

/-- The ranking `true ≻ false`. -/
def trueAbove : Ranking Bool where
  Prefers a b := a = true ∧ b = false
  irrefl a h := by cases a <;> simp_all
  trans _ _ _ h₁ h₂ := ⟨h₁.1, h₂.2⟩
  total a b h := by cases a <;> cases b <;> simp_all

/-- No voter is a dictator for majority rule: if voter `i` alone ranks `true` above `false`, the
other two voters outvote them. -/
theorem majority_not_isDictator (i : Fin 3) : ¬ majority.IsDictator i := by
  classical
  intro hi
  let P : Profile (Fin 3) Bool := fun j => if j = i then trueAbove else trueAbove.reverse
  have hP : (majority P).Prefers true false := hi P true false (by simp [P, trueAbove])
  -- Only voter `i` ranks `true` above `false`.
  have h1 : support P true false ≤ 1 := by
    unfold support
    calc _ ≤ ({i} : Finset (Fin 3)).card := by
          refine Finset.card_le_card fun j hj => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          by_contra hji
          simp only [Finset.mem_singleton] at hji
          simp [P, hji, trueAbove] at hj
      _ = 1 := Finset.card_singleton i
  have := support_add_support P (a := true) (b := false) (by decide)
  exact hP (Or.inr (by omega))

/-- With two alternatives and three voters, majority rule is weakly Pareto, satisfies IIA and is
not dictatorial: Arrow's theorem needs three alternatives. -/
example : majority.IsPareto ∧ majority.IsIIA ∧ ¬ majority.IsDictatorial :=
  ⟨majority_isPareto, majority_isIIA, fun ⟨i, hi⟩ => majority_not_isDictator i hi⟩

end Majority

/-! ### The Borda count: IIA is needed -/

section Borda

open Classical in
/-- The Borda score of `a` for two voters and three alternatives: the number of pairs `(i, x)`
such that voter `i` ranks `a` above `x`. -/
noncomputable def bordaScore (P : Profile (Fin 2) (Fin 3)) (a : Fin 3) : ℕ :=
  ∑ i, (Finset.univ.filter fun x => (P i).Prefers a x).card

/-- The Borda count: alternatives are ranked by Borda score, with ties. -/
noncomputable def borda : SocialWelfareFunction (Fin 2) (Fin 3) := fun P =>
  { AtLeast := fun a b => bordaScore P b ≤ bordaScore P a
    total := fun _ _ => le_total _ _
    trans := fun _ _ _ hab hbc => hbc.trans hab }

theorem borda_prefers {P : Profile (Fin 2) (Fin 3)} {a b : Fin 3} :
    (borda P).Prefers a b ↔ bordaScore P b < bordaScore P a :=
  not_le

/-- If every voter ranks `a` above `b`, each voter ranks `a` above strictly more alternatives
than `b`. -/
theorem borda_isPareto : borda.IsPareto := by
  classical
  intro P a b h
  rw [borda_prefers]
  unfold bordaScore
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).2 ⟨b, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (P i).trans _ _ _ (h i) hx
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h i
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (P i).irrefl b

open Classical in
/-- A ranking of three alternatives places the two alternatives other than `a` below or above
`a`. -/
theorem card_below_add_card_above (r : Ranking (Fin 3)) (a : Fin 3) :
    (Finset.univ.filter fun x => r.Prefers a x).card +
      (Finset.univ.filter fun x => r.Prefers x a).card = 2 := by
  have hsplit : (Finset.univ.filter fun x => ¬ r.Prefers a x) =
      insert a (Finset.univ.filter fun x => r.Prefers x a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hx : x = a
    · subst hx
      exact iff_of_true (r.irrefl x) (Or.inl rfl)
    · rw [r.not_prefers_iff (Ne.symm hx)]
      exact ⟨Or.inr, fun h => h.resolve_left hx⟩
  have hnotMem : a ∉ Finset.univ.filter fun x => r.Prefers x a := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact r.irrefl a
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun x => r.Prefers a x)
  rw [hsplit, Finset.card_insert_of_notMem hnotMem, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- When voter `1` reverses voter `0`'s ranking, every alternative has Borda score `2`. -/
theorem bordaScore_reverse (r : Ranking (Fin 3)) (a : Fin 3) :
    bordaScore ![r, r.reverse] a = 2 := by
  unfold bordaScore
  rw [Fin.sum_univ_two]
  convert card_below_add_card_above r a using 4
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Ranking.reverse_prefers]

/-- No voter is a dictator for the Borda count: in a profile where the voters hold opposite
rankings, society is indifferent between all alternatives. -/
theorem borda_not_isDictator (i : Fin 2) : ¬ borda.IsDictator i := by
  intro hi
  obtain ⟨r⟩ := Ranking.nonempty (Fin 3)
  have hnone : ∀ a b, ¬ (borda ![r, r.reverse]).Prefers a b := fun a b h => by
    rw [borda_prefers, bordaScore_reverse, bordaScore_reverse] at h
    exact lt_irrefl _ h
  rcases (![r, r.reverse] i).total 0 1 (by decide) with h | h
  · exact hnone _ _ (hi _ _ _ h)
  · exact hnone _ _ (hi _ _ _ h)

/-- The Borda count is weakly Pareto and not dictatorial, so by Arrow's theorem it violates IIA. -/
theorem borda_not_isIIA : ¬ borda.IsIIA := fun hI =>
  let ⟨i, hi⟩ := isDictatorial_of_three_le_card borda_isPareto hI (by simp)
  borda_not_isDictator i hi

/-- With two voters and three alternatives, the Borda count is weakly Pareto and not
dictatorial: Arrow's theorem needs IIA. -/
example : borda.IsPareto ∧ ¬ borda.IsIIA ∧ ¬ borda.IsDictatorial :=
  ⟨borda_isPareto, borda_not_isIIA, fun ⟨i, hi⟩ => borda_not_isDictator i hi⟩

end Borda

/-! ### Mathlib order API through the bridge instances -/

example (r : Ranking (Fin 3)) (a b : Fin 3) : r.Prefers a b ∨ a = b ∨ r.Prefers b a :=
  trichotomous a b

example (R : WeakRanking (Fin 3)) (a b c : Fin 3) (hab : R.AtLeast a b) (hbc : R.AtLeast b c) :
    R.AtLeast a c :=
  _root_.trans hab hbc

example (r : Ranking (Fin 3)) (a b : Fin 3) :
    r.toWeakRanking.AtLeast a b ↔ a = b ∨ r.Prefers a b := by
  simp

/-! ### Universal indifference: weak Pareto is needed -/

/-- The rule ranking all alternatives equally. -/
def indifference : SocialWelfareFunction (Fin 3) (Fin 3) := fun _ =>
  { AtLeast := fun _ _ => True, total := fun _ _ => Or.inl trivial,
    trans := fun _ _ _ _ _ => trivial }

/-- Universal indifference satisfies IIA and is not dictatorial; it is not weakly Pareto. -/
example : indifference.IsIIA ∧ ¬ indifference.IsPareto ∧ ¬ indifference.IsDictatorial := by
  have hnP : ¬ indifference.IsPareto := fun h => by
    obtain ⟨r⟩ := Ranking.nonempty (Fin 3)
    rcases r.total 0 1 (by decide) with h01 | h10
    · exact h (fun _ => r) 0 1 (fun _ => h01) trivial
    · exact h (fun _ => r) 1 0 (fun _ => h10) trivial
  exact ⟨fun _ _ _ _ _ => Iff.rfl, hnP, fun ⟨_, hi⟩ => hnP hi.isPareto⟩

end CslibFrontierTests.GameTheory.SocialChoice
