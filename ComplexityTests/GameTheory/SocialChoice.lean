/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.SocialChoice.Arrow
import Mathlib.Data.Fintype.Card

/-!
# Arrow's theorem clients

Each hypothesis of Arrow's theorem is checked against a rule that drops it. Dictatorship satisfies
weak Pareto and IIA, so the theorem is not vacuous. With three voters and only two alternatives,
majority rule satisfies weak Pareto and IIA but is not dictatorial, so three alternatives are
needed. The rule that ranks every alternative equally satisfies IIA but not weak Pareto.
-/

namespace ComplexityTests.GameTheory.SocialChoice

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

end ComplexityTests.GameTheory.SocialChoice
