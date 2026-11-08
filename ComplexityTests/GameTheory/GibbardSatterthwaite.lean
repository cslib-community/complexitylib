/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.SocialChoice.GibbardSatterthwaite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gibbard–Satterthwaite clients

This is a `module` importing the public surface of
`Complexity.GameTheory.SocialChoice.GibbardSatterthwaite`, so it checks that clients can use the
exposed definitions.

* A dictatorship is strategy-proof and onto, so the theorem is not vacuous, and the theorem
  applies to three voters and three alternatives.
* **Three alternatives in the range are needed.** Majority rule between two alternatives `a` and
  `b`, with ties going to `b`, is strategy-proof and, with at least two voters, not dictatorial.
  On `Bool` it is onto two alternatives. On three alternatives its range is `{a, b}`, so it also
  shows that the hypothesis is on the range, not on the number of alternatives.
* **The Borda count is manipulable.** With two voters and three alternatives, voter `0` ranks
  `1 ≻ 0 ≻ 2` and voter `1` ranks `0 ≻ 1 ≻ 2`; the Borda count, with ties broken towards the
  smaller alternative, chooses `0`. By reporting `1 ≻ 2 ≻ 0`, voter `0` makes it choose `1`.
-/

@[expose] public section

namespace ComplexityTests.GameTheory.GibbardSatterthwaite

open Cslib.GameTheory.SocialChoice SocialChoiceFunction

/-! ### Dictatorship: the hypotheses are satisfiable -/

/-- The dictatorship of voter `0` among three voters, on three alternatives, is strategy-proof
and onto, so the hypotheses of the Gibbard–Satterthwaite theorem are not vacuous. -/
example : (dictatorship (V := Fin 3) (A := Fin 3) 0).IsStrategyProof ∧
    Function.Surjective (dictatorship (V := Fin 3) (A := Fin 3) 0) :=
  ⟨isStrategyProof_dictatorship 0, surjective_dictatorship 0⟩

/-- The Gibbard–Satterthwaite theorem for three voters and three alternatives: the
strategy-proof onto rules are the dictatorships. -/
example (f : SocialChoiceFunction (Fin 3) (Fin 3)) (hf : f.IsStrategyProof)
    (hs : Function.Surjective f) : ∃ i, f = dictatorship i :=
  (isStrategyProof_and_surjective_iff ⟨0, 1, 2, by decide, by decide, by decide⟩).1 ⟨hf, hs⟩

/-- The range form: a strategy-proof rule taking at least three values has a dictator, whose
favourite value of the range is always chosen. -/
example (f : SocialChoiceFunction (Fin 5) ℕ) (hf : f.IsStrategyProof)
    (h3 : 3 ≤ (Set.range f).encard) :
    ∃ i, ∀ P x, x ∈ Set.range f → x ≠ f P → (P i).Prefers (f P) x :=
  isDictatorial_of_isStrategyProof hf h3

/-! ### Majority rule between two alternatives: three alternatives are needed -/

section Majority

variable {V A : Type*} [Fintype V]

open Classical in
/-- The number of voters ranking `a` above `b`. -/
noncomputable def support (P : Profile V A) (a b : A) : ℕ :=
  (Finset.univ.filter fun i => (P i).Prefers a b).card

open Classical in
/-- **Majority rule** between `a` and `b`: choose `a` when a strict majority of the voters rank
`a` above `b`, and `b` otherwise. -/
noncomputable def pairMajority (a b : A) : SocialChoiceFunction V A := fun P =>
  if Fintype.card V < 2 * support P a b then a else b

theorem pairMajority_eq_a_or_b (a b : A) (P : Profile V A) :
    pairMajority a b P = a ∨ pairMajority a b P = b := by
  unfold pairMajority
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Majority rule is monotone in the support: if every voter ranking `a` above `b` at `Q` also
does at `P`, and `a` wins at `Q`, then `a` wins at `P`. -/
theorem pairMajority_mono {a b : A} (hab : a ≠ b) {P Q : Profile V A}
    (h : ∀ i, (Q i).Prefers a b → (P i).Prefers a b) (hQ : pairMajority a b Q = a) :
    pairMajority a b P = a := by
  classical
  unfold pairMajority at hQ ⊢
  have hle : support Q a b ≤ support P a b := by
    unfold support
    exact Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact h i hi
  split_ifs at hQ with hlt
  · rw [ite_eq_left (by omega)]
  · exact absurd hQ.symm hab

/-- Majority rule between two alternatives is strategy-proof: a voter can only move the outcome
in the direction of their report, which is against their true ranking. -/
theorem isStrategyProof_pairMajority {a b : A} (hab : a ≠ b) :
    (pairMajority (V := V) a b).IsStrategyProof := by
  intro P Q i hPQ hman
  have hne := (P i).ne_of_prefers hman
  rcases pairMajority_eq_a_or_b a b P with hP | hP <;>
    rcases pairMajority_eq_a_or_b a b Q with hQ | hQ <;>
    rw [hP, hQ] at hne hman
  · exact hne rfl
  · -- The outcome moves from `a` to `b`, which `i` prefers; so `i` ranks `b` above `a`, and
    -- every voter ranking `a` above `b` at `P` also does at `Q`.
    refine hab ((pairMajority_mono hab (fun j hj => ?_) hP).symm.trans hQ)
    by_cases hji : j = i
    · subst hji
      exact absurd hj ((P j).asymm hman)
    · rw [← hPQ j hji]
      exact hj
  · refine hab ((pairMajority_mono hab (fun j hj => ?_) hQ).symm.trans hP)
    by_cases hji : j = i
    · subst hji
      exact (P j).prefers_of_not_prefers (Ne.symm hab) ((P j).asymm hman)
    · rw [hPQ j hji]
      exact hj
  · exact hne rfl

/-- For distinct `a` and `b` there is a ranking that puts `a` above `b`. -/
theorem exists_ranking_prefers {a b : A} (hab : a ≠ b) : ∃ r : Ranking A, r.Prefers a b := by
  obtain ⟨r⟩ := Ranking.nonempty A
  exact ⟨r.toTop a, r.isTop_toTop a b (Ne.symm hab)⟩

/-- If every voter reports the same ranking with `a` above `b`, majority rule picks `a`. -/
theorem pairMajority_const_eq_left [Nonempty V] {a b : A} {r : Ranking A} (h : r.Prefers a b) :
    pairMajority (V := V) a b (fun _ => r) = a := by
  classical
  unfold pairMajority support
  rw [Finset.filter_true_of_mem fun _ _ => h, Finset.card_univ, ite_eq_left (by
    have := Fintype.card_pos (α := V); omega)]

/-- If every voter reports the same ranking with `b` above `a`, majority rule picks `b`. -/
theorem pairMajority_const_eq_right {a b : A} {r : Ranking A} (h : r.Prefers b a) :
    pairMajority (V := V) a b (fun _ => r) = b := by
  classical
  unfold pairMajority support
  rw [Finset.filter_false_of_mem fun _ _ => r.asymm h, Finset.card_empty, ite_eq_right (by omega)]

/-- The range of majority rule is `{a, b}`. -/
theorem range_pairMajority [Nonempty V] {a b : A} (hab : a ≠ b) :
    Set.range (pairMajority (V := V) a b) = {a, b} := by
  obtain ⟨r, hr⟩ := exists_ranking_prefers hab
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨P, rfl⟩
    exact pairMajority_eq_a_or_b a b P
  · rintro (rfl | rfl)
    · exact ⟨_, pairMajority_const_eq_left hr⟩
    · exact ⟨_, pairMajority_const_eq_right (r := r.reverse) (r.reverse_prefers.2 hr)⟩

/-- With at least two voters, majority rule between two alternatives has no dictator: if one
voter ranks `a` above `b` and all others rank `b` above `a`, the outcome is `b`. -/
theorem not_isDictator_pairMajority {a b : A} (hab : a ≠ b) (hV : 2 ≤ Fintype.card V) (i : V) :
    ¬ (pairMajority (V := V) a b).IsDictator i := by
  classical
  intro hi
  have : Nonempty V := ⟨i⟩
  obtain ⟨r, hr⟩ := exists_ranking_prefers hab
  let P : Profile V A := fun j => if j = i then r else r.reverse
  have hsupp : support P a b = 1 := by
    unfold support
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.ext fun j => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = i
    · simp only [P, hj, ite_true, iff_true]
      exact hr
    · simp only [P, hj, ite_false, Ranking.reverse_prefers, iff_false]
      exact r.asymm hr
  have hPb : pairMajority a b P = b := by
    unfold pairMajority
    rw [hsupp, ite_eq_right (by omega)]
  have ha : a ∈ Set.range (pairMajority (V := V) a b) := by
    rw [range_pairMajority hab]
    exact Set.mem_insert a _
  have h := hi P a ha (by rw [hPb]; exact hab)
  rw [hPb] at h
  have hPi : P i = r := by simp only [P, ite_true]
  rw [hPi] at h
  exact r.asymm hr h

/-- With an odd number of voters, majority rule on two alternatives is strategy-proof, onto and
not dictatorial, so the Gibbard–Satterthwaite theorem needs three alternatives. -/
example : (pairMajority (V := Fin 3) true false).IsStrategyProof ∧
    Function.Surjective (pairMajority (V := Fin 3) true false) ∧
    ¬ (pairMajority (V := Fin 3) true false).IsDictatorial := by
  refine ⟨isStrategyProof_pairMajority (by decide), fun x => ?_,
    fun ⟨i, hi⟩ => not_isDictator_pairMajority (by decide) (by simp) i hi⟩
  have hx : x ∈ ({true, false} : Set Bool) := by cases x <;> simp
  rw [← range_pairMajority (V := Fin 3) (show true ≠ false by decide)] at hx
  exact hx

/-- On three alternatives, majority rule between `0` and `1` is strategy-proof and not
dictatorial, and its range has two elements: the theorem needs three alternatives in the range,
not merely three alternatives. -/
example : (pairMajority (V := Fin 3) (0 : Fin 3) 1).IsStrategyProof ∧
    ¬ (pairMajority (V := Fin 3) (0 : Fin 3) 1).IsDictatorial ∧
    (Set.range (pairMajority (V := Fin 3) (0 : Fin 3) 1)).encard = 2 := by
  refine ⟨isStrategyProof_pairMajority (by decide),
    fun ⟨i, hi⟩ => not_isDictator_pairMajority (by decide) (by simp) i hi, ?_⟩
  rw [range_pairMajority (by decide), Set.encard_pair (by decide)]

end Majority

/-! ### The Borda count is manipulable -/

section Borda

/-- The ranking of `Fin 3` by a score vector with distinct entries: higher scores rank higher. -/
def ofScore (s : Fin 3 → ℕ) (hs : Function.Injective s) : Ranking (Fin 3) where
  Prefers x y := s y < s x
  irrefl x := lt_irrefl _
  trans _ _ _ h1 h2 := h2.trans h1
  total x y hxy := by
    rcases lt_trichotomy (s x) (s y) with h | h | h
    · exact Or.inr h
    · exact absurd (hs h) hxy
    · exact Or.inl h

open Classical in
/-- The Borda score of `a`: the number of pairs of a voter and an alternative that the voter
ranks below `a`. -/
noncomputable def bordaScore (P : Profile (Fin 2) (Fin 3)) (a : Fin 3) : ℕ :=
  ∑ i, (Finset.univ.filter fun x => (P i).Prefers a x).card

/-- The **Borda count** on three alternatives, ties broken towards the smaller alternative. -/
noncomputable def borda : SocialChoiceFunction (Fin 2) (Fin 3) := fun P =>
  if bordaScore P 1 ≤ bordaScore P 0 ∧ bordaScore P 2 ≤ bordaScore P 0 then 0
  else if bordaScore P 2 ≤ bordaScore P 1 then 1 else 2

/-- Voter `0`'s true ranking `1 ≻ 0 ≻ 2`. -/
def truth₀ : Ranking (Fin 3) := ofScore ![1, 2, 0] (by decide)

/-- Voter `0`'s misreport `1 ≻ 2 ≻ 0`, which buries `0`. -/
def lie₀ : Ranking (Fin 3) := ofScore ![0, 2, 1] (by decide)

/-- Voter `1`'s ranking `0 ≻ 1 ≻ 2`. -/
def vote₁ : Ranking (Fin 3) := ofScore ![2, 1, 0] (by decide)

theorem bordaScore_ofScore (s t : Fin 3 → ℕ) (hs : Function.Injective s)
    (ht : Function.Injective t) (a : Fin 3) :
    bordaScore ![ofScore s hs, ofScore t ht] a =
      (Finset.univ.filter fun x => s x < s a).card +
        (Finset.univ.filter fun x => t x < t a).card := by
  unfold bordaScore
  rw [Fin.sum_univ_two]
  -- The two sides differ only in their decidability instances.
  convert rfl <;> exact Iff.rfl

/-- With the true rankings, the Borda scores are `(3, 3, 0)` and the outcome is `0`. -/
theorem borda_truth : borda ![truth₀, vote₁] = 0 := by
  unfold borda truth₀ vote₁
  simp only [bordaScore_ofScore]
  decide

/-- With voter `0`'s misreport, the Borda scores are `(2, 3, 1)` and the outcome is `1`. -/
theorem borda_lie : borda ![lie₀, vote₁] = 1 := by
  unfold borda lie₀ vote₁
  simp only [bordaScore_ofScore]
  decide

/-- **The Borda count is not strategy-proof**: voter `0` truly prefers `1` to `0`, and obtains
`1` instead of `0` by reporting `1 ≻ 2 ≻ 0`. -/
theorem borda_not_isStrategyProof : ¬ borda.IsStrategyProof := by
  intro h
  refine h ![truth₀, vote₁] ![lie₀, vote₁] 0 (fun j hj => ?_) ?_
  · have hj : j = 1 := by omega
    subst hj
    rfl
  · rw [borda_truth, borda_lie]
    change (![1, 2, 0] : Fin 3 → ℕ) 0 < (![1, 2, 0] : Fin 3 → ℕ) 1
    decide

end Borda

end ComplexityTests.GameTheory.GibbardSatterthwaite
