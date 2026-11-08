/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Brackets of selected positions

Fix `kk` positions `u 0 < u 1 < ⋯ < u (kk - 1)` of an input of length `n`; the input with those
positions set is the input with weight `kk` they select. A *bracket* is a list of pairs `(j, s)`,
read as "the `j`-th selected position is `s`". This file shows that brackets of bounded size
describe enough of the selected input for evaluating circuits of small depth, which is the core
of the reduction from weft-one circuits to `Clique`.

`know kk P s` is what the bracket `P` tells about position `s`: `some true` when `P` names `s`,
`some false` when `P` names two consecutive selected positions around `s` (or the first selected
position after `s`, or the last before it), and `none` otherwise. When the bracket is correct
these answers are right (`know_sound`). For every set `S` of positions there is a set of at most
`2 * S.card` indices whose correct bracket knows every position of `S` (`exists_cover`).

Two brackets are *consistent* (`consistent`) when their pairs are pairwise compatible
(`pairOk`): equal indices name equal positions, and indices and positions are in the same order.

## Main definitions

* `Cslib.Complexity.WCS.ToClique.know`: what a bracket tells about a position.
* `Cslib.Complexity.WCS.ToClique.pairOk`, `Cslib.Complexity.WCS.ToClique.consistent`:
  compatibility of pairs and consistency of brackets.

## Main results

* `Cslib.Complexity.WCS.ToClique.know_sound`: a correct bracket answers correctly.
* `Cslib.Complexity.WCS.ToClique.exists_cover`: few indices let a correct bracket know every
  position of a set.
* `Cslib.Complexity.WCS.ToClique.computableInPolyTime_know`,
  `Cslib.Complexity.WCS.ToClique.computableInPolyTime_consistent`: both tests are
  polynomial-time.
-/

@[expose] public section

namespace Cslib.Complexity.WCS.ToClique

open Turing.MultiTapeTM

/-! ### What a bracket knows -/

/-- What the bracket `P` tells about position `s` when `kk` positions are selected: `some true`
when `P` names `s`, `some false` when `P` shows that `s` is not selected, and `none`
otherwise. -/
def know (kk : ℕ) (P : List (ℕ × ℕ)) (s : ℕ) : Option Bool :=
  if P.any (fun p => p.2 == s) then some true
  else if kk = 0 then some false
  else if P.any (fun p => p.1 == 0 && decide (s < p.2)) then some false
  else if P.any (fun p => p.1 + 1 == kk && decide (p.2 < s)) then some false
  else if P.any (fun p => P.any fun q => q.1 == p.1 + 1 && decide (p.2 < s) && decide (s < q.2))
    then some false
  else none

/-- **A correct bracket answers correctly.** If the `kk` selected positions `u 0 < ⋯ < u (kk - 1)`
increase and every pair of `P` is correct, every answer of `know kk P` is right. -/
theorem know_sound {kk : ℕ} {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk))
    {P : List (ℕ × ℕ)} (hP : ∀ p ∈ P, p.1 < kk ∧ p.2 = u p.1) {s : ℕ} {b : Bool}
    (h : know kk P s = some b) : b = decide (∃ i < kk, u i = s) := by
  have hlt : ∀ {i j}, i < kk → j < kk → (u i < u j ↔ i < j) := fun hi hj =>
    hu.lt_iff_lt (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj)
  unfold know at h
  split_ifs at h with h₁ h₂ h₃ h₄ h₅ <;> cases h
  · obtain ⟨p, hp, hps⟩ := List.any_eq_true.1 h₁
    have hps' : p.2 = s := by simpa using hps
    exact (decide_eq_true ⟨p.1, (hP p hp).1, (hP p hp).2 ▸ hps'⟩).symm
  · simp [h₂]
  · obtain ⟨p, hp, hps⟩ := List.any_eq_true.1 h₃
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hps
    refine (decide_eq_false ?_).symm
    rintro ⟨i, hi, rfl⟩
    obtain ⟨hp1, hp2⟩ := hP p hp
    have h0 : 0 < kk := by omega
    rw [hp2, hps.1] at hps
    have := (hlt hi h0).1 hps.2
    omega
  · obtain ⟨p, hp, hps⟩ := List.any_eq_true.1 h₄
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hps
    refine (decide_eq_false ?_).symm
    rintro ⟨i, hi, rfl⟩
    obtain ⟨hp1, hp2⟩ := hP p hp
    rw [hp2] at hps
    have := (hlt hp1 hi).1 hps.2
    omega
  · obtain ⟨p, hp, hpq'⟩ := List.any_eq_true.1 h₅
    obtain ⟨q, hq, hpq⟩ := List.any_eq_true.1 hpq'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpq
    refine (decide_eq_false ?_).symm
    rintro ⟨i, hi, rfl⟩
    obtain ⟨hp1, hp2⟩ := hP p hp
    obtain ⟨hq1, hq2⟩ := hP q hq
    rw [hp2, hq2] at hpq
    have a := (hlt hp1 hi).1 hpq.1.2
    have b := (hlt hi hq1).1 hpq.2
    omega

/-- **Two indices suffice for one position.** For every position `s` there are at most two
indices whose correct pairs make `know kk P s` defined. -/
theorem exists_pair_know {kk : ℕ} {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk)) (s : ℕ) :
    ∃ J : Finset ℕ, J.card ≤ 2 ∧ (∀ j ∈ J, j < kk) ∧
      ∀ P : List (ℕ × ℕ), (∀ j ∈ J, (j, u j) ∈ P) → know kk P s ≠ none := by
  have hlt : ∀ {i j}, i < kk → j < kk → (u i < u j ↔ i < j) := fun hi hj =>
    hu.lt_iff_lt (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj)
  by_cases hhit : ∃ i < kk, u i = s
  · obtain ⟨i, hi, rfl⟩ := hhit
    refine ⟨{i}, by simp, by simpa using hi, fun P hP => ?_⟩
    have hmem := hP i (Finset.mem_singleton_self i)
    have : P.any (fun p => p.2 == u i) = true := List.any_eq_true.2 ⟨_, hmem, by simp⟩
    simp [know, this]
  rcases Nat.eq_zero_or_pos kk with hk | hk
  · refine ⟨∅, by simp, by simp, fun P _ => ?_⟩
    unfold know
    split_ifs <;> simp_all
  have hne : ∀ i < kk, u i ≠ s := fun i hi h => hhit ⟨i, hi, h⟩
  by_cases hlow : s < u 0
  · refine ⟨{0}, by simp, by simpa using hk, fun P hP => ?_⟩
    have hmem := hP 0 (Finset.mem_singleton_self 0)
    have : P.any (fun p => p.1 == 0 && decide (s < p.2)) = true :=
      List.any_eq_true.2 ⟨_, hmem, by simp [hlow]⟩
    unfold know
    split_ifs <;> simp_all
  by_cases hhigh : u (kk - 1) < s
  · refine ⟨{kk - 1}, by simp, by simp; omega, fun P hP => ?_⟩
    have hmem := hP (kk - 1) (Finset.mem_singleton_self _)
    have : P.any (fun p => p.1 + 1 == kk && decide (p.2 < s)) = true :=
      List.any_eq_true.2 ⟨_, hmem, by simp [hhigh]; omega⟩
    unfold know
    split_ifs <;> simp_all
  -- `s` lies strictly between two consecutive selected positions.
  rw [not_lt] at hlow hhigh
  have hk2 : 2 ≤ kk := by
    by_contra hcon
    have : kk = 1 := by omega
    subst this
    exact hne 0 (by omega) (le_antisymm hlow hhigh)
  have hex : ∃ j, j + 1 < kk ∧ s < u (j + 1) := by
    refine ⟨kk - 2, by omega, ?_⟩
    have : kk - 2 + 1 = kk - 1 := by omega
    rw [this]
    exact lt_of_le_of_ne hhigh (fun h => hne (kk - 1) (by omega) h.symm)
  classical
  let j₁ := Nat.find hex
  have hj₁ : j₁ + 1 < kk ∧ s < u (j₁ + 1) := Nat.find_spec hex
  have hj₀ : u j₁ < s := by
    rcases Nat.eq_zero_or_pos j₁ with h0 | h0
    · rw [h0]
      exact lt_of_le_of_ne hlow (hne 0 hk)
    · have hmin := Nat.find_min hex (show j₁ - 1 < j₁ by omega)
      rw [not_and_or] at hmin
      rcases hmin with hmin | hmin
      · omega
      · have : j₁ - 1 + 1 = j₁ := by omega
        rw [this, not_lt] at hmin
        exact lt_of_le_of_ne hmin (hne j₁ (by omega))
  refine ⟨{j₁, j₁ + 1}, Finset.card_le_two, ?_, fun P hP => ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  have hm₀ := hP j₁ (by simp)
  have hm₁ := hP (j₁ + 1) (by simp)
  have : P.any (fun p => P.any fun q =>
      q.1 == p.1 + 1 && decide (p.2 < s) && decide (s < q.2)) = true :=
    List.any_eq_true.2 ⟨_, hm₀, List.any_eq_true.2 ⟨_, hm₁, by simp [hj₀, hj₁.2]⟩⟩
  unfold know
  split_ifs <;> simp_all

/-- **Covering a set of positions.** For every set `S` of positions there is a set of at most
`2 * S.card` indices whose correct pairs make `know kk P s` defined for every `s ∈ S`. -/
theorem exists_cover {kk : ℕ} {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk)) (S : Finset ℕ) :
    ∃ J : Finset ℕ, J.card ≤ 2 * S.card ∧ (∀ j ∈ J, j < kk) ∧
      ∀ P : List (ℕ × ℕ), (∀ j ∈ J, (j, u j) ∈ P) → ∀ s ∈ S, know kk P s ≠ none := by
  classical
  choose J hJcard hJlt hJknow using fun s => exists_pair_know hu s
  refine ⟨S.biUnion J, ?_, ?_, ?_⟩
  · calc (S.biUnion J).card ≤ ∑ s ∈ S, (J s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ S, 2 := Finset.sum_le_sum fun s _ => hJcard s
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro j hj
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 hj
    exact hJlt s j hs
  · intro P hP s hs
    exact hJknow s P fun j hj => hP j (Finset.mem_biUnion.2 ⟨s, hs, hj⟩)

/-! ### Consistency -/

/-- Two pairs are compatible: equal indices name equal positions, and indices and positions are
in the same order. -/
def pairOk (p q : ℕ × ℕ) : Bool :=
  ((p.1 == q.1) == (p.2 == q.2)) && (decide (p.1 < q.1) == decide (p.2 < q.2))

theorem pairOk_iff (p q : ℕ × ℕ) :
    pairOk p q = true ↔ (p.1 = q.1 ↔ p.2 = q.2) ∧ (p.1 < q.1 ↔ p.2 < q.2) := by
  unfold pairOk
  by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;> by_cases h₃ : p.1 < q.1 <;>
    by_cases h₄ : p.2 < q.2 <;> simp [h₁, h₂, h₃, h₄]

/-- Two brackets are consistent when all their pairs are compatible. -/
def consistent (P Q : List (ℕ × ℕ)) : Bool :=
  P.all fun p => Q.all fun q => pairOk p q

theorem consistent_iff {P Q : List (ℕ × ℕ)} :
    consistent P Q = true ↔ ∀ p ∈ P, ∀ q ∈ Q, pairOk p q = true := by
  simp only [consistent, List.all_eq_true]

/-! ### Polynomial time -/

/-- The conditions of `know`, as Booleans. -/
private theorem know_eq (kk : ℕ) (P : List (ℕ × ℕ)) (s : ℕ) : know kk P s =
    if P.any (fun p => p.2 == s) then some true
    else if (kk == 0 || P.any (fun p => p.1 == 0 && decide (s < p.2)) ||
      P.any (fun p => p.1 + 1 == kk && decide (p.2 < s)) ||
      P.any (fun p => P.any fun q => q.1 == p.1 + 1 && decide (p.2 < s) && decide (s < q.2)))
    then some false else none := by
  unfold know
  by_cases h₁ : P.any (fun p => p.2 == s) = true
  · simp only [h₁, ↓reduceIte]
  · simp only [h₁, Bool.false_eq_true, ↓reduceIte]
    by_cases h₂ : kk = 0
    · simp [h₂]
    · have h₂' : (kk == 0) = false := by simpa using h₂
      simp only [h₂, ↓reduceIte, h₂', Bool.false_or]
      by_cases h₃ : P.any (fun p => p.1 == 0 && decide (s < p.2)) = true
      · simp only [h₃, ↓reduceIte, Bool.true_or]
      · simp only [h₃, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
        by_cases h₄ : P.any (fun p => p.1 + 1 == kk && decide (p.2 < s)) = true
        · simp only [h₄, ↓reduceIte, Bool.true_or]
        · simp only [h₄, Bool.false_eq_true, ↓reduceIte, Bool.false_or]

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- `know` is polynomial-time, with the count, the pairs and the position in unary. -/
theorem computableInPolyTime_know {kk s : γ → ℕ} {P : γ → List (ℕ × ℕ)}
    (hkk : ComputableInPolyTime kk encIn encUnary)
    (hP : ComputableInPolyTime P encIn (encList (encPair encUnary encUnary)))
    (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime (fun a => know (kk a) (P a) (s a)) encIn (encOption encBool) := by
  have hkk' := hkk.tidy
  have hP' := hP.tidy
  have hs' := hs.tidy
  refine ComputableInPolyTime.of_tidy ?_
  simp only [know_eq]
  fun_prop

/-- Consistency of brackets is polynomial-time, with the pairs in unary. -/
theorem computableInPolyTime_consistent {P Q : γ → List (ℕ × ℕ)}
    (hP : ComputableInPolyTime P encIn (encList (encPair encUnary encUnary)))
    (hQ : ComputableInPolyTime Q encIn (encList (encPair encUnary encUnary))) :
    ComputableInPolyTime (fun a => consistent (P a) (Q a)) encIn encBool := by
  have hP' := hP.tidy
  have hQ' := hQ.tidy
  refine ComputableInPolyTime.of_tidy ?_
  unfold consistent pairOk
  fun_prop

end Cslib.Complexity.WCS.ToClique
