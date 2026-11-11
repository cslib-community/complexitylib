/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.SocialChoice.Ranking
import Mathlib.Data.Fintype.EquivFin

/-!
# Arrow's impossibility theorem

A finite electorate `V` ranks a set `A` of alternatives. Each voter holds a strict linear order
(`Ranking A`), and a *social welfare function* (`SocialWelfareFunction V A`) turns every profile
`V → Ranking A` into a social ranking. The social ranking is a complete preorder
(`WeakRanking A`), so society may be indifferent between alternatives, as in Arrow's
formulation [Arrow1951]. Arrow's theorem says that with at least three alternatives, weak Pareto
(unanimity) and independence of irrelevant alternatives (IIA) force a dictator.

The proof is the first of the three proofs of [Geanakoplos2005]. *Extremal lemma:* if every
voter ranks an alternative `b` at the top or at the bottom, society ranks `b` strictly at the
top or strictly at the bottom. *Pivotal voter:* starting from the profile in which everyone ranks
`b` last and moving `b` to the top one voter at a time, there is a voter `n` whose move takes `b`
from the social bottom to the social top (an *extremely pivotal* voter). *Dictatorship:* `n`
dictates every pair of alternatives other than `b`, and the extremely pivotal voters of
different alternatives coincide, so `n` dictates every pair.

**Scope.** Voters' rankings are strict, so the domain consists of all profiles of linear orders;
society's ranking may contain ties. Excluding individual indifference makes the theorem formally
stronger, not weaker: Pareto and IIA are only assumed on the smaller domain of strict profiles, so
the theorem applies to more rules. The version in which voters may also be indifferent follows
from this one by a short IIA reduction, which is not formalized here. Strict-valued rules are
covered by composing with `Ranking.toWeakRanking`. The set of alternatives may be infinite: the
theorem only needs three distinct alternatives. The electorate must be finite; with infinitely
many voters, rules defined from a nonprincipal ultrafilter satisfy Pareto and IIA without a
dictator (Fishburn 1970), which is not formalized here. The tests show that the hypotheses of
three alternatives and of IIA are needed: majority rule for three voters on two alternatives is
Pareto, IIA and not dictatorial, and the Borda count for two voters on three alternatives is
Pareto and not dictatorial (so, by the theorem, not IIA).

**Representation.** The preference model (`Ranking`, `WeakRanking`, `Profile`) is in
`Complexity.GameTheory.SocialChoice.Ranking`, which explains why rankings are bundled structures
rather than instances of Mathlib's `LinearOrder`.

## Main definitions

* `SocialWelfareFunction`: maps every `Profile` of rankings to a `WeakRanking` (both from
  `Complexity.GameTheory.SocialChoice.Ranking`).
* `SocialWelfareFunction.IsPareto`, `SocialWelfareFunction.IsIIA`,
  `SocialWelfareFunction.IsDictator`, `SocialWelfareFunction.IsDictatorial`,
  `SocialWelfareFunction.dictatorship`.

## Main results

* `SocialWelfareFunction.isTop_or_isBottom_of_extremal`: the extremal lemma.
* `SocialWelfareFunction.isDictatorial_of_isPareto_of_isIIA`: **Arrow's impossibility
  theorem**; `SocialWelfareFunction.isDictatorial_of_three_le_card` for finite `A`.
* `SocialWelfareFunction.existsUnique_isDictator_of_isPareto_of_isIIA`: the dictator is unique.
* `SocialWelfareFunction.isPareto_and_isIIA_iff`: the Pareto IIA rules are exactly the
  dictatorships.
* `SocialWelfareFunction.isDictator_iff_eq_dictatorship`: a rule with dictator `i` is the
  dictatorship of `i`.

## References

* [K. J. Arrow, *Social Choice and Individual Values*][Arrow1951]
* [J. Geanakoplos, *Three brief proofs of Arrow's impossibility theorem*][Geanakoplos2005]
-/

public section

namespace Cslib.GameTheory.SocialChoice

variable {A : Type*}

/-- A **social welfare function** aggregates every preference profile into a weak ranking. -/
abbrev SocialWelfareFunction (V A : Type*) := Profile V A → WeakRanking A

namespace SocialWelfareFunction

variable {V : Type*} (F : SocialWelfareFunction V A)

/-- **Weak Pareto** (unanimity): if every voter ranks `a` above `b`, so does society. -/
@[expose] def IsPareto : Prop :=
  ∀ (P : Profile V A) (a b : A), (∀ i, (P i).Prefers a b) → (F P).Prefers a b

/-- **Independence of irrelevant alternatives**: society's comparison of `a` and `b` depends
only on the voters' comparisons of `a` and `b`. -/
@[expose] def IsIIA : Prop :=
  ∀ (P Q : Profile V A) (a b : A), (∀ i, ((P i).Prefers a b ↔ (Q i).Prefers a b)) →
    ((F P).AtLeast a b ↔ (F Q).AtLeast a b)

/-- Voter `i` is a **dictator** for `F`: whenever `i` ranks `a` above `b`, so does society. -/
@[expose] def IsDictator (i : V) : Prop :=
  ∀ (P : Profile V A) (a b : A), (P i).Prefers a b → (F P).Prefers a b

/-- `F` is **dictatorial** if it has a dictator. -/
@[expose] def IsDictatorial : Prop := ∃ i, F.IsDictator i

/-- The **dictatorship** of voter `i`: society adopts `i`'s ranking. -/
@[expose] def dictatorship (i : V) : SocialWelfareFunction V A := fun P => (P i).toWeakRanking

theorem isDictator_dictatorship (i : V) : (dictatorship (A := A) i).IsDictator i :=
  fun P _ _ h => (P i).toWeakRanking_prefers.mpr h

variable {F}

/-- IIA, stated for the strict social comparison. -/
theorem IsIIA.prefers_iff (hF : F.IsIIA) {P Q : Profile V A} {a b : A}
    (h : ∀ i, ((P i).Prefers a b ↔ (Q i).Prefers a b)) :
    (F P).Prefers a b ↔ (F Q).Prefers a b := by
  by_cases hab : a = b
  · subst hab; exact iff_of_false ((F P).prefers_irrefl a) ((F Q).prefers_irrefl a)
  refine not_congr (hF P Q b a fun i => ?_)
  rw [← (P i).not_prefers_iff hab, ← (Q i).not_prefers_iff hab, h i]

/-- Two profiles in which `b` is at the top of, or at the bottom of, each voter's ranking,
consistently, agree on every comparison involving `b`. -/
private theorem prefers_iff_of_extremal {P Q : Profile V A} {b x y : A}
    (hPQ : ∀ i, ((P i).IsTop b ∧ (Q i).IsTop b) ∨ ((P i).IsBottom b ∧ (Q i).IsBottom b))
    (hxy : x = b ∨ y = b) (i : V) : (P i).Prefers x y ↔ (Q i).Prefers x y := by
  rcases hPQ i with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · exact (P i).prefers_iff_of_isTop hP hQ hxy
  · exact (P i).prefers_iff_of_isBottom hP hQ hxy

/-- There is a third alternative distinct from any two given ones. -/
private theorem exists_ne_ne (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (x y : A) :
    ∃ z, z ≠ x ∧ z ≠ y := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  by_contra! h
  by_cases hax : a = x
  · subst hax
    exact hbc ((h b hab.symm).trans (h c hac.symm).symm)
  · by_cases hbx : b = x
    · subst hbx
      exact hac ((h a hab).trans (h c hbc.symm).symm)
    · exact hab ((h a hax).trans (h b hbx).symm)

/-- **Extremal lemma** ([Geanakoplos2005], first proof): if every voter ranks `b` at the top or
at the bottom, society ranks `b` strictly at the top or strictly at the bottom. The hypothesis of
three alternatives is needed: with two alternatives, majority rule over an even electorate can
tie them. -/
theorem isTop_or_isBottom_of_extremal (hP : F.IsPareto) (hI : F.IsIIA)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) {P : Profile V A} {b : A}
    (hb : ∀ i, (P i).IsTop b ∨ (P i).IsBottom b) :
    (F P).IsTop b ∨ (F P).IsBottom b := by
  classical
  by_contra! h
  obtain ⟨hT, hB⟩ := h
  simp only [WeakRanking.IsTop, WeakRanking.IsBottom, WeakRanking.Prefers, not_forall,
    not_not] at hT hB
  obtain ⟨a₀, ha₀b, hab₀⟩ := hT
  obtain ⟨c₀, hc₀b, hbc₀⟩ := hB
  -- Find distinct `a, c ≠ b` with `a ≥ b ≥ c` socially.
  obtain ⟨a, c, hab, hcb, hac, hab', hbc'⟩ : ∃ a c, a ≠ b ∧ c ≠ b ∧ a ≠ c ∧
      (F P).AtLeast a b ∧ (F P).AtLeast b c := by
    by_cases hac₀ : a₀ = c₀
    · subst hac₀
      obtain ⟨d, hdb, hda⟩ := exists_ne_ne h3 b a₀
      rcases (F P).total d b with hdb' | hbd'
      · exact ⟨d, a₀, hdb, ha₀b, hda, hdb', hbc₀⟩
      · exact ⟨a₀, d, ha₀b, hdb, Ne.symm hda, hab₀, hbd'⟩
    · exact ⟨a₀, c₀, ha₀b, hc₀b, hac₀, hab₀, hbc₀⟩
  -- Move `c` just above `a` without moving `b`.
  let Q : Profile V A := fun i =>
    if (P i).IsTop b then ((P i).toTop c).toTop b else ((P i).toTop c).toBottom b
  have hQ : ∀ i, ((P i).IsTop b ∧ (Q i).IsTop b) ∨ ((P i).IsBottom b ∧ (Q i).IsBottom b) := by
    intro i
    by_cases ht : (P i).IsTop b
    · left
      refine ⟨ht, ?_⟩
      simp only [Q, ht, ite_true]
      exact ((P i).toTop c).isTop_toTop b
    · right
      refine ⟨(hb i).resolve_left ht, ?_⟩
      simp only [Q, ht, ite_false]
      exact ((P i).toTop c).isBottom_toBottom b
  have hca : ∀ i, (Q i).Prefers c a := by
    intro i
    by_cases ht : (P i).IsTop b
    · simp only [Q, ht, ite_true]
      exact (((P i).toTop c).toTop_prefers_of_ne hcb hab).2 ((P i).isTop_toTop c a hac)
    · simp only [Q, ht, ite_false]
      exact (((P i).toTop c).toBottom_prefers_of_ne hcb hab).2 ((P i).isTop_toTop c a hac)
  have h1 := (hI P Q a b (prefers_iff_of_extremal hQ (Or.inr rfl))).1 hab'
  have h2 := (hI P Q b c (prefers_iff_of_extremal hQ (Or.inl rfl))).1 hbc'
  exact hP Q c a hca ((F Q).trans _ _ _ h1 h2)

/-- `F` turns a profile in which `b` is at the top or bottom of every ranking, with society
ranking `b` at the bottom, into one with society ranking `b` at the top, when the single voter
`n` moves `b` from the bottom to the top of their ranking. This is the *extremely pivotal voter*
of [Geanakoplos2005]. -/
private def IsPivot (F : SocialWelfareFunction V A) (b : A) (n : V) : Prop :=
  ∃ P₁ P₂ : Profile V A, (∀ j, j ≠ n → P₁ j = P₂ j) ∧
    (∀ j, (P₁ j).IsTop b ∨ (P₁ j).IsBottom b) ∧ (P₁ n).IsBottom b ∧ (P₂ n).IsTop b ∧
    (F P₁).IsBottom b ∧ (F P₂).IsTop b

/-- Along the insertions building a finset where `T` holds, from `∅` where it fails, there is a
first insertion that makes `T` hold. -/
private theorem exists_insert_flip {V : Type*} [DecidableEq V] {T : Finset V → Prop}
    (h0 : ¬ T ∅) (s : Finset V) (hs : T s) :
    ∃ t : Finset V, ∃ i ∉ t, ¬ T t ∧ T (insert i t) := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs h0
  | insert i t hi ih =>
    by_cases ht : T t
    · exact ih ht
    · exact ⟨t, i, hi, ht, hs⟩

/-- For every alternative `b` there is an extremely pivotal voter ([Geanakoplos2005], first
proof): move `b` from the bottom to the top of the voters' rankings one voter at a time. -/
private theorem exists_isPivot [Finite V] (hP : F.IsPareto) (hI : F.IsIIA)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (b : A) : ∃ n, IsPivot F b n := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨r⟩ := Ranking.nonempty A
  obtain ⟨a, hab, -⟩ := exists_ne_ne h3 b b
  let P : Finset V → Profile V A := fun S j => if j ∈ S then r.toTop b else r.toBottom b
  have hext : ∀ S j, (P S j).IsTop b ∨ (P S j).IsBottom b := by
    intro S j
    by_cases hj : j ∈ S
    · left; simp only [P, hj, ite_true]; exact r.isTop_toTop b
    · right; simp only [P, hj, ite_false]; exact r.isBottom_toBottom b
  let T : Finset V → Prop := fun S => (F (P S)).IsTop b
  have h0 : ¬ T ∅ := by
    intro hT
    have hlow : (F (P ∅)).Prefers a b := hP _ a b fun j => by
      simp only [P, Finset.notMem_empty, ite_false]
      exact r.isBottom_toBottom b a hab
    exact (F (P ∅)).prefers_asymm hlow (hT a hab)
  have huniv : T Finset.univ := fun x hx => hP _ b x fun j => by
    simp only [P, Finset.mem_univ, ite_true]
    exact r.isTop_toTop b x hx
  obtain ⟨S, n, hn, hS, hS'⟩ := exists_insert_flip h0 _ huniv
  refine ⟨n, P S, P (insert n S), fun j hj => ?_, hext S, ?_, ?_, ?_, hS'⟩
  · simp only [P, Finset.mem_insert, hj, false_or]
  · simp only [P, hn, ite_false]; exact r.isBottom_toBottom b
  · simp only [P, Finset.mem_insert, true_or, ite_true]; exact r.isTop_toTop b
  · exact (isTop_or_isBottom_of_extremal hP hI h3 (hext S)).resolve_left hS

/-- An extremely pivotal voter for `b` dictates society's comparison of every pair of
alternatives other than `b` ([Geanakoplos2005], first proof). -/
private theorem IsPivot.prefers (hI : F.IsIIA) {b : A} {n : V} (hn : IsPivot F b n)
    (P : Profile V A) {x y : A} (hxb : x ≠ b) (hyb : y ≠ b) (hxy : (P n).Prefers x y) :
    (F P).Prefers x y := by
  classical
  obtain ⟨P₁, P₂, hP₁₂, hext, h₁n, h₂n, hF₁, hF₂⟩ := hn
  -- Voter `n` ranks `x` above `b` above `y`; every other voter keeps `b` where `P₁` has it.
  let Q : Profile V A := fun j =>
    if j = n then ((P j).toTop b).toTop x
    else if (P₁ j).IsTop b then (P j).toTop b else (P j).toBottom b
  have hxy' : x ≠ y := (P n).ne_of_prefers hxy
  -- `Q` keeps `b` where `P₁` has it, for every voter other than `n`.
  have hQ : ∀ j, j ≠ n → ((P₁ j).IsTop b ∧ (Q j).IsTop b) ∨
      ((P₁ j).IsBottom b ∧ (Q j).IsBottom b) := by
    intro j hj
    by_cases ht : (P₁ j).IsTop b
    · refine Or.inl ⟨ht, ?_⟩
      simp only [Q, hj, ht, ite_true, ite_false]
      exact (P j).isTop_toTop b
    · refine Or.inr ⟨(hext j).resolve_left ht, ?_⟩
      simp only [Q, hj, ht, ite_false]
      exact (P j).isBottom_toBottom b
  have hQn : Q n = ((P n).toTop b).toTop x := by simp only [Q, ite_true]
  -- Society ranks `x` above `b` at `Q`, as at `P₁`.
  have h1 : (F Q).Prefers x b := by
    refine (hI.prefers_iff fun j => ?_).1 (hF₁ x hxb)
    by_cases hj : j = n
    · subst hj
      rw [hQn]
      exact iff_of_true (h₁n x hxb) (((P j).toTop b).isTop_toTop x b hxb.symm)
    · rcases hQ j hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact (P₁ j).prefers_iff_of_isTop h₁ h₂ (Or.inr rfl)
      · exact (P₁ j).prefers_iff_of_isBottom h₁ h₂ (Or.inr rfl)
  -- Society ranks `b` above `y` at `Q`, as at `P₂`.
  have h2 : (F Q).Prefers b y := by
    refine (hI.prefers_iff fun j => ?_).1 (hF₂ y hyb)
    by_cases hj : j = n
    · subst hj
      rw [hQn]
      refine iff_of_true (h₂n y hyb) ?_
      rw [((P j).toTop b).toTop_prefers_of_ne hxb.symm (Ne.symm hxy')]
      exact (P j).isTop_toTop b y hyb
    · rw [← hP₁₂ j hj]
      rcases hQ j hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact (P₁ j).prefers_iff_of_isTop h₁ h₂ (Or.inl rfl)
      · exact (P₁ j).prefers_iff_of_isBottom h₁ h₂ (Or.inl rfl)
  -- `Q` agrees with `P` on `x` versus `y`.
  refine (hI.prefers_iff fun j => ?_).2 ((F Q).prefers_trans h1 h2)
  by_cases hj : j = n
  · subst hj
    rw [hQn]
    refine iff_of_true hxy ?_
    exact ((P j).toTop b).isTop_toTop x y (Ne.symm hxy')
  · simp only [Q, hj, ite_false]
    split_ifs
    · exact ((P j).toTop_prefers_of_ne hxb hyb).symm
    · exact ((P j).toBottom_prefers_of_ne hxb hyb).symm

/-- The extremely pivotal voters for two different alternatives coincide. -/
private theorem IsPivot.eq (hI : F.IsIIA) (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {b c : A} (hbc : b ≠ c) {n m : V} (hn : IsPivot F b n) (hm : IsPivot F c m) : n = m := by
  by_contra hnm
  obtain ⟨P₁, P₂, hP₁₂, -, -, -, hF₁, hF₂⟩ := hn
  obtain ⟨a, hab, hac⟩ := exists_ne_ne h3 b c
  rcases (P₁ m).total a b hab with h | h
  · -- `m` ranks `a` above `b` in both profiles, but society ranks `b` above `a` at `P₂`.
    have h' : (P₂ m).Prefers a b := hP₁₂ m (Ne.symm hnm) ▸ h
    exact (F P₂).prefers_asymm (hF₂ a hab) (hm.prefers hI P₂ hac hbc h')
  · exact (F P₁).prefers_asymm (hF₁ a hab) (IsPivot.prefers hI hm P₁ hbc hac h)

/-- A dictator makes the rule weakly Pareto. -/
theorem IsDictator.isPareto {i : V} (hi : F.IsDictator i) : F.IsPareto :=
  fun P a b h => hi P a b (h i)

/-- A dictatorship is weakly Pareto. -/
theorem isPareto_dictatorship (i : V) : (dictatorship (A := A) i).IsPareto :=
  (isDictator_dictatorship i).isPareto

/-- A dictatorship satisfies independence of irrelevant alternatives. -/
theorem isIIA_dictatorship (i : V) : (dictatorship (A := A) i).IsIIA := by
  intro P Q a b h
  change a = b ∨ (P i).Prefers a b ↔ a = b ∨ (Q i).Prefers a b
  rw [h i]

/-- Voter `i` is a dictator exactly when `F` is the dictatorship of `i`: society's weak ranking
is then `i`'s ranking, with no ties. -/
theorem isDictator_iff_eq_dictatorship {i : V} : F.IsDictator i ↔ F = dictatorship i := by
  constructor
  · intro hi
    funext P
    ext a b
    change (F P).AtLeast a b ↔ a = b ∨ (P i).Prefers a b
    by_cases hab : a = b
    · subst hab
      exact iff_of_true ((F P).refl a) (Or.inl rfl)
    constructor
    · intro h
      exact Or.inr (by_contra fun hn => hi P b a ((P i).prefers_of_not_prefers hab hn) h)
    · rintro (rfl | h)
      · exact (F P).refl a
      · exact (F P).atLeast_of_prefers (hi P a b h)
  · rintro rfl
    exact isDictator_dictatorship i

/-- With at least two alternatives, a rule has at most one dictator. -/
theorem IsDictator.unique [Nontrivial A] {i j : V} (hi : F.IsDictator i) (hj : F.IsDictator j) :
    i = j := by
  classical
  by_contra hij
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  obtain ⟨r⟩ := Ranking.nonempty A
  obtain ⟨s, hs⟩ : ∃ s : Ranking A, s.Prefers a b := by
    rcases r.total a b hab with h | h
    · exact ⟨r, h⟩
    · exact ⟨r.reverse, r.reverse_prefers.2 h⟩
  let P : Profile V A := fun k => if k = i then s else s.reverse
  have h1 : (F P).Prefers a b := hi P a b (by simp only [P, ite_true]; exact hs)
  have h2 : (F P).Prefers b a := hj P b a (by
    simp only [P, Ne.symm hij, ite_false]; exact s.reverse_prefers.2 hs)
  exact (F P).prefers_asymm h1 h2

/-- **Arrow's impossibility theorem** ([Arrow1951], [Geanakoplos2005]): with finitely many
voters and at least three alternatives, every weakly Pareto social welfare function satisfying
independence of irrelevant alternatives is dictatorial. -/
theorem isDictatorial_of_isPareto_of_isIIA [Finite V] (hP : F.IsPareto) (hI : F.IsIIA)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) : F.IsDictatorial := by
  obtain ⟨b, -⟩ := id h3
  obtain ⟨n, hn⟩ := exists_isPivot hP hI h3 b
  refine ⟨n, fun P x y hxy => ?_⟩
  obtain ⟨d, hdx, hdy⟩ := exists_ne_ne h3 x y
  obtain ⟨m, hm⟩ := exists_isPivot hP hI h3 d
  by_cases hbd : b = d
  · subst hbd
    exact hn.prefers hI P (Ne.symm hdx) (Ne.symm hdy) hxy
  · obtain rfl := IsPivot.eq hI h3 hbd hn hm
    exact hm.prefers hI P (Ne.symm hdx) (Ne.symm hdy) hxy

/-- **Arrow's impossibility theorem** for a finite set of at least three alternatives. -/
theorem isDictatorial_of_three_le_card [Fintype A] [Finite V] (hP : F.IsPareto)
    (hI : F.IsIIA) (hA : 3 ≤ Fintype.card A) : F.IsDictatorial :=
  isDictatorial_of_isPareto_of_isIIA hP hI (Fintype.two_lt_card_iff.1 hA)

/-- Under the hypotheses of Arrow's theorem the dictator is unique. -/
theorem existsUnique_isDictator_of_isPareto_of_isIIA [Finite V] (hP : F.IsPareto)
    (hI : F.IsIIA) (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) : ∃! i, F.IsDictator i := by
  obtain ⟨a, b, -, hab, -⟩ := id h3
  have : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  obtain ⟨i, hi⟩ := isDictatorial_of_isPareto_of_isIIA hP hI h3
  exact ⟨i, hi, fun j hj => hj.unique hi⟩

/-- With finitely many voters and at least three alternatives, the weakly Pareto social welfare
functions satisfying IIA are exactly the dictatorships. -/
theorem isPareto_and_isIIA_iff [Finite V] (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    F.IsPareto ∧ F.IsIIA ↔ ∃ i, F = dictatorship i := by
  constructor
  · rintro ⟨hP, hI⟩
    obtain ⟨i, hi⟩ := isDictatorial_of_isPareto_of_isIIA hP hI h3
    exact ⟨i, isDictator_iff_eq_dictatorship.1 hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨isPareto_dictatorship i, isIIA_dictatorship i⟩

end SocialWelfareFunction

end Cslib.GameTheory.SocialChoice
