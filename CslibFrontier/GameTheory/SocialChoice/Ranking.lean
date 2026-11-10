/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
import Mathlib.Order.Extension.Linear

/-!
# Rankings of alternatives

The preference model of social choice. A voter's preference is a `Ranking A`, a strict linear
order on the alternatives `A`. A social ranking is a `WeakRanking A`, a complete preorder, so
society may be indifferent. A `Profile V A` assigns a ranking to every voter. Arrow's theorem
(`CslibFrontier.GameTheory.SocialChoice.Arrow`) and the Gibbard–Satterthwaite theorem
(`CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaite`) are stated on this model.

**Representation.** Rankings are bundled structures holding one relation, not instances of
Mathlib's `LinearOrder`. A profile assigns different orders on the same type `A` to different
voters, and the proofs build new rankings pointwise (`Ranking.toTop`, `Ranking.toBottom`,
`Ranking.toTopSet`, `Ranking.extend`). Typeclass-carried orders, which also hold decidability
and `min`/`max` data, would make both awkward. Bridge instances
(`IsStrictTotalOrder A r.Prefers`, `IsPreorder A R.AtLeast`, `Std.Total R.AtLeast`) give access
to Mathlib's unbundled order API.

## Main definitions

* `Ranking`: a strict linear order on the alternatives. `Ranking.reverse` reverses it,
  `Ranking.toTop` and `Ranking.toBottom` move one alternative to the top or the bottom, and
  `Ranking.toTopSet` moves a set of alternatives to the top ([Nisan2007], Definition 9.9).
* `Ranking.IsTop`, `Ranking.IsBottom`: an alternative is at the top or the bottom.
  `Ranking.top` is the top alternative of a ranking of a finite nonempty type.
* `Ranking.restrict`, `Ranking.extend`: restrict a ranking to a set of alternatives, and extend a
  ranking of a set to all alternatives by ranking the set above its complement.
* `WeakRanking`: a complete preorder, with strict part `WeakRanking.Prefers`.
  `Ranking.toWeakRanking` views a ranking as a weak ranking with no ties.
* `Profile V A`: one ranking for each voter.

## Main results

* `Ranking.nonempty`: every type carries a ranking, by the Szpilrajn extension theorem.
* `Ranking.isTop_iff_eq_top`: the top alternative is unique.

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory.SocialChoice

/-- A **ranking** of the alternatives `A`: a strict linear order, read `r.Prefers a b` as
"`a` is ranked above `b`". -/
@[ext] structure Ranking (A : Type*) where
  /-- `Prefers a b`: the alternative `a` is ranked strictly above `b`. -/
  Prefers : A → A → Prop
  irrefl : ∀ a, ¬ Prefers a a
  trans : ∀ a b c, Prefers a b → Prefers b c → Prefers a c
  total : ∀ a b, a ≠ b → Prefers a b ∨ Prefers b a

/-- A **weak ranking** of the alternatives `A`: a complete preorder, read `R.AtLeast a b` as
"`a` is ranked at least as high as `b`". Ties are allowed. -/
@[ext] structure WeakRanking (A : Type*) where
  /-- `AtLeast a b`: the alternative `a` is ranked at least as high as `b`. -/
  AtLeast : A → A → Prop
  total : ∀ a b, AtLeast a b ∨ AtLeast b a
  trans : ∀ a b c, AtLeast a b → AtLeast b c → AtLeast a c

variable {A : Type*}

namespace Ranking

variable (r : Ranking A)

theorem asymm {a b : A} (h : r.Prefers a b) : ¬ r.Prefers b a :=
  fun h' => r.irrefl a (r.trans a b a h h')

theorem ne_of_prefers {a b : A} (h : r.Prefers a b) : a ≠ b := by
  rintro rfl
  exact r.irrefl a h

theorem prefers_of_not_prefers {a b : A} (hab : a ≠ b) (h : ¬ r.Prefers a b) : r.Prefers b a :=
  (r.total a b hab).resolve_left h

theorem not_prefers_iff {a b : A} (hab : a ≠ b) : ¬ r.Prefers a b ↔ r.Prefers b a :=
  ⟨r.prefers_of_not_prefers hab, r.asymm⟩

instance isStrictTotalOrder (r : Ranking A) : IsStrictTotalOrder A r.Prefers where
  irrefl := r.irrefl
  trans := r.trans
  trichotomous a b hab hba := by
    by_contra h
    exact (r.total a b h).elim hab hba

/-- The reverse ranking. -/
def reverse : Ranking A where
  Prefers a b := r.Prefers b a
  irrefl := r.irrefl
  trans _ _ _ hab hbc := r.trans _ _ _ hbc hab
  total a b h := (r.total a b h).symm

@[simp] theorem reverse_prefers {a b : A} : r.reverse.Prefers a b ↔ r.Prefers b a := Iff.rfl

/-- Move `b` to the top of `r`, keeping the order of the other alternatives. -/
def toTop (b : A) : Ranking A where
  Prefers x y := x ≠ y ∧ (x = b ∨ (y ≠ b ∧ r.Prefers x y))
  irrefl x h := h.1 rfl
  trans x y z := by
    rintro ⟨hxy, hx | ⟨hy, h1⟩⟩ ⟨hyz, hy' | ⟨hz, h2⟩⟩
    · exact absurd (hx.trans hy'.symm) hxy
    · exact ⟨by rintro rfl; exact hz hx, Or.inl hx⟩
    · exact absurd hy' hy
    · exact ⟨r.ne_of_prefers (r.trans _ _ _ h1 h2), Or.inr ⟨hz, r.trans _ _ _ h1 h2⟩⟩
  total x y hxy := by
    by_cases hx : x = b
    · exact Or.inl ⟨hxy, Or.inl hx⟩
    by_cases hy : y = b
    · exact Or.inr ⟨hxy.symm, Or.inl hy⟩
    rcases r.total x y hxy with h | h
    · exact Or.inl ⟨hxy, Or.inr ⟨hy, h⟩⟩
    · exact Or.inr ⟨hxy.symm, Or.inr ⟨hx, h⟩⟩

/-- Move `b` to the bottom of `r`, keeping the order of the other alternatives. -/
def toBottom (b : A) : Ranking A := (r.reverse.toTop b).reverse

/-- `b` is ranked above every other alternative. -/
@[expose] def IsTop (b : A) : Prop := ∀ x, x ≠ b → r.Prefers b x

/-- `b` is ranked below every other alternative. -/
@[expose] def IsBottom (b : A) : Prop := ∀ x, x ≠ b → r.Prefers x b

theorem toTop_prefers_of_ne {b x y : A} (hx : x ≠ b) (hy : y ≠ b) :
    (r.toTop b).Prefers x y ↔ r.Prefers x y := by
  constructor
  · rintro ⟨-, h | ⟨-, h⟩⟩
    · exact absurd h hx
    · exact h
  · intro h
    exact ⟨r.ne_of_prefers h, Or.inr ⟨hy, h⟩⟩

theorem toBottom_prefers_of_ne {b x y : A} (hx : x ≠ b) (hy : y ≠ b) :
    (r.toBottom b).Prefers x y ↔ r.Prefers x y :=
  r.reverse.toTop_prefers_of_ne hy hx

theorem isTop_toTop (b : A) : (r.toTop b).IsTop b :=
  fun _ hx => ⟨hx.symm, Or.inl rfl⟩

theorem isBottom_toBottom (b : A) : (r.toBottom b).IsBottom b :=
  r.reverse.isTop_toTop b

/-- If `b` is at the top of two rankings, they agree on every comparison involving `b`. -/
theorem prefers_iff_of_isTop {s : Ranking A} {b x y : A} (hr : r.IsTop b) (hs : s.IsTop b)
    (hxy : x = b ∨ y = b) : r.Prefers x y ↔ s.Prefers x y := by
  rcases hxy with rfl | rfl
  · by_cases hy : y = x
    · subst hy; exact iff_of_false (r.irrefl _) (s.irrefl _)
    · exact iff_of_true (hr y hy) (hs y hy)
  · by_cases hx : x = y
    · subst hx; exact iff_of_false (r.irrefl _) (s.irrefl _)
    · exact iff_of_false (r.asymm (hr x hx)) (s.asymm (hs x hx))

/-- If `b` is at the bottom of two rankings, they agree on every comparison involving `b`. -/
theorem prefers_iff_of_isBottom {s : Ranking A} {b x y : A} (hr : r.IsBottom b)
    (hs : s.IsBottom b) (hxy : x = b ∨ y = b) : r.Prefers x y ↔ s.Prefers x y :=
  r.reverse.prefers_iff_of_isTop (s := s.reverse) hr hs hxy.symm

/-- Every type carries a ranking, by the Szpilrajn extension theorem
(`extend_partialOrder`). -/
theorem nonempty (A : Type*) : Nonempty (Ranking A) := by
  have : IsPartialOrder A (· = ·) :=
    { refl := fun _ => rfl, trans := fun _ _ _ => Eq.trans, antisymm := fun _ _ h _ => h }
  obtain ⟨s, hs, -⟩ := extend_partialOrder (α := A) (· = ·)
  exact ⟨{ Prefers := fun a b => s a b ∧ a ≠ b
           irrefl := fun a h => h.2 rfl
           trans := fun a b c hab hbc => ⟨hs.trans _ _ _ hab.1 hbc.1, fun hac => by
             subst hac; exact hab.2 (hs.antisymm _ _ hab.1 hbc.1)⟩
           total := fun a b hab => (hs.total a b).imp (⟨·, hab⟩) (⟨·, hab.symm⟩) }⟩

instance (A : Type*) : Nonempty (Ranking A) := Ranking.nonempty A

/-- Two alternatives at the top of the same ranking coincide. -/
theorem IsTop.unique {r : Ranking A} {a b : A} (ha : r.IsTop a) (hb : r.IsTop b) : a = b := by
  by_contra hab
  exact r.asymm (ha b (Ne.symm hab)) (hb a hab)

/-- The **top** alternative of a ranking of a finite nonempty type. -/
noncomputable def top [Finite A] [Nonempty A] : A :=
  (Finite.wellFounded_of_trans_of_irrefl r.Prefers).min Set.univ Set.univ_nonempty

theorem isTop_top [Finite A] [Nonempty A] : r.IsTop r.top := by
  intro x hx
  have hwf := Finite.wellFounded_of_trans_of_irrefl r.Prefers
  refine r.prefers_of_not_prefers hx fun h => ?_
  exact hwf.not_lt_min Set.univ (Set.mem_univ x) h

theorem isTop_iff_eq_top [Finite A] [Nonempty A] {a : A} : r.IsTop a ↔ a = r.top :=
  ⟨fun h => h.unique r.isTop_top, fun h => h ▸ r.isTop_top⟩

/-- Move the alternatives of `S` to the top of `r`, keeping the order within `S` and within its
complement ([Nisan2007], Definition 9.9). -/
def toTopSet (S : Set A) : Ranking A where
  Prefers x y := (x ∈ S ∧ y ∉ S) ∨ ((x ∈ S ↔ y ∈ S) ∧ r.Prefers x y)
  irrefl x h := h.elim (fun h => h.2 h.1) fun h => r.irrefl x h.2
  trans x y z := by
    rintro (⟨hx, hy⟩ | ⟨hxy, h1⟩) (⟨hy', hz⟩ | ⟨hyz, h2⟩)
    · exact absurd hy' hy
    · exact Or.inl ⟨hx, fun hz => hy (hyz.2 hz)⟩
    · exact Or.inl ⟨hxy.2 hy', hz⟩
    · exact Or.inr ⟨hxy.trans hyz, r.trans _ _ _ h1 h2⟩
  total x y hxy := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact (r.total x y hxy).imp (fun h => Or.inr ⟨iff_of_true hx hy, h⟩)
        fun h => Or.inr ⟨iff_of_true hy hx, h⟩
    · exact Or.inl (Or.inl ⟨hx, hy⟩)
    · exact Or.inr (Or.inl ⟨hy, hx⟩)
    · exact (r.total x y hxy).imp (fun h => Or.inr ⟨iff_of_false hx hy, h⟩)
        fun h => Or.inr ⟨iff_of_false hy hx, h⟩

theorem toTopSet_prefers_of_mem_of_notMem {S : Set A} {x y : A} (hx : x ∈ S) (hy : y ∉ S) :
    (r.toTopSet S).Prefers x y :=
  Or.inl ⟨hx, hy⟩

theorem toTopSet_prefers_iff_of_mem {S : Set A} {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    (r.toTopSet S).Prefers x y ↔ r.Prefers x y :=
  ⟨fun h => h.elim (fun h => absurd hy h.2) And.right,
    fun h => Or.inr ⟨iff_of_true hx hy, h⟩⟩

/-- If `x ∈ S`, `toTopSet S` ranks `x` above `y` exactly when `y ∉ S` or `r` ranks `x` above
`y`. -/
theorem toTopSet_prefers_of_mem {S : Set A} {x y : A} (hx : x ∈ S) :
    (r.toTopSet S).Prefers x y ↔ y ∉ S ∨ r.Prefers x y := by
  by_cases hy : y ∈ S
  · rw [r.toTopSet_prefers_iff_of_mem hx hy]
    exact ⟨Or.inr, fun h => h.resolve_left (not_not.2 hy)⟩
  · exact iff_of_true (r.toTopSet_prefers_of_mem_of_notMem hx hy) (Or.inl hy)

/-- Extend a ranking `s` of the alternatives in `S` to all alternatives, ranking `S` above its
complement, which is ordered by `r`. -/
def extend {S : Set A} (s : Ranking S) : Ranking A where
  Prefers x y :=
    (∃ (hx : x ∈ S) (hy : y ∈ S), s.Prefers ⟨x, hx⟩ ⟨y, hy⟩) ∨ (x ∈ S ∧ y ∉ S) ∨
      (x ∉ S ∧ y ∉ S ∧ r.Prefers x y)
  irrefl x := by
    rintro (⟨hx, hx₂, h⟩ | ⟨hx, hx'⟩ | ⟨-, -, h⟩)
    · exact s.irrefl _ h
    · exact hx' hx
    · exact r.irrefl x h
  trans x y z := by
    rintro (⟨hx, hy, h1⟩ | ⟨hx, hy⟩ | ⟨hx, hy, h1⟩) (⟨hy', hz, h2⟩ | ⟨hy', hz⟩ | ⟨hy', hz, h2⟩)
    · exact Or.inl ⟨hx, hz, s.trans _ _ _ h1 h2⟩
    · exact Or.inr (Or.inl ⟨hx, hz⟩)
    · exact absurd hy hy'
    · exact absurd hy' hy
    · exact absurd hy' hy
    · exact Or.inr (Or.inl ⟨hx, hz⟩)
    · exact absurd hy' hy
    · exact absurd hy' hy
    · exact Or.inr (Or.inr ⟨hx, hz, r.trans _ _ _ h1 h2⟩)
  total x y hxy := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · have hne : (⟨x, hx⟩ : S) ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
      exact (s.total _ _ hne).imp (fun h => Or.inl ⟨hx, hy, h⟩) fun h => Or.inl ⟨hy, hx, h⟩
    · exact Or.inl (Or.inr (Or.inl ⟨hx, hy⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
    · exact (r.total x y hxy).imp (fun h => Or.inr (Or.inr ⟨hx, hy, h⟩))
        fun h => Or.inr (Or.inr ⟨hy, hx, h⟩)

/-- On alternatives of `S`, the extension of `s` agrees with `s`. -/
theorem extend_prefers_of_mem {S : Set A} (s : Ranking S) {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    (r.extend s).Prefers x y ↔ s.Prefers ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · rintro (⟨hx₂, hy₂, h⟩ | ⟨-, hy'⟩ | ⟨hx', -⟩)
    · exact h
    · exact absurd hy hy'
    · exact absurd hx hx'
  · exact fun h => Or.inl ⟨hx, hy, h⟩

/-- The restriction of a ranking to the alternatives in `S`. -/
def restrict (S : Set A) : Ranking S where
  Prefers x y := r.Prefers x y
  irrefl x := r.irrefl x
  trans x y z := r.trans x y z
  total x y hxy := r.total x y fun h => hxy (Subtype.ext h)

@[simp] theorem restrict_prefers {S : Set A} {x y : S} :
    (r.restrict S).Prefers x y ↔ r.Prefers x y := Iff.rfl

/-- `toTopSet S` ranks `x` above `y` when `x ∈ S` and `y ∉ S`, or when `x` and `y` are on the same
side of `S` and `r` ranks `x` above `y`. -/
theorem toTopSet_prefers_iff {S : Set A} {x y : A} :
    (r.toTopSet S).Prefers x y ↔ (x ∈ S ∧ y ∉ S) ∨ ((x ∈ S ↔ y ∈ S) ∧ r.Prefers x y) :=
  Iff.rfl

/-- If `x ∉ S`, `toTopSet S` ranks `x` above `y` exactly when `y ∉ S` and `r` ranks `x` above
`y`. -/
theorem toTopSet_prefers_of_notMem {S : Set A} {x y : A} (hx : x ∉ S) :
    (r.toTopSet S).Prefers x y ↔ y ∉ S ∧ r.Prefers x y := by
  rw [toTopSet_prefers_iff]
  constructor
  · rintro (⟨hx', -⟩ | ⟨hxy, h⟩)
    · exact absurd hx' hx
    · exact ⟨fun hy => hx (hxy.2 hy), h⟩
  · exact fun ⟨hy, h⟩ => Or.inr ⟨iff_of_false hx hy, h⟩

/-- `r.extend s` ranks `x` above `y` when both lie in `S` and `s` ranks `x` above `y`, when
`x ∈ S` and `y ∉ S`, or when neither lies in `S` and `r` ranks `x` above `y`. -/
theorem extend_prefers_iff {S : Set A} (s : Ranking S) {x y : A} :
    (r.extend s).Prefers x y ↔
      (∃ (hx : x ∈ S) (hy : y ∈ S), s.Prefers ⟨x, hx⟩ ⟨y, hy⟩) ∨ (x ∈ S ∧ y ∉ S) ∨
        (x ∉ S ∧ y ∉ S ∧ r.Prefers x y) :=
  Iff.rfl

/-- The extension of a ranking of `S` ranks the alternatives of `S` above the others. -/
theorem extend_prefers_of_mem_of_notMem {S : Set A} (s : Ranking S) {x y : A} (hx : x ∈ S)
    (hy : y ∉ S) : (r.extend s).Prefers x y :=
  Or.inr (Or.inl ⟨hx, hy⟩)

/-- Off `S`, the extension of a ranking of `S` agrees with `r`. -/
theorem extend_prefers_of_notMem {S : Set A} (s : Ranking S) {x y : A} (hx : x ∉ S)
    (hy : y ∉ S) : (r.extend s).Prefers x y ↔ r.Prefers x y := by
  rw [extend_prefers_iff]
  constructor
  · rintro (⟨hx', -, -⟩ | ⟨hx', -⟩ | ⟨-, -, h⟩)
    · exact absurd hx' hx
    · exact absurd hx' hx
    · exact h
  · exact fun h => Or.inr (Or.inr ⟨hx, hy, h⟩)

/-- Two rankings that agree on whether `a` is above `b` also agree on whether `b` is above
`a`. -/
theorem prefers_iff_swap {s t : Ranking A} {a b : A} (h : s.Prefers a b ↔ t.Prefers a b) :
    s.Prefers b a ↔ t.Prefers b a := by
  by_cases hab : a = b
  · subst hab; exact h
  · rw [← s.not_prefers_iff hab, ← t.not_prefers_iff hab, h]

end Ranking

namespace WeakRanking

variable (R : WeakRanking A)

/-- The strict part of a weak ranking: `a` is ranked strictly above `b`. -/
@[expose] def Prefers (a b : A) : Prop := ¬ R.AtLeast b a

theorem refl (a : A) : R.AtLeast a a := (R.total a a).elim id id

instance isPreorder (R : WeakRanking A) : IsPreorder A R.AtLeast where
  refl := R.refl
  trans := R.trans

instance instTotal (R : WeakRanking A) : Std.Total R.AtLeast := ⟨R.total⟩

theorem atLeast_of_prefers {a b : A} (h : R.Prefers a b) : R.AtLeast a b :=
  (R.total a b).resolve_right h

theorem prefers_irrefl (a : A) : ¬ R.Prefers a a := fun h => h (R.refl a)

theorem prefers_asymm {a b : A} (h : R.Prefers a b) : ¬ R.Prefers b a :=
  fun h' => h' (R.atLeast_of_prefers h)

theorem prefers_trans {a b c : A} (hab : R.Prefers a b) (hbc : R.Prefers b c) :
    R.Prefers a c :=
  fun hca => hbc (R.trans _ _ _ hca (R.atLeast_of_prefers hab))

/-- `b` is ranked strictly above every other alternative. -/
@[expose] def IsTop (b : A) : Prop := ∀ x, x ≠ b → R.Prefers b x

/-- `b` is ranked strictly below every other alternative. -/
@[expose] def IsBottom (b : A) : Prop := ∀ x, x ≠ b → R.Prefers x b

end WeakRanking

/-- A ranking, viewed as a weak ranking with no ties. -/
@[expose] def Ranking.toWeakRanking (r : Ranking A) : WeakRanking A where
  AtLeast a b := a = b ∨ r.Prefers a b
  total a b := by
    by_cases h : a = b
    · exact Or.inl (Or.inl h)
    · exact (r.total a b h).imp Or.inr Or.inr
  trans a b c := by
    rintro (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · exact Or.inr (r.trans _ _ _ hab hbc)

@[simp] theorem Ranking.toWeakRanking_atLeast (r : Ranking A) {a b : A} :
    r.toWeakRanking.AtLeast a b ↔ a = b ∨ r.Prefers a b := Iff.rfl

@[simp] theorem Ranking.toWeakRanking_prefers (r : Ranking A) {a b : A} :
    r.toWeakRanking.Prefers a b ↔ r.Prefers a b := by
  constructor
  · intro h
    have hab : a ≠ b := fun hab => h (Or.inl hab.symm)
    exact (r.not_prefers_iff hab.symm).1 fun h' => h (Or.inr h')
  · rintro h (hba | hba)
    · exact r.ne_of_prefers h hba.symm
    · exact r.asymm h hba

/-- A **preference profile**: one ranking for each voter. -/
abbrev Profile (V A : Type*) := V → Ranking A

end Cslib.GameTheory.SocialChoice
