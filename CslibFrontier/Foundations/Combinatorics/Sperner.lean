/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-!
# Sperner's lemma on the triangulated square grid

Cutting each unit cell of the `W × H` integer grid along its main diagonal triangulates it by the
`GridTriangle`s of `triangles W H`. A colouring `c : ℕ × ℕ → Fin 3` of the grid points of the
`N × N` grid is a *Sperner colouring* (`IsSpernerColoring`) when it agrees on the boundary with the
boundary colouring `boundaryColor` of Chen, Deng and Teng [ChenDengTeng2009] (Section 4.1, the
valid colourings of Theorem 4.1 and Definition 4.4 with `d = 2`, colour `3` written `0`): colour
`2` on the bottom edge, colour `1` on the rest of the left edge and colour `0` on the rest of the
boundary. Sperner's lemma says that such a colouring has a trichromatic triangle; here it is proved
in its parity form, by the path-following argument that underlies `PPAD` [Papadimitriou1994PPAD].
(Mathlib's `IsAntichain.sperner` is Sperner's theorem on antichains, an unrelated result.)

An edge of a triangle whose endpoints are coloured `1` and `2` is a *door*; traversing the corners
counterclockwise, it is an *exit* (`2` then `1`, `IsExit`) or an *entry* (`1` then `2`, `IsEntry`).
A triangle has at most one exit and at most one entry, it is trichromatic exactly when it has
exactly one door (`trichromatic_iff_isSink_or_isSource`), and crossing an interior door turns an
exit into an entry (`gluing`, `isEntry_across`). Crossing interior exits (`next`) and interior
entries (`prev`) therefore defines a directed graph of in- and out-degree at most one, and counting
doors gives, for every colouring of every `W × H` grid, the index theorem
`#sinks + #boundary exits = #sources + #boundary entries`
(`card_isSink_add_card_hasBoundaryExit`). A Sperner colouring has no boundary exit and exactly one
boundary entry, the left edge of `start`, so it has one more sink than sources and an odd number of
trichromatic triangles.

The last section identifies the door graph of a Sperner colouring as an end-of-line graph whose
distinguished source is `start` and whose other unbalanced vertices are exactly the trichromatic
triangles (`IsSpernerColoring.door_out_iff`, `IsSpernerColoring.door_in_iff`,
`IsSpernerColoring.trichromatic_iff`). The circuit-presented search problem built on it is
`Cslib.Complexity.Sperner2D`.

## Main definitions

* `Cslib.Sperner.GridTriangle`, `Cslib.Sperner.triangles`: the triangles of the triangulated grid,
  with corners `GridTriangle.corner` and neighbours `GridTriangle.across`.
* `Cslib.Sperner.IsExit`, `Cslib.Sperner.IsEntry`, `Cslib.Sperner.Trichromatic`: doors and
  trichromatic triangles of a colouring.
* `Cslib.Sperner.next`, `Cslib.Sperner.prev`: the door graph.
* `Cslib.Sperner.IsSink`, `Cslib.Sperner.IsSource`: its unbalanced vertices.
* `Cslib.Sperner.boundaryColor`, `Cslib.Sperner.IsSpernerColoring`, `Cslib.Sperner.start`.

## Main results

* `Cslib.Sperner.card_isSink_add_card_hasBoundaryExit`: the index theorem for an arbitrary
  colouring of an arbitrary grid.
* `Cslib.Sperner.IsSpernerColoring.card_isSink`: a Sperner colouring has one more sink than
  sources.
* `Cslib.Sperner.IsSpernerColoring.odd_card_trichromatic`: **Sperner's lemma**, parity form.
* `Cslib.Sperner.IsSpernerColoring.exists_trichromatic`: **Sperner's lemma**.
* `Cslib.Sperner.IsSpernerColoring.trichromatic_iff`: the trichromatic triangles are the unbalanced
  vertices of the door graph other than `start`, together with `start` when it is a sink.

## References

* [X. Chen, X. Deng and S.-H. Teng, *Settling the complexity of computing two-player Nash
  equilibria*][ChenDengTeng2009]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
-/

@[expose] public section

namespace Cslib.Sperner

/-- A triangle of the standard triangulation of the integer grid. -/
structure GridTriangle where
  /-- `true` for the lower triangle `(x, y), (x + 1, y), (x + 1, y + 1)` of the cell, `false` for
  the upper triangle `(x, y), (x + 1, y + 1), (x, y + 1)`. -/
  lower : Bool
  /-- The `x`-coordinate of the lower-left corner of the cell. -/
  x : ℕ
  /-- The `y`-coordinate of the lower-left corner of the cell. -/
  y : ℕ
  deriving DecidableEq

namespace GridTriangle

/-- The corners of a grid triangle, in counterclockwise order. -/
def corner : GridTriangle → Fin 3 → ℕ × ℕ
  | ⟨false, x, y⟩, 0 => (x, y)
  | ⟨false, x, y⟩, 1 => (x + 1, y + 1)
  | ⟨false, x, y⟩, 2 => (x, y + 1)
  | ⟨true, x, y⟩, 0 => (x, y)
  | ⟨true, x, y⟩, 1 => (x + 1, y)
  | ⟨true, x, y⟩, 2 => (x + 1, y + 1)

/-- The triangle on the other side of edge `k`, from `corner t k` to `corner t (k + 1)`. -/
def across : GridTriangle → Fin 3 → GridTriangle
  | ⟨false, x, y⟩, 0 => ⟨true, x, y⟩
  | ⟨false, x, y⟩, 1 => ⟨true, x, y + 1⟩
  | ⟨false, x, y⟩, 2 => ⟨true, x - 1, y⟩
  | ⟨true, x, y⟩, 0 => ⟨false, x, y - 1⟩
  | ⟨true, x, y⟩, 1 => ⟨false, x + 1, y⟩
  | ⟨true, x, y⟩, 2 => ⟨false, x, y⟩

/-- Edge `k` of `t` is an interior edge of the `W × H` grid. -/
def interior (W H : ℕ) : GridTriangle → Fin 3 → Bool
  | ⟨false, _, _⟩, 0 => true
  | ⟨false, _, y⟩, 1 => decide (y + 1 < H)
  | ⟨false, x, _⟩, 2 => decide (0 < x)
  | ⟨true, _, y⟩, 0 => decide (0 < y)
  | ⟨true, x, _⟩, 1 => decide (x + 1 < W)
  | ⟨true, _, _⟩, 2 => true

/-- The index of the shared edge in the neighbouring triangle. -/
def mate : GridTriangle → Fin 3 → Fin 3
  | ⟨false, _, _⟩, k => k + 2
  | ⟨true, _, _⟩, k => k + 1

/-- `t` lies in the `W × H` grid. -/
def InGrid (W H : ℕ) (t : GridTriangle) : Prop := t.x < W ∧ t.y < H

instance (W H : ℕ) (t : GridTriangle) : Decidable (InGrid W H t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Crossing an interior edge `k` of a triangle `t` of the grid leads to a triangle of the grid that
shares the edge, traversed in the opposite direction, as its edge `mate t k`; crossing back returns
to `t`. -/
theorem gluing {W H : ℕ} {t : GridTriangle} {k : Fin 3} (ht : InGrid W H t)
    (hk : interior W H t k = true) :
    InGrid W H (across t k) ∧ interior W H (across t k) (mate t k) = true ∧
      across (across t k) (mate t k) = t ∧
      corner (across t k) (mate t k) = corner t (k + 1) ∧
      corner (across t k) (mate t k + 1) = corner t k := by
  obtain ⟨_ | _, x, y⟩ := t <;> fin_cases k <;>
    simp_all [InGrid, interior, across, mate, corner] <;> omega

/-- Grid triangles are triples `(lower, x, y)`. -/
def equivProd : GridTriangle ≃ Bool × ℕ × ℕ where
  toFun t := (t.lower, t.x, t.y)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GridTriangle

open GridTriangle

/-- The triangles of the `W × H` grid. -/
def triangles (W H : ℕ) : Finset GridTriangle :=
  ((Finset.univ : Finset Bool) ×ˢ (Finset.range W ×ˢ Finset.range H)).map
    equivProd.symm.toEmbedding

@[simp]
theorem mem_triangles {W H : ℕ} {t : GridTriangle} : t ∈ triangles W H ↔ InGrid W H t := by
  simp [triangles, Finset.mem_map_equiv, InGrid, equivProd]

variable (c : ℕ × ℕ → Fin 3)

/-- Edge `k` of `t` is an exit door: its endpoints are coloured `2` then `1`. -/
def IsExit (t : GridTriangle) (k : Fin 3) : Prop := c (t.corner k) = 2 ∧ c (t.corner (k + 1)) = 1

/-- Edge `k` of `t` is an entry door: its endpoints are coloured `1` then `2`. -/
def IsEntry (t : GridTriangle) (k : Fin 3) : Prop := c (t.corner k) = 1 ∧ c (t.corner (k + 1)) = 2

instance (t : GridTriangle) (k : Fin 3) : Decidable (IsExit c t k) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (t : GridTriangle) (k : Fin 3) : Decidable (IsEntry c t k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The corners of `t` carry three distinct colours. -/
def Trichromatic (t : GridTriangle) : Prop := Function.Injective (c ∘ t.corner)

instance (t : GridTriangle) : Decidable (Trichromatic c t) :=
  inferInstanceAs (Decidable (Function.Injective _))

private theorem fin3_exit_unique (f : Fin 3 → Fin 3) (k l : Fin 3)
    (hk : f k = 2 ∧ f (k + 1) = 1) (hl : f l = 2 ∧ f (l + 1) = 1) : k = l := by
  revert f k l
  decide

theorem isExit_unique {t : GridTriangle} {k l : Fin 3} (hk : IsExit c t k) (hl : IsExit c t l) :
    k = l :=
  fin3_exit_unique (c ∘ t.corner) k l hk hl

private theorem fin3_entry_unique (f : Fin 3 → Fin 3) (k l : Fin 3)
    (hk : f k = 1 ∧ f (k + 1) = 2) (hl : f l = 1 ∧ f (l + 1) = 2) : k = l := by
  revert f k l
  decide

theorem isEntry_unique {t : GridTriangle} {k l : Fin 3} (hk : IsEntry c t k)
    (hl : IsEntry c t l) : k = l :=
  fin3_entry_unique (c ∘ t.corner) k l hk hl

/-- An exit door of `t` is an entry door of the neighbouring triangle. -/
theorem isEntry_across {W H : ℕ} {t : GridTriangle} {k : Fin 3} (ht : InGrid W H t)
    (hk : interior W H t k = true) (h : IsExit c t k) :
    IsEntry c (across t k) (mate t k) := by
  obtain ⟨-, -, -, h1, h2⟩ := gluing ht hk
  exact ⟨h1 ▸ h.2, h2 ▸ h.1⟩

/-- An entry door of `t` is an exit door of the neighbouring triangle. -/
theorem isExit_across {W H : ℕ} {t : GridTriangle} {k : Fin 3} (ht : InGrid W H t)
    (hk : interior W H t k = true) (h : IsEntry c t k) :
    IsExit c (across t k) (mate t k) := by
  obtain ⟨-, -, -, h1, h2⟩ := gluing ht hk
  exact ⟨h1 ▸ h.2, h2 ▸ h.1⟩

variable (W H : ℕ)

/-- Follow the interior exit door of `t`, if any; otherwise stay at `t`. -/
def next (t : GridTriangle) : GridTriangle :=
  if IsExit c t 0 ∧ interior W H t 0 = true then across t 0
  else if IsExit c t 1 ∧ interior W H t 1 = true then across t 1
  else if IsExit c t 2 ∧ interior W H t 2 = true then across t 2
  else t

/-- Follow the interior entry door of `t` backwards, if any; otherwise stay at `t`. -/
def prev (t : GridTriangle) : GridTriangle :=
  if IsEntry c t 0 ∧ interior W H t 0 = true then across t 0
  else if IsEntry c t 1 ∧ interior W H t 1 = true then across t 1
  else if IsEntry c t 2 ∧ interior W H t 2 = true then across t 2
  else t

variable {c W H}

theorem next_eq_across {t : GridTriangle} {k : Fin 3} (h : IsExit c t k)
    (hk : interior W H t k = true) : next c W H t = across t k := by
  have hu := fun l (hl : IsExit c t l) => isExit_unique c hl h
  unfold next
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  · rw [ite_eq_left ⟨h, hk⟩]
  · rw [ite_eq_right fun h' => absurd (hu 0 h'.1) (by decide), ite_eq_left ⟨h, hk⟩]
  · rw [ite_eq_right fun h' => absurd (hu 0 h'.1) (by decide),
      ite_eq_right fun h' => absurd (hu 1 h'.1) (by decide), ite_eq_left ⟨h, hk⟩]

theorem next_eq_self {t : GridTriangle} (h : ∀ k, IsExit c t k → interior W H t k = false) :
    next c W H t = t := by
  unfold next
  rw [ite_eq_right fun h' => absurd h'.2 (by rw [h 0 h'.1]; decide),
    ite_eq_right fun h' => absurd h'.2 (by rw [h 1 h'.1]; decide),
    ite_eq_right fun h' => absurd h'.2 (by rw [h 2 h'.1]; decide)]

theorem prev_eq_across {t : GridTriangle} {k : Fin 3} (h : IsEntry c t k)
    (hk : interior W H t k = true) : prev c W H t = across t k := by
  have hu := fun l (hl : IsEntry c t l) => isEntry_unique c hl h
  unfold prev
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  · rw [ite_eq_left ⟨h, hk⟩]
  · rw [ite_eq_right fun h' => absurd (hu 0 h'.1) (by decide), ite_eq_left ⟨h, hk⟩]
  · rw [ite_eq_right fun h' => absurd (hu 0 h'.1) (by decide),
      ite_eq_right fun h' => absurd (hu 1 h'.1) (by decide), ite_eq_left ⟨h, hk⟩]

theorem prev_eq_self {t : GridTriangle} (h : ∀ k, IsEntry c t k → interior W H t k = false) :
    prev c W H t = t := by
  unfold prev
  rw [ite_eq_right fun h' => absurd h'.2 (by rw [h 0 h'.1]; decide),
    ite_eq_right fun h' => absurd h'.2 (by rw [h 1 h'.1]; decide),
    ite_eq_right fun h' => absurd h'.2 (by rw [h 2 h'.1]; decide)]

theorem prev_next {t : GridTriangle} {k : Fin 3} (ht : InGrid W H t) (h : IsExit c t k)
    (hk : interior W H t k = true) : prev c W H (next c W H t) = t := by
  obtain ⟨-, hk', hback, -, -⟩ := gluing ht hk
  rw [next_eq_across h hk, prev_eq_across (isEntry_across c ht hk h) hk', hback]

theorem next_prev {t : GridTriangle} {k : Fin 3} (ht : InGrid W H t) (h : IsEntry c t k)
    (hk : interior W H t k = true) : next c W H (prev c W H t) = t := by
  obtain ⟨-, hk', hback, -, -⟩ := gluing ht hk
  rw [prev_eq_across h hk, next_eq_across (isExit_across c ht hk h) hk', hback]


/-! ### Doors and the index theorem -/

variable (c W H)

/-- `t` has an exit door. -/
def HasExit (t : GridTriangle) : Prop := ∃ k, IsExit c t k

/-- `t` has an entry door. -/
def HasEntry (t : GridTriangle) : Prop := ∃ k, IsEntry c t k

/-- `t` has an exit door that is an interior edge of the `W × H` grid. -/
def HasInteriorExit (t : GridTriangle) : Prop := ∃ k, IsExit c t k ∧ interior W H t k = true

/-- `t` has an exit door on the boundary of the `W × H` grid. -/
def HasBoundaryExit (t : GridTriangle) : Prop := ∃ k, IsExit c t k ∧ interior W H t k = false

/-- `t` has an entry door that is an interior edge of the `W × H` grid. -/
def HasInteriorEntry (t : GridTriangle) : Prop := ∃ k, IsEntry c t k ∧ interior W H t k = true

/-- `t` has an entry door on the boundary of the `W × H` grid. -/
def HasBoundaryEntry (t : GridTriangle) : Prop :=
  ∃ k, IsEntry c t k ∧ interior W H t k = false

/-- A *sink* of the door graph: an entry door but no exit door. -/
def IsSink (t : GridTriangle) : Prop := HasEntry c t ∧ ¬HasExit c t

/-- A *source* of the door graph: an exit door but no entry door. -/
def IsSource (t : GridTriangle) : Prop := HasExit c t ∧ ¬HasEntry c t

instance (t : GridTriangle) : Decidable (HasExit c t) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : GridTriangle) : Decidable (HasEntry c t) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : GridTriangle) : Decidable (HasInteriorExit c W H t) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : GridTriangle) : Decidable (HasBoundaryExit c W H t) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : GridTriangle) : Decidable (HasInteriorEntry c W H t) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : GridTriangle) : Decidable (HasBoundaryEntry c W H t) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : GridTriangle) : Decidable (IsSink c t) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (t : GridTriangle) : Decidable (IsSource c t) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {c W H}

private theorem fin3_injective_iff (f : Fin 3 → Fin 3) :
    Function.Injective f ↔
      ((∃ k, f k = 1 ∧ f (k + 1) = 2) ∧ ¬∃ k, f k = 2 ∧ f (k + 1) = 1) ∨
        ((∃ k, f k = 2 ∧ f (k + 1) = 1) ∧ ¬∃ k, f k = 1 ∧ f (k + 1) = 2) := by
  revert f
  decide

/-- A triangle is trichromatic exactly when it is a sink or a source of the door graph. -/
theorem trichromatic_iff_isSink_or_isSource {t : GridTriangle} :
    Trichromatic c t ↔ IsSink c t ∨ IsSource c t :=
  fin3_injective_iff (c ∘ t.corner)

theorem hasExit_iff {t : GridTriangle} :
    HasExit c t ↔ HasInteriorExit c W H t ∨ HasBoundaryExit c W H t := by
  constructor
  · rintro ⟨k, hk⟩
    cases h : interior W H t k
    · exact .inr ⟨k, hk, h⟩
    · exact .inl ⟨k, hk, h⟩
  · rintro (⟨k, hk, -⟩ | ⟨k, hk, -⟩) <;> exact ⟨k, hk⟩

theorem hasEntry_iff {t : GridTriangle} :
    HasEntry c t ↔ HasInteriorEntry c W H t ∨ HasBoundaryEntry c W H t := by
  constructor
  · rintro ⟨k, hk⟩
    cases h : interior W H t k
    · exact .inr ⟨k, hk, h⟩
    · exact .inl ⟨k, hk, h⟩
  · rintro (⟨k, hk, -⟩ | ⟨k, hk, -⟩) <;> exact ⟨k, hk⟩

theorem not_hasInteriorExit_and_hasBoundaryExit {t : GridTriangle} :
    ¬(HasInteriorExit c W H t ∧ HasBoundaryExit c W H t) := by
  rintro ⟨⟨k, hk, hi⟩, ⟨l, hl, hb⟩⟩
  obtain rfl := isExit_unique c hk hl
  simp_all

theorem not_hasInteriorEntry_and_hasBoundaryEntry {t : GridTriangle} :
    ¬(HasInteriorEntry c W H t ∧ HasBoundaryEntry c W H t) := by
  rintro ⟨⟨k, hk, hi⟩, ⟨l, hl, hb⟩⟩
  obtain rfl := isEntry_unique c hk hl
  simp_all

private theorem card_filter_of_iff_or {α : Type*} (s : Finset α)
    {p q r : α → Prop} [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hr : ∀ a, r a ↔ p a ∨ q a) (h : ∀ a, ¬(p a ∧ q a)) :
    (s.filter r).card = (s.filter p).card + (s.filter q).card := by
  classical
  rw [Finset.filter_congr fun a _ => hr a, Finset.filter_or, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter.mpr fun a _ hp hq => h a ⟨hp, hq⟩

/-- Interior exit doors and interior entry doors are matched by crossing the door. -/
theorem card_hasInteriorExit_eq :
    ((triangles W H).filter (HasInteriorExit c W H)).card =
      ((triangles W H).filter (HasInteriorEntry c W H)).card := by
  refine Finset.card_nbij' (next c W H) (prev c W H) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, mem_triangles, Set.mem_ofPred_eq] at ht ⊢
    obtain ⟨hg, k, hk, hi⟩ := ht
    obtain ⟨hg', hi', -, -, -⟩ := gluing hg hi
    rw [next_eq_across hk hi]
    exact ⟨hg', _, isEntry_across c hg hi hk, hi'⟩
  · intro t ht
    simp only [Finset.coe_filter, mem_triangles, Set.mem_ofPred_eq] at ht ⊢
    obtain ⟨hg, k, hk, hi⟩ := ht
    obtain ⟨hg', hi', -, -, -⟩ := gluing hg hi
    rw [prev_eq_across hk hi]
    exact ⟨hg', _, isExit_across c hg hi hk, hi'⟩
  · intro t ht
    simp only [Finset.coe_filter, mem_triangles, Set.mem_ofPred_eq] at ht
    obtain ⟨hg, k, hk, hi⟩ := ht
    exact prev_next hg hk hi
  · intro t ht
    simp only [Finset.coe_filter, mem_triangles, Set.mem_ofPred_eq] at ht
    obtain ⟨hg, k, hk, hi⟩ := ht
    exact next_prev hg hk hi

/-- **Index theorem for the door graph.** In every colouring of the `W × H` grid, the number of
sinks plus the number of boundary exit doors equals the number of sources plus the number of
boundary entry doors. -/
theorem card_isSink_add_card_hasBoundaryExit :
    ((triangles W H).filter (IsSink c)).card +
        ((triangles W H).filter (HasBoundaryExit c W H)).card =
      ((triangles W H).filter (IsSource c)).card +
        ((triangles W H).filter (HasBoundaryEntry c W H)).card := by
  have hex := card_filter_of_iff_or (triangles W H)
    (fun t => hasExit_iff (c := c) (W := W) (H := H) (t := t))
    fun t => not_hasInteriorExit_and_hasBoundaryExit
  have hen := card_filter_of_iff_or (triangles W H)
    (fun t => hasEntry_iff (c := c) (W := W) (H := H) (t := t))
    fun t => not_hasInteriorEntry_and_hasBoundaryEntry
  have hsink := card_filter_of_iff_or (triangles W H)
    (r := fun t => IsSink c t ∨ HasExit c t) (fun _ => Iff.rfl) fun t h => h.1.2 h.2
  have hsrc := card_filter_of_iff_or (triangles W H)
    (r := fun t => IsSource c t ∨ HasEntry c t) (fun _ => Iff.rfl) fun t h => h.1.2 h.2
  have hsame : (triangles W H).filter (fun t => IsSink c t ∨ HasExit c t) =
      (triangles W H).filter (fun t => IsSource c t ∨ HasEntry c t) := by
    refine Finset.filter_congr fun t _ => ?_
    unfold IsSink IsSource
    tauto
  have := card_hasInteriorExit_eq (c := c) (W := W) (H := H)
  rw [hsame] at hsink
  omega

/-! ### Sperner colourings of the square grid -/

/-- The boundary colouring of the `N × N` grid (Chen, Deng and Teng, Definition 4.4, `d = 2`, with
their colour `3` written `0`): the bottom edge `y = 0` has colour `2`, the rest of the left edge
`x = 0` has colour `1`, and the rest of the boundary has colour `0`. -/
def boundaryColor (p : ℕ × ℕ) : Fin 3 :=
  if p.2 = 0 then 2 else if p.1 = 0 then 1 else 0

/-- A colouring of the `N × N` grid is a *Sperner colouring* if it agrees with `boundaryColor` on
the boundary. -/
def IsSpernerColoring (N : ℕ) (c : ℕ × ℕ → Fin 3) : Prop :=
  ∀ x y, x ≤ N → y ≤ N → (x = 0 ∨ y = 0 ∨ x = N ∨ y = N) → c (x, y) = boundaryColor (x, y)

/-- The triangle whose left edge is the unique boundary door of a Sperner colouring. -/
def start : GridTriangle := ⟨false, 0, 0⟩

variable {N : ℕ}

private theorem boundary_corners {t : GridTriangle} {k : Fin 3} (ht : InGrid N N t)
    (hk : interior N N t k = false) :
    ((t.corner k).1 ≤ N ∧ (t.corner k).2 ≤ N ∧ ((t.corner k).1 = 0 ∨ (t.corner k).2 = 0 ∨
        (t.corner k).1 = N ∨ (t.corner k).2 = N)) ∧
      ((t.corner (k + 1)).1 ≤ N ∧ (t.corner (k + 1)).2 ≤ N ∧ ((t.corner (k + 1)).1 = 0 ∨
        (t.corner (k + 1)).2 = 0 ∨ (t.corner (k + 1)).1 = N ∨ (t.corner (k + 1)).2 = N)) := by
  obtain ⟨_ | _, x, y⟩ := t
  all_goals
    obtain ⟨hx, hy⟩ := ht
    fin_cases k <;> simp_all only [interior, corner] <;> simp at hk ⊢ <;> omega

private theorem boundary_door {t : GridTriangle} {k : Fin 3} (ht : InGrid N N t)
    (hk : interior N N t k = false) :
    (boundaryColor (t.corner k) = 2 ∧ boundaryColor (t.corner (k + 1)) = 1 → False) ∧
      (boundaryColor (t.corner k) = 1 ∧ boundaryColor (t.corner (k + 1)) = 2 → t = start) := by
  obtain ⟨_ | _, x, y⟩ := t <;> fin_cases k <;>
    simp_all [InGrid, interior, corner, boundaryColor, start]

theorem IsSpernerColoring.not_hasBoundaryExit (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) : ¬HasBoundaryExit c N N t := by
  rintro ⟨k, ⟨h1, h2⟩, hk⟩
  obtain ⟨⟨a1, b1, e1⟩, ⟨a2, b2, e2⟩⟩ := boundary_corners ht hk
  rw [hc _ _ a1 b1 e1] at h1
  rw [hc _ _ a2 b2 e2] at h2
  exact (boundary_door ht hk).1 ⟨h1, h2⟩

theorem IsSpernerColoring.isEntry_start (hc : IsSpernerColoring N c) (hN : 0 < N) :
    IsEntry c start 2 := by
  constructor
  · rw [show start.corner 2 = (0, 1) from rfl, hc 0 1 (Nat.zero_le _) hN (.inl rfl)]
    rfl
  · rw [show start.corner (2 + 1) = (0, 0) from rfl, hc 0 0 (Nat.zero_le _) (Nat.zero_le _)
      (.inl rfl)]
    rfl

theorem interior_start_two : interior N N start 2 = false := rfl

theorem inGrid_start_iff : InGrid N N start ↔ 0 < N := by
  simp [InGrid, start]

theorem IsSpernerColoring.hasBoundaryEntry_iff (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) : HasBoundaryEntry c N N t ↔ t = start := by
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, hk⟩
    obtain ⟨⟨a1, b1, e1⟩, ⟨a2, b2, e2⟩⟩ := boundary_corners ht hk
    rw [hc _ _ a1 b1 e1] at h1
    rw [hc _ _ a2 b2 e2] at h2
    exact (boundary_door ht hk).2 ⟨h1, h2⟩
  · rintro rfl
    exact ⟨2, hc.isEntry_start (inGrid_start_iff.mp ht), interior_start_two⟩

/-- In a Sperner colouring of the `N × N` grid (`0 < N`), the door graph has exactly one more
sink than it has sources. -/
theorem IsSpernerColoring.card_isSink (hc : IsSpernerColoring N c) (hN : 0 < N) :
    ((triangles N N).filter (IsSink c)).card = ((triangles N N).filter (IsSource c)).card + 1 := by
  have h := card_isSink_add_card_hasBoundaryExit (c := c) (W := N) (H := N)
  have h0 : (triangles N N).filter (HasBoundaryExit c N N) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun t ht => hc.not_hasBoundaryExit (mem_triangles.mp ht)
  have h1 : (triangles N N).filter (HasBoundaryEntry c N N) = {start} := by
    ext t
    simp only [Finset.mem_filter, mem_triangles, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, h⟩
      exact (hc.hasBoundaryEntry_iff ht).mp h
    · rintro rfl
      have hs : InGrid N N start := inGrid_start_iff.mpr hN
      exact ⟨hs, (hc.hasBoundaryEntry_iff hs).mpr rfl⟩
  rw [h0, h1, Finset.card_empty, Finset.card_singleton] at h
  omega

/-- **Sperner's lemma, parity form.** A Sperner colouring of the `N × N` grid (`0 < N`) has an odd
number of trichromatic triangles. -/
theorem IsSpernerColoring.odd_card_trichromatic (hc : IsSpernerColoring N c) (hN : 0 < N) :
    Odd ((triangles N N).filter (Trichromatic c)).card := by
  have h := card_filter_of_iff_or (triangles N N)
    (fun t => trichromatic_iff_isSink_or_isSource (c := c) (t := t)) fun t h => h.1.2 h.2.1
  rw [h, hc.card_isSink hN]
  exact ⟨((triangles N N).filter (IsSource c)).card, by omega⟩

/-- **Sperner's lemma.** A Sperner colouring of the `N × N` grid (`0 < N`) has a trichromatic
triangle. -/
theorem IsSpernerColoring.exists_trichromatic (hc : IsSpernerColoring N c) (hN : 0 < N) :
    ∃ t, InGrid N N t ∧ Trichromatic c t := by
  obtain ⟨k, hk⟩ := hc.odd_card_trichromatic hN
  obtain ⟨t, ht⟩ := Finset.card_pos.mp
    (show 0 < ((triangles N N).filter (Trichromatic c)).card by omega)
  rw [Finset.mem_filter, mem_triangles] at ht
  exact ⟨t, ht⟩

/-! ### The door graph as an end-of-line graph -/

theorem across_ne_self (t : GridTriangle) (k : Fin 3) : across t k ≠ t := by
  obtain ⟨_ | _, x, y⟩ := t <;> fin_cases k <;> simp [across]

theorem next_eq_self_of_not {t : GridTriangle} (h : ¬HasInteriorExit c W H t) :
    next c W H t = t :=
  next_eq_self fun k hk => Bool.eq_false_iff.mpr fun hi => h ⟨k, hk, hi⟩

theorem prev_eq_self_of_not {t : GridTriangle} (h : ¬HasInteriorEntry c W H t) :
    prev c W H t = t :=
  prev_eq_self fun k hk => Bool.eq_false_iff.mpr fun hi => h ⟨k, hk, hi⟩

theorem inGrid_next {t : GridTriangle} (ht : InGrid W H t) : InGrid W H (next c W H t) := by
  by_cases h : HasInteriorExit c W H t
  · obtain ⟨k, hk, hi⟩ := h
    rw [next_eq_across hk hi]
    exact (gluing ht hi).1
  · rwa [next_eq_self_of_not h]

theorem inGrid_prev {t : GridTriangle} (ht : InGrid W H t) : InGrid W H (prev c W H t) := by
  by_cases h : HasInteriorEntry c W H t
  · obtain ⟨k, hk, hi⟩ := h
    rw [prev_eq_across hk hi]
    exact (gluing ht hi).1
  · rwa [prev_eq_self_of_not h]

theorem next_ne_self_iff {t : GridTriangle} : next c W H t ≠ t ↔ HasInteriorExit c W H t := by
  refine ⟨fun h => by_contra fun h' => h (next_eq_self_of_not h'), fun ⟨k, hk, hi⟩ => ?_⟩
  rw [next_eq_across hk hi]
  exact across_ne_self t k

theorem prev_ne_self_iff {t : GridTriangle} : prev c W H t ≠ t ↔ HasInteriorEntry c W H t := by
  refine ⟨fun h => by_contra fun h' => h (prev_eq_self_of_not h'), fun ⟨k, hk, hi⟩ => ?_⟩
  rw [prev_eq_across hk hi]
  exact across_ne_self t k

theorem prev_next_of_hasInteriorExit {t : GridTriangle} (ht : InGrid W H t)
    (h : HasInteriorExit c W H t) : prev c W H (next c W H t) = t :=
  let ⟨_, hk, hi⟩ := h
  prev_next ht hk hi

theorem next_prev_of_hasInteriorEntry {t : GridTriangle} (ht : InGrid W H t)
    (h : HasInteriorEntry c W H t) : next c W H (prev c W H t) = t :=
  let ⟨_, hk, hi⟩ := h
  next_prev ht hk hi

/-- Following an interior exit door never leads back to `start`: the entry door of `start` lies
on the boundary. -/
theorem IsSpernerColoring.next_ne_start (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) (h : HasInteriorExit c N N t) : next c N N t ≠ start := by
  obtain ⟨k, hk, hi⟩ := h
  obtain ⟨hg, hi', -, -, -⟩ := gluing ht hi
  rw [next_eq_across hk hi]
  intro hs
  have he := isEntry_across c ht hi hk
  rw [hs] at he hi' hg
  have h2 := isEntry_unique c he (hc.isEntry_start (inGrid_start_iff.mp hg))
  rw [h2, interior_start_two] at hi'
  exact Bool.false_ne_true hi'

theorem IsSpernerColoring.hasInteriorExit_iff (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) : HasInteriorExit c N N t ↔ HasExit c t := by
  rw [hasExit_iff (W := N) (H := N), or_iff_left (hc.not_hasBoundaryExit ht)]

theorem IsSpernerColoring.hasInteriorEntry_iff (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) : HasInteriorEntry c N N t ↔ HasEntry c t ∧ t ≠ start := by
  rw [hasEntry_iff (W := N) (H := N), ne_eq, ← hc.hasBoundaryEntry_iff ht]
  constructor
  · intro h
    exact ⟨.inl h, fun hb => not_hasInteriorEntry_and_hasBoundaryEntry ⟨h, hb⟩⟩
  · rintro ⟨h | h, hb⟩
    exacts [h, absurd h hb]

/-- The door graph of a Sperner colouring has an outgoing edge at `t` exactly when `t` has an exit
door. -/
theorem IsSpernerColoring.door_out_iff (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) :
    (prev c N N (next c N N t) = t ∧ next c N N t ≠ t ∧ next c N N t ≠ start) ↔ HasExit c t := by
  rw [← hc.hasInteriorExit_iff ht]
  refine ⟨fun h => next_ne_self_iff.mp h.2.1, fun h => ?_⟩
  exact ⟨prev_next_of_hasInteriorExit ht h, next_ne_self_iff.mpr h, hc.next_ne_start ht h⟩

/-- The door graph of a Sperner colouring has an incoming edge at `t` exactly when `t` has an entry
door and is not `start`. -/
theorem IsSpernerColoring.door_in_iff (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) :
    (next c N N (prev c N N t) = t ∧ prev c N N t ≠ t ∧ t ≠ start) ↔
      HasEntry c t ∧ t ≠ start := by
  rw [← hc.hasInteriorEntry_iff ht]
  refine ⟨fun h => prev_ne_self_iff.mp h.2.1, fun h => ?_⟩
  exact ⟨next_prev_of_hasInteriorEntry ht h, prev_ne_self_iff.mpr h,
    ((hc.hasInteriorEntry_iff ht).mp h).2⟩

/-- **Trichromatic triangles are the unbalanced vertices of the door graph.** For a Sperner
colouring, a triangle `t ≠ start` is trichromatic exactly when it has exactly one of an entry and an
exit door, and `start` (which always has an entry door) is trichromatic exactly when it has no exit
door. -/
theorem IsSpernerColoring.trichromatic_iff (hc : IsSpernerColoring N c) {t : GridTriangle}
    (ht : InGrid N N t) :
    Trichromatic c t ↔ (((HasEntry c t ∧ t ≠ start) ↔ HasExit c t) ↔ t = start) := by
  rw [trichromatic_iff_isSink_or_isSource]
  unfold IsSink IsSource
  by_cases hs : t = start
  · subst hs
    have he : HasEntry c start := ⟨2, hc.isEntry_start (inGrid_start_iff.mp ht)⟩
    tauto
  · tauto

end Cslib.Sperner
