/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Data.List.Defs
public import Mathlib.Basic.Real.Basic
import Aesop

/-!
# Finite orthogonal polygonal routes

The data are lists of integer points. Their geometric interpretation uses Mathlib's closed real
segments, including every real point between consecutive listed points, rather than only lattice
points. A singleton route has singleton support; an empty route has empty support.

## Main definitions

* `Cslib.Orthogonal.Point`, `Cslib.Orthogonal.Route`: finite integer-coordinate data.
* `Cslib.Orthogonal.support`: the continuous support of a polygonal route.
* `Cslib.Orthogonal.IsOrthogonal`: every consecutive segment is axis aligned and nondegenerate.
* `Cslib.Orthogonal.wireLength`: total Manhattan length.

## Main results

* `Cslib.Orthogonal.mem_horizontal`, `Cslib.Orthogonal.mem_vertical`: real segment membership
  characterized by coordinate intervals.

## References

The finite-route definitions and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- An integer grid point. -/
abbrev Point := ℤ × ℤ

/-- Explicit finite polygonal route data. -/
abbrev Route := List Point

/-- Inclusion of the integer grid into the real plane. -/
def realPoint (p : Point) : ℝ × ℝ := (p.1, p.2)

/-- The geometric inclusion does not identify distinct grid points. -/
theorem realPoint_injective : Function.Injective realPoint := by
  rintro ⟨ax, ay⟩ ⟨bx, by'⟩ h
  simp only [realPoint, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

/-- A closed real segment between two integer grid points. -/
def segment (a b : Point) : Set (ℝ × ℝ) := _root_.segment ℝ (realPoint a) (realPoint b)

/-- All real points on a finite polygonal route, including isolated listed points. -/
def support (r : Route) : Set (ℝ × ℝ) :=
  {p | (∃ a ∈ r, p = realPoint a) ∨ ∃ e ∈ r.consecutivePairs, p ∈ segment e.1 e.2}

/-- Splitting off the first segment agrees with the continuous polygonal support. -/
theorem support_cons_cons (a b : Point) (r : Route) :
    support (a :: b :: r) = segment a b ∪ support (b :: r) := by
  ext p
  simp only [support, Set.mem_ofPred_eq, List.mem_cons, List.consecutivePairs, List.tail_cons,
    List.zip_cons_cons, exists_eq_or_imp, Set.mem_union]
  have ha : realPoint a ∈ segment a b := left_mem_segment ℝ _ _
  aesop

/-- A proper axis-aligned segment; zero-length segments are excluded. -/
def AxisAligned (a b : Point) : Prop :=
  (a.1 = b.1 ∨ a.2 = b.2) ∧ a ≠ b

instance (a b : Point) : Decidable (AxisAligned a b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every consecutive segment is proper and axis aligned. -/
def IsOrthogonal (r : Route) : Prop := ∀ e ∈ r.consecutivePairs, AxisAligned e.1 e.2

/-- Orthogonality is decidable by checking the finitely many consecutive segments. -/
instance : DecidablePred IsOrthogonal :=
  fun r => inferInstanceAs (Decidable (∀ e ∈ r.consecutivePairs, AxisAligned e.1 e.2))

/-- Removing the initial listed point preserves proper orthogonality. -/
theorem IsOrthogonal.of_cons {a : Point} {r : Route} (h : IsOrthogonal (a :: r)) :
    IsOrthogonal r := by
  cases r with
  | nil => simp [IsOrthogonal, List.consecutivePairs]
  | cons b r =>
    intro e he
    exact h e (List.mem_cons_of_mem (a, b) he)

/-- Manhattan length of one segment. -/
def length (a b : Point) : ℕ := (b.1 - a.1).natAbs + (b.2 - a.2).natAbs

/-- A pair of lattice points one Manhattan unit apart forms a proper axis-aligned segment. -/
theorem axisAligned_of_length_eq_one {a b : Point} (h : length a b = 1) : AxisAligned a b := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp only [length] at h
  simp only [AxisAligned, ne_eq, Prod.mk.injEq]
  omega

/-- Total Manhattan length of the consecutive segments. -/
def wireLength (r : Route) : ℕ := (r.consecutivePairs.map fun e => length e.1 e.2).sum

/-- A bounding rectangle controls the length of any one segment. -/
theorem length_le_box {a b : Point} {w h : ℕ}
    (ha : 0 ≤ a.1 ∧ a.1 ≤ w ∧ 0 ≤ a.2 ∧ a.2 ≤ h)
    (hb : 0 ≤ b.1 ∧ b.1 ≤ w ∧ 0 ≤ b.2 ∧ b.2 ≤ h) : length a b ≤ w + h := by
  have hx : (b.1 - a.1).natAbs ≤ w := by omega
  have hy : (b.2 - a.2).natAbs ≤ h := by omega
  exact Nat.add_le_add hx hy

/-- Bounding all listed points bounds the total wire length by the number of segments times
the sum of the rectangle sides. -/
theorem wireLength_le_box {r : Route} {w h : ℕ}
    (hr : ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ w ∧ 0 ≤ p.2 ∧ p.2 ≤ h) :
    wireLength r ≤ r.consecutivePairs.length * (w + h) := by
  unfold wireLength
  calc
    _ ≤ (r.consecutivePairs.map fun _ => w + h).sum := by
      apply List.sum_le_sum
      intro e he
      have hmem := List.of_mem_zip he
      exact length_le_box (hr e.1 hmem.1) (hr e.2 (List.mem_of_mem_tail hmem.2))
    _ = _ := by simp

/-- A strict transverse horizontal/vertical crossing at a real point. The strict inequalities
exclude endpoints and bends. -/
def Transverse (a b c d : Point) (p : ℝ × ℝ) : Prop :=
  (a.2 = b.2 ∧ c.1 = d.1 ∧ p = ((c.1 : ℝ), (a.2 : ℝ)) ∧
    min a.1 b.1 < c.1 ∧ c.1 < max a.1 b.1 ∧ min c.2 d.2 < a.2 ∧ a.2 < max c.2 d.2) ∨
  (a.1 = b.1 ∧ c.2 = d.2 ∧ p = ((a.1 : ℝ), (c.2 : ℝ)) ∧
    min c.1 d.1 < a.1 ∧ a.1 < max c.1 d.1 ∧ min a.2 b.2 < c.2 ∧ c.2 < max a.2 b.2)

/-- Every real segment lies in its coordinate bounding rectangle. -/
theorem mem_segment_bounds {a b : Point} {p : ℝ × ℝ} (hp : p ∈ segment a b) :
    p.1 ∈ Set.uIcc (a.1 : ℝ) (b.1 : ℝ) ∧
    p.2 ∈ Set.uIcc (a.2 : ℝ) (b.2 : ℝ) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
  constructor <;> rw [← segment_eq_uIcc] <;> exact ⟨s, t, hs, ht, hst, rfl⟩

/-- Horizontal real segment membership is a one-dimensional interval test. -/
theorem mem_horizontal {a b y : ℝ} {p : ℝ × ℝ} :
    p ∈ _root_.segment ℝ (a, y) (b, y) ↔ p.2 = y ∧ p.1 ∈ Set.uIcc a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    constructor
    · change s * y + t * y = y
      rw [← add_mul, hst, one_mul]
    · rw [← segment_eq_uIcc]
      exact ⟨s, t, hs, ht, hst, rfl⟩
  · rintro ⟨hy, hx⟩
    rw [← segment_eq_uIcc] at hx
    obtain ⟨s, t, hs, ht, hst, hx⟩ := hx
    refine ⟨s, t, hs, ht, hst, Prod.ext hx ?_⟩
    change s * y + t * y = p.2
    rw [hy]
    rw [← add_mul, hst, one_mul]

/-- Vertical real segment membership is a one-dimensional interval test. -/
theorem mem_vertical {x a b : ℝ} {p : ℝ × ℝ} :
    p ∈ _root_.segment ℝ (x, a) (x, b) ↔ p.1 = x ∧ p.2 ∈ Set.uIcc a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    constructor
    · change s * x + t * x = x
      rw [← add_mul, hst, one_mul]
    · rw [← segment_eq_uIcc]
      exact ⟨s, t, hs, ht, hst, rfl⟩
  · rintro ⟨hx, hy⟩
    rw [← segment_eq_uIcc] at hy
    obtain ⟨s, t, hs, ht, hst, hy⟩ := hy
    refine ⟨s, t, hs, ht, hst, Prod.ext ?_ hy⟩
    change s * x + t * x = p.1
    rw [hx]
    rw [← add_mul, hst, one_mul]

/-- Integer points on an axis-aligned segment can be checked using integer inequalities. -/
theorem realPoint_mem_segment_iff {a b p : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    realPoint p ∈ segment a b ↔
      min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧
      min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2 := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  rcases p with ⟨px, py⟩
  rcases h with h | h
  · change ax = bx at h
    subst bx
    simp only [segment, realPoint, mem_vertical, Set.mem_uIcc]
    norm_cast
    omega
  · change ay = by' at h
    subst by'
    simp only [segment, realPoint, mem_horizontal, Set.mem_uIcc]
    norm_cast
    omega

/-- Integer-point membership in an orthogonal route is an entirely integer-arithmetic test,
while its meaning remains membership in the continuous real support. -/
theorem realPoint_mem_support_iff {r : Route} (hr : IsOrthogonal r) (p : Point) :
    realPoint p ∈ support r ↔ p ∈ r ∨ ∃ e ∈ r.consecutivePairs,
      min e.1.1 e.2.1 ≤ p.1 ∧ p.1 ≤ max e.1.1 e.2.1 ∧
      min e.1.2 e.2.2 ≤ p.2 ∧ p.2 ≤ max e.1.2 e.2.2 := by
  simp only [support, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨a, ha, heq⟩ | ⟨e, he, hp⟩)
    · exact Or.inl (realPoint_injective heq ▸ ha)
    · exact Or.inr ⟨e, he, (realPoint_mem_segment_iff (hr e he).1).1 hp⟩
  · rintro (hp | ⟨e, he, hp⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨e, he, (realPoint_mem_segment_iff (hr e he).1).2 hp⟩

end Cslib.Orthogonal
