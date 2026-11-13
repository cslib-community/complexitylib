/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Finite polygonal routes in the plane

A route has a positive finite number of actual straight real segments in the complex plane.
Segment parameters include all real numbers in `[0,1]`. Simplicity identifies only adjacent
segment endpoints and, for a closed route, its first and last parameter. In particular it
excludes degenerate segments, retracing, tangencies and nonadjacent contacts.

This is original finite geometric infrastructure, with no numerical genus certificate or
topological drawing theorem among its data or hypotheses.

## Main definitions

* `Cslib.Polygonal.Route`: a finite nonempty chain of real planar segments.
* `Cslib.Polygonal.Route.IsSimple`: injectivity except for the intended endpoint closure.
* `Cslib.Polygonal.Route.germ`: the actual outgoing first or last segment vector.
-/

public section

namespace Cslib.Polygonal

/-- A nonempty finite segment chain. `bends + 1` is its number of segments; extra collinear
vertices are permitted. `IsSimple` allows closure only between the first and last parameters. -/
structure Route where
  /-- Number of internal listed points. -/
  bends : ℕ
  /-- Listed points, including both ends. -/
  point : Fin (bends + 2) → ℂ

namespace Route

variable (p : Route)

/-- The number of actual segments. -/
abbrev segments : ℕ := p.bends + 1

/-- First listed point. -/
@[expose] def start : ℂ := p.point 0

/-- Last listed point. -/
@[expose] def finish : ℂ := p.point (Fin.last p.segments)

/-- The endpoint selected by a dart's Boolean end tag. -/
@[expose] def endpoint (b : Bool) : ℂ := if b then p.finish else p.start

/-- The actual `i`-th segment, with its full real affine parameter. -/
@[expose] noncomputable def eval (i : Fin p.segments) (t : ℝ) : ℂ :=
  AffineMap.lineMap (p.point i.castSucc) (p.point i.succ) t

/-- The parameter on the entire chain, identifying successive segment endpoints. -/
@[expose] def position (i : Fin p.segments) (t : ℝ) : ℝ := (i.val : ℝ) + t

/-- A parameter is at one of the two ends of the entire chain. -/
@[expose] def AtEnd (i : Fin p.segments) (t : ℝ) (b : Bool) : Prop :=
  p.position i t = if b then (p.segments : ℝ) else 0

/-- All real points on all listed segments. -/
@[expose] noncomputable def support : Set ℂ :=
  ⋃ i : Fin p.segments, segment ℝ (p.point i.castSucc) (p.point i.succ)

/-- Every segment parameter belongs to the continuous support. -/
theorem at_mem_support (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    p.eval i t ∈ p.support :=
  Set.mem_iUnion.mpr ⟨i, lineMap_mem_segment ℝ _ _ ht⟩

/-- Membership in the support means membership at an actual real segment parameter. -/
theorem mem_support_iff (z : ℂ) : z ∈ p.support ↔
    ∃ (i : Fin p.segments) (t : ℝ), t ∈ Set.Icc 0 1 ∧ p.eval i t = z := by
  simp only [support, Set.mem_iUnion, segment_eq_image_lineMap, Set.mem_image, eval]

/-- The chain parameter stays in its closed global interval. -/
theorem position_mem (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    p.position i t ∈ Set.Icc 0 (p.segments : ℝ) := by
  have hi : (i.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast i.isLt
  exact ⟨add_nonneg (Nat.cast_nonneg _) ht.1, (add_le_add_right ht.2 _).trans hi⟩

/-- At the first chain parameter the segment point is the first listed point. -/
theorem at_eq_start (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (h : p.position i t = 0) : p.eval i t = p.start := by
  have hi : (i.val : ℝ) = 0 := by
    have := ht.1
    have := Nat.cast_nonneg (α := ℝ) i.val
    dsimp [position] at h
    linarith
  have hiNat : i.val = 0 := by exact_mod_cast hi
  have hi' : i = 0 := Fin.ext hiNat
  have ht' : t = 0 := by simpa only [hi', position, Fin.val_zero, Nat.cast_zero, zero_add] using h
  subst i
  subst t
  simp [eval, start]

/-- At the last chain parameter the segment point is the last listed point. -/
theorem at_eq_finish (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (h : p.position i t = p.segments) : p.eval i t = p.finish := by
  have hi : (i.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast i.isLt
  have ht' : t = 1 := by dsimp [position] at h; linarith [ht.2]
  have hi' : i = Fin.last p.bends := by
    apply Fin.ext
    dsimp [position, segments] at h
    simp only [ht'] at h
    have : (i.val : ℝ) = p.bends := by push_cast at h; linarith
    exact_mod_cast this
  subst i
  subst t
  simp [eval, finish, segments]

/-- The point of a parameter at a selected end is that endpoint. -/
theorem at_eq_endpoint (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (b : Bool) (h : p.AtEnd i t b) : p.eval i t = p.endpoint b := by
  cases b
  · exact p.at_eq_start i ht h
  · exact p.at_eq_finish i ht h

/-- Equal points have equal global parameters, except for the two ends of a closed route.
This tests the actual continuum of each segment, not only the listed points. -/
@[expose] def IsSimple : Prop :=
  ∀ (i j : Fin p.segments) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
    p.eval i s = p.eval j t → p.position i s = p.position j t ∨
      (p.AtEnd i s false ∧ p.AtEnd j t true) ∨
      (p.AtEnd i s true ∧ p.AtEnd j t false)

/-- Every actual segment of a simple route is nondegenerate. -/
theorem IsSimple.segment_ne {p : Route} (hp : p.IsSimple) (i : Fin p.segments) :
    p.point i.castSucc ≠ p.point i.succ := by
  intro heq
  have h := hp i i (1 / 3) (2 / 3) (by constructor <;> norm_num)
    (by constructor <;> norm_num) (by simp [eval, heq])
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  rcases h with h | ⟨h, -⟩ | ⟨-, h⟩ <;> dsimp [position, AtEnd] at h <;> linarith

/-- Outgoing vector of the first segment at the first end, or the reversed last segment
at the last end. Thus loops still have two separately defined geometric germs. -/
@[expose] def germ (b : Bool) : ℂ :=
  if b then p.point (Fin.last p.bends).castSucc - p.finish
  else p.point (0 : Fin p.segments).succ - p.start

/-- A simple route has nonzero outgoing germs at both ends. -/
theorem IsSimple.germ_ne_zero {p : Route} (hp : p.IsSimple) (b : Bool) : p.germ b ≠ 0 := by
  cases b
  · simpa only [germ, Bool.false_eq_true, ↓reduceIte, sub_ne_zero, start, Fin.castSucc_zero] using
      (hp.segment_ne 0).symm
  · simpa only [germ, ↓reduceIte, sub_ne_zero, finish, Fin.succ_last, segments] using
      hp.segment_ne (Fin.last p.bends)

end Route
end Cslib.Polygonal
