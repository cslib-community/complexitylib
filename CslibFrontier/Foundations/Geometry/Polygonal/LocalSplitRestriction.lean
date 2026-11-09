/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Germs

/-!
# Cutting the two ends of a finite polygonal route

`Route.cutEnds` moves the two listed endpoints into their original end segments and leaves
all internal listed points unchanged. The two cuts are independent, including when the
route has a single segment. The real local parameters are tracked explicitly, so support
containment and simplicity refer to every real point of every segment.

The sum of the two cut parameters must be less than one. This suffices even for a
single-segment open edge; no artificial bend or degenerate segment is introduced.
-/

public section

namespace Cslib.Polygonal.Route

/-- Cut the initial and final outgoing segments by parameters `s` and `t`. Internal
points and their order are unchanged. Zero cuts are permitted. -/
@[expose] noncomputable def cutEnds (p : Route) (s t : ℝ) : Route where
  bends := p.bends
  point := fun i => if i.val = 0 then p.eval 0 s else
    if i.val = p.segments then p.eval (Fin.last p.bends) (1 - t) else p.point i

/-- The lower original parameter retained in a given segment after the two cuts. -/
@[expose] def cutLower (p : Route) (s : ℝ) (i : Fin p.segments) : ℝ :=
  if i.val = 0 then s else 0

/-- The upper original parameter retained in a given segment after the two cuts. -/
@[expose] def cutUpper (p : Route) (t : ℝ) (i : Fin p.segments) : ℝ :=
  if i.val + 1 = p.segments then 1 - t else 1

/-- The old real segment parameter of a point on the cut route. -/
@[expose] noncomputable def cutTime (p : Route) (s t : ℝ)
    (i : Fin p.segments) (u : ℝ) : ℝ :=
  AffineMap.lineMap (p.cutLower s i) (p.cutUpper t i) u

/-- The two new route ends are the chosen real parameters of the two old end segments. -/
theorem endpoint_cutEnds (p : Route) (s t : ℝ) (b : Bool) :
    (p.cutEnds s t).endpoint b =
      p.eval (p.endSegment b) (endTime b (if b then t else s)) := by
  cases b
  · rfl
  · simp [endpoint, finish, cutEnds, endSegment, endTime, segments]

private theorem point_cutEnds_castSucc (p : Route) (s t : ℝ) (i : Fin p.segments) :
    (p.cutEnds s t).point i.castSucc = p.eval i (p.cutLower s i) := by
  have hlast : ¬i.val = p.segments := Nat.ne_of_lt i.isLt
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    rfl
  · simp [cutEnds, cutLower, hi, hlast, eval]

private theorem point_cutEnds_succ (p : Route) (s t : ℝ) (i : Fin p.segments) :
    (p.cutEnds s t).point i.succ = p.eval i (p.cutUpper t i) := by
  have hzero : ¬i.val + 1 = 0 := by omega
  by_cases hi : i.val + 1 = p.segments
  · have hi' : i = Fin.last p.bends := by
      apply Fin.ext
      change i.val = p.bends
      dsimp [segments] at hi
      omega
    subst i
    simp [cutEnds, cutUpper, segments]
  · change (if i.val + 1 = 0 then p.eval 0 s else
      if i.val + 1 = p.segments then p.eval (Fin.last p.bends) (1 - t) else p.point i.succ) = _
    rw [ite_eq_right hzero, ite_eq_right hi]
    simp only [cutUpper, ite_eq_right hi, eval, AffineMap.lineMap_apply_one]

/-- Every cut segment is an affine subsegment of the original segment at the same index,
including when the first and last segment are the same. -/
theorem eval_cutEnds (p : Route) (s t : ℝ) (i : Fin p.segments) (u : ℝ) :
    (p.cutEnds s t).eval i u = p.eval i (p.cutTime s t i u) := by
  change AffineMap.lineMap ((p.cutEnds s t).point i.castSucc)
    ((p.cutEnds s t).point i.succ) u = _
  rw [point_cutEnds_castSucc, point_cutEnds_succ]
  exact ((AffineMap.lineMap (p.point i.castSucc) (p.point i.succ)).apply_lineMap _ _ _).symm

/-- Both retained local segment endpoints lie in the old unit interval, in strict order. -/
theorem cut_bounds (p : Route) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (i : Fin p.segments) :
    0 ≤ p.cutLower s i ∧ p.cutLower s i < p.cutUpper t i ∧ p.cutUpper t i ≤ 1 := by
  dsimp [cutLower, cutUpper]
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Every cut parameter lies between the two retained endpoints of its old segment. -/
theorem cutTime_bounds (p : Route) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t < 1) (i : Fin p.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    p.cutLower s i ≤ p.cutTime s t i u ∧ p.cutTime s t i u ≤ p.cutUpper t i := by
  obtain ⟨_, hlu, _⟩ := p.cut_bounds hs ht hst i
  dsimp [cutTime]
  rw [AffineMap.lineMap_apply_ring']
  constructor <;> nlinarith [hu.1, hu.2]

/-- The lower end of an affine subsegment has only the new zero parameter. -/
theorem cutTime_eq_lower_iff (p : Route) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1) (i : Fin p.segments) (u : ℝ) :
    p.cutTime s t i u = p.cutLower s i ↔ u = 0 := by
  obtain ⟨_, hlu, _⟩ := p.cut_bounds hs ht hst i
  dsimp [cutTime]
  simp only [AffineMap.lineMap_eq_left_iff, ne_of_lt hlu, false_or]

/-- The upper end of an affine subsegment has only the new unit parameter. -/
theorem cutTime_eq_upper_iff (p : Route) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1) (i : Fin p.segments) (u : ℝ) :
    p.cutTime s t i u = p.cutUpper t i ↔ u = 1 := by
  obtain ⟨_, hlu, _⟩ := p.cut_bounds hs ht hst i
  dsimp [cutTime]
  simp only [AffineMap.lineMap_eq_right_iff, ne_of_lt hlu, false_or]

/-- Cutting both ends never sends a retained real parameter outside its old segment. -/
theorem cutTime_mem (p : Route) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t < 1) (i : Fin p.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    p.cutTime s t i u ∈ Set.Icc 0 1 := by
  obtain ⟨hl, hlu, hh⟩ := p.cut_bounds hs ht hst i
  dsimp [cutTime]
  rw [AffineMap.lineMap_apply_ring']
  constructor <;> nlinarith [hu.1, hu.2]

private theorem cutTime_eq_zero (p : Route) {s t u : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (i : Fin p.segments) (hu : u ∈ Set.Icc 0 1) (heq : p.cutTime s t i u = 0) :
    u = 0 := by
  obtain ⟨hl, hlu, _⟩ := p.cut_bounds hs ht hst i
  dsimp [cutTime] at heq
  rw [AffineMap.lineMap_apply_ring'] at heq
  nlinarith [hu.1]

private theorem cutTime_eq_one (p : Route) {s t u : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (i : Fin p.segments) (hu : u ∈ Set.Icc 0 1) (heq : p.cutTime s t i u = 1) :
    u = 1 := by
  obtain ⟨_, hlu, hh⟩ := p.cut_bounds hs ht hst i
  dsimp [cutTime] at heq
  rw [AffineMap.lineMap_apply_ring'] at heq
  nlinarith [hu.2]

/-- Cutting both ends only removes actual points from the continuous support. -/
theorem support_cutEnds_subset (p : Route) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1) :
    (p.cutEnds s t).support ⊆ p.support := by
  intro z hz
  obtain ⟨i, u, hu, rfl⟩ := ((p.cutEnds s t).mem_support_iff z).mp hz
  change Fin p.segments at i
  rw [eval_cutEnds p s t i u]
  exact p.at_mem_support i (p.cutTime_mem hs ht hst i hu)

private theorem cut_position_eq {p : Route} {s t u v : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (i j : Fin p.segments) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (heq : p.position i (p.cutTime s t i u) = p.position j (p.cutTime s t j v)) :
    (p.cutEnds s t).position i u = (p.cutEnds s t).position j v := by
  have hi := p.cutTime_mem hs ht hst i hu
  have hj := p.cutTime_mem hs ht hst j hv
  by_cases hij : i = j
  · subst j
    obtain ⟨_, hlt, _⟩ := p.cut_bounds hs ht hst i
    dsimp [position, cutTime] at heq ⊢
    rw [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_ring'] at heq
    have huv : u = v := by nlinarith
    rw [huv]
  · have side {i j : Fin p.segments} {u v : ℝ}
        (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
        (hij : i.val < j.val)
        (heq : p.position i (p.cutTime s t i u) = p.position j (p.cutTime s t j v)) :
        (p.cutEnds s t).position i u = (p.cutEnds s t).position j v := by
      have hi := p.cutTime_mem hs ht hst i hu
      have hj := p.cutTime_mem hs ht hst j hv
      have hcast : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
      have hi1 : p.cutTime s t i u = 1 := by dsimp [position] at heq; linarith [hi.2, hj.1]
      have hj0 : p.cutTime s t j v = 0 := by dsimp [position] at heq; linarith [hi.2, hj.1]
      have hu1 := cutTime_eq_one p hs ht hst i hu hi1
      have hv0 := cutTime_eq_zero p hs ht hst j hv hj0
      dsimp [position] at heq ⊢
      rw [hi1, hj0] at heq
      rw [hu1, hv0]
      exact heq
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with hij | hij
    · exact side hu hv hij heq
    · exact (side hv hu hij heq.symm).symm

/-- If a retained point was at an old route end, it is at the same end of the cut route.
The converse need not hold: a positive cut creates a new end in an old segment interior. -/
theorem atEnd_cutEnds_of_atEnd {p : Route} {s t u : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (i : Fin p.segments) (hu : u ∈ Set.Icc 0 1) (b : Bool)
    (heq : p.AtEnd i (p.cutTime s t i u) b) : (p.cutEnds s t).AtEnd i u b := by
  have hi := p.cutTime_mem hs ht hst i hu
  have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast i.isLt
  cases b
  · have hu0 : p.cutTime s t i u = 0 := by dsimp [AtEnd, position] at heq; linarith [hi.1]
    have hu' := cutTime_eq_zero p hs ht hst i hu hu0
    dsimp [AtEnd, position] at heq ⊢
    rw [hu0] at heq
    rw [hu']
    exact heq
  · have hu1 : p.cutTime s t i u = 1 := by dsimp [AtEnd, position] at heq; linarith [hi.2]
    have hu' := cutTime_eq_one p hs ht hst i hu hu1
    dsimp [AtEnd, position] at heq ⊢
    rw [hu1] at heq
    rw [hu']
    exact heq

/-- Cutting the two end segments preserves continuous simplicity, also for a closed loop
and for a one-segment open edge. The two cuts may have different parameters. -/
theorem IsSimple.cutEnds {p : Route} (hp : p.IsSimple) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1) : (p.cutEnds s t).IsSimple := by
  intro i j u v hu hv heq
  change Fin p.segments at i j
  rw [eval_cutEnds p s t i u, eval_cutEnds p s t j v] at heq
  rcases hp i j _ _ (p.cutTime_mem hs ht hst i hu)
      (p.cutTime_mem hs ht hst j hv) heq with h | ⟨h, k⟩ | ⟨h, k⟩
  · exact Or.inl (cut_position_eq hs ht hst i j hu hv h)
  · exact Or.inr (Or.inl ⟨atEnd_cutEnds_of_atEnd hs ht hst i hu false h,
      atEnd_cutEnds_of_atEnd hs ht hst j hv true k⟩)
  · exact Or.inr (Or.inr ⟨atEnd_cutEnds_of_atEnd hs ht hst i hu true h,
      atEnd_cutEnds_of_atEnd hs ht hst j hv false k⟩)

end Cslib.Polygonal.Route
