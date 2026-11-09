/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route

/-!
# Adding one segment to either end of a polygonal route

`Route.prepend` and `Route.append` each add exactly one real segment. Their contact
conditions distinguish the two parameter ends, including when the new route closes.
Adding a segment to an already closed route cannot preserve simplicity, and a new
degenerate segment is rejected.

These are original finite route constructions. No topological path replacement theorem
or geometric drawing provider is assumed.
-/

public section

namespace Cslib.Polygonal.Route

/-- Add the segment from `a` to the old start. This adds exactly one segment. -/
@[expose] def prepend (a : ℂ) (p : Route) : Route where
  bends := p.bends + 1
  point := Fin.cases a p.point

/-- Add the segment from the old finish to `b`. This adds exactly one segment. -/
@[expose] def append (p : Route) (b : ℂ) : Route where
  bends := p.bends + 1
  point := Fin.lastCases b p.point

/-- Prepending adds exactly one segment. -/
@[simp] theorem segments_prepend (a : ℂ) (p : Route) :
    (Route.prepend a p).segments = p.segments + 1 := rfl

/-- Appending adds exactly one segment. -/
@[simp] theorem segments_append (p : Route) (b : ℂ) :
    (p.append b).segments = p.segments + 1 := rfl

/-- The new initial segment has its full real affine parameter. -/
theorem eval_prepend_zero (a : ℂ) (p : Route) (t : ℝ) :
    (Route.prepend a p).eval 0 t = AffineMap.lineMap a p.start t := rfl

/-- Every old segment retains its orientation and local real parameter after prepending. -/
theorem eval_prepend_succ (a : ℂ) (p : Route) (i : Fin p.segments) (t : ℝ) :
    (Route.prepend a p).eval i.succ t = p.eval i t := by
  simp only [eval, prepend, Fin.castSucc_succ, Fin.cases_succ]

/-- Every old segment retains its orientation and local real parameter after appending. -/
theorem eval_append_castSucc (p : Route) (b : ℂ) (i : Fin p.segments) (t : ℝ) :
    (p.append b).eval i.castSucc t = p.eval i t := by
  simp only [eval, append, Fin.succ_castSucc, Fin.lastCases_castSucc]

/-- The new final segment has its full real affine parameter. -/
theorem eval_append_last (p : Route) (b : ℂ) (t : ℝ) :
    (p.append b).eval (Fin.last p.segments) t = AffineMap.lineMap p.finish b t := by
  simp [eval, append, finish, segments]

/-- Prepending changes only the start endpoint. -/
@[simp] theorem endpoint_prepend (a : ℂ) (p : Route) (b : Bool) :
    (Route.prepend a p).endpoint b = if b then p.finish else a := by
  cases b
  · rfl
  · simp [endpoint, finish, prepend, segments, ← Fin.succ_last]

/-- Appending changes only the finish endpoint. -/
@[simp] theorem endpoint_append (p : Route) (b : ℂ) (side : Bool) :
    (p.append b).endpoint side = if side then b else p.start := by
  cases side
  · simp only [endpoint, Bool.false_eq_true, ↓reduceIte, start, append]
    change Fin.lastCases b p.point (0 : Fin (p.bends + 2)).castSucc = p.point 0
    rw [Fin.lastCases_castSucc]
  · simp [endpoint, finish, append, segments]

/-- The new start germ is the added segment; the old final outgoing germ is unchanged. -/
@[simp] theorem germ_prepend (a : ℂ) (p : Route) (b : Bool) :
    (Route.prepend a p).germ b = if b then p.germ true else p.start - a := by
  cases b
  · rfl
  · simp only [germ, ↓reduceIte, prepend, finish, segments, ← Fin.succ_last,
      Fin.castSucc_succ, Fin.cases_succ]

/-- The old initial germ is unchanged; the new finish germ points back along the added segment. -/
@[simp] theorem germ_append (p : Route) (b : ℂ) (side : Bool) :
    (p.append b).germ side = if side then p.finish - b else p.germ false := by
  cases side
  · simp only [germ, Bool.false_eq_true, ↓reduceIte, append, start]
    change (Fin.lastCases b p.point (0 : Fin p.segments).succ.castSucc : ℂ) -
      (Fin.lastCases b p.point (0 : Fin (p.bends + 2)).castSucc : ℂ) = _
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
  · simp [germ, append, finish, segments]

/-- Prepending shifts every old global route parameter by one. -/
theorem position_prepend_succ (a : ℂ) (p : Route) (i : Fin p.segments) (t : ℝ) :
    (Route.prepend a p).position i.succ t = 1 + p.position i t := by
  simp only [position, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- Appending preserves every old global route parameter. -/
theorem position_append_castSucc (p : Route) (b : ℂ) (i : Fin p.segments) (t : ℝ) :
    (p.append b).position i.castSucc t = p.position i t := rfl

private theorem position_eq_of_open {p : Route} (hp : p.IsSimple)
    (hopen : p.start ≠ p.finish) (i j : Fin p.segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) (heq : p.eval i s = p.eval j t) :
    p.position i s = p.position j t := by
  rcases hp i j s t hs ht heq with h | ⟨h, k⟩ | ⟨h, k⟩
  · exact h
  · exact False.elim (hopen ((p.at_eq_start i hs h).symm.trans
      (heq.trans (p.at_eq_finish j ht k))))
  · exact False.elim (hopen ((p.at_eq_start j ht k).symm.trans
      (heq.symm.trans (p.at_eq_finish i hs h))))

private theorem start_finish_ne_of_prepend_contacts {p : Route} {a : ℂ}
    (hcontact : ∀ (j : Fin p.segments) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      AffineMap.lineMap a p.start s = p.eval j t →
        (s = 1 ∧ p.AtEnd j t false) ∨ (s = 0 ∧ p.AtEnd j t true)) :
    p.start ≠ p.finish := by
  intro heq
  have hpoint : AffineMap.lineMap a p.start (1 : ℝ) =
      p.eval (Fin.last p.bends) 1 := by simp [eval, finish, heq, segments]
  have h := hcontact (Fin.last p.bends) 1 1 ⟨by norm_num, le_rfl⟩
    ⟨by norm_num, le_rfl⟩ hpoint
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · dsimp [AtEnd, position] at h
    have hn : 0 ≤ (p.bends : ℝ) := Nat.cast_nonneg _
    linarith
  · norm_num at h

/-- A simple route may be prepended with one nondegenerate segment if every contact
is either the intended join or the two distinct parameter ends of the new closed route.
The latter alternative is allowed only by actual geometric equality. -/
theorem IsSimple.prepend {p : Route} (hp : p.IsSimple) {a : ℂ} (ha : a ≠ p.start)
    (hcontact : ∀ (j : Fin p.segments) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      AffineMap.lineMap a p.start s = p.eval j t →
        (s = 1 ∧ p.AtEnd j t false) ∨ (s = 0 ∧ p.AtEnd j t true)) :
    (Route.prepend a p).IsSimple := by
  have hopen := start_finish_ne_of_prepend_contacts hcontact
  intro i j s t hs ht heq
  change Fin (p.segments + 1) at i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero =>
      change AffineMap.lineMap a p.start s = AffineMap.lineMap a p.start t at heq
      have hst := AffineMap.lineMap_injective ℝ ha heq
      exact Or.inl (congrArg _ hst)
    | succ j =>
      change AffineMap.lineMap a p.start s = p.eval j t at heq
      rcases hcontact j s t hs ht heq with ⟨hs1, ht0⟩ | ⟨hs0, ht1⟩
      · left
        rw [position_prepend_succ, show p.position j t = 0 from ht0, hs1]
        simp [position]
      · right
        left
        refine ⟨?_, ?_⟩
        · simp [AtEnd, position, hs0]
        · change (Route.prepend a p).position j.succ t = ((Route.prepend a p).segments : ℝ)
          rw [position_prepend_succ, show p.position j t = (p.segments : ℝ) from ht1,
            segments_prepend, Nat.cast_add, Nat.cast_one]
          simp [segments, Nat.cast_add, Nat.cast_one, add_comm]
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      change p.eval i s = AffineMap.lineMap a p.start t at heq
      rcases hcontact i t s ht hs heq.symm with ⟨ht1, hs0⟩ | ⟨ht0, hs1⟩
      · left
        rw [position_prepend_succ, show p.position i s = 0 from hs0, ht1]
        simp [position]
      · right
        right
        refine ⟨?_, ?_⟩
        · change (Route.prepend a p).position i.succ s = ((Route.prepend a p).segments : ℝ)
          rw [position_prepend_succ, show p.position i s = (p.segments : ℝ) from hs1,
            segments_prepend, Nat.cast_add, Nat.cast_one]
          simp [segments, Nat.cast_add, Nat.cast_one, add_comm]
        · simp [AtEnd, position, ht0]
    | succ j =>
      rw [eval_prepend_succ a p i s, eval_prepend_succ a p j t] at heq
      left
      rw [position_prepend_succ, position_prepend_succ,
        position_eq_of_open hp hopen i j hs ht heq]

private theorem start_finish_ne_of_append_contacts {p : Route} {b : ℂ}
    (hcontact : ∀ (i : Fin p.segments) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      p.eval i s = AffineMap.lineMap p.finish b t →
        (p.AtEnd i s true ∧ t = 0) ∨ (p.AtEnd i s false ∧ t = 1)) :
    p.start ≠ p.finish := by
  intro heq
  have hpoint : p.eval 0 0 = AffineMap.lineMap p.finish b (0 : ℝ) := by
    simpa only [start, eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero] using heq
  have h := hcontact 0 0 0 ⟨le_rfl, by norm_num⟩ ⟨le_rfl, by norm_num⟩ hpoint
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · dsimp [AtEnd, position, segments] at h
    have hn : 0 ≤ (p.bends : ℝ) := Nat.cast_nonneg _
    simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at h
    linarith
  · norm_num at h

/-- A simple route may be appended with one nondegenerate segment under the exact
parameter-level join and possible new-loop closure contact alternatives. -/
theorem IsSimple.append {p : Route} (hp : p.IsSimple) {b : ℂ} (hb : p.finish ≠ b)
    (hcontact : ∀ (i : Fin p.segments) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      p.eval i s = AffineMap.lineMap p.finish b t →
        (p.AtEnd i s true ∧ t = 0) ∨ (p.AtEnd i s false ∧ t = 1)) :
    (p.append b).IsSimple := by
  have hopen := start_finish_ne_of_append_contacts hcontact
  intro i j s t hs ht heq
  change Fin (p.segments + 1) at i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      rw [eval_append_last p b s, eval_append_last p b t] at heq
      have hst := AffineMap.lineMap_injective ℝ hb heq
      exact Or.inl (congrArg _ hst)
    | cast j =>
      rw [eval_append_last p b s, eval_append_castSucc p b j t] at heq
      rcases hcontact j t s ht hs heq.symm with ⟨ht1, hs0⟩ | ⟨ht0, hs1⟩
      · left
        rw [position_append_castSucc, show p.position j t = (p.segments : ℝ) from ht1]
        simp [position, hs0]
      · right
        right
        refine ⟨?_, ?_⟩
        · simp [AtEnd, position, hs1, segments]
        · exact ht0
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [eval_append_castSucc p b i s, eval_append_last p b t] at heq
      rcases hcontact i s t hs ht heq with ⟨hs1, ht0⟩ | ⟨hs0, ht1⟩
      · left
        rw [position_append_castSucc, show p.position i s = (p.segments : ℝ) from hs1]
        simp [position, ht0]
      · right
        left
        refine ⟨hs0, ?_⟩
        simp [AtEnd, position, ht1, segments]
    | cast j =>
      rw [eval_append_castSucc p b i s, eval_append_castSucc p b j t] at heq
      left
      exact position_eq_of_open hp hopen i j hs ht heq

/-- Simplicity rejects a degenerate newly prepended segment. -/
theorem IsSimple.prepend_ne {p : Route} {a : ℂ} (h : (Route.prepend a p).IsSimple) :
    a ≠ p.start := h.segment_ne 0

/-- Simplicity rejects a degenerate newly appended segment. -/
theorem IsSimple.append_ne {p : Route} {b : ℂ} (h : (p.append b).IsSimple) :
    p.finish ≠ b := by
  have hne := h.segment_ne (Fin.last p.segments)
  simpa [Route.append, finish, segments] using hne

/-- A route that was already closed cannot be extended at its start while remaining
simple: its two old end occurrences would become an interior contact. -/
theorem IsSimple.prepend_start_ne_finish {p : Route} {a : ℂ}
    (h : (Route.prepend a p).IsSimple) : p.start ≠ p.finish := by
  intro heq
  have heval : (Route.prepend a p).eval 0 1 =
      (Route.prepend a p).eval (Fin.last p.bends).succ 1 := by
    rw [eval_prepend_zero a p 1, eval_prepend_succ a p (Fin.last p.bends) 1]
    simpa [eval, finish, segments] using heq
  have hfirst : (Route.prepend a p).position 0 1 = 1 := by simp [position]
  have hlast : (Route.prepend a p).position (Fin.last p.bends).succ 1 =
      (p.segments : ℝ) + 1 := by
    rw [position_prepend_succ]
    simp [position, segments, Nat.cast_add, Nat.cast_one, add_comm]
  have hn : 1 ≤ (p.segments : ℝ) := by exact_mod_cast Nat.le_add_left 1 p.bends
  rcases h 0 (Fin.last p.bends).succ 1 1 ⟨by norm_num, le_rfl⟩
      ⟨by norm_num, le_rfl⟩ heval with h | ⟨h, _⟩ | ⟨h, _⟩
  · rw [hfirst, hlast] at h
    linarith
  · change (Route.prepend a p).position 0 1 = 0 at h
    rw [hfirst] at h
    norm_num at h
  · change (Route.prepend a p).position 0 1 = ((Route.prepend a p).segments : ℝ) at h
    rw [hfirst, segments_prepend, Nat.cast_add, Nat.cast_one] at h
    linarith

/-- A route that was already closed cannot be extended at its finish while remaining
simple. The old finish is an interior parameter after appending. -/
theorem IsSimple.append_start_ne_finish {p : Route} {b : ℂ}
    (h : (p.append b).IsSimple) : p.start ≠ p.finish := by
  intro heq
  have heval : (p.append b).eval (0 : Fin p.segments).castSucc 0 =
      (p.append b).eval (Fin.last p.segments) 0 := by
    rw [eval_append_castSucc, eval_append_last]
    simpa only [eval, AffineMap.lineMap_apply_zero, start, Fin.castSucc_zero] using heq
  have hfirst : (p.append b).position (0 : Fin p.segments).castSucc 0 = 0 := by
    simp [position]
  have hlast : (p.append b).position (Fin.last p.segments) 0 = (p.segments : ℝ) := by
    simp [position]
  have hn : 1 ≤ (p.segments : ℝ) := by exact_mod_cast Nat.le_add_left 1 p.bends
  rcases h (0 : Fin p.segments).castSucc (Fin.last p.segments) 0 0
      ⟨le_rfl, by norm_num⟩ ⟨le_rfl, by norm_num⟩ heval with h | ⟨_, h⟩ | ⟨h, _⟩
  · rw [hfirst, hlast] at h
    linarith
  · change (p.append b).position (Fin.last p.segments) 0 = ((p.append b).segments : ℝ) at h
    rw [hlast, segments_append, Nat.cast_add, Nat.cast_one] at h
    norm_num [segments] at h
  · change (p.append b).position (0 : Fin p.segments).castSucc 0 =
      ((p.append b).segments : ℝ) at h
    rw [hfirst, segments_append, Nat.cast_add, Nat.cast_one] at h
    linarith

end Cslib.Polygonal.Route
