/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Join

/-!
# Parameters of routes with attached end segments

Every actual segment parameter is either an unchanged old parameter or a parameter of
an attached end segment. The global position is recorded exactly, so contact proofs can
recover the original route ends after one or both attachments.
-/

public section

namespace Cslib.Polygonal.Route

/-- Every parameter of a prepended route is an old parameter shifted by one, or a
parameter of the new initial segment. The statement holds for every real parameter. -/
theorem prepend_eval_cases (a : ℂ) (p : Route) (i : Fin (Route.prepend a p).segments) (t : ℝ) :
    (∃ j : Fin p.segments, (Route.prepend a p).eval i t = p.eval j t ∧
      (Route.prepend a p).position i t = 1 + p.position j t) ∨
    ((Route.prepend a p).eval i t = AffineMap.lineMap a p.start t ∧
      (Route.prepend a p).position i t = t) := by
  induction i using Fin.cases with
  | zero => exact Or.inr ⟨eval_prepend_zero a p t, by simp [position]⟩
  | succ j =>
    change Fin p.segments at j
    exact Or.inl ⟨j, eval_prepend_succ a p j t, position_prepend_succ a p j t⟩

/-- Every parameter of an appended route is an unchanged old parameter or a parameter
of its new final segment, with its exact global position. -/
theorem append_eval_cases (p : Route) (b : ℂ) (i : Fin (p.append b).segments) (t : ℝ) :
    (∃ j : Fin p.segments, (p.append b).eval i t = p.eval j t ∧
      (p.append b).position i t = p.position j t) ∨
    ((p.append b).eval i t = AffineMap.lineMap p.finish b t ∧
      (p.append b).position i t = (p.segments : ℝ) + t) := by
  induction i using Fin.lastCases with
  | last => exact Or.inr ⟨eval_append_last p b t, rfl⟩
  | cast j =>
    change Fin p.segments at j
    exact Or.inl ⟨j, eval_append_castSucc p b j t, position_append_castSucc p b j t⟩

/-- Attaching both ends retains every old parameter and distinguishes both new
segments, even when the new route is closed. -/
theorem attach_eval_cases (a : ℂ) (p : Route) (b : ℂ)
    (i : Fin ((Route.prepend a p).append b).segments) (t : ℝ) :
    (∃ j : Fin p.segments, ((Route.prepend a p).append b).eval i t = p.eval j t ∧
      ((Route.prepend a p).append b).position i t = 1 + p.position j t) ∨
    (((Route.prepend a p).append b).eval i t = AffineMap.lineMap a p.start t ∧
      ((Route.prepend a p).append b).position i t = t) ∨
    (((Route.prepend a p).append b).eval i t = AffineMap.lineMap p.finish b t ∧
      ((Route.prepend a p).append b).position i t = (p.segments : ℝ) + 1 + t) := by
  rcases append_eval_cases (Route.prepend a p) b i t with ⟨j, heval, hpos⟩ | ⟨heval, hpos⟩
  · rcases prepend_eval_cases a p j t with ⟨k, heval', hpos'⟩ | ⟨heval', hpos'⟩
    · exact Or.inl ⟨k, heval.trans heval', hpos.trans hpos'⟩
    · exact Or.inr (Or.inl ⟨heval.trans heval', hpos.trans hpos'⟩)
  · right
    right
    have hfinish : (Route.prepend a p).finish = p.finish := endpoint_prepend a p true
    refine ⟨heval.trans (congrArg (fun x => AffineMap.lineMap x b t) hfinish), ?_⟩
    simpa only [segments_prepend, Nat.cast_add, Nat.cast_one] using hpos

end Cslib.Polygonal.Route
