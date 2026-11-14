/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route

/-!
# Translating finite polygonal routes

Translation acts on every listed point and every actual segment, preserves the route
parameter and its two ends, and leaves outgoing germs unchanged.
-/

public section

namespace Cslib.Polygonal.Route

/-- Translate every point of a finite polygonal route by the same plane vector. -/
@[expose] def translate (p : Route) (z : ℂ) : Route where
  bends := p.bends
  point := fun i => z + p.point i

/-- Translation commutes with the actual affine segment evaluation. -/
@[simp] theorem eval_translate (p : Route) (z : ℂ) (i : Fin p.segments) (t : ℝ) :
    (p.translate z).eval i t = z + p.eval i t := by
  simp only [eval, translate, AffineMap.lineMap_apply_module', add_sub_add_left_eq_sub]
  ac_rfl

/-- Translation moves either endpoint by the same plane vector. -/
@[simp] theorem endpoint_translate (p : Route) (z : ℂ) (b : Bool) :
    (p.translate z).endpoint b = z + p.endpoint b := by
  cases b <;> rfl

/-- Translation preserves the actual outgoing end vectors, including both loop ends. -/
@[simp] theorem germ_translate (p : Route) (z : ℂ) (b : Bool) :
    (p.translate z).germ b = p.germ b := by
  cases b <;> simp only [germ, translate, start, finish, Bool.false_eq_true, ↓reduceIte,
    add_sub_add_left_eq_sub]
  rfl

/-- Translating a simple route preserves simplicity at every real segment parameter. -/
theorem IsSimple.translate {p : Route} (hp : p.IsSimple) (z : ℂ) :
    (p.translate z).IsSimple := by
  intro i j s t hs ht heq
  change Fin p.segments at i j
  rw [eval_translate p z i s, eval_translate p z j t, add_right_inj] at heq
  exact hp i j s t hs ht heq

end Cslib.Polygonal.Route
