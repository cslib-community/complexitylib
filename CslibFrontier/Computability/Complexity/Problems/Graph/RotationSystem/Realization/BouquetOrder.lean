/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Loop

/-!
# Laminar port ranks for numerical genus-zero loop graphs

Literal first-hit port ranks give disjoint or nested intervals for distinct indexed loops
at a common vertex. The order is derived from numerical genus zero.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- In numerical genus zero, the linear intervals of two distinct indexed loops at one
vertex are disjoint or strictly nested. This derives the ordering from the numerical
hypothesis; a noncrossing matching is not an input. -/
theorem portRank_loops_laminar
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (e f : Fin G.2.length) (hef : e ≠ f)
    (he : (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true))
    (hf : (Dart.vertex (G := G) (f, false)) = Dart.vertex (f, true))
    (hv : (Dart.vertex (G := G) (e, false)) = Dart.vertex (f, false)) :
    max (r.portRank (e, false)) (r.portRank (e, true)) <
        min (r.portRank (f, false)) (r.portRank (f, true)) ∨
      max (r.portRank (f, false)) (r.portRank (f, true)) <
        min (r.portRank (e, false)) (r.portRank (e, true)) ∨
      (min (r.portRank (e, false)) (r.portRank (e, true)) <
          min (r.portRank (f, false)) (r.portRank (f, true)) ∧
        max (r.portRank (f, false)) (r.portRank (f, true)) <
          max (r.portRank (e, false)) (r.portRank (e, true))) ∨
      (min (r.portRank (f, false)) (r.portRank (f, true)) <
          min (r.portRank (e, false)) (r.portRank (e, true)) ∧
        max (r.portRank (e, false)) (r.portRank (e, true)) <
          max (r.portRank (f, false)) (r.portRank (f, true))) := by
  have hends (i : Fin G.2.length) : (i, false) ≠ (i, true) := by simp
  have hcross (b c : Bool) : (e, b) ≠ (f, c) :=
    fun h => hef (congrArg Prod.fst h)
  have hva : (Dart.vertex (G := G) (f, false)) = Dart.vertex (e, false) := hv.symm
  have hvb : (Dart.vertex (G := G) (f, false)) = Dart.vertex (e, true) := hv.symm.trans he
  have hsame : ((e, false) ∈ r.rotationInterval (f, false) (f, true)) ↔
      ((e, true) ∈ r.rotationInterval (f, false) (f, true)) := by
    have hnot : ¬(((e, false) ∈ r.rotationInterval (f, false) (f, true)) ↔
        ((e, true) ∉ r.rotationInterval (f, false) (f, true))) := fun h =>
      r.not_alternates_loops hG hr e f hef he hf
        ⟨hends e, hends f, hcross false false, hcross false true,
          hcross true false, hcross true true, he, hf, hv, h⟩
    constructor
    · intro ha
      by_contra hb
      exact hnot ⟨fun _ => hb, fun _ => ha⟩
    · intro hb
      by_contra ha
      exact hnot ⟨fun h => False.elim (ha h), fun h => False.elim (h hb)⟩
  rw [r.mem_rotationInterval_iff_portRank _ _ _ hva (hv.trans hf)
      (hcross false false).symm (hcross false true) (hends f),
    r.mem_rotationInterval_iff_portRank _ _ _ hvb (he.symm.trans (hv.trans hf))
      (hcross true false).symm (hcross true true) (hends f)] at hsame
  have hneq (b c : Bool) : r.portRank (e, b) ≠ r.portRank (f, c) := by
    have hvertex : (Dart.vertex (G := G) (e, b)) = Dart.vertex (f, c) := by
      cases b <;> cases c <;> omega
    exact fun h => hcross b c (r.portRank_injective _ _ hvertex h)
  have haa : r.portRank (e, false) ≠ r.portRank (e, true) :=
    fun h => hends e (r.portRank_injective _ _ he h)
  have hcc : r.portRank (f, false) ≠ r.portRank (f, true) :=
    fun h => hends f (r.portRank_injective _ _ hf h)
  have hac := hneq false false
  have had := hneq false true
  have hbc := hneq true false
  have hbd := hneq true true
  by_cases hab : r.portRank (e, false) ≤ r.portRank (e, true) <;>
    by_cases hcd : r.portRank (f, false) ≤ r.portRank (f, true) <;>
    simp only [min_def, max_def, hab, hcd, ↓reduceIte] <;> omega

end Cslib.Complexity.Graph.RotationSystem
