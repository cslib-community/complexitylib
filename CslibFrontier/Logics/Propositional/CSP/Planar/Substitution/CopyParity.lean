/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyOccurrences
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VertexParity

/-!
# Parity on actual copied constraint fibers

A target vertex-even labeling has zero sum on every original gadget body's copied constraint.
The exact copy map proves the complete target fiber internally, retaining indexed duplicate
rows, repeated argument names and arbitrary empty bodies.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Every actual copied body constraint inherits even parity from the complete target
vertex-even labeling. No local planarity or source validity assumption is needed. -/
theorem sum_copied_constraint_eq_false
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x) :
    (((CSP.incidenceList (gadgets F[i.val].rel).body).filter
      (fun p => decide (p.1 = o.1))).map fun p =>
        x (incidenceDart (replacementOccurrence gadgets B F i p) true).1).sum = false := by
  let T := replaceGadgets B (fun r => (gadgets r).template) F
  let selected := (CSP.incidenceList (gadgets F[i.val].rel).body).filter
    (fun p => decide (p.1 = o.1))
  let e := replacementOccurrence gadgets B F i
  have hinj : Function.Injective (fun p => incidenceDart (e p) true) := by
    intro p q he
    have hcopy : e p = e q := incidenceDart_injective true he
    have hs : (⟨i, p⟩ : (j : Fin F.length) × (gadgets F[j.val].rel).body.Occurrence) = ⟨i, q⟩ :=
      replacementOccurrence_injective gadgets B F hcopy
    exact eq_of_heq (Sigma.mk.inj hs).2
  have hn : (selected.map fun p => incidenceDart (e p) true).Nodup :=
    ((CSP.incidenceList_nodup _).filter _).map hinj
  have hw (d : Dart (incidenceGraph T)) :
      d ∈ selected.map (fun p => incidenceDart (e p) true) ↔
        d.vertex = (incidenceDart (e o) true).vertex := by
    constructor
    · intro hd
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
      have hrow : p.1 = o.1 := of_decide_eq_true (List.mem_filter.mp hp).2
      apply (vertex_incidenceDart_eq_iff (e p) (e o) true true).mpr
      refine ⟨rfl, ?_⟩
      exact (replacementOccurrence_constraint_eq_iff gadgets B F i i p o).mpr
        ⟨rfl, congrArg Fin.val hrow⟩
    · intro hd
      obtain ⟨p, hp⟩ := exists_incidenceDart d
      have hv := (vertex_incidenceDart_eq_iff p (e o) d.2 true).mp (hp ▸ hd)
      have hcenter : p.1 = (e o).1 := by simpa only [hv.1, ite_true] using hv.2
      obtain ⟨k, q, hq⟩ := exists_replacementOccurrence gadgets B F p
      rw [← hq] at hcenter
      have hrow := (replacementOccurrence_constraint_eq_iff gadgets B F k i q o).mp hcenter
      have hki : k = i := Fin.ext hrow.1
      subst k
      refine List.mem_map.mpr ⟨q, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨CSP.mem_incidenceList q, decide_eq_true (Fin.ext hrow.2)⟩
      · exact (congrArg (fun p => incidenceDart p true) hq).trans (hv.1 ▸ hp)
  have h := hx (incidenceDart (e o) true).vertex
  rw [(incidenceGraph T).vertexParity_eq_sum_word x _ _ hn hw, List.map_map] at h
  exact h

end Cslib.Complexity.CSP.GadgetRotation
