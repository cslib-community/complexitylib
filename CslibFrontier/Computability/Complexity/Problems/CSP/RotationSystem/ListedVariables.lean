/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentPermutation
public import CslibFrontier.Foundations.GroupTheory.Perm.ListCycles
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VertexFibers
import CslibFrontier.Foundations.GroupTheory.Perm.SumCycles

/-!
# Incidence rotations from listed variable cycles

A complete interval of occurrence positions and its exact equal-variable orbit law determine
an actual incidence rotation. Variable ends follow the listed directed cycles; constraint ends
follow the original argument permutation. The two sides are combined through a disjoint-sum
permutation, so no permutation or endpoint-fiber property is an unchecked table flag.

This is a mathematical constructor from positional invariants, without a genus assertion or
native gadget runtime. Its application to substitution must prove those invariants internally.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

private noncomputable def variableArgumentCoordinates (F : CSP Rel V) :
    Fin (incidenceGraph F).edges.length ⊕ F.Occurrence ≃ Dart (incidenceGraph F) :=
  Equiv.ofBijective
    (Sum.elim (fun i => (i, false)) (fun o => incidenceDart o true)) ⟨by
      intro x y he
      cases x with
      | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (congrArg Prod.fst he)
        | inr p => exact False.elim (Bool.false_ne_true (congrArg Prod.snd he))
      | inr o =>
        cases y with
        | inl j => exact False.elim (Bool.false_ne_true (congrArg Prod.snd he).symm)
        | inr p => exact congrArg Sum.inr (incidenceDart_injective true he), by
      rintro ⟨i, side⟩
      cases side
      · exact ⟨Sum.inl i, rfl⟩
      · obtain ⟨o, ho⟩ := exists_incidenceDart ((i, true) : Dart (incidenceGraph F))
        exact ⟨Sum.inr o, ho⟩⟩

/-- A positional variable-cycle partition with its proved variable fibers determines an
actual ordered incidence rotation. These invariants do not assert numerical genus zero. -/
noncomputable def rotationOfVariableCycles (F : CSP Rel V) (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) : RotationSystem (incidenceGraph F) where
  rotate := (variableArgumentCoordinates F).permCongr
    (Equiv.sumCongr (List.finiteCyclePermutation cycles hcover) (argumentPermutation F))
  sameCycle_iff d e := by
    obtain ⟨x, rfl⟩ := (variableArgumentCoordinates F).surjective d
    obtain ⟨y, rfl⟩ := (variableArgumentCoordinates F).surjective e
    rw [Equiv.Perm.sameCycle_equiv_iff (variableArgumentCoordinates F)
      (Equiv.sumCongr (List.finiteCyclePermutation cycles hcover) (argumentPermutation F))
      _ (fun z => by simp) x y, Equiv.Perm.sameCycle_sumCongr_iff]
    cases x with
    | inl i =>
      obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) i.val i.isLt
      have he : (⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩ :
          Fin (incidenceGraph F).edges.length) = i := Fin.ext ho
      subst i
      cases y with
      | inl j =>
        obtain ⟨p, hp⟩ := exists_incidenceEdgeIndex (F := F) j.val j.isLt
        have he : (⟨incidenceEdgeIndex p, incidenceEdgeIndex_lt p⟩ :
            Fin (incidenceGraph F).edges.length) = j := Fin.ext hp
        subst j
        change (List.finiteCyclePermutation cycles hcover).SameCycle _ _ ↔
          (incidenceDart o false).vertex = (incidenceDart p false).vertex
        rw [List.sameCycle_finiteCyclePermutation_iff, hfibers,
          vertex_incidenceDart_eq_iff]
        simp
      | inr p =>
        change False ↔ (incidenceDart o false).vertex = (incidenceDart p true).vertex
        rw [vertex_incidenceDart_eq_iff]
        simp
    | inr o =>
      cases y with
      | inl j =>
        obtain ⟨p, hp⟩ := exists_incidenceEdgeIndex (F := F) j.val j.isLt
        have he : (⟨incidenceEdgeIndex p, incidenceEdgeIndex_lt p⟩ :
            Fin (incidenceGraph F).edges.length) = j := Fin.ext hp
        subst j
        change False ↔ (incidenceDart o true).vertex = (incidenceDart p false).vertex
        rw [vertex_incidenceDart_eq_iff]
        simp
      | inr p =>
        change (argumentPermutation F).SameCycle o p ↔
          (incidenceDart o true).vertex = (incidenceDart p true).vertex
        rw [sameCycle_argumentPermutation, vertex_incidenceDart_eq_iff]
        simp

/-- The constructed constraint-side successor is exactly the original ordered scope step. -/
theorem rotate_rotationOfVariableCycles_true (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) (o : F.Occurrence) :
    (rotationOfVariableCycles F cycles hcover hfibers).rotate (incidenceDart o true) =
      incidenceDart (argumentSuccessor o) true := by
  change (variableArgumentCoordinates F).permCongr
    (Equiv.sumCongr (List.finiteCyclePermutation cycles hcover) (argumentPermutation F))
      ((variableArgumentCoordinates F) (Sum.inr o)) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

/-- Ordered scopes are preserved without a separate argument-order premise. -/
theorem respectsArgumentOrder_rotationOfVariableCycles (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) :
    RespectsArgumentOrder (rotationOfVariableCycles F cycles hcover hfibers) :=
  rotate_rotationOfVariableCycles_true cycles hcover hfibers

/-- The variable-side successor retains its exact finite occurrence position and end tag. -/
theorem rotate_rotationOfVariableCycles_false (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) (o : F.Occurrence) :
    (rotationOfVariableCycles F cycles hcover hfibers).rotate (incidenceDart o false) =
      (List.finiteCyclePermutation cycles hcover
        ⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩, false) := by
  change (variableArgumentCoordinates F).permCongr
    (Equiv.sumCongr (List.finiteCyclePermutation cycles hcover) (argumentPermutation F))
      ((variableArgumentCoordinates F) (Sum.inl
        ⟨incidenceEdgeIndex o, incidenceEdgeIndex_lt o⟩)) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

/-- At variable ends, the constructed permutation executes the actual bounded successor scan. -/
theorem val_rotate_rotationOfVariableCycles_false (cycles : List (List ℕ))
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < (incidenceGraph F).edges.length)
    (hfibers : ∀ o p : F.Occurrence,
      (List.cyclePermutation cycles).SameCycle (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔
        o.var = p.var) (hn : cycles.flatten.Nodup) (o : F.Occurrence) :
    ((rotationOfVariableCycles F cycles hcover hfibers).rotate (incidenceDart o false)).1.val =
      List.nextInCycles cycles (incidenceEdgeIndex o) := by
  rw [rotate_rotationOfVariableCycles_false]
  exact List.val_finiteCyclePermutation_eq_nextInCycles cycles hcover hn _

end Cslib.Complexity.CSP
