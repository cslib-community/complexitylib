/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.OccurrenceTransport
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus
import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Actual incidence transport for joining two constraint centers

The occurrence correspondence retains variable fibers and identifies exactly the two
selected constraint positions. Dense variable names remain below every constraint center.
The generic vertex merge is transported to the actual target incidence graph; the target
genus follows from source genus and actual different components.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph Graph.RotationSystem

variable {Rel Other V W : Type} [DecidableEq V] [DecidableEq W]

private theorem update_add (v a b c : ℕ) :
    Function.update id (v + b) (v + a) (v + c) = v + Function.update id b a c := by
  by_cases hc : c = b
  · subst c
    simp only [Function.update_self]
  · rw [Function.update_of_ne (by omega : v + c ≠ v + b), Function.update_of_ne hc]
    rfl

/-- Transport retained edge/end positions after the literal constraint-center merge. -/
@[expose] noncomputable def constraintJoinDartEquiv {F : CSP Rel V} {T : CSP Other W}
    (e : F.Occurrence ≃ T.Occurrence) (h k : Dart (incidenceGraph F)) :
    Dart (mergeGraph h k) ≃ Dart (incidenceGraph T) :=
  (mergeDartEquiv h k).symm.trans (occurrenceDartEquiv e)

/-- Exact endpoint guard for joining constraint centers. Variable fibers are retained;
constraint-position fibers have exactly the selected-pair kernel. -/
theorem constraintJoinDartEquiv_vertex_eq_iff {F : CSP Rel V} {T : CSP Other W}
    (e : F.Occurrence ≃ T.Occurrence) (a b : ℕ)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.numVars + a) (hk : k.vertex = F.numVars + b)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔
      Function.update id b a o.1.val = Function.update id b a p.1.val)
    (d f : Dart (mergeGraph h k)) :
    (constraintJoinDartEquiv e h k d).vertex = (constraintJoinDartEquiv e h k f).vertex ↔
      d.vertex = f.vertex := by
  obtain ⟨d, rfl⟩ := (mergeDartEquiv h k).surjective d
  obtain ⟨f, rfl⟩ := (mergeDartEquiv h k).surjective f
  simp only [constraintJoinDartEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective d
  obtain ⟨⟨p, other⟩, rfl⟩ := (incidenceDartEquiv F).surjective f
  simp only [incidenceDartEquiv_apply, occurrenceDartEquiv_apply, vertex_mergeDartEquiv]
  rw [vertex_incidenceDart_eq_iff, hv, hc]
  simp only [hh, hk, vertex_incidenceDart]
  have hbound (o : F.Occurrence) : F.distinctVars.idxOf o.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)
  have ho := hbound o
  have hp := hbound p
  have hupdate (o : F.Occurrence) : Function.update id (F.numVars + b) (F.numVars + a)
      (F.distinctVars.idxOf o.var) = F.distinctVars.idxOf o.var := by
    have := hbound o
    exact Function.update_of_ne (by omega) _ _
  cases side <;> cases other
  · simp only [Bool.false_eq_true, ite_false, true_and, hupdate]
    exact (List.idxOf_inj (CSP.mem_distinctVars.mpr o.var_mem)).symm
  · simp only [Bool.false_eq_true, ite_false, ite_true, false_and, hupdate, update_add,
      false_iff]
    omega
  · simp only [Bool.false_eq_true, ite_false, ite_true, Bool.true_eq_false, false_and,
      hupdate, update_add, false_iff]
    omega
  · simp only [ite_true, true_and, update_add]
    omega

/-- Literal outgoing swap followed by the proved target occurrence transport. -/
@[expose] noncomputable def constraintJoinRotation {F : CSP Rel V} {T : CSP Other W}
    (e : F.Occurrence ≃ T.Occurrence) (a b : ℕ) (hab : a ≠ b)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.numVars + a) (hk : k.vertex = F.numVars + b)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔
      Function.update id b a o.1.val = Function.update id b a p.1.val)
    (r : RotationSystem (incidenceGraph F)) : RotationSystem (incidenceGraph T) :=
  (r.mergeVertices h k (by rw [hh, hk]; omega)).transport (constraintJoinDartEquiv e h k)
    (constraintJoinDartEquiv_vertex_eq_iff e a b h k hh hk hv hc)

/-- Actual indexed reversals are retained through constraint-center identification. -/
theorem reverse_constraintJoinDartEquiv {F : CSP Rel V} {T : CSP Other W}
    (e : F.Occurrence ≃ T.Occurrence) (h k : Dart (incidenceGraph F))
    (d : Dart (mergeGraph h k)) :
    constraintJoinDartEquiv e h k d.reverse = (constraintJoinDartEquiv e h k d).reverse := by
  obtain ⟨d, rfl⟩ := (mergeDartEquiv h k).surjective d
  simp only [constraintJoinDartEquiv, Equiv.trans_apply, ← mergeDartEquiv_reverse,
    Equiv.symm_apply_apply, occurrenceDartEquiv_reverse]

/-- Numerical genus is derived internally from source genus and different actual components. -/
theorem numericalGenusZero_constraintJoinRotation {F : CSP Rel V} {T : CSP Other W}
    (e : F.Occurrence ≃ T.Occurrence) (a b : ℕ) (hab : a ≠ b)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.numVars + a) (hk : k.vertex = F.numVars + b)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔
      Function.update id b a o.1.val = Function.update id b a p.1.val)
    (r : RotationSystem (incidenceGraph F)) (hr : r.NumericalGenusZero)
    (hd : ¬ RotationCertificate.SameComponent (incidenceGraph F) h.vertex k.vertex) :
    (constraintJoinRotation e a b hab h k hh hk hv hc r).NumericalGenusZero := by
  have hne : h.vertex ≠ k.vertex := by rw [hh, hk]; omega
  exact (r.mergeVertices h k hne).numericalGenusZero_transport (constraintJoinDartEquiv e h k)
    (constraintJoinDartEquiv_vertex_eq_iff e a b h k hh hk hv hc)
    (reverse_constraintJoinDartEquiv e h k)
    (mergeGraph_endpoints_declared h k (incidenceVertices_declared F))
    (incidenceVertices_declared T)
    (r.numericalGenusZero_mergeVertices_of_not_sameComponent (incidenceVertices_declared F)
      hr h k hne hd)

/-- The transported successor is exactly the selected outgoing swap on old indexed darts. -/
theorem rotate_constraintJoinRotation {F : CSP Rel V} {T : CSP Other W}
    (e : F.Occurrence ≃ T.Occurrence) (a b : ℕ) (hab : a ≠ b)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.numVars + a) (hk : k.vertex = F.numVars + b)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔
      Function.update id b a o.1.val = Function.update id b a p.1.val)
    (r : RotationSystem (incidenceGraph F)) (d : Dart (incidenceGraph F)) :
    (constraintJoinRotation e a b hab h k hh hk hv hc r).rotate (occurrenceDartEquiv e d) =
      occurrenceDartEquiv e (r.rotate (Equiv.swap h k d)) := by
  simp [constraintJoinRotation, transport, constraintJoinDartEquiv, mergeVertices]

end Cslib.Complexity.CSP
