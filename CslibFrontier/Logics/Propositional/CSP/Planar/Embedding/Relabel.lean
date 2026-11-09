/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Relabel

/-!
# Ordered actual-body boundary transport under port renaming

The same finite successor table certifies a body after an injection on its occurring and
boundary names. This transports both actual-body and probe checks without permuting darts,
reflecting argument scopes or introducing new relation symbols. Repeated boundary occurrences
are retained. The map may behave arbitrarily on unused names.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V W : Type}

/-- The structural probe follows the same pointwise port renaming as the actual body. -/
theorem probeBody_relabel (F : CSP Rel V) (ports : List V) (f : V → W) :
    (probeBody F ports).relabel f = probeBody (F.relabel f) (ports.map f) := by
  simp [probeBody, CSP.relabel, Constraint.relabel, List.map_map, Function.comp_def]

/-- The augmented occurrence word is the old word followed by the reversed boundary word. -/
theorem vars_probeBody (F : CSP Rel V) (ports : List V) :
    (probeBody F ports).vars = F.vars ++ ports.reverse := by
  simp [probeBody, CSP.vars, List.flatMap_map, List.flatMap_append]

/-- Pointwise renaming retains the body-prefix restriction of every raw successor table. -/
theorem bodyCertificate_relabel (F : CSP Rel V) (f : V → W)
    (c : Graph.RotationCertificate) : bodyCertificate (F.relabel f) c = bodyCertificate F c := by
  simp only [bodyCertificate, CSP.occurrences_relabel, List.length_map]

variable [DecidableEq V] [DecidableEq W]

/-- Rename the actual body and all boundary positions using one injection on used names.
The literal table is unchanged, including for nullaries, closed components and repeated visits. -/
@[expose] def Witness.relabel {F : CSP Rel V} {ports : List V} (w : Witness F ports) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ F.vars ∨ v ∈ ports}) :
    Witness (F.relabel f) (ports.map f) where
  certificate := w.certificate
  accepted := by
    apply (verify_eq_true_iff _ _ _).mpr
    constructor
    · rw [bodyCertificate_relabel, verifyRotationCertificate_relabel_of_injOn F f
        (fun _ hx _ hy => hf (Or.inl hx) (Or.inl hy))]
      exact w.body_accepted
    · rw [← probeBody_relabel, verifyRotationCertificate_relabel_of_injOn
        (probeBody F ports) f (by
          intro x hx y hy he
          change x ∈ (probeBody F ports).vars at hx
          change y ∈ (probeBody F ports).vars at hy
          rw [vars_probeBody, List.mem_append, List.mem_reverse] at hx hy
          exact hf hx hy he)]
      exact w.probe_accepted

/-- Port renaming retains the literal successor table, including repeated boundary visits. -/
theorem Witness.relabel_certificate {F : CSP Rel V} {ports : List V} (w : Witness F ports)
    (f : V → W) (hf : Set.InjOn f {v | v ∈ F.vars ∨ v ∈ ports}) :
    (w.relabel f hf).certificate = w.certificate := rfl

end Cslib.Complexity.CSP.OrderedBoundary
