/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Cyclic
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import CslibFrontier.Logics.Propositional.CSP.Planar.Construction.Gadget

/-!
# Cyclic rotation of the existing original-language gadget constructor

The boundary moves backwards before the actual free labels move forwards. The resulting
canonical free-port word is distinct and in its inherited positive order. The body is exactly
`PPGadget.relabelFree (fun i => i + 1)`, as used by `Construction.gadget`; no reflection or
new relation symbol is used. These are static finite realization constructions, with no
uniform preprocessing-time assertion.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- Cyclically rotate the exact existing semantic gadget body and canonical free ports.
Both the inherited boundary order and its distinctness are discharged internally. -/
noncomputable def GadgetWitness.rotate {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) :
    GadgetWitness (g.relabelFree (fun i => i + 1)) := by
  have hn : (List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux)).Nodup :=
    List.nodup_ofFn.mpr Sum.inl_injective
  let w' := w.unrotateOfFn hn
  let f : Fin (n + 1) ⊕ Fin g.numAux → Fin (n + 1) ⊕ Fin g.numAux :=
    Sum.map (fun i => i + 1) id
  have hf : Function.Injective f := Sum.map_injective.mpr ⟨by
    intro i j he
    apply (finRotate (n + 1)).injective
    simpa only [finRotate_apply] using he, Function.injective_id⟩
  let h := w'.relabel f (fun _ _ _ _ he => hf he)
  have hp : (List.ofFn ((Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux) ∘
      (finRotate (n + 1)).symm)).map f = List.ofFn Sum.inl := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change Sum.inl (((finRotate (n + 1)).symm i) + 1) = Sum.inl i
    rw [← finRotate_apply, Equiv.apply_symm_apply]
  refine ⟨h.certificate, ?_⟩
  change verify (g.body.relabel f) (List.ofFn Sum.inl) h.certificate = true
  rw [← hp]
  exact h.accepted

end Cslib.Complexity.CSP.OrderedBoundary
