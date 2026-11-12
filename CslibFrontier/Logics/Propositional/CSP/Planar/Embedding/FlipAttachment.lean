/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BinaryAttachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
import Mathlib.Tactic.FinCases

/-!
# Flipping a coordinate on the exact original-language body

The fresh exposed marker is inserted before the selected old marker. Deleting the old
marker and swapping its label with the fresh last label gives the required final order.
Thus no canonical boundary is asserted for the enlarged intermediate gadget. Hiding the
last label puts that old coordinate before the two unchanged auxiliary blocks.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private theorem flip_body {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) (j : Fin n)
    (d : PPGadget arity sem RelationMinor.disequality) :
    ((((g.body.relabel Sum.inl ++ d.body.relabel Sum.inr).relabel
      (attachPortLabel n g.numAux d.numAux j 1)).relabel
        (Sum.map (Equiv.swap j.castSucc (Fin.last n)) id)).relabel
          (PPGadget.substitutePort (g.numAux + d.numAux)
            (PPGadget.hidePort (Fin.last n)))) = (g.flip j d).body := by
  simp only [PPGadget.flip, PPGadget.project, PPGadget.retarget, PPGadget.substitute,
    PPGadget.conj, PPGadget.relabelFree, CSP.relabel, Constraint.relabel, List.map_append,
    List.map_map, Function.comp_def]
  congr 1
  · apply List.map_congr_left
    rintro ⟨r, scope⟩ _
    congr 1
    apply List.map_congr_left
    intro z _
    cases z with
    | inl i =>
      by_cases hi : i = j
      · subst i
        simp [attachPortLabel, PPGadget.flipPort, PPGadget.substitutePort]
      · have hcast : i.castSucc ≠ j.castSucc := fun he => hi (Fin.castSucc_injective _ he)
        simp [attachPortLabel, PPGadget.flipPort, PPGadget.substitutePort, hi,
          Equiv.swap_apply_of_ne_of_ne hcast (Fin.castSucc_ne_last i)]
    | inr i => simp [attachPortLabel, PPGadget.substitutePort]
  · apply List.map_congr_left
    rintro ⟨r, scope⟩ _
    congr 1
    apply List.map_congr_left
    intro z _
    cases z with
    | inl i =>
      fin_cases i <;> simp [attachPortLabel, PPGadget.substitutePort]
    | inr i => simp [attachPortLabel, PPGadget.substitutePort]

/-- The exact existing flip interpreter has an actual ordered numerical witness. Its
noncanonical enlarged boundary is used directly before hiding the old selected marker. -/
noncomputable def GadgetWitness.flip {n : ℕ} {R : Set (Fin n → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) (j : Fin n)
    {d : PPGadget arity sem RelationMinor.disequality} (v : GadgetWitness d) :
    GadgetWitness (g.flip j d) := by
  let F := (g.body.relabel Sum.inl ++ d.body.relabel Sum.inr).relabel
    (attachPortLabel n g.numAux d.numAux j 1)
  let Q := Sum.map (Equiv.swap j.castSucc (Fin.last n)) (id : Fin (g.numAux + d.numAux) → _)
  let P := PPGadget.substitutePort (g.numAux + d.numAux) (PPGadget.hidePort (Fin.last n))
  let first : Witness F (binaryAttachmentPorts n (g.numAux + d.numAux) j) :=
    w.attachBinary v j 1
  let deleted := first.forgetAt (j.val + 1) (nodup_binaryAttachmentPorts _ _ j)
    (by rw [length_binaryAttachmentPorts]; omega)
  have hQ : Function.Injective Q :=
    Sum.map_injective.mpr ⟨(Equiv.swap _ _).injective, Function.injective_id⟩
  let swapped := deleted.relabel Q (fun _ _ _ _ he => hQ he)
  have hword := eraseIdx_binaryAttachmentPorts_swap n (g.numAux + d.numAux) j
  let swappedCertificate := swapped.certificate
  let swapped' : Witness (F.relabel Q)
      (List.ofFn (fun i : Fin n => Sum.inl i.castSucc)) :=
    ⟨swappedCertificate, by
      have he := congrArg (fun labels => verify (F.relabel Q) labels swappedCertificate) hword
      exact he ▸ swapped.accepted⟩
  let final := swapped'.relabel P (fun _ _ _ _ he =>
    projectPort_injective n (g.numAux + d.numAux) (Fin.last n) he)
  have hfinal : (List.ofFn (fun i : Fin n =>
      (Sum.inl i.castSucc : Fin (n + 1) ⊕ Fin (g.numAux + d.numAux)))).map P =
        List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin (1 + (g.numAux + d.numAux))) := by
    simp [P, List.map_ofFn, Function.comp_def, PPGadget.substitutePort, PPGadget.hidePort]
  let certificate := final.certificate
  refine ⟨certificate, ?_⟩
  have hp := congrArg (fun labels => verify ((F.relabel Q).relabel P) labels certificate) hfinal
  have hacc := hp ▸ final.accepted
  have hb := congrArg (fun body : CSP Rel (Fin n ⊕ Fin (1 + (g.numAux + d.numAux))) =>
    verify body (List.ofFn Sum.inl) certificate) (flip_body g j d)
  exact hb ▸ hacc

end Cslib.Complexity.CSP.OrderedBoundary
