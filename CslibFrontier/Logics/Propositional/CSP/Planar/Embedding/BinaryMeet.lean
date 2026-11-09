/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Attachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AttachmentLabels
public import CslibFrontier.Logics.Propositional.CSP.Planar.Construction.Gadget
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
import Mathlib.Tactic.FinCases

/-!
# Binary intersection on the exact appended gadget body

Two ordered binary boundaries share their ports in the two-digon arrangement. The first
join uses disjoint components, and the remaining adjacent markers supply the cofacial
second join. The body is precisely `PPGadget.conj`, with left then right auxiliary blocks.
The result is restricted to arity two; no general all-port conjunction is asserted.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private def meetSecond (a : ℕ) : Fin 3 ⊕ Fin a → Fin 2 ⊕ Fin a :=
  Sum.map (fun i => if i = 0 then 0 else 1) id

private theorem meetSecond_kernel (a : ℕ) (u v : Fin 3 ⊕ Fin a) :
    meetSecond a u = meetSecond a v ↔
      Function.update id (Sum.inl 2) (Sum.inl 1) u =
        Function.update id (Sum.inl 2) (Sum.inl 1) v := by
  rw [Function.update_id_apply_eq_iff]
  cases u with
  | inl i =>
    cases v with
    | inl j => fin_cases i <;> fin_cases j <;> simp [meetSecond]
    | inr j => fin_cases i <;> simp [meetSecond]
  | inr i =>
    cases v with
    | inl j => fin_cases j <;> simp [meetSecond]
    | inr j => simp [meetSecond]

private theorem meet_body {R S : Set (Fin 2 → Bool)} (g : PPGadget arity sem R)
    (h : PPGadget arity sem S) :
    (((g.body.relabel Sum.inl ++ h.body.relabel Sum.inr).relabel
      (attachPortLabel 2 g.numAux h.numAux 0 0)).relabel (meetSecond (g.numAux + h.numAux))) =
        (g.conj h).body := by
  simp only [PPGadget.conj, CSP.relabel, Constraint.relabel, List.map_append, List.map_map,
    Function.comp_def]
  congr 1
  · apply List.map_congr_left
    rintro ⟨r, scope⟩ _
    congr 1
    apply List.map_congr_left
    intro z _
    cases z with
    | inl i => fin_cases i <;> rfl
    | inr i => rfl
  · apply List.map_congr_left
    rintro ⟨r, scope⟩ _
    congr 1
    apply List.map_congr_left
    intro z _
    cases z with
    | inl i => fin_cases i <;> rfl
    | inr i => rfl

/-- Actual arity-two conjunction has its own checked ordered numerical witness, with exact
original body rows and disjoint auxiliary blocks. Every join guard is derived internally. -/
noncomputable def GadgetWitness.binaryMeet {R S : Set (Fin 2 → Bool)}
    {g : PPGadget arity sem R} {h : PPGadget arity sem S}
    (w : GadgetWitness g) (v : GadgetWitness h) : GadgetWitness (g.conj h) := by
  let w' : Witness g.body ([] ++ Sum.inl (0 : Fin 2) :: [Sum.inl 1]) :=
    ⟨w.certificate, w.accepted⟩
  let v' : Witness h.body [Sum.inl (0 : Fin 2), Sum.inl 1] :=
    ⟨v.certificate, v.accepted⟩
  let vr := v'.rotateCons (by simp)
  let v'' : Witness h.body ([Sum.inl (1 : Fin 2)] ++ [Sum.inl 0]) := vr
  let first := w'.attachDisjoint v'' (attachPortLabel 2 g.numAux h.numAux 0 0) (by simp) (by simp)
    (attachPortLabel_kernel 2 g.numAux h.numAux 0 0) (by simp [attachPortLabel])
  let first' : Witness ((g.body.relabel Sum.inl ++ h.body.relabel Sum.inr).relabel
      (attachPortLabel 2 g.numAux h.numAux 0 0)) [Sum.inl 2, Sum.inl 0, Sum.inl 1] := first
  let rotated := first'.unrotateSnoc (ports := [Sum.inl 2, Sum.inl 0]) (p := Sum.inl 1) (by simp)
  let second := rotated.identifyHead (meetSecond (g.numAux + h.numAux)) (by simp)
    (by intro a _ b _; exact meetSecond_kernel (g.numAux + h.numAux) a b) (by simp [meetSecond])
  let second' : Witness _ [Sum.inl (1 : Fin 2), Sum.inl 0] := second
  let result := second'.rotateCons (by simp)
  let certificate := result.certificate
  refine ⟨certificate, ?_⟩
  have hacc := result.accepted
  change verify _ [Sum.inl (0 : Fin 2), Sum.inl 1] certificate = true at hacc
  have he := congrArg (fun F : CSP Rel (Fin 2 ⊕ Fin (g.numAux + h.numAux)) =>
    verify F [Sum.inl 0, Sum.inl 1] certificate) (meet_body g h)
  have ht := he ▸ hacc
  exact ht

end Cslib.Complexity.CSP.OrderedBoundary
