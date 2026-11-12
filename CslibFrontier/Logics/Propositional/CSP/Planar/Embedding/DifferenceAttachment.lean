/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BinaryAttachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
import CslibFrontier.Foundations.Data.List.OfFnPositions
import Mathlib.Tactic.FinCases

/-!
# Disequality deletion on the exact original-language body

Attach the first disequality port at old coordinate zero using different components,
hide that boundary marker, and identify the remaining consecutive pair. The two joins
derive their own component/cofacial guards. The auxiliary blocks are precisely those of
the existing `differentDrop` interpreter, with the hidden old coordinate first.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private def foldLast (n a : ℕ) : Fin (n + 2) ⊕ Fin a → Fin (n + 1) ⊕ Fin a :=
  Sum.map (Fin.lastCases 0 id) id

private theorem foldLast_kernel (n a : ℕ) (u v : Fin (n + 2) ⊕ Fin a) :
    foldLast n a u = foldLast n a v ↔
      Function.update id (Sum.inl 0) (Sum.inl (Fin.last (n + 1))) u =
        Function.update id (Sum.inl 0) (Sum.inl (Fin.last (n + 1))) v := by
  rw [Function.update_id_apply_eq_iff]
  cases u with
  | inl i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · cases v with
      | inl q =>
        rcases Fin.eq_castSucc_or_eq_last q with ⟨q, rfl⟩ | rfl
        · simp [foldLast, Fin.ext_iff, -Fin.val_eq_zero_iff]
          omega
        · simp [foldLast, Fin.ext_iff, -Fin.val_eq_zero_iff]
          omega
      | inr q => simp [foldLast]
    · cases v with
      | inl q =>
        rcases Fin.eq_castSucc_or_eq_last q with ⟨q, rfl⟩ | rfl
        · simp [foldLast, Fin.ext_iff, -Fin.val_eq_zero_iff]
          omega
        · simp [foldLast]
      | inr q => simp [foldLast]
  | inr i =>
    cases v with
    | inl q =>
      rcases Fin.eq_castSucc_or_eq_last q with ⟨q, rfl⟩ | rfl
      all_goals simp [foldLast]
    | inr q => simp [foldLast]

private theorem different_body {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
    (g : PPGadget arity sem R) (d : PPGadget arity sem RelationMinor.disequality) :
    ((((g.body.relabel Sum.inl ++ d.body.relabel Sum.inr).relabel
      (attachPortLabel (n + 2) g.numAux d.numAux 0 0)).relabel
        (PPGadget.substitutePort (g.numAux + d.numAux)
          (PPGadget.hidePort (0 : Fin (n + 3))))).relabel
          (foldLast n (1 + (g.numAux + d.numAux)))) = (g.differentDrop d).body := by
  simp only [PPGadget.differentDrop, PPGadget.project, PPGadget.retarget, PPGadget.substitute,
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
      cases i using Fin.cases <;>
        simp [attachPortLabel, foldLast, PPGadget.substitutePort, PPGadget.hidePort]
    | inr i => simp [attachPortLabel, foldLast, PPGadget.substitutePort]
  · apply List.map_congr_left
    rintro ⟨r, scope⟩ _
    congr 1
    apply List.map_congr_left
    intro z _
    cases z with
    | inl i =>
      fin_cases i <;> simp [attachPortLabel, foldLast, PPGadget.substitutePort, PPGadget.hidePort]
    | inr i => simp [attachPortLabel, foldLast, PPGadget.substitutePort]

/-- The existing first-pair disequality deletion has an actual ordered numerical witness
on exactly its original body. No pin, disequality or target-genus provider remains beyond
the supplied actual source gadget witnesses. -/
noncomputable def GadgetWitness.differentDrop {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
    {g : PPGadget arity sem R} {d : PPGadget arity sem RelationMinor.disequality}
    (w : GadgetWitness g) (v : GadgetWitness d) : GadgetWitness (g.differentDrop d) := by
  let F := (g.body.relabel Sum.inl ++ d.body.relabel Sum.inr).relabel
    (attachPortLabel (n + 2) g.numAux d.numAux 0 0)
  let P := PPGadget.substitutePort (g.numAux + d.numAux) (PPGadget.hidePort (0 : Fin (n + 3)))
  let first : Witness F (Sum.inl (Fin.last (n + 2)) ::
      List.ofFn (fun i : Fin (n + 2) => Sum.inl i.castSucc)) := w.attachBinary v 0 0
  let projected := first.relabel P (fun _ _ _ _ he =>
    projectPort_injective (n + 2) (g.numAux + d.numAux) 0 he)
  have hPlast : P (Sum.inl (Fin.last (n + 2))) = Sum.inl (Fin.last (n + 1)) := by
    change P (Sum.inl (Fin.succ (Fin.last (n + 1)))) = _
    simp [P, PPGadget.substitutePort, PPGadget.hidePort]
  have hPzero : P (Sum.inl 0) = Sum.inr 0 := by
    change Sum.inr (Fin.castAdd (g.numAux + d.numAux) (0 : Fin 1)) =
      (Sum.inr 0 : Fin (n + 2) ⊕ Fin (1 + (g.numAux + d.numAux)))
    apply congrArg Sum.inr
    apply Fin.ext
    rfl
  have hPsucc (i : Fin (n + 1)) : P (Sum.inl i.succ.castSucc) = Sum.inl i.castSucc := by
    simp [P, PPGadget.substitutePort, PPGadget.hidePort]
  have hports : (Sum.inl (Fin.last (n + 2)) ::
      List.ofFn (fun i : Fin (n + 2) => Sum.inl i.castSucc)).map P =
        Sum.inl (Fin.last (n + 1)) :: Sum.inr 0 ::
          List.ofFn (fun i : Fin (n + 1) => Sum.inl i.castSucc) := by
    rw [List.map_cons, List.ofFn_succ, List.map_cons, List.map_ofFn]
    change P (Sum.inl (Fin.last (n + 2))) :: P (Sum.inl 0) ::
      List.ofFn (fun i : Fin (n + 1) => P (Sum.inl i.succ.castSucc)) = _
    rw [hPlast, hPzero]
    simp only [hPsucc]
  have hn := (nodup_binaryAttachmentPorts (n + 2) (g.numAux + d.numAux) 0).map
    (projectPort_injective (n + 2) (g.numAux + d.numAux) 0)
  change ((Sum.inl (Fin.last (n + 2)) ::
    List.ofFn (fun i : Fin (n + 2) => Sum.inl i.castSucc)).map P).Nodup at hn
  rw [hports] at hn
  let projected' : Witness (F.relabel P) (Sum.inl (Fin.last (n + 1)) :: Sum.inr 0 ::
      List.ofFn (fun i : Fin (n + 1) => Sum.inl i.castSucc)) :=
    ⟨projected.certificate, by rw [← hports]; exact projected.accepted⟩
  let deleted := projected'.forgetAt 1 hn (by simp)
  have hdelword : (Sum.inl (Fin.last (n + 1)) :: Sum.inr (0 : Fin (1 +
      (g.numAux + d.numAux))) :: List.ofFn (fun i : Fin (n + 1) => Sum.inl i.castSucc)).eraseIdx 1 =
        Sum.inl (Fin.last (n + 1)) :: Sum.inl 0 ::
          List.ofFn (fun i : Fin n => Sum.inl i.succ.castSucc) := by
    simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero]
    rw [List.ofFn_succ]
    rfl
  let deletedCertificate := deleted.certificate
  let deleted' : Witness (F.relabel P) (Sum.inl (Fin.last (n + 1)) :: Sum.inl 0 ::
      List.ofFn (fun i : Fin n => Sum.inl i.succ.castSucc)) :=
    ⟨deletedCertificate, by
      have he := congrArg (fun labels => verify (F.relabel P) labels deletedCertificate) hdelword
      exact he ▸ deleted.accepted⟩
  have hword : (Sum.inl (0 : Fin (n + 2)) ::
      List.ofFn (fun i : Fin n => Sum.inl i.succ.castSucc)).map
        (foldLast n (1 + (g.numAux + d.numAux))) = List.ofFn Sum.inl := by
    change (Sum.inl (0 : Fin (n + 1)).castSucc ::
      List.ofFn (fun i : Fin n => Sum.inl i.succ.castSucc)).map
        (foldLast n (1 + (g.numAux + d.numAux))) = _
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, foldLast, Sum.map_inl,
      Fin.lastCases_castSucc, id_eq]
    exact (List.ofFn_succ (f := Sum.inl)).symm
  let final := deleted'.identifyHead (foldLast n (1 + (g.numAux + d.numAux)))
    (by simp [Fin.ext_iff]) (by intro a _ b _; exact foldLast_kernel _ _ a b)
    (by rw [hword]; exact List.nodup_ofFn.mpr Sum.inl_injective)
  let certificate := final.certificate
  refine ⟨certificate, ?_⟩
  have hp := congrArg (fun labels => verify ((F.relabel P).relabel
    (foldLast n (1 + (g.numAux + d.numAux)))) labels certificate) hword
  have hacc := hp.symm.trans final.accepted
  have hb := congrArg (fun body : CSP Rel (Fin (n + 1) ⊕ Fin (1 + (g.numAux + d.numAux))) =>
    verify body (List.ofFn Sum.inl) certificate) (different_body g d)
  exact hb ▸ hacc

end Cslib.Complexity.CSP.OrderedBoundary
