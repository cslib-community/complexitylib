/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Attachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
import CslibFrontier.Foundations.Data.List.OfFnPositions
import Mathlib.Data.List.TakeDrop

/-!
# Unary pins on the exact cofactor body

The pin's actual ordered source witness is attached at the selected free coordinate.
The exact existing cofactor label map puts the hidden coordinate first, followed by the
left and right old auxiliary blocks. Deleting its boundary marker gives the inherited
free order, including a nullary result and completely unused original free labels.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private def unaryInto (n a b : ℕ) (j : Fin (n + 1)) :
    (Fin (n + 1) ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin b) → Fin (n + 1) ⊕ Fin (a + b) :=
  Sum.elim (Sum.map id (Fin.castAdd b)) (Sum.map (fun _ => j) (Fin.natAdd a))

private def cofactorLabel (n a b : ℕ) (j : Fin (n + 1)) :
    (Fin (n + 1) ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin b) → Fin n ⊕ Fin (1 + (a + b)) :=
  PPGadget.substitutePort (a + b) (PPGadget.hidePort j) ∘ unaryInto n a b j

private theorem cofactorLabel_kernel (n a b : ℕ) (j : Fin (n + 1))
    (u v : (Fin (n + 1) ⊕ Fin a) ⊕ (Fin 1 ⊕ Fin b)) :
    cofactorLabel n a b j u = cofactorLabel n a b j v ↔
      Function.update id (Sum.inl (Sum.inl j)) (Sum.inr (Sum.inl 0)) u =
        Function.update id (Sum.inl (Sum.inl j)) (Sum.inr (Sum.inl 0)) v := by
  change PPGadget.substitutePort _ _ (unaryInto n a b j u) =
    PPGadget.substitutePort _ _ (unaryInto n a b j v) ↔ _
  rw [(projectPort_injective n (a + b) j).eq_iff, Function.update_id_apply_eq_iff]
  rcases u with (i | i) | (i | i) <;> rcases v with (k | k) | (k | k) <;>
    simp [unaryInto, Fin.ext_iff] <;> omega

private theorem cofactorLabel_body {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    (g : PPGadget arity sem R) (j : Fin (n + 1)) (b : Bool)
    (p : PPGadget arity sem (RelationMinor.pin b)) :
    ((g.body.relabel Sum.inl ++ p.body.relabel Sum.inr).relabel
      (cofactorLabel n g.numAux p.numAux j)) = (g.cofactor j b p).body := by
  simp only [PPGadget.cofactor, PPGadget.project, PPGadget.retarget, PPGadget.substitute,
    PPGadget.conj, PPGadget.relabelFree, CSP.relabel, Constraint.relabel,
    List.map_append, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  rintro ⟨r, scope⟩ _
  congr 1
  apply List.map_congr_left
  intro z _
  cases z <;> rfl

/-- Attach an actual unary pin and hide the selected coordinate on exactly `PPGadget.cofactor`.
The pin is an original-language gadget with its own witness, with no new relation symbol. -/
noncomputable def GadgetWitness.cofactor {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) (j : Fin (n + 1)) (b : Bool)
    {p : PPGadget arity sem (RelationMinor.pin b)} (v : GadgetWitness p) :
    GadgetWitness (g.cofactor j b p) := by
  let ports : List (Fin (n + 1) ⊕ Fin g.numAux) := List.ofFn Sum.inl
  let left := ports.take j.val
  let right := ports.drop (j.val + 1)
  have hj : j.val < ports.length := by simpa only [ports, List.length_ofFn] using j.isLt
  have hsplit : left ++ Sum.inl j :: right = ports := by
    have he : ports[j.val] = Sum.inl j := by simp only [ports, List.getElem_ofFn]
    change ports.take j.val ++ Sum.inl j :: ports.drop (j.val + 1) = ports
    rw [← he, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let w' : Witness g.body (left ++ Sum.inl j :: right) :=
    ⟨w.certificate, by rw [hsplit]; exact w.accepted⟩
  let v' : Witness p.body ([] ++ [Sum.inl (0 : Fin 1)]) :=
    ⟨v.certificate, by
      simpa only [List.ofFn_succ, List.ofFn_zero, List.nil_append] using v.accepted⟩
  let f := cofactorLabel n g.numAux p.numAux j
  have hxy : f (Sum.inl (Sum.inl j)) = f (Sum.inr (Sum.inl 0)) := rfl
  have hports : ((left.map Sum.inl ++ ([] : List (Fin 1 ⊕ Fin p.numAux)).map Sum.inr) ++
      Sum.inr (Sum.inl 0) :: right.map Sum.inl).map f =
      List.ofFn (fun i : Fin (n + 1) =>
        PPGadget.substitutePort (g.numAux + p.numAux) (PPGadget.hidePort j) (Sum.inl i)) := by
    simp only [List.map_nil, List.append_nil, List.map_append, List.map_cons, List.map_map]
    rw [← hxy]
    have he := congrArg (fun l => (l.map Sum.inl).map f) hsplit
    simp only [List.map_append, List.map_cons, List.map_map, ports, List.map_ofFn] at he
    exact he
  have hnout : (List.ofFn (fun i : Fin (n + 1) =>
      PPGadget.substitutePort (g.numAux + p.numAux) (PPGadget.hidePort j) (Sum.inl i))).Nodup :=
    List.nodup_ofFn.mpr ((projectPort_injective n (g.numAux + p.numAux) j).comp Sum.inl_injective)
  let h := w'.attachDisjoint v' f (by rw [hsplit]; exact List.nodup_ofFn.mpr Sum.inl_injective)
    (by simp) (cofactorLabel_kernel n g.numAux p.numAux j) (by rw [hports]; exact hnout)
  let h' : Witness ((g.body.relabel Sum.inl ++ p.body.relabel Sum.inr).relabel f)
      (List.ofFn (fun i : Fin (n + 1) =>
      PPGadget.substitutePort (g.numAux + p.numAux) (PPGadget.hidePort j) (Sum.inl i))) :=
    ⟨h.certificate, by rw [← hports]; exact h.accepted⟩
  let deleted := h'.forgetAt j.val hnout (by simpa only [List.length_ofFn] using j.isLt)
  have hfinal : (List.ofFn (fun i : Fin (n + 1) =>
      PPGadget.substitutePort (g.numAux + p.numAux) (PPGadget.hidePort j) (Sum.inl i))).eraseIdx
        j.val = List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin (1 + (g.numAux + p.numAux))) := by
    rw [List.eraseIdx_ofFn]
    congr 1
    funext i
    simp [PPGadget.substitutePort, PPGadget.hidePort]
  let certificate := deleted.certificate
  refine ⟨certificate, ?_⟩
  have hb := congrArg (fun labels : List (Fin n ⊕ Fin (1 + (g.numAux + p.numAux))) =>
    verify ((g.body.relabel Sum.inl ++ p.body.relabel Sum.inr).relabel f) labels certificate) hfinal
  have hacc := hb.symm.trans deleted.accepted
  have he := congrArg (fun F : CSP Rel (Fin n ⊕ Fin (1 + (g.numAux + p.numAux))) =>
    verify F (List.ofFn Sum.inl) certificate) (cofactorLabel_body g j b p)
  exact he ▸ hacc

end Cslib.Complexity.CSP.OrderedBoundary
