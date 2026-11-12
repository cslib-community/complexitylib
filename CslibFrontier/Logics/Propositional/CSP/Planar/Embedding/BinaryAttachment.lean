/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Attachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AttachmentLabels
import Mathlib.Tactic.FinCases
import Batteries.Data.List.Lemmas

/-!
# Attaching an ordered two-port body at any old coordinate

The remaining external port is a fresh last free name. Its boundary marker is inserted
immediately before the selected old marker. This explicit boundary word need not be the
canonical enlarged free order. Later hiding and identification use this actual word.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- The fresh last name is inserted just before old coordinate `j`; all old coordinates
retain their order and are cast into the enlarged free block. -/
@[expose] def binaryAttachmentPorts (k a : ℕ) (j : Fin k) : List (Fin (k + 1) ⊕ Fin a) :=
  let old := List.ofFn (fun i : Fin k => (Sum.inl i.castSucc : Fin (k + 1) ⊕ Fin a))
  old.take j.val ++ Sum.inl (Fin.last k) :: old.drop j.val

/-- The explicit noncanonical enlarged boundary contains distinct actual free labels. -/
theorem nodup_binaryAttachmentPorts (k a : ℕ) (j : Fin k) :
    (binaryAttachmentPorts k a j).Nodup := by
  let output : List (Fin (k + 1) ⊕ Fin a) := List.ofFn (fun i : Fin k => Sum.inl i.castSucc)
  have hno : output.Nodup := List.nodup_ofFn.mpr
    (fun i q he => Fin.castSucc_injective _ (Sum.inl.inj he))
  have hlast : Sum.inl (Fin.last k) ∉ output := by
    intro he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    have hv := congrArg Fin.val (Sum.inl.inj hi)
    have hb := i.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  have hn := List.nodup_cons.mpr ⟨hlast, hno⟩
  have hp := (List.perm_append_comm (l₁ := [Sum.inl (Fin.last k)])
    (l₂ := output.take j.val)).append_right (output.drop j.val)
  have hp' : (Sum.inl (Fin.last k) :: output).Perm
      (output.take j.val ++ Sum.inl (Fin.last k) :: output.drop j.val) := by
    simpa only [List.singleton_append, List.cons_append, List.append_assoc,
      List.take_append_drop, List.nil_append] using hp
  exact hn.perm hp'

/-- Exactly one fresh free marker is added to the existing `k` markers. -/
theorem length_binaryAttachmentPorts (k a : ℕ) (j : Fin k) :
    (binaryAttachmentPorts k a j).length = k + 1 := by
  simp only [binaryAttachmentPorts, List.length_append, List.length_take, List.length_cons,
    List.length_drop, List.length_ofFn]
  rw [Nat.min_eq_left j.isLt.le]
  omega

/-- Remove the selected old marker after the insertion, then swap its name with the fresh
last name. The remaining word is exactly the old canonical free order. -/
theorem eraseIdx_binaryAttachmentPorts_swap (k a : ℕ) (j : Fin k) :
    ((binaryAttachmentPorts k a j).eraseIdx (j.val + 1)).map
        (Sum.map (Equiv.swap j.castSucc (Fin.last k)) id) =
      List.ofFn (fun i : Fin k => (Sum.inl i.castSucc : Fin (k + 1) ⊕ Fin a)) := by
  let old : List (Fin (k + 1) ⊕ Fin a) := List.ofFn (fun i : Fin k => Sum.inl i.castSucc)
  have hj : j.val < old.length := by simpa only [old, List.length_ofFn] using j.isLt
  have htake : (old.take j.val).length = j.val := by
    simp only [List.length_take, old, List.length_ofFn, Nat.min_eq_left j.isLt.le]
  have herase : (binaryAttachmentPorts k a j).eraseIdx (j.val + 1) =
      old.set j.val (Sum.inl (Fin.last k)) := by
    change (old.take j.val ++ Sum.inl (Fin.last k) :: old.drop j.val).eraseIdx (j.val + 1) = _
    rw [List.eraseIdx_append_of_length_le (by rw [htake]; omega), htake]
    simp only [Nat.add_sub_cancel_left]
    rw [List.drop_eq_getElem_cons hj]
    simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero]
    exact (List.set_eq_take_cons_drop (Sum.inl (Fin.last k)) hj).symm
  rw [herase]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_set, old]
  · intro i hi hb
    have hib : i < k := by simpa only [old, List.length_ofFn] using hb
    rw [List.getElem_map]
    by_cases he : j.val = i
    · subst i
      rw [List.getElem_set_self (by simpa only [List.length_set] using hj)]
      simp only [List.getElem_ofFn]
      change Sum.inl (Equiv.swap j.castSucc (Fin.last k) (Fin.last k)) = Sum.inl j.castSucc
      rw [Equiv.swap_apply_right]
    · rw [List.getElem_set_ne he]
      simp only [old, List.getElem_ofFn]
      change Sum.inl (Equiv.swap j.castSucc (Fin.last k) (Fin.castSucc ⟨i, hib⟩)) =
        Sum.inl (Fin.castSucc ⟨i, hib⟩)
      rw [Equiv.swap_apply_of_ne_of_ne ?_ (Fin.castSucc_ne_last _)]
      intro he'
      exact he (congrArg Fin.val he').symm

/-- Source binary argument order starting with the other port and ending at the attachment.
At two ports both cases are positive cyclic shifts, never a higher-arity reflection. -/
noncomputable def GadgetWitness.binaryBoundary {S : Set (Fin 2 → Bool)}
    {d : PPGadget arity sem S} (v : GadgetWitness d) (t : Fin 2) :
    Witness d.body [Sum.inl t.rev, Sum.inl t] := by
  let v' : Witness d.body [Sum.inl (0 : Fin 2), Sum.inl 1] := ⟨v.certificate, v.accepted⟩
  refine Fin.cases ?_ (fun i => ?_) t
  · exact v'.rotateCons (by simp)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact v'

/-- The actual boundary after attachment uses the new last name immediately before `j`.
The body rows are exact disjoint copies followed by the proved one-pair label map. -/
noncomputable def GadgetWitness.attachBinary {k : ℕ} {R : Set (Fin k → Bool)}
    {S : Set (Fin 2 → Bool)} {g : PPGadget arity sem R} {d : PPGadget arity sem S}
    (w : GadgetWitness g) (v : GadgetWitness d) (j : Fin k) (t : Fin 2) :
    Witness ((g.body.relabel Sum.inl ++ d.body.relabel Sum.inr).relabel
      (attachPortLabel k g.numAux d.numAux j t))
      ((List.ofFn (fun i : Fin k => (Sum.inl i.castSucc : Fin (k + 1) ⊕
        Fin (g.numAux + d.numAux)))).take j.val ++
          Sum.inl (Fin.last k) :: (List.ofFn (fun i : Fin k =>
            (Sum.inl i.castSucc : Fin (k + 1) ⊕ Fin (g.numAux + d.numAux)))).drop j.val) := by
  let ports : List (Fin k ⊕ Fin g.numAux) := List.ofFn Sum.inl
  let output : List (Fin (k + 1) ⊕ Fin (g.numAux + d.numAux)) :=
    List.ofFn (fun i : Fin k => Sum.inl i.castSucc)
  let left := ports.take j.val
  let right := ports.drop (j.val + 1)
  let f := attachPortLabel k g.numAux d.numAux j t
  have hj : j.val < ports.length := by simpa only [ports, List.length_ofFn] using j.isLt
  have hsplit : left ++ Sum.inl j :: right = ports := by
    have he : ports[j.val] = Sum.inl j := by simp only [ports, List.getElem_ofFn]
    change ports.take j.val ++ Sum.inl j :: ports.drop (j.val + 1) = ports
    rw [← he, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let w' : Witness g.body (left ++ Sum.inl j :: right) :=
    ⟨w.certificate, by rw [hsplit]; exact w.accepted⟩
  let v' : Witness d.body ([Sum.inl t.rev] ++ [Sum.inl t]) := v.binaryBoundary t
  have ht : t.rev ≠ t := by fin_cases t <;> decide
  have hmap : ports.map (fun a => f (Sum.inl a)) = output := by
    simp only [ports, List.map_ofFn]
    rfl
  have hout : ((left.map Sum.inl ++ [Sum.inl t.rev].map Sum.inr) ++
      Sum.inr (Sum.inl t) :: right.map Sum.inl).map f =
        output.take j.val ++ Sum.inl (Fin.last k) :: output.drop j.val := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
    have hl : left.map (f ∘ Sum.inl) = output.take j.val := by
      change (ports.take j.val).map (fun a => f (Sum.inl a)) = _
      rw [List.map_take, hmap]
    have hr : right.map (f ∘ Sum.inl) = output.drop (j.val + 1) := by
      change (ports.drop (j.val + 1)).map (fun a => f (Sum.inl a)) = _
      rw [List.map_drop, hmap]
    rw [hl, hr]
    have hjo : j.val < output.length := by simpa only [output, List.length_ofFn] using j.isLt
    rw [List.drop_eq_getElem_cons hjo]
    have hjv : output[j.val] = Sum.inl j.castSucc := by simp only [output, List.getElem_ofFn]
    rw [hjv]
    simp only [f, attachPortLabel, Sum.elim_inr, Sum.map_inl, ht, ite_false, ite_true,
      List.append_assoc, List.singleton_append]
  have hnout := nodup_binaryAttachmentPorts k (g.numAux + d.numAux) j
  let h := w'.attachDisjoint v' f (by rw [hsplit]; exact List.nodup_ofFn.mpr Sum.inl_injective)
    (by simp [ht]) (attachPortLabel_kernel k g.numAux d.numAux j t)
    (by rw [hout]; exact hnout)
  let certificate := h.certificate
  refine ⟨certificate, ?_⟩
  have he := congrArg (fun labels => verify
    ((g.body.relabel Sum.inl ++ d.body.relabel Sum.inr).relabel f) labels certificate) hout
  exact he ▸ h.accepted

end Cslib.Complexity.CSP.OrderedBoundary
