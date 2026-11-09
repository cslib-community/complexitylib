/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.Embedding.Probe
public import Complexity.Logics.Propositional.CSP.Planar.Embedding.BoundaryDeletion
public import Complexity.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import Complexity.Logics.Propositional.CSP.Planar.Construction.Gadget
import Complexity.Foundations.Data.List.OfFnPositions

/-!
# Ordered existential projection on actual gadget bodies

Hiding any selected free port deletes its structural boundary marker, then applies the exact
`PPGadget.project` variable map. The first-port specialization retains its simpler literal
prefix program; arbitrary positions use finite cyclic transport and restore survivor order.
Original relation arguments are unchanged, and the newly
hidden port precedes the old auxiliary block. All numerical and argument-order checks are
supplied internally by the source witness and actual last-edge surgery.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private theorem projectPort_injective (n a : ℕ) (j : Fin (n + 1)) :
    Function.Injective (PPGadget.substitutePort a (PPGadget.hidePort j)) := by
  let back : Fin n ⊕ Fin (1 + a) → Fin (n + 1) ⊕ Fin a :=
    Sum.elim (fun i => Sum.inl (j.succAbove i)) (Fin.addCases (fun _ => Sum.inl j) Sum.inr)
  apply Function.LeftInverse.injective (g := back)
  intro x
  cases x with
  | inl i =>
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩ <;>
      simp [back, PPGadget.substitutePort, PPGadget.hidePort]
  | inr i => simp [back, PPGadget.substitutePort]

/-- The existing semantic gadget's first-port projection has an internally supplied ordered
actual-body realization. Its output body is exactly `PPGadget.project`, with one fresh hidden
label before the old auxiliaries; no auxiliary relation symbol or embedding provider is added. -/
def GadgetWitness.projectHead {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) : GadgetWitness (g.project 0) := by
  let ports : List (Fin (n + 1) ⊕ Fin g.numAux) := List.ofFn (fun i : Fin n => Sum.inl i.succ)
  let hw : Witness g.body (Sum.inl 0 :: ports) := ⟨w.certificate, by
    simpa only [List.ofFn_succ] using w.accepted⟩
  have hn : ports.Nodup := List.nodup_ofFn.mpr (fun i j h =>
    (Fin.succ_injective n) (Sum.inl.inj h))
  let h := (hw.forgetHead hn).relabel
    (PPGadget.substitutePort g.numAux (PPGadget.hidePort (0 : Fin (n + 1))))
    (fun _ _ _ _ he => projectPort_injective n g.numAux 0 he)
  have hp : ports.map (PPGadget.substitutePort g.numAux (PPGadget.hidePort (0 : Fin (n + 1)))) =
      List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin (1 + g.numAux)) := by
    simp only [ports, List.map_ofFn]
    congr 1
  refine ⟨h.certificate, ?_⟩
  change verify (g.body.relabel (PPGadget.substitutePort g.numAux
    (PPGadget.hidePort (0 : Fin (n + 1))))) (List.ofFn Sum.inl) h.certificate = true
  rw [← hp]
  exact h.accepted

/-- The first-port projection's supplied certificate is exactly the original table
restricted to its body and remaining probe occurrences. This equation exposes the actual
program without exposing proof-only construction helpers. -/
theorem GadgetWitness.projectHead_certificate {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) :
    w.projectHead.certificate = restrictPrefix (2 * (g.body.occurrences.length + n))
      w.certificate := by
  change restrictPrefix (2 * (probeBody g.body
    (List.ofFn (fun i : Fin n => Sum.inl i.succ))).occurrences.length) w.certificate = _
  rw [length_occurrences_probeBody, List.length_ofFn]

/-- Existential deletion of any selected free port has an internally supplied ordered
realization on exactly the existing semantic `PPGadget.project j` body. The original argument
scopes are retained; the hidden port becomes fresh auxiliary zero. All surviving free-port
names and their inherited order are proved through the actual constructors. -/
noncomputable def GadgetWitness.project {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) (j : Fin (n + 1)) :
    GadgetWitness (g.project j) := by
  have hn : (List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux)).Nodup :=
    List.nodup_ofFn.mpr Sum.inl_injective
  let f := PPGadget.substitutePort g.numAux (PPGadget.hidePort j)
  let h := (w.forgetAt j.val hn (by simpa only [List.length_ofFn] using j.isLt)).relabel f
    (fun _ _ _ _ he => projectPort_injective n g.numAux j he)
  have hp : ((List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux)).eraseIdx
      j.val).map f = List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin (1 + g.numAux)) := by
    rw [List.eraseIdx_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp [f, PPGadget.substitutePort, PPGadget.hidePort]
  refine ⟨h.certificate, ?_⟩
  change verify (g.body.relabel f) (List.ofFn Sum.inl) h.certificate = true
  rw [← hp]
  exact h.accepted

end Cslib.Complexity.CSP.OrderedBoundary
