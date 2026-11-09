/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.Embedding.Probe
public import Complexity.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import Complexity.Logics.Propositional.CSP.Planar.Construction.Gadget
public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.AdjacentIdentification
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.AppendScope
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.AppendScopeIndex
import Complexity.Logics.Propositional.CSP.Occurrence.Symbols
import Complexity.Foundations.Data.List.OfFnPositions
import Complexity.Foundations.Logic.Function.UpdateKernel
import Complexity.Foundations.GroupTheory.Perm.Fin

/-!
# Adjacent equality restriction on the actual original-language body

The first two free labels are identified at the corners supplied by their consecutive probe
arguments. The duplicate probe marker is then deleted before actual-body extraction uses
distinct surviving ports. The body is exactly the existing `PPGadget.equalDrop`, with no
equality relation added to the language. This original static realization retains arbitrary
body degree, repeated occurrences, nullaries and closed components.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private theorem foldFirstTwo_kernel (n a : ℕ) (x y : Fin (n + 2) ⊕ Fin a) :
    Sum.map (Fin.cases (0 : Fin (n + 1)) id) id x =
      Sum.map (Fin.cases (0 : Fin (n + 1)) id) id y ↔
    Function.update id (Sum.inl (1 : Fin (n + 2))) (Sum.inl (0 : Fin (n + 2))) x =
      Function.update id (Sum.inl (1 : Fin (n + 2))) (Sum.inl (0 : Fin (n + 2))) y := by
  have hk (i j : Fin (n + 2)) :
      (Fin.cases 0 id : Fin (n + 2) → Fin (n + 1)) i =
        (Fin.cases 0 id : Fin (n + 2) → Fin (n + 1)) j ↔
      i = j ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    change _ ↔ i = j ∨ (i = 0 ∧ j = Fin.succ 0) ∨ (i = Fin.succ 0 ∧ j = 0)
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [Fin.cases_zero, Fin.cases_succ, id_eq, Fin.succ_inj] <;> simp [eq_comm]
  rw [Function.update_id_apply_eq_iff]
  cases x with
  | inl x =>
    cases y with
    | inl y => simpa only [Sum.map_inl, Sum.inl.injEq] using hk x y
    | inr y => simp
  | inr x => cases y <;> simp

/-- Literal adjacent-equality table program: swap the last probe corner with the
predecessor of the penultimate probe end, then remove the last probe edge. The clocks
are the actual body/boundary counts and supplied table length, never an encoded label.
The residual arity `n` is a static parameter; no uniform binary-arity runtime bound is claimed. -/
@[expose] def equalDropCertificate {V : Type} (F : CSP Rel V) (n : ℕ)
    (c : RotationCertificate) : RotationCertificate :=
  restrictPrefix (2 * (F.occurrences.length + (n + 1)))
    (c.swapSuccessors (2 * (F.occurrences.length + n + 1))
      (c.successor.idxOf (2 * (F.occurrences.length + n))))

/-- Identify the first two free ports on exactly `PPGadget.equalDrop`. Their structural
probe arguments internally supply cofacial corners; the first duplicate marker is removed
before deriving the actual-body certificate with canonical distinct surviving free ports. -/
noncomputable def GadgetWitness.equalDrop {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) : GadgetWitness g.equalDrop := by
  let B : CSP (Option Rel) (Fin (n + 2) ⊕ Fin g.numAux) := g.body.map (fun c => (some c.1, c.2))
  let scope : Fin (n + 2) → Fin (n + 2) ⊕ Fin g.numAux := fun i => Sum.inl i.rev
  let S : CSP (Option Rel) (Fin (n + 2) ⊕ Fin g.numAux) := B ++ [(none, List.ofFn scope)]
  let o : S.Occurrence := appendOfFnOccurrenceEquiv B none scope (Sum.inr (Fin.last (n + 1)))
  let p : S.Occurrence := appendOfFnOccurrenceEquiv B none scope (Sum.inr ⟨n, by omega⟩)
  have hv0 : o.var = Sum.inl (0 : Fin (n + 2)) := by
    have he := congrArg (fun record => record.2.2)
      (record_appendOfFnOccurrenceEquiv_inr B none scope (Fin.last (n + 1)))
    change o.var = scope (Fin.last (n + 1)) at he
    rw [he]
    apply congrArg Sum.inl
    apply Fin.ext
    simp [Fin.rev]
  have hv1 : p.var = Sum.inl (1 : Fin (n + 2)) := by
    have he := congrArg (fun record => record.2.2)
      (record_appendOfFnOccurrenceEquiv_inr B none scope ⟨n, by omega⟩)
    change p.var = scope ⟨n, by omega⟩ at he
    rw [he]
    apply congrArg Sum.inl
    apply Fin.ext
    simp only [Fin.rev, Fin.val_mk, Fin.val_one]
    omega
  have hv : o.var ≠ p.var := by
    rw [hv0, hv1]
    intro he
    have hval := congrArg (fun x : Fin (n + 2) => x.val) (Sum.inl.inj he)
    simp only [Fin.val_zero, Fin.val_one] at hval
    omega
  have hsucc : argumentSuccessor p = o := by
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr]
    apply congrArg (fun i => appendOfFnOccurrenceEquiv B none scope (Sum.inr i))
    apply Fin.ext
    rw [val_finRotate]
    simp only [Fin.val_last]
    split_ifs <;> omega
  let f : Fin (n + 2) ⊕ Fin g.numAux → Fin (n + 1) ⊕ Fin g.numAux :=
    Sum.map (Fin.cases 0 id) id
  have hkernel : ∀ a ∈ S.vars, ∀ b ∈ S.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b := by
    intro a _ b _
    rw [hv0, hv1]
    exact foldFirstTwo_kernel n g.numAux a b
  have hsource : S = probeBody g.body (List.ofFn Sum.inl) := by
    simp only [S, B, scope, probeBody, List.reverse_ofFn]
  have hs : verifyRotationCertificate S w.certificate = true := by
    rw [hsource]
    exact w.probe_accepted
  have hrot := ((verifyRotationCertificate_eq_true_iff S w.certificate).mp hs).choose
  let c := identifyConsecutiveCertificate S f o p hv hkernel w.certificate hrot
  have ht := verifyRotationCertificate_identifyConsecutiveCertificate S f o p hv hkernel
    hsucc w.certificate hrot hs
  have hpmap : (List.ofFn (Sum.inl : Fin (n + 2) → Fin (n + 2) ⊕ Fin g.numAux)).map f =
      Sum.inl 0 :: List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux) := by
    rw [List.ofFn_succ, List.map_cons, List.map_ofFn]
    rfl
  have hprobe : verifyRotationCertificate
      (probeBody (g.body.relabel f) (Sum.inl 0 :: List.ofFn Sum.inl)) c = true := by
    rw [← hpmap, ← probeBody_relabel, ← hsource]
    exact ht
  have htail := verifyRotationCertificate_restrictPrefix_probe_cons
    (g.body.relabel f) (Sum.inl 0) (List.ofFn Sum.inl) c hprobe
  have hn : (List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux)).Nodup :=
    List.nodup_ofFn.mpr Sum.inl_injective
  exact Witness.ofProbe hn _ htail

/-- The supplied adjacent-equality witness uses exactly the explicit outgoing swap and
bounded prefix restriction on the original raw table. No rotation search or embedding provider
appears in this generated-table equation. -/
theorem GadgetWitness.equalDrop_certificate {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) :
    w.equalDrop.certificate = equalDropCertificate g.body n w.certificate := by
  unfold GadgetWitness.equalDrop
  change restrictPrefix _ (identifyConsecutiveCertificate _ _ _ _ _ _ _ _) = _
  rw [identifyConsecutiveCertificate_eq_swapSuccessors]
  simp only [Dart.index, incidenceDart, incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr,
    Bool.toNat_false, Nat.add_zero, length_occurrences_probeBody, CSP.occurrences_relabel,
    List.length_map, List.length_ofFn, Fin.val_last, equalDropCertificate,
    CSP.occurrences_mapRelation]
  rfl

end Cslib.Complexity.CSP.OrderedBoundary
