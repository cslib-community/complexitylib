/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.OccurrenceTransport
public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
public import Complexity.Logics.Propositional.CSP.Occurrence.ScopeReindex
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.AppendScope

/-!
# Directed cyclic reindexing of an actual last constraint scope

Every scope-position permutation supplies a numerical incidence isomorphism. Ordered
argument compatibility additionally requires commuting with the positive cyclic successor;
that condition excludes reflection at higher arity. Body constraints and their indexed
occurrences are unchanged. The selected scope is structural when used for a boundary probe.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Rel V : Type}

/-- A last-scope reindexing intertwines actual clockwise argument succession when its
positional permutation commutes with the positive cycle. Arity zero remains vacuous. -/
theorem argumentSuccessor_reindexLastScopeOccurrenceEquiv (F : CSP Rel V) (r : Rel)
    {n : ℕ} (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (hq : ∀ j, q (finRotate n j) = finRotate n (q j))
    (o : (F ++ [(r, List.ofFn scope)]).Occurrence) :
    reindexLastScopeOccurrenceEquiv F r scope q (argumentSuccessor o) =
      argumentSuccessor (reindexLastScopeOccurrenceEquiv F r scope q o) := by
  have hqs (j : Fin n) : q.symm (finRotate n j) = finRotate n (q.symm j) := by
    apply q.injective
    rw [Equiv.apply_symm_apply, hq, Equiv.apply_symm_apply]
  obtain ⟨o, rfl⟩ := (appendOfFnOccurrenceEquiv F r scope).surjective o
  cases o with
  | inl o =>
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inl,
      reindexLastScopeOccurrenceEquiv_apply, reindexLastScopeOccurrenceEquiv_apply]
    change appendOfFnOccurrenceEquiv F r (scope ∘ q) (Sum.inl (argumentSuccessor o)) =
      argumentSuccessor (appendOfFnOccurrenceEquiv F r (scope ∘ q) (Sum.inl o))
    exact (argumentSuccessor_appendOfFnOccurrenceEquiv_inl F r (scope ∘ q) o).symm
  | inr j =>
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr,
      reindexLastScopeOccurrenceEquiv_apply, reindexLastScopeOccurrenceEquiv_apply]
    change appendOfFnOccurrenceEquiv F r (scope ∘ q) (Sum.inr (q.symm (finRotate n j))) =
      argumentSuccessor (appendOfFnOccurrenceEquiv F r (scope ∘ q) (Sum.inr (q.symm j)))
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr, hqs]


private theorem reindex_variable_fibers (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (o p : (F ++ [(r, List.ofFn scope)]).Occurrence) :
    (reindexLastScopeOccurrenceEquiv F r scope q o).var =
      (reindexLastScopeOccurrenceEquiv F r scope q p).var ↔ o.var = p.var := by
  have ho := congrArg Prod.snd (header_reindexLastScopeOccurrenceEquiv F r scope q o)
  have hp := congrArg Prod.snd (header_reindexLastScopeOccurrenceEquiv F r scope q p)
  dsimp only at ho hp
  rw [ho, hp]

private theorem reindex_constraint_fibers (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (o p : (F ++ [(r, List.ofFn scope)]).Occurrence) :
    (reindexLastScopeOccurrenceEquiv F r scope q o).1 =
      (reindexLastScopeOccurrenceEquiv F r scope q p).1 ↔ o.1 = p.1 := by
  have ho := congrArg Prod.fst (header_reindexLastScopeOccurrenceEquiv F r scope q o)
  have hp := congrArg Prod.fst (header_reindexLastScopeOccurrenceEquiv F r scope q p)
  dsimp only at ho hp
  rw [Fin.ext_iff, Fin.ext_iff, ho, hp]

variable [DecidableEq V]

/-- Construct the target rotation from the actual source, with an explicit positional scope
bijection. This supplies no order claim for an arbitrary noncyclic scope permutation. -/
noncomputable def reindexLastScopeRotation (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn scope)]))) :
    RotationSystem (incidenceGraph (F ++ [(r, List.ofFn (scope ∘ q))])) :=
  occurrenceTransport rho (reindexLastScopeOccurrenceEquiv F r scope q)
    (reindex_variable_fibers F r scope q) (reindex_constraint_fibers F r scope q)

/-- Numerical genus is retained internally on the actual target incidence graph, including
closed components, nullaries, repeated variable names and empty scopes. -/
theorem numericalGenusZero_reindexLastScopeRotation (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn scope)])))
    (hr : rho.NumericalGenusZero) : (reindexLastScopeRotation F r scope q rho).NumericalGenusZero :=
  numericalGenusZero_occurrenceTransport rho (reindexLastScopeOccurrenceEquiv F r scope q)
    (reindex_variable_fibers F r scope q) (reindex_constraint_fibers F r scope q) hr

/-- Clockwise source order is retained with the explicit positive-cycle commutation
hypothesis; no target order or genus provider is assumed. -/
theorem respectsArgumentOrder_reindexLastScopeRotation (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (hq : ∀ j, q (finRotate n j) = finRotate n (q j))
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn scope)])))
    (hr : RespectsArgumentOrder rho) :
    RespectsArgumentOrder (reindexLastScopeRotation F r scope q rho) :=
  respectsArgumentOrder_occurrenceTransport rho (reindexLastScopeOccurrenceEquiv F r scope q)
    (reindex_variable_fibers F r scope q) (reindex_constraint_fibers F r scope q)
    (argumentSuccessor_reindexLastScopeOccurrenceEquiv F r scope q hq) hr

/-- Static finite table obtained by the explicit occurrence conjugacy of the decoded raw
source. This constructor makes no uniform native runtime assertion. -/
@[expose] noncomputable def reindexLastScopeCertificate (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n)) (c : RotationCertificate)
    (hrot : RotationCertificate.verifyRotation
      (incidenceGraph (F ++ [(r, List.ofFn scope)])) c = true) : RotationCertificate :=
  RotationCertificate.ofRotation (reindexLastScopeRotation F r scope q
    (RotationCertificate.decode _ c hrot))

/-- The actual target checker accepts the constructed conjugated table when the source
check accepts and the supplied scope permutation preserves the positive cyclic successor. -/
theorem verifyRotationCertificate_reindexLastScopeCertificate (F : CSP Rel V) (r : Rel)
    {n : ℕ} (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (hq : ∀ j, q (finRotate n j) = finRotate n (q j)) (c : RotationCertificate)
    (hrot : RotationCertificate.verifyRotation
      (incidenceGraph (F ++ [(r, List.ofFn scope)])) c = true)
    (h : verifyRotationCertificate (F ++ [(r, List.ofFn scope)]) c = true) :
    verifyRotationCertificate (F ++ [(r, List.ofFn (scope ∘ q))])
      (reindexLastScopeCertificate F r scope q c hrot) = true := by
  obtain ⟨hr, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp h
  let rho := RotationCertificate.decode (incidenceGraph (F ++ [(r, List.ofFn scope)])) c hrot
  let tau := reindexLastScopeRotation F r scope q rho
  have hgenus : tau.NumericalGenusZero :=
    numericalGenusZero_reindexLastScopeRotation F r scope q rho hg
  have horder : RespectsArgumentOrder tau :=
    respectsArgumentOrder_reindexLastScopeRotation F r scope q hq rho ho
  exact verifyRotationCertificate_ofRotation tau hgenus horder

/-- Each actual supplied source-table step becomes its exact reindexed target-table step.
This supports complete generated-table inspection without reducing choice-based inverse
coordinates or assuming a target certificate. -/
theorem getD_reindexLastScopeCertificate_of_step (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n)) (c : RotationCertificate)
    (hrot : RotationCertificate.verifyRotation
      (incidenceGraph (F ++ [(r, List.ofFn scope)])) c = true)
    (o p : (F ++ [(r, List.ofFn scope)]).Occurrence) (side other : Bool)
    (hstep : c.successor.getD (incidenceDart o side).index 0 = (incidenceDart p other).index) :
    (reindexLastScopeCertificate F r scope q c hrot).successor.getD
        (incidenceDart (reindexLastScopeOccurrenceEquiv F r scope q o) side).index 0 =
      (incidenceDart (reindexLastScopeOccurrenceEquiv F r scope q p) other).index := by
  let rho := RotationCertificate.decode (incidenceGraph (F ++ [(r, List.ofFn scope)])) c hrot
  let e := reindexLastScopeOccurrenceEquiv F r scope q
  have hr : rho.rotate (incidenceDart o side) = incidenceDart p other := by
    apply (Dart.indexEquiv _).injective
    apply Fin.ext
    change (rho.rotate (incidenceDart o side)).index = (incidenceDart p other).index
    rw [RotationCertificate.index_decode_rotate]
    exact hstep
  rw [reindexLastScopeCertificate, RotationCertificate.getD_ofRotation]
  change ((occurrenceTransport rho e (reindex_variable_fibers F r scope q)
    (reindex_constraint_fibers F r scope q)).rotate (incidenceDart (e o) side)).index = _
  rw [← occurrenceDartEquiv_apply e o side, occurrenceTransport_rotate, hr,
    occurrenceDartEquiv_apply]

end Cslib.Complexity.CSP
