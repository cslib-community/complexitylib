/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.Embedding.EdgeDeletion
public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.LastArgument
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CertificateTransport
import Complexity.Logics.Propositional.CSP.Occurrence.AppendLast
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentIndices
import Mathlib.Data.List.GetD

/-!
# Actual CSP last-argument deletion and the boundary restriction program

The positional incidence transports retain the literal generated table, even when dense
variable and constraint names change. This identifies actual CSP deletion with the existing
bounded boundary scan. Accepted raw certificates supply their own exact clock length.
Target rotation validity, clockwise argument order and componentwise numerical genus are
proved internally. In gadget recipes this structural deletion removes a probe argument;
original-language relation scopes and their semantics are retained separately by the recipe.

## Main results

* `Cslib.Complexity.CSP.OrderedBoundary.ofRotation_deleteLastArgumentRotation`: exact output table.
* `Cslib.Complexity.CSP.OrderedBoundary.verifyRotationCertificate_restrictPrefix_lastArgument`:
  ordered numerical target acceptance from the actual supplied source certificate.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V]

/-- An accepted source table funds the scan by its actual occurrence count, including
the one final argument being removed. This applies directly to raw supplied certificates. -/
theorem length_accepted_lastArgument_certificate (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (c : RotationCertificate)
    (h : RotationCertificate.verifyRotation (incidenceGraph (F ++ [(r, scope ++ [v])])) c = true) :
    c.successor.length = 2 * ((F ++ [(r, scope)]).occurrences.length + 1) := by
  rw [RotationCertificate.length_of_verifyRotation h, incidenceGraph_edges,
    List.length_map, CSP.occurrences_append_last_argument, List.length_append,
    List.length_singleton]

/-- Actual CSP scope deletion produces exactly the boundary program's table. The equality
accounts for changing dense vertex names through positional dart transport. -/
theorem ofRotation_deleteLastArgumentRotation (F : CSP Rel V) (r : Rel) (scope : List V) (v : V)
    (ρ : RotationSystem (incidenceGraph (F ++ [(r, scope ++ [v])]))) :
    RotationCertificate.ofRotation (deleteLastArgumentRotation F r scope v ρ) =
      restrictPrefix (2 * (F ++ [(r, scope)]).occurrences.length)
        (RotationCertificate.ofRotation ρ) := by
  have he : (lastArgumentPrefixGraph F r scope v).2.length =
      (F ++ [(r, scope)]).occurrences.length := by
    simp [lastArgumentPrefixGraph]
  change RotationCertificate.ofRotation
    (((lastArgumentSourceRotation F r scope v ρ).deleteLastEdge
      (G := lastArgumentPrefixGraph F r scope v)
      (u := (F ++ [(r, scope ++ [v])]).distinctVars.idxOf v)
      (v := (F ++ [(r, scope ++ [v])]).numVars + F.length)).transport
        (lastArgumentDartEquiv F r scope v) (lastArgumentDartEquiv_vertex_eq_iff F r scope v)) = _
  rw [ofRotation_transport _ _ _ (by intro a; rfl)]
  rw [← restrictPrefix_ofRotation_deleteLastEdge, he]
  rw [lastArgumentSourceRotation, ofRotation_graphEqDartEquiv]

/-- On an accepted raw numerical source certificate, the literal boundary restriction
passes the actual target numerical checker. Dense renaming, repeated variables and
nullary or disconnected constraints are handled internally by positional transport. -/
theorem verifyGenusZero_restrictPrefix_lastArgument (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (c : RotationCertificate)
    (h : RotationCertificate.verifyGenusZero (incidenceGraph (F ++ [(r, scope ++ [v])])) c = true) :
    RotationCertificate.verifyGenusZero (incidenceGraph (F ++ [(r, scope)]))
      (restrictPrefix (2 * (F ++ [(r, scope)]).occurrences.length) c) = true := by
  obtain ⟨hrot, hgenus⟩ := (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp h
  let ρ := RotationCertificate.decode (incidenceGraph (F ++ [(r, scope ++ [v])])) c hrot
  let τ := deleteLastArgumentRotation F r scope v ρ
  have hτ : τ.NumericalGenusZero :=
    numericalGenusZero_deleteLastArgumentRotation F r scope v ρ hgenus
  have hout : RotationCertificate.ofRotation τ =
      restrictPrefix (2 * (F ++ [(r, scope)]).occurrences.length) c := by
    rw [ofRotation_deleteLastArgumentRotation, RotationCertificate.ofRotation_decode hrot]
  rw [← hout]
  apply (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mpr
  refine ⟨RotationCertificate.verifyRotation_ofRotation τ (incidenceVertices_declared _), ?_⟩
  rw [RotationCertificate.decode_ofRotation _ (incidenceVertices_declared _)]
  exact hτ

omit [DecidableEq V] in
private theorem argumentOrder_restrictPrefix_lastArgument_of_clock (F : CSP Rel V)
    (r : Rel) (scope : List V) (v : V)
    (c : RotationCertificate) (hc : 2 ≤ c.successor.length)
    (ho : verifyArgumentOrder (F ++ [(r, scope ++ [v])]) c = true) :
    verifyArgumentOrder (F ++ [(r, scope)])
      (restrictPrefix (2 * (F ++ [(r, scope)]).occurrences.length) c) = true := by
  have hpre : (F ++ [(r, scope ++ [v])]).occurrences.zipIdx =
      (F ++ [(r, scope)]).occurrences.zipIdx ++
        [((F.length, scope.length, v), (F ++ [(r, scope)]).occurrences.length)] := by
    simp [CSP.occurrences_append_last_argument, List.zipIdx_append]
  rw [verifyArgumentOrder, List.all_eq_true] at ho ⊢
  intro entry he
  rcases entry with ⟨⟨i, j, w⟩, k⟩
  apply decide_eq_true
  have hsrc := of_decide_eq_true (ho ((i, j, w), k) (by
    rw [hpre]
    exact List.mem_append_left _ he))
  change c.successor.getD (2 * k + 1) 0 =
    2 * argumentNextIndex (F ++ [(r, scope ++ [v])]) i j + 1 at hsrc
  obtain ⟨hk, hrec⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
  have hm : (i, j, w) ∈ (F ++ [(r, scope)]).occurrences :=
    List.mem_iff_getElem.mpr ⟨k, hk, hrec⟩
  obtain ⟨o, hrecord⟩ := CSP.mem_occurrences.mp hm
  have hcoords : o.1.val = i ∧ o.2.val = j ∧ o.var = w := by
    simpa only [CSP.Occurrence.record, Prod.mk.injEq] using hrecord
  rcases hcoords with ⟨hi, hj, hw⟩
  subst i
  subst j
  subst w
  have hn := argumentNextIndex_lt_occurrences o
  by_cases hlast : o.1.val = F.length ∧ o.2.val + 1 = scope.length
  · rw [argumentNextIndex_append_last_argument, ite_eq_left hlast] at hsrc
    have hwrap := of_decide_eq_true (ho
      ((F.length, scope.length, v), (F ++ [(r, scope)]).occurrences.length) (by
        rw [hpre]
        exact List.mem_append_right _ (by simp)))
    change c.successor.getD (2 * (F ++ [(r, scope)]).occurrences.length + 1) 0 =
      2 * argumentNextIndex (F ++ [(r, scope ++ [v])]) F.length scope.length + 1 at hwrap
    rw [argumentNextIndex_append_last_argument_wrap F r scope v o hlast.1 hlast.2] at hwrap
    have hr := getD_restrictPrefix_two c (2 * (F ++ [(r, scope)]).occurrences.length)
      (2 * k + 1) (by omega) hc (by rw [hsrc]; omega) (by rw [hsrc, hwrap]; omega)
    rw [hsrc, hwrap] at hr
    exact hr
  · rw [argumentNextIndex_append_last_argument, ite_eq_right hlast] at hsrc
    rw [getD_restrictPrefix_one c _ _ (by omega) (by omega) (by rw [hsrc]; omega), hsrc]

/-- An accepted raw source rotation retains its clockwise cyclic argument order under the
actual last-argument restriction program. The source checker supplies the scan clock. -/
theorem verifyArgumentOrder_restrictPrefix_lastArgument (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (c : RotationCertificate)
    (h : RotationCertificate.verifyRotation (incidenceGraph (F ++ [(r, scope ++ [v])])) c = true)
    (ho : verifyArgumentOrder (F ++ [(r, scope ++ [v])]) c = true) :
    verifyArgumentOrder (F ++ [(r, scope)])
      (restrictPrefix (2 * (F ++ [(r, scope)]).occurrences.length) c) = true := by
  apply argumentOrder_restrictPrefix_lastArgument_of_clock F r scope v c _ ho
  rw [length_accepted_lastArgument_certificate F r scope v c h]
  omega

/-- Full ordered numerical acceptance of the computed target certificate on the original
CSP lists. Source acceptance is the only certificate premise: target rotation, argument
order and componentwise numerical genus are all proved internally. -/
theorem verifyRotationCertificate_restrictPrefix_lastArgument (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) (c : RotationCertificate)
    (h : verifyRotationCertificate (F ++ [(r, scope ++ [v])]) c = true) :
    verifyRotationCertificate (F ++ [(r, scope)])
      (restrictPrefix (2 * (F ++ [(r, scope)]).occurrences.length) c) = true := by
  simp only [verifyRotationCertificate, Bool.and_eq_true] at h ⊢
  obtain ⟨hg, ho⟩ := h
  obtain ⟨hr, -⟩ := (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp hg
  exact ⟨verifyGenusZero_restrictPrefix_lastArgument F r scope v c hg,
    verifyArgumentOrder_restrictPrefix_lastArgument F r scope v c hr ho⟩

end Cslib.Complexity.CSP.OrderedBoundary
