/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Identification
public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentCorners
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CertificatePredecessor

/-!
# Identifying variables at consecutive directed argument positions

The selected later variable corner and the predecessor of the earlier variable corner are
cofacial by two literal face steps. The constructor merges precisely those outgoing blocks,
then transports to the actual renamed CSP. Full target order and numerical-genus acceptance
are derived internally. No cofaciality or target-planarity provider remains in this application.
The construction is original and static; no native runtime bound is claimed here.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

private theorem predecessor_vertex (F : CSP Rel V)
    (rho : RotationSystem (incidenceGraph F)) (o : F.Occurrence) :
    (rho.rotate.symm (incidenceDart o false)).vertex = F.distinctVars.idxOf o.var :=
  (rho.mirror.vertex_rotate (incidenceDart o false)).trans (by
    simp only [vertex_incidenceDart, Bool.false_eq_true, ite_false])

/-- Merge the variable names of two selected occurrences at their directed corner blocks.
The label map identifies exactly those names on the actual occurring set. -/
@[expose] def identifyConsecutiveRotation (F : CSP Rel V) (f : V → W) (o p : F.Occurrence)
    (hv : o.var ≠ p.var)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b)
    (rho : RotationSystem (incidenceGraph F)) : RotationSystem (incidenceGraph (F.relabel f)) :=
  identifyVariablesRotation F f o.var p.var o.var_mem p.var_mem hv
    (incidenceDart o false) (rho.rotate.symm (incidenceDart p false))
    (by simp only [vertex_incidenceDart, Bool.false_eq_true, ite_false])
    (by exact predecessor_vertex F rho p) hkernel rho

/-- Ordered consecutive arguments internally discharge the cofaciality needed by the
actual variable merge. Disconnected components, nullaries and points are handled by the
generic numerical surgery and actual incidence transport. -/
theorem numericalGenusZero_identifyConsecutiveRotation (F : CSP Rel V) (f : V → W)
    (o p : F.Occurrence) (hv : o.var ≠ p.var)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b)
    (hp : argumentSuccessor p = o) (rho : RotationSystem (incidenceGraph F))
    (hr : rho.NumericalGenusZero) (ho : RespectsArgumentOrder rho) :
    (identifyConsecutiveRotation F f o p hv hkernel rho).NumericalGenusZero :=
  numericalGenusZero_identifyVariablesRotation F f o.var p.var o.var_mem p.var_mem hv
    (incidenceDart o false) (rho.rotate.symm (incidenceDart p false)) _ _ hkernel rho hr
    (sameCycle_variable_corners_of_argumentSuccessor rho ho o p hp)

/-- Both selected outgoing corners are variable ends, so original argument chirality
survives the literal merge and the dense-name transport. -/
theorem respectsArgumentOrder_identifyConsecutiveRotation (F : CSP Rel V) (f : V → W)
    (o p : F.Occurrence) (hv : o.var ≠ p.var)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b)
    (rho : RotationSystem (incidenceGraph F)) (ho : RespectsArgumentOrder rho) :
    RespectsArgumentOrder (identifyConsecutiveRotation F f o p hv hkernel rho) :=
  respectsArgumentOrder_identifyVariablesRotation F f o.var p.var o.var_mem p.var_mem hv
    (incidenceDart o false) (rho.rotate.symm (incidenceDart p false)) _ _ hkernel rfl
    (side_rotate_symm_variable rho p) rho ho

/-- Generate the target successor table from the supplied source table by actual corner
identification. The source verification proof only decodes the supplied rotation. -/
@[expose] noncomputable def identifyConsecutiveCertificate (F : CSP Rel V) (f : V → W)
    (o p : F.Occurrence) (hv : o.var ≠ p.var)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b)
    (c : RotationCertificate)
    (hrot : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    RotationCertificate :=
  RotationCertificate.ofRotation
    (identifyConsecutiveRotation F f o p hv hkernel (RotationCertificate.decode _ c hrot))

/-- Full target checker soundness, with the original positive argument cycles and internally
derived numerical genus. No cofaciality or target-certificate premise is supplied by a caller. -/
theorem verifyRotationCertificate_identifyConsecutiveCertificate (F : CSP Rel V) (f : V → W)
    (o p : F.Occurrence) (hv : o.var ≠ p.var)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b)
    (hp : argumentSuccessor p = o) (c : RotationCertificate)
    (hrot : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (hc : verifyRotationCertificate F c = true) :
    verifyRotationCertificate (F.relabel f)
      (identifyConsecutiveCertificate F f o p hv hkernel c hrot) = true := by
  obtain ⟨_, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff F c).mp hc
  exact verifyRotationCertificate_ofRotation _
    (numericalGenusZero_identifyConsecutiveRotation F f o p hv hkernel hp _ hg ho)
    (respectsArgumentOrder_identifyConsecutiveRotation F f o p hv hkernel _ ho)

/-- Exact full successor-table program for consecutive identification. The only selected
predecessor is the actual inverse rotation of the earlier argument's variable end. -/
theorem identifyConsecutiveCertificate_eq_swapSuccessors (F : CSP Rel V) (f : V → W)
    (o p : F.Occurrence) (hv : o.var ≠ p.var)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b)
    (c : RotationCertificate)
    (hrot : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    identifyConsecutiveCertificate F f o p hv hkernel c hrot =
      c.swapSuccessors (incidenceDart o false).index
        (c.successor.idxOf (incidenceDart p false).index) := by
  unfold identifyConsecutiveCertificate identifyConsecutiveRotation
  rw [ofRotation_identifyVariablesRotation, RotationCertificate.ofRotation_decode,
    RotationCertificate.index_decode_rotate_symm]

end Cslib.Complexity.CSP
