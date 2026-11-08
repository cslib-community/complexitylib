/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
public import Complexity.Logics.Propositional.CSP.PrimitivePositive
import Mathlib.Data.List.Find

/-!
# Checked ordered boundaries of actual CSP bodies

A structural probe star meets the listed boundary **positions** in reverse order. Its center
occupies the exterior of the gadget disk; its fixed rotation records orientation. A probe is
only certificate scaffolding: it has no relation semantics and is never a constraint in the
original-language gadget body. Repeated boundary names retain distinct probe occurrences.
Unused free ports become probe leaves. Closed components, isolated nullary constraints, and
an empty boundary remain explicit in the existing componentwise numerical checks.

The stored successor list supplies both a rotation of the probe-augmented incidence graph
and, by a bounded first-return scan, the rotation of the actual unaugmented body. Both are
checked by `CSP.verifyRotationCertificate`. No embedding oracle, geometric equivalence, or
Boolean condition on a nullary relation is built into this interface.

The boundary orientation follows [DvorakKupec2015], Section 2, printed p. 436: port order is
the reverse outer boundary order. The probe-star and executable first-return representation
are original. Fulla–Živný, arXiv:1602.06323v3, Section 2.1, use ordered incidence graphs of
positive-arity valued constraints; our unweighted decision bodies also retain nullaries.
Their constraints are indexed, matching the positional list model here. Dvořák–Kupec instead
write a set of constraint tuples; we do not deduplicate bodies or identify these source
models literally. The nullary extension and probe representation are original.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel V : Type} [DecidableEq V]

/-- Append one structural probe with the reversed boundary word. Old constraint/scope
positions are retained; probe arguments are separate positions even at repeated names. -/
@[expose] def probeBody (F : CSP Rel V) (ports : List V) : CSP (Option Rel) V :=
  F.map (fun c => (some c.1, c.2)) ++ [(none, ports.reverse)]

/-- Delete a suffix of darts by following successors to the first retained dart. The loop
clock is the supplied list length, never a binary entry or vertex label. Invalid tables
have total fallback zero; acceptance is checked separately. -/
@[expose] def restrictPrefix (darts : ℕ) (c : Graph.RotationCertificate) :
    Graph.RotationCertificate :=
  ⟨(List.range darts).map fun i =>
    (((List.range c.successor.length).map fun k =>
      Graph.RotationCertificate.walk c.successor (k + 1) i).find?
        (fun j => decide (j < darts))).getD 0⟩

/-- The canonical body restriction retains exactly its original number of indexed darts. -/
theorem length_restrictPrefix (darts : ℕ) (c : Graph.RotationCertificate) :
    (restrictPrefix darts c).successor.length = darts := by
  simp [restrictPrefix]

/-- Restrict an augmented table to the actual original-body incidence darts. Probe edges
are appended after all original occurrences, independently of variable-name enumeration. -/
@[expose] def bodyCertificate (F : CSP Rel V) (c : Graph.RotationCertificate) :
    Graph.RotationCertificate :=
  restrictPrefix (2 * F.occurrences.length) c

/-- Check the same finite table as an ordered probe rotation and check its canonical
restriction as an ordered rotation of the actual body. Each check uses componentwise
numerical genus zero, including the isolated-point convention. -/
@[expose] def verify (F : CSP Rel V) (ports : List V)
    (c : Graph.RotationCertificate) : Bool :=
  verifyRotationCertificate F (bodyCertificate F c) &&
    verifyRotationCertificate (probeBody F ports) c

/-- A single finite table with checked boundary and actual-body rotations. -/
structure Witness (F : CSP Rel V) (ports : List V) where
  /-- Successors on actual body darts followed by probe darts. -/
  certificate : Graph.RotationCertificate
  /-- Both the original body and augmented boundary checks succeed. -/
  accepted : verify F ports certificate = true

/-- Exact split of the two executed checks. -/
theorem verify_eq_true_iff (F : CSP Rel V) (ports : List V)
    (c : Graph.RotationCertificate) : verify F ports c = true ↔
      verifyRotationCertificate F (bodyCertificate F c) = true ∧
        verifyRotationCertificate (probeBody F ports) c = true :=
  by simp only [verify, Bool.and_eq_true]

/-- The witness supplies an accepted certificate for the literal gadget body. -/
theorem Witness.body_accepted {F : CSP Rel V} {ports : List V} (w : Witness F ports) :
    verifyRotationCertificate F (bodyCertificate F w.certificate) = true :=
  ((verify_eq_true_iff _ _ _).mp w.accepted).1

/-- The augmented rotation is checked with the literal reversed probe scope. -/
theorem Witness.probe_accepted {F : CSP Rel V} {ports : List V} (w : Witness F ports) :
    verifyRotationCertificate (probeBody F ports) w.certificate = true :=
  ((verify_eq_true_iff _ _ _).mp w.accepted).2

/-- The actual unaugmented incidence graph has an ordered componentwise numerical
sphere rotation, internally extracted from this witness's concrete successor list. -/
theorem Witness.body_realization {F : CSP Rel V} {ports : List V} (w : Witness F ports) :
    ∃ r : Graph.RotationSystem (incidenceGraph F),
      r.NumericalGenusZero ∧ RespectsArgumentOrder r := by
  obtain ⟨h, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.body_accepted
  exact ⟨Graph.RotationCertificate.decode _ _ h, hg, ho⟩

/-- The structural exterior probe also supplies an actual ordered numerical rotation. -/
theorem Witness.probe_realization {F : CSP Rel V} {ports : List V} (w : Witness F ports) :
    ∃ r : Graph.RotationSystem (incidenceGraph (probeBody F ports)),
      r.NumericalGenusZero ∧ RespectsArgumentOrder r := by
  obtain ⟨h, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted
  exact ⟨Graph.RotationCertificate.decode _ _ h, hg, ho⟩

/-- An ordered gadget boundary uses all its actual free labels in index order, including
unused labels. Existential labels and the actual body are those of `PPGadget` itself. -/
abbrev GadgetWitness {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {n : ℕ} {R : Set (Fin n → Bool)} (g : CSP.PPGadget arity sem R) :=
  Witness g.body (List.ofFn Sum.inl)

end Cslib.Complexity.CSP.OrderedBoundary
