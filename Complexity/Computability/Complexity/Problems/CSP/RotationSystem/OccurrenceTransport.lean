/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.VertexFibers
public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Darts
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Transport

/-!
# Directed transport along actual CSP occurrence bijections

An occurrence bijection retaining the variable and constraint fiber partitions transports the
actual incidence rotation. Intertwining the original cyclic argument successor preserves its
sign, and numerical genus follows from indexed edge/reversal transport. Isolated nullary
constraints need no occurrence or invented dart. These original structural tools do not
provide an embedding: concrete scope operations must supply and prove their actual bijections.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph Graph.RotationSystem

variable {Rel Other V W : Type} [DecidableEq V] [DecidableEq W]
  {F : CSP Rel V} {H : CSP Other W}

/-- Reindex the actual two ends of each occurrence, retaining their endpoint side tags. -/
@[expose] noncomputable def occurrenceDartEquiv (e : F.Occurrence ≃ H.Occurrence) :
    Dart (incidenceGraph F) ≃ Dart (incidenceGraph H) :=
  (incidenceDartEquiv F).symm.trans
    ((e.prodCongr (Equiv.refl Bool)).trans (incidenceDartEquiv H))

/-- The occurrence/end formula is literal and retains each original end tag. -/
theorem occurrenceDartEquiv_apply (e : F.Occurrence ≃ H.Occurrence)
    (o : F.Occurrence) (side : Bool) :
    occurrenceDartEquiv e (incidenceDart o side) = incidenceDart (e o) side := by
  have hi := (incidenceDartEquiv F).symm_apply_apply (o, side)
  change (incidenceDartEquiv F).symm (incidenceDart o side) = (o, side) at hi
  simp only [occurrenceDartEquiv, Equiv.trans_apply, hi, Equiv.prodCongr_apply,
    incidenceDartEquiv_apply]
  rfl

/-- Fiber hypotheses concern actual names and constraint positions, not dense numbering.
They allow arbitrary repeated original variable labels and constraint records. -/
theorem occurrenceDartEquiv_vertex_eq_iff (e : F.Occurrence ≃ H.Occurrence)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔ o.1 = p.1)
    (a b : Dart (incidenceGraph F)) :
    (occurrenceDartEquiv e a).vertex = (occurrenceDartEquiv e b).vertex ↔ a.vertex = b.vertex := by
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective a
  obtain ⟨⟨p, other⟩, rfl⟩ := (incidenceDartEquiv F).surjective b
  simp only [incidenceDartEquiv_apply, occurrenceDartEquiv_apply,
    vertex_incidenceDart_eq_iff, hv, hc]

/-- Reversal commutes with the occurrence bijection, including repeated/parallel edges. -/
theorem occurrenceDartEquiv_reverse (e : F.Occurrence ≃ H.Occurrence)
    (d : Dart (incidenceGraph F)) :
    occurrenceDartEquiv e d.reverse = (occurrenceDartEquiv e d).reverse := by
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective d
  simp only [incidenceDartEquiv_apply]
  change occurrenceDartEquiv e (incidenceDart o (!side)) =
    (occurrenceDartEquiv e (incidenceDart o side)).reverse
  rw [occurrenceDartEquiv_apply, occurrenceDartEquiv_apply]
  rfl

/-- Transport the existing rotation along an actual fiber-preserving occurrence bijection. -/
@[expose] noncomputable def occurrenceTransport
    (r : RotationSystem (incidenceGraph F)) (e : F.Occurrence ≃ H.Occurrence)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔ o.1 = p.1) : RotationSystem (incidenceGraph H) :=
  r.transport (occurrenceDartEquiv e) (occurrenceDartEquiv_vertex_eq_iff e hv hc)

/-- Directed rotation intertwining on each actual source dart. -/
theorem occurrenceTransport_rotate (r : RotationSystem (incidenceGraph F))
    (e : F.Occurrence ≃ H.Occurrence)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔ o.1 = p.1) (d : Dart (incidenceGraph F)) :
    (occurrenceTransport r e hv hc).rotate (occurrenceDartEquiv e d) =
      occurrenceDartEquiv e (r.rotate d) := by
  simp [occurrenceTransport, transport]

/-- Componentwise numerical genus is retained internally, including arbitrary nullary and
point components. No connectedness or target-genus provider is assumed. -/
theorem numericalGenusZero_occurrenceTransport (r : RotationSystem (incidenceGraph F))
    (e : F.Occurrence ≃ H.Occurrence)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔ o.1 = p.1) (hr : r.NumericalGenusZero) :
    (occurrenceTransport r e hv hc).NumericalGenusZero :=
  r.numericalGenusZero_transport (occurrenceDartEquiv e)
    (occurrenceDartEquiv_vertex_eq_iff e hv hc) (occurrenceDartEquiv_reverse e)
    (incidenceVertices_declared F) (incidenceVertices_declared H) hr

/-- The original clockwise argument order survives precisely directed successor
intertwining. A reflected higher-arity scope cannot silently satisfy this premise. -/
theorem respectsArgumentOrder_occurrenceTransport (r : RotationSystem (incidenceGraph F))
    (e : F.Occurrence ≃ H.Occurrence)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔ o.1 = p.1)
    (hn : ∀ o, e (argumentSuccessor o) = argumentSuccessor (e o))
    (hr : RespectsArgumentOrder r) : RespectsArgumentOrder (occurrenceTransport r e hv hc) := by
  intro p
  obtain ⟨o, rfl⟩ := e.surjective p
  rw [← occurrenceDartEquiv_apply, occurrenceTransport_rotate, hr,
    occurrenceDartEquiv_apply, hn]

end Cslib.Complexity.CSP
