/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary
public import CslibFrontier.Logics.Propositional.CSP.Planar.Crossover
public import CslibFrontier.Logics.Propositional.CSP.Planar.OneInThree

/-!
# Ordered numerical certificates for the two crossover bodies and NAND triangle

The certificates are for the literal existing PP bodies, with a structural exterior probe
in reverse free-port order. Both the augmented table and its actual-body restriction execute
the existing ordered numerical certificate checker. Every relation scope retains its
orientation and positional identity. This gives the fixed macro skeletons, before expansion
of their symbols into original-language gadgets.

The scopes are [DvorakKupec2015], Figure 1(a,b), printed pp. 440–441. The NAND triangle is
an original reconstruction of the proof omitted after its Lemma 4, printed pp. 438–439.
The explicit incidence successor tables and probe representation are original.
-/

public section

namespace Cslib.Logic.PL.CSP

open Cslib.Complexity.CSP.OrderedBoundary

namespace Crossover

/-- Probe-augmented positional rotation for the actual four-constraint Figure 1(a) body. -/
@[expose] def figureOneABoundaryCertificate : Cslib.Complexity.Graph.RotationCertificate :=
  ⟨[16, 3, 8, 5, 24, 7, 30, 1, 26, 11, 18, 13, 6, 15, 20, 9,
    0, 19, 10, 17, 14, 23, 28, 21, 4, 27, 2, 29, 22, 31, 12, 25]⟩

/-- The actual Figure 1(a) body has an internally supplied ordered numerical boundary. -/
def figureOneABoundary : Witness figureOneABody (List.ofFn Sum.inl) where
  certificate := figureOneABoundaryCertificate
  accepted := by decide +kernel

/-- Retargeting Figure 1(a)'s semantics preserves its literal certificate and port order. -/
def figureOneAStandardizedBoundary (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)]
    (h : Cslib.BitString.IsStandardizedInconsistent R) :
    GadgetWitness (figureOneAStandardized R h) := figureOneABoundary

/-- Probe-augmented positional rotation for the actual two-constraint Figure 1(b) body. -/
@[expose] def figureOneBBoundaryCertificate : Cslib.Complexity.Graph.RotationCertificate :=
  ⟨[22, 3, 20, 5, 12, 7, 10, 1, 18, 11, 16, 13, 4, 15, 2, 9,
    6, 19, 8, 21, 14, 23, 0, 17]⟩

/-- The actual Figure 1(b) CROSS gadget has ordered free ports `0,1,2,3`. -/
def figureOneBBoundary : GadgetWitness figureOneB where
  certificate := figureOneBBoundaryCertificate
  accepted := by decide +kernel

end Crossover

namespace NonSelfDual

/-- Probe-augmented rotation of the actual ternary body followed by NAND on `01,12,20`. -/
@[expose] def triangleBoundaryCertificate : Cslib.Complexity.Graph.RotationCertificate :=
  ⟨[16, 3, 8, 5, 12, 1, 0, 9, 20, 7, 2, 13, 18, 11, 4, 17,
    22, 15, 14, 21, 10, 23, 6, 19]⟩

/-- The literal NAND-triangle skeleton has the inherited free-port order `0,1,2`. -/
def triangleBoundary : Witness triangleBody (List.ofFn Sum.inl) where
  certificate := triangleBoundaryCertificate
  accepted := by decide +kernel

end NonSelfDual
end Cslib.Logic.PL.CSP
