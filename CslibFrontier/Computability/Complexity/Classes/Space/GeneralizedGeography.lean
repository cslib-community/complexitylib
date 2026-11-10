/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.GeneralizedGeography.Membership
public import CslibFrontier.Computability.Complexity.Classes.Space.GeneralizedGeography.Reduction

/-!
# Generalized Geography is `PSPACE`-complete

Generalized Geography (`Cslib.Complexity.GeneralizedGeography`: a directed graph with a start
vertex, on which two players alternately move a token along arcs to unvisited vertices, the first
player unable to move losing, and the instance is in the set when the first player has a winning
strategy) is `PSPACE`-complete [Sipser, Theorem 8.14][Sipser2013] [Lichtenstein and
Sipser][LichtensteinSipser1980]. This is the vertex version of the game; Schaefer's original
Generalized Geography, in which arcs may not be reused, is not treated [Schaefer1978]. The proof
has two halves:

* it is in `PSPACE` (`Cslib.Complexity.GeneralizedGeography_mem_PSPACE`): it is a game of
  polynomially many moves with a polynomial-time winning condition, decided in polynomial space by
  the characterization of `PSPACE` through such games;
* it is `PSPACE`-hard (`Cslib.Complexity.GeneralizedGeography_pspaceHard`): true quantified Boolean
  formulas in alternating prenex conjunctive normal form (`Cslib.Complexity.TQBFCNF`), which are
  `PSPACE`-hard, reduce to it by the diamond construction of Sipser's proof, which adapts
  Schaefer's reduction from quantified formulas to geography games.

Both are relative to the encoding `encPair encGraph encNat` of a graph, as lists of binary vertices
and arcs, with a binary start vertex.

## Main results

* `Cslib.Complexity.GeneralizedGeography_pspaceComplete`: Generalized Geography is
  `PSPACE`-complete.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.14][Sipser2013]
* [D. Lichtenstein, M. Sipser, *GO is polynomial-space hard*][LichtensteinSipser1980]
* [T. J. Schaefer, *On the complexity of some two-person perfect-information games*][Schaefer1978]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Generalized Geography is `PSPACE`-complete** [Sipser, Theorem 8.14][Sipser2013]
[LichtensteinSipser1980]. -/
theorem GeneralizedGeography_pspaceComplete :
    PSPACEComplete (encPair encGraph encNat) GeneralizedGeography :=
  ⟨GeneralizedGeography_mem_PSPACE, GeneralizedGeography_pspaceHard⟩

end Cslib.Complexity
