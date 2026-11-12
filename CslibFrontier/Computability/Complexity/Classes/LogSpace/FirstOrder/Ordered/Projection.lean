/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction
public import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Reduction

/-!
# Ordered projection reductions in logarithmic space

Every first-order or quantifier-free projection reduction between ordered queries is in particular
an ordered first-order reduction (`ProjectionReduces.reduces`, `QFProjectionReduces.reduces`), and
so induces a logarithmic-space many-one reduction between the source-only encoded query languages
at `encStructure` through `Reduces.logSpaceReducible`. Keeping these corollaries here avoids
importing Turing-machine and space-complexity infrastructure into the first-order logic layer.

## Main results

* `Cslib.Logic.FO.Ordered.ProjectionReduces.logSpaceReducible`: first-order projection reductions
  induce logspace reductions of encoded ordered queries.
* `Cslib.Logic.FO.Ordered.QFProjectionReduces.logSpaceReducible`: quantifier-free projection
  reductions induce logspace reductions of encoded ordered queries.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definition 3.6 and Proposition 3.7.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 3.1 and Proposition 3.10.
-/

public section

open FirstOrder Language Turing

namespace Cslib.Logic.FO.Ordered

variable {L L' : Language} [L.IsRelational] [L'.IsRelational] (v : Vocabulary L)
  (v' : Vocabulary L') {K : Query L} {K' : Query L'}

/-- **First-order projection reductions are logspace reductions**: a first-order projection
reduction of the ordered query `K` to `K'` induces a logspace many-one reduction between their
source-only encoded query languages at `encStructure`. -/
theorem ProjectionReduces.logSpaceReducible (h : ProjectionReduces K K') :
    Complexity.LogSpaceReducible encStructure encStructure (K.encodedLanguage v)
      (K'.encodedLanguage v') :=
  h.reduces.logSpaceReducible v v'

/-- **Quantifier-free projection reductions are logspace reductions**: a quantifier-free projection
reduction of the ordered query `K` to `K'` induces a logspace many-one reduction between their
source-only encoded query languages at `encStructure`. -/
theorem QFProjectionReduces.logSpaceReducible (h : QFProjectionReduces K K') :
    Complexity.LogSpaceReducible encStructure encStructure (K.encodedLanguage v)
      (K'.encodedLanguage v') :=
  h.projectionReduces.logSpaceReducible v v'

end Cslib.Logic.FO.Ordered
