/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Projection
public import Mathlib.ModelTheory.Graph
import CslibFrontier.Tactic.FirstOrder

/-!
# Graph projections

The loop-free directed complement is a quantifier-free projection: equality of the endpoints
selects false on the diagonal; otherwise the output is the negation of one input edge. The
numeric interpretation is the identity, so this construction preserves any chosen relational numeric
structure. It works for every universe, including the empty one, and needs neither order nor BIT.
For simple graphs this is the usual graph complement. Both properties are proved by the automation
of `CslibFrontier.Tactic.FirstOrder`: `fo_qf` for quantifier-freeness and `fo_simp` for the edge
predicate.

## Main definitions

* `Cslib.Logic.FO.Projection.offDiagonalComplement`: complement off the diagonal, with identity
  numeric data.

## Main results

* `Cslib.Logic.FO.Projection.realize_offDiagonalComplement`: the output edge predicate is inequality
  and nonadjacency.
* `Cslib.Logic.FO.Projection.isQF_offDiagonalComplement`: all numeric tests and definitions are
  quantifier-free.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

namespace Cslib.Logic.FO.Projection

open FirstOrder Language Structure

/-- Complement a binary edge relation off the diagonal. Equality is a numeric test and the
negative edge literal supplies the only input bit inspected by each output bit. -/
def offDiagonalComplement (N : Language) : Projection N N Language.graph Language.graph Unit where
  numeric := .id N
  rel
    | .adj =>
      .branch ((Term.var (0, ())).equal (.var (1, ()))) (.leaf (.const false))
        (.leaf (.rel Language.adj (fun i => (i, ())) true))

/-- The loop-free directed complement is quantifier-free. -/
theorem isQF_offDiagonalComplement (N : Language) : (offDiagonalComplement N).IsQF := by
  fo_qf

/-- The output contains precisely the unequal, nonadjacent pairs. No symmetry or irreflexivity
assumption is imposed on the input relation. -/
theorem realize_offDiagonalComplement (N : Language) {M : Type*}
    [N.Structure M] [Language.graph.Structure M] (x : Fin 2 × Unit → M) :
    ((offDiagonalComplement N).rel .adj).toFormula.Realize x ↔
      x (0, ()) ≠ x (1, ()) ∧ ¬ RelMap Language.adj (fun i => x (i, ())) := by
  fo_simp

end Cslib.Logic.FO.Projection
