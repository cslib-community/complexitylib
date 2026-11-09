/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi

/-!
# Encodings of constraint tables and tester calls

The executable PCP constructions store a binary constraint over a fixed finite alphabet `α` as
its complete Boolean table, a function `α → α → Bool`. An assignment tester computes its queries
from such a table, a coin string and a query index, and the edges of a composed gadget graph
carry the same triple as their constraint descriptor. This module names those two encodings by
role, so that statements need not spell out the nested tables.

Both names are reducible abbreviations, so `fun_prop`, instance search and the combinators' lemmas
see through them. `omega` does not, since it compares atoms syntactically: state the bounds that it
combines with the same spelling.

## Main definitions

* `Cslib.PCP.Encoded.encConstraintTable`: the complete table of a binary constraint.
* `Cslib.PCP.Encoded.encTableCoinsQuery`: a constraint table with a coin string and a query index.
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Turing.MultiTapeTM

/-- The complete Boolean table of a binary constraint `c : α → α → Bool` over a fixed finite
alphabet `α`: the concatenation of the framed rows `c a`, each the concatenation of the framed
bits `c a b`. Both indices run in the order of `Fintype.equivFin α`, so the length is bounded in
terms of `Fintype.card α` alone (`Cslib.PCP.Encoded.Graph.length_constraintTable_le`). -/
noncomputable abbrev encConstraintTable {α : Type} [Fintype α] : (α → α → Bool) ↪ List Bool :=
  encPi (encPi encBool)

/-- Triple `(c, r, q)` of a constraint table `c` (`encConstraintTable`), a coin string `r` encoded
by `coinsEncoding` and a query index `q` encoded by `queryEncoding`: the input of an assignment
tester's query function, and the constraint descriptor of an edge of a composed gadget graph. The
table and the coins are framed; the query index is not. -/
noncomputable abbrev encTableCoinsQuery {α R Q : Type} [Fintype α]
    (coinsEncoding : R ↪ List Bool) (queryEncoding : Q ↪ List Bool) :
    (α → α → Bool) × R × Q ↪ List Bool :=
  encPair encConstraintTable (encPair coinsEncoding queryEncoding)

end Cslib.PCP.Encoded
