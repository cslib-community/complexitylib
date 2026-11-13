/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Complete
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT

/-!
# A reduction from 3SAT to its complement collapses PH

Exercise 3, Chapter 5 of the 2007 draft [AroraBarak07] (printed page 100 / PDF page 116).
`ThreeSAT` means satisfiable CNFs with clause width at most three. Its complement is taken in
all `CNF ℕ`, including formulas with wider clauses; this is a total-language reduction, not a
promise reduction on well-formed three-CNFs. The hypothesis is a native polynomial-time many-one
reduction using `encCNF`. The conclusion holds for every explicit encoding of output instances.
-/

public section

namespace Cslib.Complexity

/-- **Arora–Barak 2007, Chapter 5, Exercise 3:** `3SAT ≤ₚ complement(3SAT)` implies `PH = NP`.
The overline in the rendered source is essential. -/
theorem PH_eq_NP_of_ThreeSAT_reducible_compl {α : Type} (enc : α ↪ List Bool)
    (h : PolyTimeReducible encCNF encCNF ThreeSAT ThreeSATᶜ) : PH enc = NP enc :=
  ThreeSAT_npComplete.PH_eq_NP_of_reducible_compl h

end Cslib.Complexity
