/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF

/-!
# Variables of concatenated formulas

The variables of a concatenation of formulas (`Cslib.Logic.PL.CNF.vars`) are those of the first
formula followed by those of the second. Reductions that assemble a formula from blocks of clauses
use this to count or locate the variables of each block.

## Main results

* `Cslib.Logic.PL.CNF.vars_append`: the variables of `φ ++ ψ`.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- The variables of a concatenation of formulas are those of the first formula, then those of
the second. -/
theorem CNF.vars_append (φ ψ : CNF V) : (φ ++ ψ).vars = φ.vars ++ ψ.vars := by
  simp only [CNF.vars, List.flatten_append, List.map_append]

end Cslib.Logic.PL
