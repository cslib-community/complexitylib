/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Logics.Propositional.CNF.ModelCount.Relabel

/-!
# Model counts under compact variable numbering

First-occurrence numbering preserves the number of satisfying assignments on the variables
occurring in a formula. The variable type may be infinite or empty.

## Main results

* `Cslib.Logic.PL.CNF.modelCount_compact`: compaction preserves the model count.

## References

This is an elementary counting property of the existing compaction construction.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*} [DecidableEq V]

/-- First-occurrence numbering preserves the number of satisfying assignments, including for
empty formulas, empty clauses, and repeated literal occurrences. -/
theorem modelCount_compact (φ : CNF V) : φ.compact.modelCount = φ.modelCount := by
  exact modelCount_relabel_of_injOn φ (fun _ ha _ _ h => (List.idxOf_inj ha).1 h)

end Cslib.Logic.PL.CNF
