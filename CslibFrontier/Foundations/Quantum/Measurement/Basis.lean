/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement

/-!
# Measuring computational basis states

## Main results

* `Cslib.Quantum.measure_ket`: the full measurement distribution of a basis state is pure.
-/

public section

namespace Cslib.Quantum

/-- Measuring a computational basis state returns its index with certainty. -/
@[simp] theorem measure_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι) :
    measure (ket x) (norm_ket x) = PMF.pure x := by
  ext y
  simp [PMF.pure_apply, apply_ite]

end Cslib.Quantum
