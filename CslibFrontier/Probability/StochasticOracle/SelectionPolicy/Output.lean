/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Record
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection

/-!
# Certification of actual oracle-policy outputs

`CertifiedOutput` checks a returned family against actual coverage, the feasible
dual objective and accrued physical duration. This predicate is shared by finite
response tables and arbitrary discrete extraction kernels. Failed outputs need
not satisfy a provenance constraint; successful selection-only output must come
from the actually proposed candidates.
-/

public section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy
open PartialCover AdaptiveSelection

/-- Actual certified coverage and physical deadline of a returned candidate family. -/
@[expose] def CertifiedOutput {B R E J : Type} [DecidableEq E]
    (I : Instance E J) (ρ D : ℝ) (duration : List (Record B R) → B → R → ℝ)
    (h : List (Record B R)) (C : Finset J) : Prop :=
  I.covered C = I.ground ∧ I.cost C ≤ ρ * ∑ e ∈ I.ground, I.dual e ∧
    accruedBill (recordResource duration) h ≤ D

/-- A halt record reveals no new elements, for arbitrary batch/response types. -/
theorem record_reveals_none {B R E J : Type} [DecidableEq E] [DecidableEq J]
    (propose : List (Record B R) → B → R → List (Finset J))
    (I : Instance E J) (h : List (Record B R)) :
    reveals I (recordProposals propose) h none = false := by
  simp [reveals, revealed, recordProposals, Instance.covered]

end Cslib.Probability.StochasticOracle.SelectionPolicy
