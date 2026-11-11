/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.OracleFormula
public import CslibFrontier.Computability.MCSP.FormulaMagnification

/-!
# Locality of the Oliveira–Santhanam formula construction

Draft module docstring.
-/

public section

namespace Cslib.Circuits.Boolean

open MCSP

/-- The oracle language of the Oliveira–Santhanam construction: the encoded `SuccinctMCSP`
yes-instances. -/
abbrev succinctMCSPOracle : Language Bool :=
  SuccinctMCSP.enc '' SuccinctMCSP

/-- The oracle gate on `succinctWord n S s` answers whether the sampled instance is a
`SuccinctMCSP` yes-instance. -/
theorem eval_query_succinctWord_eq_true_iff (n : ℕ) (S : Finset (BitString n)) (s : ℕ)
    (T : BitString (2 ^ n)) :
    (OracleFormula.query (succinctWord n S s)).eval (oracleInterpretation succinctMCSPOracle) T =
        true ↔
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP := by
  rw [OracleFormula.eval_query_eq_true_iff]
  change evalWord (succinctWord n S s) T ∈ succinctMCSPOracle ↔ _
  rw [evalWord_succinctWord]
  exact SuccinctMCSP.enc.injective.mem_set_image

end Cslib.Circuits.Boolean
