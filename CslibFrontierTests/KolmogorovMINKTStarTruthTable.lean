/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of CslibFrontier.Computability.Kolmogorov.MINKTStar.TruthTable)

import CslibFrontier.Computability.Kolmogorov.MINKTStar.TruthTable
import CslibFrontier.Computability.MCSP.Basic

/-! # Tests for `MINKT*` on indexed patterns and truth tables -/

namespace CslibFrontierTests.KolmogorovMINKTStarTruthTable

open Cslib Cslib.Kolmogorov

/-- The truth tables listed here are the lists of `MCSP.truthTable`. -/
example {L : ℕ} (h : BooleanFunction L) :
    (List.ofFn fun i => h ((BitString.equivFin L).symm i)) = List.ofFn (MCSP.truthTable L h) :=
  rfl

/-- The pattern `1*` is consistent with `10` and `11`, entrywise. -/
example : MINKTStar.Consistent (List.ofFn ![some true, none]) (List.ofFn ![true, false]) :=
  MINKTStar.consistent_ofFn_iff.mpr fun i b hb => by
    fin_cases i <;> simp_all

/-- The pattern `1*` is not consistent with `01`. -/
example : ¬ MINKTStar.Consistent (List.ofFn ![some true, none]) (List.ofFn ![false, true]) := by
  rw [MINKTStar.consistent_ofFn_iff]
  intro h
  simpa using h 0 true rfl

/-- With an all-`*` pattern, a yes-instance is a Boolean function whose truth table has small
`K^t`. -/
example {L t s : ℕ} :
    (⟨List.ofFn fun _ : Fin (2 ^ L) => none, t, s⟩ : MINKTStar.Instance) ∈ MINKTStar ↔
      ∃ h : BooleanFunction L,
        timeBoundedAt t (List.ofFn fun i => h ((BitString.equivFin L).symm i)) ≤ s := by
  rw [MINKTStar.mk_ofFn_mem_iff_exists_booleanFunction]
  simp

end CslibFrontierTests.KolmogorovMINKTStarTruthTable
