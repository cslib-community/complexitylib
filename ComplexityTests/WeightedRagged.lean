/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.WeightedRaggedResources

/-! # Ragged original-input counting clients

Rows have lengths zero, one and three, repeated opposite literals and a large binary weight.
The third declared variable is unused. Empty contradictions and malformed inputs remain distinct.
-/

public section

namespace ComplexityTests.WeightedRagged

open Cslib.Logic.PL.WeightedRow Cslib.Logic.PL.WeightedRow.BinaryRagged Turing.MultiTapeTM

/-- A genuinely ragged system, with an 81-bit coefficient and an unused declared variable. -/
def mixed : Input := (3, [([], 0), ([(0, true, 1)], 1),
  ([(0, true, 2 ^ 80), (0, false, 3), (1, true, 5)], 2 ^ 80 + 5)])

example : admit 0 mixed = true := by decide
example : (mixed.2.map fun row => row.1.length) = [0, 1, 3] := by decide
example : parse (encInput mixed) = some mixed := parse_encode mixed
example : recode mixed = mixed := recode_eq ((shape_iff mixed).mp (by decide))
example : BinaryPlan.WithinBudget mixed.1 0 (BinaryPlan.compile 0 mixed.1 mixed.2) :=
  compile_admitted_budget (x := mixed) (d := 0) (by decide)
example : Fintype.card {σ // Holds mixed σ} = 2 := by decide

/-- Empty contradictions pass structural admission and are rejected by actual normalization. -/
def contradiction : Input := (3, [([], 1)])
example : admit 0 contradiction = true := by decide
example : Fintype.card {σ // Holds contradiction σ} = 0 := by decide
example : admit 0 (0, [([], 0)]) = true := by decide
example : Fintype.card {σ // Holds (0, [([], 0)]) σ} = 1 := by decide
example : Fintype.card {σ // Holds (0, [([], -1)]) σ} = 0 := by decide
example : Fintype.card {σ // Holds (3, []) σ} = 8 := by decide

example : admit 1 (2, [([(2 ^ 80, true, 1)], 1)]) = false := by decide
example : admit 1 (2, [([(0, true, 0)], 0)]) = false := by decide
example : admit 1 (2, [([(0, false, -1)], -1)]) = false := by decide
example : parse [] = none := by decide
example : canonical [] = false := by decide

/-- One certificate witnesses actual word counting, global workspace, both edge counts and
malformed-word rejection; no counter or desired resource bound is supplied by this client. -/
example : ∃ count : List Bool → ℕ, ∃ cs : Cslib.GenericRAM.NativeCertificate count encBits encNat,
    ∃ C e : ℕ, (∀ w, cs.space w ≤ C * (w.length + 1) ^ e) ∧
      count (encInput mixed) = 2 ∧ count (encInput contradiction) = 0 ∧ count [] = 0 := by
  obtain ⟨count, cs, C, e, _, hs, _, hc, hb, _⟩ := exists_countWords_sharp_certificate 0
  refine ⟨count, cs, C, e, hs, ?_, ?_, hb [] (by decide)⟩
  · rw [hc mixed (by decide)]
    decide
  · rw [hc contradiction (by decide)]
    decide

end ComplexityTests.WeightedRagged
