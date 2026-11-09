/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.CNF.ThreeCNF
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT

/-!
# Tests for splitting clauses into width three
-/

namespace CslibFrontierTests.ThreeCNF

open Cslib.Logic.PL Cslib.Complexity

/-- A clause of width five becomes a chain of three clauses with two auxiliary variables. -/
example :
    Clause.split3 (fun j => Sum.inr (0, j)) 0
        ([(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inl 2, false), (Sum.inl 3, true),
          (Sum.inl 4, true)] : Clause (ℕ ⊕ (ℕ × ℕ))) =
      [[(Sum.inl 0, true), (Sum.inl 1, true), (Sum.inr (0, 0), true)],
        [(Sum.inr (0, 0), false), (Sum.inl 2, false), (Sum.inr (0, 1), true)],
        [(Sum.inr (0, 1), false), (Sum.inl 3, true), (Sum.inl 4, true)]] := rfl

/-- Clauses of width at most three are kept. -/
example : Clause.split3 (fun j => Sum.inr (0, j)) 0
    ([(Sum.inl 0, true), (Sum.inl 1, false)] : Clause (ℕ ⊕ (ℕ × ℕ))) =
      [[(Sum.inl 0, true), (Sum.inl 1, false)]] := rfl

/-- The reduction to `ThreeSAT` is correct on every formula. -/
example (φ : CNF ℕ) : toThreeSAT φ ∈ ThreeSAT ↔ φ ∈ SAT := mem_ThreeSAT_toThreeSAT_iff φ

end CslibFrontierTests.ThreeCNF
