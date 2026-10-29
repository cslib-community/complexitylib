/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.Pigeonhole

/-!
# Tests: pigeonhole formulas and Haken's resolution lower bound

Satisfiability and unsatisfiability of small pigeonhole formulas; a concrete resolution refutation
of `PHP^2_1` and its monotone translation pairs; and instances of the recurrence and exponential
lower bounds.
-/

namespace ComplexityTests.ProofComplexity.Pigeonhole

open Cslib Cslib.Logic.PL Finset

/-! ### Satisfiability, size, and concrete resolution refutation of small pigeonhole formulas -/

/-- Refute `PHP^2_1` in five lines by resolving the two pigeon clauses against the hole clause. -/
private def php21Proof : List (Clause (Fin 2 × Fin 1)) :=
  [[],
   [((1, 0), false)],
   [((0, 0), false), ((1, 0), false)],
   [((1, 0), true)],
   [((0, 0), true)]]

private theorem isProof_php21 : (CNF.pigeonhole 2 1).IsProof php21Proof := by
  have h₁ : (CNF.pigeonhole 2 1).IsProof
      [[((0, 0), false), ((1, 0), false)], [((1, 0), true)], [((0, 0), true)]] :=
    ((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)
  have h₂ := h₁.resolvent (c₁ := [((0, 0), true)])
    (c₂ := [((0, 0), false), ((1, 0), false)]) (0, 0)
    (by decide) (by decide) (by decide) (by decide)
  have h₃ := h₂.resolvent (c₁ := [((1, 0), true)]) (c₂ := [((1, 0), false)]) (1, 0)
    (by decide) (by decide) (by decide) (by decide)
  exact h₃

example :
    (CNF.pigeonhole 2 2).Satisfiable ∧
    ¬ (CNF.pigeonhole 2 1).Satisfiable ∧
    ¬ (CNF.pigeonhole 3 2).Satisfiable ∧
    (CNF.pigeonhole 3 2).length = 9 ∧
    (CNF.pigeonhole 3 2).length ≤ 3 + 2 * 3 ^ 2 ∧
    (CNF.pigeonhole 3 2).vars.toFinset.card = 6 ∧
    (CNF.pigeonhole 3 2).vars.toFinset.card ≤ 3 * 2 ∧
    CNF.pigeonhole 2 1 =
      [[((0, 0), true)], [((1, 0), true)], [((0, 0), false), ((1, 0), false)]] ∧
    (CNF.pigeonhole 2 1).RefutableInSize 5 ∧
    #(Pigeonhole.satPairs (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
      (CNF.holeClause 0 1 0)) = 2 :=
  ⟨CNF.satisfiable_pigeonhole_iff.2 (by decide),
    CNF.not_satisfiable_pigeonhole (by decide),
    CNF.not_satisfiable_pigeonhole (by decide),
    by decide,
    CNF.length_pigeonhole_le 3 2,
    by decide,
    CNF.card_toFinset_vars_pigeonhole_le 3 2,
    by decide,
    ⟨php21Proof, isProof_php21, by decide, le_rfl⟩,
    by decide⟩

/-! ### Lower-bound instances -/

/-- Recurrence lower bound at `n = 8` (`2 ≤ s`), and non-refutability at `n = 24` (`s = 1`)
and `n = 48` (`s = 3`). -/
example :
    (∀ {s : ℕ}, (CNF.pigeonhole 9 8).RefutableInSize s → 2 ≤ s) ∧
    ¬ (CNF.pigeonhole 25 24).RefutableInSize 1 ∧
    ¬ (CNF.pigeonhole 49 48).RefutableInSize 3 := by
  refine ⟨fun hs => ?_,
    CNF.not_refutableInSize_pigeonhole (n := 24) (by decide),
    CNF.not_refutableInSize_pigeonhole (n := 48) (by decide)⟩
  have := CNF.pow_le_mul_of_refutableInSize_pigeonhole (n := 8) (by decide) hs
  omega

end ComplexityTests.ProofComplexity.Pigeonhole
