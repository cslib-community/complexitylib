/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Reduction.Guard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Exactly One 3SAT

`OneInThreeSAT` is exact-one satisfiability of CNFs with at most three literal occurrences per
clause and literals of either polarity. An instance is a member when some assignment makes
exactly one literal occurrence true in every clause. This is the language of
[AroraBarak07], Chapter 2 Exercise 16.

Membership in NP is the width guard applied to the unrestricted exact-one verifier.
NP-hardness is a guarded identity reduction from the positive special case
`PositiveOneInThreeSAT`: positive width-three formulas are kept, and every other input is sent to
the formula with a single empty clause, which has no exact-one model.

## Main definitions

* `OneInThreeSAT`: width-three exact-one satisfiability with signed literals.

## Main results

* `OneInThreeSAT.mem_NP`: membership in NP under `encCNF`.
* `polyTimeReducible_PositiveOneInThreeSAT_OneInThreeSAT`: the guarded identity reduction.
* `OneInThreeSAT_npComplete`: Exactly One 3SAT is NP-complete.

## References

* [AroraBarak07], Chapter 2 Exercise 16, printed page 63 / PDF page 79.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Exact-one satisfiability with at most three literal occurrences per clause and no polarity
restriction. -/
@[expose] def OneInThreeSAT : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ φ.OneSatisfiable}

namespace OneInThreeSAT

/-- The clause-width guard. -/
def syntaxCheck (φ : CNF ℕ) : Bool := φ.all fun c => decide (c.length ≤ 3)

/-- The width guard checks that every clause has at most three literal occurrences. -/
theorem syntaxCheck_iff (φ : CNF ℕ) : syntaxCheck φ = true ↔ ∀ c ∈ φ, c.length ≤ 3 := by
  simp [syntaxCheck]

/-- The width guard is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  fun_prop [syntaxCheck, encCNF]

/-- Membership is the width guard together with exact-one satisfiability. -/
theorem mem_iff_syntaxCheck (φ : CNF ℕ) :
    φ ∈ OneInThreeSAT ↔ syntaxCheck φ = true ∧ φ ∈ OneSAT := by
  simp [OneInThreeSAT, syntaxCheck_iff, OneSAT]

/-- Exactly One 3SAT belongs to NP. -/
theorem mem_NP : OneInThreeSAT ∈ NP encCNF :=
  mem_NP_of_guard computableInPolyTime_syntaxCheck OneSAT.mem_NP mem_iff_syntaxCheck

/-- The formula with one empty clause is not exact-one satisfiable. -/
theorem nil_clause_not_mem : ([[]] : CNF ℕ) ∉ OneInThreeSAT := by
  rintro ⟨-, σ, hσ⟩
  simp [CNF.evalOne] at hσ

end OneInThreeSAT

/-- The positive language is the positive slice of Exactly One 3SAT. -/
theorem mem_PositiveOneInThreeSAT_iff (φ : CNF ℕ) :
    φ ∈ PositiveOneInThreeSAT ↔
      PositiveOneInThreeSAT.syntaxCheck φ = true ∧ φ ∈ OneInThreeSAT := by
  rw [PositiveOneInThreeSAT.mem_iff_syntaxCheck, PositiveOneInThreeSAT.syntaxCheck_iff,
    OneInThreeSAT]
  exact ⟨fun ⟨h, ho⟩ => ⟨h, h.1, ho⟩, fun ⟨h, _, ho⟩ => ⟨h, ho⟩⟩

/-- The guarded identity map reduces positive to signed width-three exact-one SAT. -/
theorem polyTimeReducible_PositiveOneInThreeSAT_OneInThreeSAT :
    PolyTimeReducible encCNF encCNF PositiveOneInThreeSAT OneInThreeSAT :=
  PolyTimeReducible.of_guard [[]] PositiveOneInThreeSAT.computableInPolyTime_syntaxCheck
    ComputableInPolyTime.id' OneInThreeSAT.nil_clause_not_mem mem_PositiveOneInThreeSAT_iff

/-- Exactly One 3SAT is NP-hard. -/
theorem OneInThreeSAT_npHard : NPHard encCNF OneInThreeSAT :=
  PositiveOneInThreeSAT_npHard.trans polyTimeReducible_PositiveOneInThreeSAT_OneInThreeSAT

/-- **[AroraBarak07], Chapter 2 Exercise 16.** Exactly One 3SAT is NP-complete. -/
theorem OneInThreeSAT_npComplete : NPComplete encCNF OneInThreeSAT :=
  ⟨OneInThreeSAT.mem_NP, OneInThreeSAT_npHard⟩

end Cslib.Complexity
