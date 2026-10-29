/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.TruthTable
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Complexity.Problems.ThreeSAT

/-!
# Tests for NP and coNP closure under truth-table reduction variants
-/

namespace ComplexityTests.NPTruthTable

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Disjunctive truth-table reductions to NP -/

-- NP is closed under many-one reductions viewed as 1-query disjunctive truth-table reductions.
example : SAT ∈ NP encCNF :=
  polyTimeReducible_SAT_ThreeSAT.polyTimeDTTReducible.mem_NP ThreeSAT.mem_NP

-- Reflexive disjunctive reduction preserves NP membership.
example : ThreeSAT ∈ NP encCNF :=
  (PolyTimeDTTReducible.refl encCNF ThreeSAT).mem_NP ThreeSAT.mem_NP

/-! ### Conjunctive truth-table reductions to coNP -/

-- coNP is closed under many-one reductions viewed as 1-query conjunctive truth-table reductions.
example : SATᶜ ∈ coNP encCNF := by
  have hco : ThreeSATᶜ ∈ coNP encCNF := by
    rw [mem_coNP, compl_compl]
    exact ThreeSAT.mem_NP
  exact polyTimeReducible_SAT_ThreeSAT.compl.polyTimeCTTReducible.mem_coNP hco

-- Reflexive conjunctive reduction preserves coNP membership.
example : ThreeSATᶜ ∈ coNP encCNF := by
  have hco : ThreeSATᶜ ∈ coNP encCNF := by
    rw [mem_coNP, compl_compl]
    exact ThreeSAT.mem_NP
  exact (PolyTimeCTTReducible.refl encCNF ThreeSATᶜ).mem_coNP hco

/-! ### Conjunctive truth-table reductions to NP and disjunctive ones to coNP -/

-- NP is closed under conjunctive truth-table reductions, with no hypothesis on `NP` and `coNP`.
example : SAT ∈ NP encCNF :=
  polyTimeReducible_SAT_ThreeSAT.polyTimeCTTReducible.mem_NP ThreeSAT.mem_NP

-- coNP is closed under disjunctive truth-table reductions.
example : SATᶜ ∈ coNP encCNF := by
  have hco : ThreeSATᶜ ∈ coNP encCNF := by
    rw [mem_coNP, compl_compl]
    exact ThreeSAT.mem_NP
  exact polyTimeReducible_SAT_ThreeSAT.compl.polyTimeDTTReducible.mem_coNP hco

/-! ### A reduction making two different queries -/

/-- Query `0` asks about the word, every later query about its reversal. -/
def wordOrReverse (p : List Bool × ℕ) : List Bool := if p.2 = 0 then p.1 else p.1.reverse

theorem computableInPolyTime_wordOrReverse :
    ComputableInPolyTime wordOrReverse (encPair encBits encUnary) encBits := by
  unfold wordOrReverse
  fun_prop

/-- Asking whether both a word and its reversal lie in `B` is a two-query conjunctive
truth-table reduction to `B`. -/
theorem polyTimeCTTReducible_and_reverse (B : Set (List Bool)) :
    PolyTimeCTTReducible encBits encBits {w | w ∈ B ∧ w.reverse ∈ B} B := by
  refine ⟨fun _ => 2, wordOrReverse, by fun_prop, computableInPolyTime_wordOrReverse, fun w => ?_⟩
  simp only [Set.mem_ofPred_eq, wordOrReverse]
  constructor
  · rintro ⟨hw, hrev⟩ i hi
    by_cases h0 : i = 0 <;> simp [h0, hw, hrev]
  · intro h
    exact ⟨by simpa using h 0 (by decide), by simpa using h 1 (by decide)⟩

-- NP is closed under this two-query conjunctive reduction.
example (B : Set (List Bool)) (hB : B ∈ NP encBits) :
    {w | w ∈ B ∧ w.reverse ∈ B} ∈ NP encBits :=
  (polyTimeCTTReducible_and_reverse B).mem_NP hB

-- The same reduction, viewed as a positive truth-table reduction.
example (B : Set (List Bool)) (hB : B ∈ NP encBits) :
    {w | w ∈ B ∧ w.reverse ∈ B} ∈ NP encBits :=
  (polyTimeCTTReducible_and_reverse B).polyTimePTTReducible.mem_NP hB

end ComplexityTests.NPTruthTable
