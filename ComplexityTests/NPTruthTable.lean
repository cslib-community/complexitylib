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

/-! ### Conditional closures under NP = coNP -/

example (hNP : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) :
    SAT ∈ NP encCNF := by
  have hThreeSAT : ThreeSAT ∈ NP encCNF := ThreeSAT.mem_NP
  exact polyTimeReducible_SAT_ThreeSAT.polyTimeCTTReducible.mem_NP_of_NP_eq_coNP hNP hThreeSAT

example (hNP : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) :
    SATᶜ ∈ coNP encCNF := by
  have hThreeSAT_co : ThreeSATᶜ ∈ coNP encCNF := by
    rw [mem_coNP, compl_compl]
    exact ThreeSAT.mem_NP
  exact polyTimeReducible_SAT_ThreeSAT.compl.polyTimeDTTReducible.mem_coNP_of_NP_eq_coNP
    hNP hThreeSAT_co

end ComplexityTests.NPTruthTable
