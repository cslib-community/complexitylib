/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Reduction.Turing
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time Turing reduction unit tests

Tests for `PolyTimeTuringReducible`, truth-table-to-Turing embeddings, and hardness transfer:
* Prefixing bits gives many-one and Turing reductions.
* Concrete 2-query disjunctive, conjunctive, and `2`-truth-table (XOR) reductions embed into
  Turing reductions and transfer `P`-membership.
* Complemented language membership in `P` via Turing reduction.
* NP-hardness transfer applied to `SAT`.
-/

open Cslib.Complexity
open Turing.MultiTapeTM

namespace ComplexityTests.ReductionTuring

variable (B : Set (List Bool))

/-- Prefixing `true` or `false` is a many-one reduction, hence a Turing reduction. -/
example :
    PolyTimeTuringReducible encBits encBits {w | true :: w ∈ B} B ∧
    PolyTimeTuringReducible encBits encBits {w | false :: w ∈ B} B :=
  ⟨(show PolyTimeReducible encBits encBits {w | true :: w ∈ B} B from
     ⟨fun w => true :: w, by fun_prop, fun _ => Iff.rfl⟩).polyTimeTuringReducible,
   (show PolyTimeReducible encBits encBits {w | false :: w ∈ B} B from
     ⟨fun w => false :: w, by fun_prop, fun _ => Iff.rfl⟩).polyTimeTuringReducible⟩

/-- Asking for both `false :: w` and `true :: w` and accepting when either is in `B` is a
disjunctive truth-table reduction, hence a Turing reduction. -/
theorem dtt_or_prefix :
    PolyTimeDTTReducible encBits encBits {w | false :: w ∈ B ∨ true :: w ∈ B} B := by
  refine ⟨fun _ => 2, fun x => decide (x.2 = 1) :: x.1, by fun_prop, by fun_prop, fun w => ?_⟩
  constructor
  · rintro (h | h)
    · exact ⟨0, by simp, by simpa using h⟩
    · exact ⟨1, by simp, by simpa using h⟩
  · rintro ⟨i, hi, h⟩
    obtain _ | _ | i := i
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
    · simp at hi

/-- Accepting when both `false :: w` and `true :: w` are in `B` is a conjunctive truth-table
reduction, hence a Turing reduction. -/
theorem ctt_and_prefix :
    PolyTimeCTTReducible encBits encBits {w | false :: w ∈ B ∧ true :: w ∈ B} B := by
  refine ⟨fun _ => 2, fun x => decide (x.2 = 1) :: x.1, by fun_prop, by fun_prop, fun w => ?_⟩
  constructor
  · rintro ⟨h₀, h₁⟩ i hi
    obtain _ | _ | i := i
    · simpa using h₀
    · simpa using h₁
    · simp at hi
  · intro h
    exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp)⟩

/-- Taking the exclusive-or of the two prefix queries is a non-monotone `2`-truth-table reduction,
hence a Turing reduction. -/
theorem ktt_xor_prefix :
    PolyTimeKTruthTableReducible 2 encBits encBits
      {w | (false :: w ∈ B) ≠ (true :: w ∈ B)} B := by
  classical
  refine ⟨fun _ => 2, fun x => decide (x.2 = 1) :: x.1,
    fun x => x.2.headD false ^^ (x.2.drop 1).headD false, by fun_prop, by fun_prop, by fun_prop,
    fun _ => le_rfl, fun w => ?_⟩
  simp only [truthTableAnswers, Set.mem_preimage]
  by_cases h₀ : false :: w ∈ B <;> by_cases h₁ : true :: w ∈ B <;> simp [List.ofFn_succ, h₀, h₁]

/-- Disjunctive, conjunctive, and `2`-truth-table (XOR) reductions embed unconditionally into
Turing reductions. -/
example :
    PolyTimeTuringReducible encBits encBits {w | false :: w ∈ B ∨ true :: w ∈ B} B ∧
    PolyTimeTuringReducible encBits encBits {w | false :: w ∈ B ∧ true :: w ∈ B} B ∧
    PolyTimeTuringReducible encBits encBits {w | (false :: w ∈ B) ≠ (true :: w ∈ B)} B :=
  ⟨(dtt_or_prefix B).polyTimeTuringReducible,
   (ctt_and_prefix B).polyTimeTuringReducible,
   (ktt_xor_prefix B).polyTimeTuringReducible⟩

/-- Disjunctive, conjunctive, `2`-truth-table (XOR), prefix, and complement Turing reductions
pull back `P` membership. -/
example (hB : B ∈ P encBits) :
    {w | false :: w ∈ B ∨ true :: w ∈ B} ∈ P encBits ∧
    {w | false :: w ∈ B ∧ true :: w ∈ B} ∈ P encBits ∧
    {w | (false :: w ∈ B) ≠ (true :: w ∈ B)} ∈ P encBits ∧
    {w | true :: w ∈ B} ∈ P encBits ∧
    Bᶜ ∈ P encBits :=
  ⟨(dtt_or_prefix B).polyTimeTuringReducible.mem_P hB,
   (ctt_and_prefix B).polyTimeTuringReducible.mem_P hB,
   (ktt_xor_prefix B).polyTimeTuringReducible.mem_P hB,
   (show PolyTimeTuringReducible encBits encBits {w | true :: w ∈ B} B from
     (show PolyTimeReducible encBits encBits {w | true :: w ∈ B} B from
       ⟨fun w => true :: w, by fun_prop, fun _ => Iff.rfl⟩).polyTimeTuringReducible).mem_P hB,
   (PolyTimeTuringReducible.compl_self encBits B).mem_P hB⟩

/-- Transitivity of Turing reductions: composing the `2`-truth-table XOR reduction with the
disjunctive prefix reduction yields a Turing reduction for the 4-query parity-of-disjunctions
language. -/
example :
    PolyTimeTuringReducible encBits encBits
      {w | (false :: w ∈ {v | false :: v ∈ B ∨ true :: v ∈ B}) ≠
        (true :: w ∈ {v | false :: v ∈ B ∨ true :: v ∈ B})} B :=
  (ktt_xor_prefix {v | false :: v ∈ B ∨ true :: v ∈ B}).polyTimeTuringReducible.trans
    (dtt_or_prefix B).polyTimeTuringReducible

/-- Turing NP-hardness transfer applied to `SAT ≤_T^p (encCNF '' SAT)ᶜ` (`encode` composed with
`compl_self`): `(encCNF '' SAT)ᶜ ∈ P` collapses `NP` to `P`, and `(encCNF '' SAT)ᶜ ∈ NP ∩ coNP`
collapses `NP` to `coNP`. -/
example :
    ((encCNF '' SAT)ᶜ ∈ P encBits → P encBits = NP encBits) ∧
    ((encCNF '' SAT)ᶜ ∈ NP encBits → (encCNF '' SAT)ᶜ ∈ coNP encBits →
      NP encBits = coNP encBits) := by
  have henc : PolyTimeTuringReducible encCNF encBits SAT (encCNF '' SAT) :=
    polyTimeTuringReducible_bits_iff_mem_PWithOracle.mpr (PolyTimeTuringReducible.refl encCNF SAT)
  have hcompl : PolyTimeTuringReducible encBits encBits (encCNF '' SAT) (encCNF '' SAT)ᶜ := by
    simpa using PolyTimeTuringReducible.compl_self encBits (encCNF '' SAT)ᶜ
  have hred := henc.trans hcompl
  exact ⟨NPHard.P_eq_NP_of_turing_mem_P CookLevin.SAT_npHard hred,
    NPHard.NP_eq_coNP_of_turing_mem_NP_inter_coNP CookLevin.SAT_npHard hred⟩

end ComplexityTests.ReductionTuring
