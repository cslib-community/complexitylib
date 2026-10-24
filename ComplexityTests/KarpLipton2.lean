/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.SelfReduction
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Foundations.Data.BitString.Enumeration

/-!
# Tests for the SAT self-reduction and the Karp–Lipton theorem

The self-reduction on concrete formulas with a brute-force decision procedure, which satisfies the
hypothesis of `SAT.verifier_search`; advice strings for a concrete family of circuits; and axiom
checks for the headline results.
-/

namespace Cslib.Complexity.Tests.KarpLipton2

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The self-reduction -/

/-- A brute-force decision procedure for `SAT`: try every certificate with one bit for each literal
occurrence. -/
def bruteSAT (ψ : CNF ℕ) : Bool :=
  (BitString.enumList ψ.vars.length).any fun w => SAT.verifier (ψ, w)

/-- The brute-force procedure decides `SAT`, so it meets the hypothesis of
`SAT.verifier_search` at every length. -/
theorem bruteSAT_iff (ψ : CNF ℕ) : bruteSAT ψ = true ↔ ψ ∈ SAT := by
  rw [bruteSAT, List.any_eq_true]
  constructor
  · rintro ⟨w, -, hw⟩
    exact ⟨_, hw⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨ψ.vars.map τ, BitString.mem_enumList.2 (by simp), ?_⟩
    refine (CNF.eval_congr fun v hv => ?_).trans hτ
    have hlt : ψ.vars.idxOf v < ψ.vars.length := List.idxOf_lt_length_iff.2 hv
    rw [SAT.assignment, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
      List.getElem_idxOf hlt]

/-- `(x₀ ∨ x₁) ∧ ¬x₀`, with literal occurrences `x₀, x₁, x₀`. -/
def φ₁ : CNF ℕ := [[(0, true), (1, true)], [(0, false)]]

-- `x₀` is fixed to false, then `x₁` to true; the second occurrence of `x₀` repeats its value.
example : SAT.selfReduce bruteSAT φ₁ = [(0, false), (1, true), (0, false)] := by decide
example : SAT.search bruteSAT φ₁ = [false, true, false] := by decide
example : SAT.verifier (φ₁, SAT.search bruteSAT φ₁) = true := by decide

example : SAT.verifier (φ₁, SAT.search bruteSAT φ₁) = true :=
  SAT.verifier_search (fun ψ _ => bruteSAT_iff ψ) ⟨fun v => v == 1, by decide⟩

/-- `x₀ ∧ ¬x₀`. -/
def φ₂ : CNF ℕ := [[(0, true)], [(0, false)]]

-- On an unsatisfiable formula, no certificate is accepted.
example : SAT.verifier (φ₂, SAT.search bruteSAT φ₂) = false := by decide

-- With wrong answers, the self-reduction can miss a satisfying assignment.
example : SAT.search (fun _ => true) φ₁ = [true, true, true] := by decide
example : SAT.verifier (φ₁, SAT.search (fun _ => true) φ₁) = false := by decide

example : SAT.queryBound 1 = 39 := rfl

/-! ### Advice strings -/

/-- A family of circuits for the first input bit, `false` on the empty input. -/
def firstBit : (m : ℕ) → Circuit signature m 1
  | 0 => ⟨Program.empty.gate ⟨Op.const false, ![]⟩, fun _ => Wire.gate 0⟩
  | _ + 1 => ⟨Program.empty.gate ⟨Op.or, ![Wire.input 0, Wire.input 0]⟩, fun _ => Wire.gate 0⟩

theorem size_firstBit (m : ℕ) : (firstBit m).size ≤ 1 := by
  cases m <;> rfl

example : (familyAdvice 3 1 firstBit).length = 4 * certLength 3 1 :=
  length_familyAdvice fun m _ => size_firstBit m

example : evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [] = false := by decide
example : evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [true, false] = true := by
  decide
example : evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [false, true, true] = false :=
  by decide

example (x : List Bool) (hx : x.length ≤ 3) :
    evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) x =
      (firstBit x.length).eval interpretation (fun i => x[i]) 0 :=
  evalAdvice_familyAdvice (fun m _ => size_firstBit m) hx

-- Beyond the listed lengths the advice string is empty: it reads as no gates and output wire `0`,
-- the first input.
example : evalAdvice 1 (certLength 3 1) (familyAdvice 3 1 firstBit) [true, true, true, true] =
    true := by decide

/-! ### Nonuniform quantifier elimination and `PH ⊆ P/poly` -/

example (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    (k : ℕ) {A : Language Bool} (hA : (A : Set (List Bool)) ∈ SigmaP k encBits) :
    A ∈ PPoly :=
  mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly hNP hA

example (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    (k : ℕ) {A : Language Bool} (hA : (A : Set (List Bool)) ∈ PiP k encBits) :
    A ∈ PPoly :=
  mem_PPoly_of_mem_PiP_of_NP_subset_PPoly hNP hA

example (hNP : ∀ B : Language Bool, (B : Set (List Bool)) ∈ NP encBits → B ∈ PPoly)
    {A : Language Bool} (hA : (A : Set (List Bool)) ∈ PH encBits) :
    A ∈ PPoly :=
  mem_PPoly_of_mem_PH_of_NP_subset_PPoly hNP hA

example (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    {α : Type} {enc : α ↪ List Bool} (k : ℕ) {A : Set α} (hA : A ∈ SigmaP k enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  exists_mem_PPoly_of_mem_SigmaP_of_SAT hSAT hA

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.SAT.verifier_search' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.verifier_search

/--
info: 'Cslib.Complexity.SAT.computableInPolyTime_search' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.computableInPolyTime_search

/--
info: 'Cslib.Complexity.SAT.exists_search' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.exists_search

/--
info: 'Cslib.Circuits.Boolean.evalAdvice_familyAdvice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.evalAdvice_familyAdvice

/--
info: 'Cslib.Circuits.Boolean.computableInPolyTime_evalAdvice' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.computableInPolyTime_evalAdvice

/--
info: 'Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT

/--
info: 'Cslib.Complexity.PiP_two_eq_SigmaP_two_of_SAT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PiP_two_eq_SigmaP_two_of_SAT

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_SAT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_SAT

/--
info: 'Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly

/--
info: 'Cslib.Complexity.PolyTimeReducible.exists_mem_PPoly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.exists_mem_PPoly

/--
info: 'Cslib.Complexity.mem_PPoly_of_exists_frame_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PPoly_of_exists_frame_append

/--
info: 'Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff

/--
info: 'Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff_SAT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.forall_mem_NP_exists_mem_PPoly_iff_SAT

/--
info: 'Cslib.Complexity.forall_mem_NP_encBits_mem_PPoly_iff_SAT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.forall_mem_NP_encBits_mem_PPoly_iff_SAT

/--
info: 'Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP

/--
info: 'Cslib.Complexity.exists_mem_PPoly_of_mem_PiP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_PPoly_of_mem_PiP

/--
info: 'Cslib.Complexity.exists_mem_PPoly_of_mem_PH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_PPoly_of_mem_PH

/--
info: 'Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP_of_NP_subset_PPoly

/--
info: 'Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP_of_SAT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_mem_PPoly_of_mem_SigmaP_of_SAT

/--
info: 'Cslib.Complexity.SigmaP_subset_PPoly_of_NP_subset_PPoly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SigmaP_subset_PPoly_of_NP_subset_PPoly

/--
info: 'Cslib.Complexity.PiP_subset_PPoly_of_NP_subset_PPoly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_subset_PPoly_of_NP_subset_PPoly

/--
info: 'Cslib.Complexity.PH_subset_PPoly_of_NP_subset_PPoly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_subset_PPoly_of_NP_subset_PPoly

end Cslib.Complexity.Tests.KarpLipton2
