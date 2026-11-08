/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.SemanticDerivation
import Mathlib.Tactic.FinCases

/-!
# Tests: interpolation for semantic derivations

The two initial sets `x₀ = 1` (Alice's side, `SA`) and `x₀ = 0` (Bob's side, `SB`), each with one
private variable, have the three-line semantic refutation `Ã, B̃, ∅` (`lines`).

* Deciding whether `(v, q, r)` lies in a line takes one bit, and the monotone search at `Ã` takes
  none, so `IsSemanticRefutation.exists_monotone_circuit` gives a monotone separator with at most
  `(3 · 2 ^ 2 + 1) · 2 ^ 3 = 104` gates.
* Every line has communication complexity `CC ≤ 1` and monotone communication complexity
  `MCC_U ≤ 1`, so both parts of Krajíček's Theorem 5.1 apply. At `B̃` the monotone task is
  solved only by its second outcome, `∃ u' ≥ u` leaving the line.
* `![∅]` is not a semantic derivation from these initial sets.
-/

namespace ComplexityTests.SemanticDerivation

open Cslib Cslib.Communication Cslib.Circuits Cslib.Logic.PL Cslib.Logic.PL.SemanticDerivation

/-- Alice's initial set `x₀ = 1`. -/
private def SA : Set (Fin 1 ⊕ Unit → Bool) := {f | f (.inl 0) = true}

/-- Bob's initial set `x₀ = 0`. -/
private def SB : Set (Fin 1 ⊕ Unit → Bool) := {f | f (.inl 0) = false}

/-- The refutation `Ã, B̃, ∅`. -/
private def lines : Fin 3 → Set (Fin 1 ⊕ (Unit ⊕ Unit) → Bool) :=
  ![leftCylinder SA, rightCylinder SB, ∅]

private theorem mem_lines_zero {f : Fin 1 ⊕ (Unit ⊕ Unit) → Bool} :
    f ∈ lines 0 ↔ f (.inl 0) = true :=
  Iff.rfl

private theorem mem_lines_one {f : Fin 1 ⊕ (Unit ⊕ Unit) → Bool} :
    f ∈ lines 1 ↔ f (.inl 0) = false :=
  Iff.rfl

private theorem lines_isSemanticRefutation : IsSemanticRefutation (initSets {SA} {SB}) lines := by
  refine ⟨fun j => ?_, 2, rfl⟩
  fin_cases j
  · exact Or.inl (Or.inl ⟨SA, rfl, rfl⟩)
  · exact Or.inl (Or.inr ⟨SB, rfl, rfl⟩)
  · refine Or.inr (Or.inr ⟨0, 1, by decide, by decide, ?_⟩)
    rintro f ⟨h₁, h₂⟩
    rw [mem_lines_zero] at h₁
    rw [mem_lines_one, h₁] at h₂
    exact Bool.noConfusion h₂

/-- Bob decides whether `(v, q, r)` lies in a line by looking at `v₀`. -/
private def bobProto :
    Fin 3 → Protocol ((Fin 1 → Bool) × (Unit → Bool)) ((Fin 1 → Bool) × (Unit → Bool)) Bool :=
  ![.bob (fun b => b.1 0) (.output false) (.output true),
    .bob (fun b => b.1 0) (.output true) (.output false), .output false]

/-- Alice decides whether `(u, q, r)` lies in a line by looking at `u₀`. -/
private def aliceProto :
    Fin 3 → Protocol ((Fin 1 → Bool) × (Unit → Bool)) ((Fin 1 → Bool) × (Unit → Bool)) Bool :=
  ![.alice (fun a => a.1 0) (.output false) (.output true),
    .alice (fun a => a.1 0) (.output true) (.output false), .output false]

private theorem bobProto_solves (j : Fin 3) :
    (bobProto j).Solves (Decides (MemRight (lines j))) Set.univ Set.univ := by
  intro a _ b _
  fin_cases j <;> cases h : b.1 0 <;>
    simp [bobProto, Decides, MemRight, lines, leftCylinder, rightCylinder, SA, SB, h]

private theorem aliceProto_solves (j : Fin 3) :
    (aliceProto j).Solves (Decides (MemLeft (lines j))) Set.univ Set.univ := by
  intro a _ b _
  fin_cases j <;> cases h : a.1 0 <;>
    simp [aliceProto, Decides, MemLeft, lines, leftCylinder, rightCylinder, SA, SB, h]

private theorem depth_bobProto_le (j : Fin 3) : (bobProto j).depth ≤ 1 := by
  fin_cases j <;> simp [bobProto]

private theorem depth_aliceProto_le (j : Fin 3) : (aliceProto j).depth ≤ 1 := by
  fin_cases j <;> simp [aliceProto]

private theorem hmem (j : Fin 3) :
    Protocol.ecomplexity (Decides (MemRight (lines j))) (Models {SA}) (Models {SB}) ≤ 1 :=
  Protocol.ecomplexity_le_iff.2 ⟨bobProto j,
    (bobProto_solves j).mono (Set.subset_univ _) (Set.subset_univ _), depth_bobProto_le j⟩

private theorem hsearch (j : Fin 3) (S) (hS : S ∈ ({SA} : Set (Set (Fin 1 ⊕ Unit → Bool))))
    (_ : leftCylinder S = lines j) :
    Protocol.ecomplexity (Search S ExceedsAt) (Models {SA}) (Models {SB}) ≤ 1 := by
  rw [Set.mem_singleton_iff] at hS
  subst hS
  refine Protocol.ecomplexity_le_iff.2 ⟨.output (some 0), fun a _ b _ h₁ h₂ => ?_, by simp⟩
  exact ⟨0, rfl, h₁, by simpa [SA] using h₂⟩

/-- The three-line refutation gives a monotone separator with at most `104` gates. -/
example : ∃ C : Circuit Monotone.signature 1 1, C.size ≤ 104 ∧
    (∀ u q, (u, q) ∈ Models {SA} → C.eval Monotone.interpretation u 0 = true) ∧
    ∀ v r, (v, r) ∈ Models {SB} → C.eval Monotone.interpretation v 0 = false := by
  obtain ⟨C, hC, hU, hV⟩ := lines_isSemanticRefutation.exists_monotone_circuit hmem hsearch
  exact ⟨C, hC.trans (by norm_num), hU, hV⟩

/-- Every line has communication complexity at most one. -/
private theorem commComplexity_lines_le (j : Fin 3) : commComplexity (lines j) ≤ 1 := by
  refine max_le (max_le ?_ ?_) ?_
  · exact Protocol.ecomplexity_le_iff.2 ⟨aliceProto j, aliceProto_solves j, depth_aliceProto_le j⟩
  · exact Protocol.ecomplexity_le_iff.2 ⟨bobProto j, bobProto_solves j, depth_bobProto_le j⟩
  · refine Protocol.ecomplexity_le_iff.2 ⟨.output 0, fun a _ b _ h => ?_, by simp⟩
    fin_cases j <;> cases ha : a.1 0 <;> cases hb : b.1 0 <;>
      simp_all [MemLeft, MemRight, lines, leftCylinder, rightCylinder, SA, SB]

/-- **Theorem 5.1**, first part, applies to the three-line refutation. -/
example : ∃ C : Circuit Boolean.signature 1 1, C.size ≤ 104 ∧
    (∀ u q, (u, q) ∈ Models {SA} → C.eval Boolean.interpretation u 0 = true) ∧
    ∀ v r, (v, r) ∈ Models {SB} → C.eval Boolean.interpretation v 0 = false := by
  obtain ⟨C, hC, hU, hV⟩ :=
    lines_isSemanticRefutation.exists_circuit_of_commComplexity_le commComplexity_lines_le
  exact ⟨C, hC.trans (by norm_num), hU, hV⟩

/-- The monotone task: at `Ã` the answer is the coordinate `0`; at `B̃`, where `(u, q, r) ∈ B̃`
means `u₀ = 0`, the answer is `none`, witnessed by `u' = 1`. -/
private def task4Proto :
    Fin 3 → Protocol ((Fin 1 → Bool) × (Unit → Bool)) ((Fin 1 → Bool) × (Unit → Bool))
      (Option (Fin 1)) :=
  ![.output (some 0), .output none, .output none]

/-- Every line has monotone communication complexity at most one. -/
private theorem monotoneCommComplexity_lines_le (j : Fin 3) :
    monotoneCommComplexity (lines j) ≤ 1 := by
  refine max_le (commComplexity_lines_le j) ?_
  refine Protocol.ecomplexity_le_iff.2 ⟨task4Proto j, fun a _ b _ h₁ h₂ => ?_, ?_⟩
  · fin_cases j
    · simp_all [task4Proto, MemLeft, MemRight, lines, leftCylinder, SA]
    · exact ⟨fun _ => true, fun _ => le_top, by simp [MemLeft, lines, rightCylinder, SB]⟩
    · simp [MemLeft, lines] at h₁
  · fin_cases j <;> simp [task4Proto]

/-- **Theorem 5.1**, monotone part, applies to the three-line refutation. -/
example : ∃ C : Circuit Monotone.signature 1 1, C.size ≤ 104 ∧
    (∀ u q, (u, q) ∈ Models {SA} → C.eval Monotone.interpretation u 0 = true) ∧
    ∀ v r, (v, r) ∈ Models {SB} → C.eval Monotone.interpretation v 0 = false := by
  have hmono : ∀ u u' q, (u, q) ∈ Models ({SA} : Set (Set (Fin 1 ⊕ Unit → Bool))) → u ≤ u' →
      (u', q) ∈ Models {SA} := by
    intro u u' q h hu S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    have h0 : u 0 = true := h SA rfl
    have := hu 0
    rw [h0] at this
    exact top_le_iff.1 this
  obtain ⟨C, hC, hU, hV⟩ :=
    lines_isSemanticRefutation.exists_monotone_circuit_of_monotoneCommComplexity_le hmono
      monotoneCommComplexity_lines_le
  exact ⟨C, hC.trans (by norm_num), hU, hV⟩

/-- A line that is neither initial, nor everything, nor derived from earlier lines is rejected. -/
example :
    ¬ IsSemanticDerivation (initSets {SA} {SB}) ![(∅ : Set (Fin 1 ⊕ (Unit ⊕ Unit) → Bool))] := by
  intro h
  rcases h 0 with (⟨S, hS, h⟩ | ⟨S, hS, h⟩) | h | ⟨i₁, _, h₁, _⟩
  · rw [Set.mem_singleton_iff] at hS
    subst hS
    have : (fun _ => true : Fin 1 ⊕ (Unit ⊕ Unit) → Bool) ∈ leftCylinder SA := rfl
    rw [h] at this
    exact this
  · rw [Set.mem_singleton_iff] at hS
    subst hS
    have : (fun _ => false : Fin 1 ⊕ (Unit ⊕ Unit) → Bool) ∈ rightCylinder SB := rfl
    rw [h] at this
    exact this
  · exact Set.empty_ne_univ h
  · exact absurd h₁ (Fin.not_lt_zero _)

end ComplexityTests.SemanticDerivation
