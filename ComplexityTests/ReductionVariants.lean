/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.OneOne
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Concrete one-one, disjunctive, conjunctive and bounded truth-table reductions

Each example builds an explicit reduction to an arbitrary target set `B` of bit strings, by
prefixing one bit: `w ↦ b :: w`.
-/

@[expose] public section

namespace Cslib.Complexity.Tests.ReductionVariants

open Turing.MultiTapeTM

variable (B : Set (List Bool))

/-- Prefixing `true` is injective, so it is a one-one reduction. -/
example : PolyTimeOneOneReducible encBits encBits {w | true :: w ∈ B} B :=
  ⟨fun w => true :: w, ⟨by fun_prop, fun _ _ h => List.cons_injective h⟩, fun _ => Iff.rfl⟩

/-- Asking for both prefixes, and accepting when either is in `B`. -/
example : PolyTimeDTTReducible encBits encBits {w | false :: w ∈ B ∨ true :: w ∈ B} B := by
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

/-- The same queries, accepting when both are in `B`. -/
example : PolyTimeCTTReducible encBits encBits {w | false :: w ∈ B ∧ true :: w ∈ B} B := by
  refine ⟨fun _ => 2, fun x => decide (x.2 = 1) :: x.1, by fun_prop, by fun_prop, fun w => ?_⟩
  constructor
  · rintro ⟨h₀, h₁⟩ i hi
    obtain _ | _ | i := i
    · simpa using h₀
    · simpa using h₁
    · simp at hi
  · intro h
    exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp)⟩

/-- A `2`-truth-table reduction whose combiner, exclusive or, is not monotone, so it is not of
disjunctive, conjunctive or positive form. -/
example : PolyTimeKTruthTableReducible 2 encBits encBits
    {w | (false :: w ∈ B) ≠ (true :: w ∈ B)} B := by
  classical
  refine ⟨fun _ => 2, fun x => decide (x.2 = 1) :: x.1,
    fun x => x.2.headD false ^^ (x.2.drop 1).headD false, by fun_prop, by fun_prop, by fun_prop,
    fun _ => le_rfl, fun w => ?_⟩
  simp only [truthTableAnswers, Set.mem_preimage]
  by_cases h₀ : false :: w ∈ B <;> by_cases h₁ : true :: w ∈ B <;> simp [List.ofFn_succ, h₀, h₁]

/-- Pointwise order of answer words is preserved by reading a position. -/
theorem headD_drop_le {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) (n : ℕ) :
    (u.drop n).headD false ≤ (v.drop n).headD false := by
  induction h generalizing n with
  | nil => exact le_rfl
  | cons hab _ ih => cases n with
    | zero => exact hab
    | succ n => exact ih n

/-- Majority of three queries: a positive truth-table reduction that is neither disjunctive nor
conjunctive. -/
example : PolyTimePTTReducible encBits encBits
    {w | (false :: false :: w ∈ B ∧ true :: false :: w ∈ B) ∨
      (false :: false :: w ∈ B ∧ false :: true :: w ∈ B) ∨
      (true :: false :: w ∈ B ∧ false :: true :: w ∈ B)} B := by
  classical
  refine ⟨fun _ => 3, fun x => decide (x.2 = 1) :: decide (x.2 = 2) :: x.1,
    fun x => (x.2.headD false && (x.2.drop 1).headD false) ||
      (x.2.headD false && (x.2.drop 2).headD false) ||
      ((x.2.drop 1).headD false && (x.2.drop 2).headD false),
    by fun_prop, by fun_prop, by fun_prop, fun _ u v huv => ?_, fun w => ?_⟩
  · dsimp only
    have h₀ := headD_drop_le huv 0
    have h₁ := headD_drop_le huv 1
    have h₂ := headD_drop_le huv 2
    simp only [List.drop_zero] at h₀
    revert h₀ h₁ h₂
    generalize u.headD false = a; generalize (u.drop 1).headD false = b
    generalize (u.drop 2).headD false = c; generalize v.headD false = a'
    generalize (v.drop 1).headD false = b'; generalize (v.drop 2).headD false = c'
    revert a b c a' b' c'
    decide
  · simp only [truthTableAnswers, Set.mem_preimage]
    by_cases h₀ : false :: false :: w ∈ B <;> by_cases h₁ : true :: false :: w ∈ B <;>
      by_cases h₂ : false :: true :: w ∈ B <;> simp [List.ofFn_succ, h₀, h₁, h₂]

/-- Composing the exclusive-or reduction with itself: four queries `b₁ :: b₂ :: w`. -/
example : PolyTimeKTruthTableReducible 4 encBits encBits
    {w | (false :: w ∈ {v | (false :: v ∈ B) ≠ (true :: v ∈ B)}) ≠
      (true :: w ∈ {v | (false :: v ∈ B) ≠ (true :: v ∈ B)})} B := by
  have h : ∀ B' : Set (List Bool), PolyTimeKTruthTableReducible 2 encBits encBits
      {w | (false :: w ∈ B') ≠ (true :: w ∈ B')} B' := fun B' => by
    classical
    refine ⟨fun _ => 2, fun x => decide (x.2 = 1) :: x.1,
      fun x => x.2.headD false ^^ (x.2.drop 1).headD false, by fun_prop, by fun_prop, by fun_prop,
      fun _ => le_rfl, fun w => ?_⟩
    simp only [truthTableAnswers, Set.mem_preimage]
    by_cases h₀ : false :: w ∈ B' <;> by_cases h₁ : true :: w ∈ B' <;>
      simp [List.ofFn_succ, h₀, h₁]
  exact (h _).trans (h B)

end Cslib.Complexity.Tests.ReductionVariants
