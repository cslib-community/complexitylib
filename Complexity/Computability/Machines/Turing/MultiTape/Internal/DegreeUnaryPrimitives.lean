/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.UnaryMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.WordPredicates
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives

/-!
# Direct unary degree primitives

Streaming machines implement successor and saturating predecessor with linear cost and output
growth. No higher tidy computability calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM
namespace Internal.Unary

/-- Drop the first unary symbol and copy the remaining input. -/
private def predT : Transducer Bool Bool where
  q₀ := false
  step seen b := (true, if seen then [b] else [])
  final _ := []
  length_step_le seen _ := by cases seen <;> simp
  length_final_le _ := by simp

private lemma predT_run_true (w : List Bool) : predT.run true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [b] ++ predT.run true w = b :: w
    simp [ih]

private lemma predT_run (w : List Bool) : predT.run false w = w.tail := by
  cases w with
  | nil => rfl
  | cons b w =>
    change [] ++ predT.run true w = w
    simp [predT_run_true]

end Internal.Unary
namespace ComputableInDegree
open Internal.Unary

/-- Successor on unary natural numbers, including the empty encoding of zero. -/
theorem unary_succ : ComputableInDegree (· + 1) encUnary encUnary 1 1 := by
  refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, unarySuccTransducer.toTM, fun n => ?_⟩,
    ⟨1, fun n => by simp⟩⟩
  have heq : encUnary (n + 1) =
      unarySuccTransducer.run unarySuccTransducer.q₀ (encUnary n) := by
    rw [show unarySuccTransducer.q₀ = true from rfl, (unarySuccRun _).1]
    simp [List.replicate_succ]
  simpa only [heq] using unarySuccTransducer.computesInTimeAndSpace_toTM (encUnary n)

/-- Saturating predecessor on unary natural numbers. -/
theorem unary_pred : ComputableInDegree (· - 1) encUnary encUnary 1 1 := by
  refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, predT.toTM, fun n => ?_⟩,
    ⟨1, fun n => by simp; omega⟩⟩
  have heq : encUnary (n - 1) = predT.run predT.q₀ (encUnary n) := by
    rw [show predT.q₀ = false from rfl, predT_run]
    cases n <;> simp [List.replicate_succ]
  simpa only [heq] using predT.computesInTimeAndSpace_toTM (encUnary n)

/-- The unary zero test preserves the original linear cost and output-degree contract. -/
theorem unary_isZero :
    ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 1 := by
  have hn : ComputableInDegree (fun n => decide (n ≠ 0)) encUnary encBool 1 0 := by
    refine ⟨⟨fun n => 2 * (encUnary n).length + 3, fun _ => 0,
      ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
      0, _, inferInstance, Internal.WordPredicates.nonemptyT.toTM, fun n => ?_⟩,
      ⟨1, fun n => by simp⟩⟩
    have heq : encBool (decide (n ≠ 0)) = Internal.WordPredicates.nonemptyT.run
        Internal.WordPredicates.nonemptyT.q₀ (encUnary n) := by
      cases n with
      | zero => rfl
      | succ n =>
        change [true] = [true] ++ Internal.WordPredicates.nonemptyT.run true
          (List.replicate n true)
        rw [Internal.WordPredicates.nonemptyT_run_true, List.append_nil]
    simpa only [heq] using
      Internal.WordPredicates.nonemptyT.computesInTimeAndSpace_toTM (encUnary n)
  have hnot := (of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp hn
  have hz : ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 0 := by
    convert hnot using 1 <;> simp [Function.comp_def]
  exact ⟨hz.1, hz.2.mono_deg (by decide)⟩

end ComputableInDegree
end Turing.MultiTapeTM
