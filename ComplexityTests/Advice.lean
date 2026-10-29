/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Advice

/-!
# Polynomial advice clients

Prefix substitution preserves live suffix inputs, including empty prefixes and suffixes.
The empty and full languages inhabit the advice class using actual constant-time deciders.
-/

namespace ComplexityTests.Advice

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

example (x : BitString 2) (r : BitString 2) :
    (substitute (prependInputs (fun _ : Fin 1 => true)) ![false, true]) 0 = true ∧
    (substitute (prependInputs (fun _ : Fin 1 => true)) ![false, true]) 1 = false ∧
    substitute (prependInputs (n := 2) Fin.elim0) x = x ∧
    substitute (prependInputs (n := 0) r) Fin.elim0 = r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [substitute_prependInputs]
    rfl
  · rw [substitute_prependInputs]
    rfl
  · rw [substitute_prependInputs]
    ext i
    fin_cases i <;> rfl
  · rw [substitute_prependInputs]
    ext i
    fin_cases i <;> rfl

example (r : BitString 1) (x : BitString 2) :
    (substituteCircuit (prependInputs r)).eval interpretation x = Fin.append r x := by
  rw [eval_substituteCircuit, substitute_prependInputs]

private theorem top_mem_advice : (⊤ : Language Bool) ∈ PAdvice := by
  refine ⟨fun _ => [], (by change PolynomiallyBounded fun _ : ℕ => 0; fun_prop),
    Set.univ, ?_, fun _ => Iff.rfl⟩
  exact ⟨fun _ => true, ComputableInPolyTime.const _, fun _ => by simp⟩

private theorem zero_mem_advice : (0 : Language Bool) ∈ PAdvice := by
  refine ⟨fun _ => [true], (by change PolynomiallyBounded fun _ : ℕ => 1; fun_prop),
    ∅, ?_, fun _ => Iff.rfl⟩
  exact ⟨fun _ => false, ComputableInPolyTime.const _, fun _ => by simp⟩

example :
    (⊤ : Language Bool) ∈ PPoly ∧
    (0 : Language Bool) ∈ PPoly ∧
    (⊤ : Language Bool) ∈ PAdvice ∧
    (0 : Language Bool) ∈ PAdvice :=
  ⟨PAdvice_subset_PPoly top_mem_advice,
    PAdvice_subset_PPoly zero_mem_advice,
    PPoly_eq_PAdvice ▸ PPoly.of_advice PPoly.top_mem (fun _ => [])
      (by change PolynomiallyBounded fun _ : ℕ => 0; fun_prop) (fun _ => Iff.rfl),
    PPoly_subset_PAdvice PPoly.zero_mem⟩

example (N : Polynomial ℕ) :
    ∃ (S W P : Polynomial ℕ) (α : ℕ → List Bool),
      (∀ n, (α n).length = P.eval n) ∧
      PolynomiallyBounded (fun n => (α n).length) ∧
      ∀ n (x : List Bool), x.length ≤ N.eval n →
        (evalAdvice (S.eval n) (W.eval n) (α n) x = true ↔ x ∈ (⊤ : Language Bool)) :=
  PPoly.exists_evalAdvice PPoly.top_mem N

end ComplexityTests.Advice
