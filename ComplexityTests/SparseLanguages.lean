/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Sparse

/-!
# Sparse and unary language clients

The unary clients allow an arbitrary set of lengths, without a decidability assumption.
Finite slice clients cover an empty truth table and the unique zero-input assignment.
-/

namespace ComplexityTests.SparseLanguages

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

private def unaryLengths (S : Set ℕ) : Language Bool :=
  {w | w.length ∈ S ∧ ∀ b ∈ w, b = true}

example (S : Set ℕ) :
    unaryLengths S ∈ (SIZE fun n => n + 1) ∧
    unaryLengths S ∈ PPoly ∧
    ([] : List Bool) ∈ unaryLengths {0} ∧
    [true, true] ∈ unaryLengths {2} ∧
    [true, false] ∉ unaryLengths Set.univ :=
  ⟨mem_SIZE_of_unary fun _ hw => hw.2,
    PPoly.of_unary fun _ hw => hw.2,
    by change _ ∧ _; simp,
    by change _ ∧ _; simp,
    by change ¬ (_ ∧ _); simp⟩

example (n : ℕ) :
    complexity interpretation (single ((0 : Language Bool).slice n)) ≤ 1 ∧
    complexity interpretation (single ((⊤ : Language Bool).slice 0)) ≤ 3 := by
  refine ⟨?_, ?_⟩
  · have h : #{x : BitString n | (0 : Language Bool).slice n x = true} ≤ 0 := by
      apply le_of_eq
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro x
      simp only [mem_filter, mem_univ, true_and]
      exact fun hx => Language.slice_eq_true_iff.mp hx
    simpa using complexity_slice_le_of_card_le h
  · apply complexity_slice_le_of_card_le (k := 1)
    exact (Finset.card_filter_le _ _).trans (by simp)

example : (0 : Language Bool) ∈ PPoly := by
  apply PPoly.of_sparse (s := fun _ => 0) (by fun_prop)
  intro n
  apply le_of_eq
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x
  simp only [mem_filter, mem_univ, true_and]
  exact fun hx => Language.slice_eq_true_iff.mp hx

end ComplexityTests.SparseLanguages
