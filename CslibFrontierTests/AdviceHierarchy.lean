/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Boolean.Advice.Hierarchy

/-! # Advice hierarchy clients and boundary cases

Assemble the strict P/1 versus P/poly endpoint, extract an actual separating language,
and check constant and maximal-capacity schedules. Zero advice cannot be strictly separated
from its natural predecessor; constant schedules need capacity only eventually.
-/

open Cslib.Complexity Cslib.Circuits.Boolean

-- Goldreich Theorem 3.7's strictness, together with a witness requiring two advice bits.
example : PWithAdvice (fun _ => 1) ⊂ PPoly ∧
    ∃ L, L ∈ PWithAdvice (fun _ => 2) ∧ L ∉ PWithAdvice (fun _ => 1) :=
  ⟨PWithAdvice_const_ssubset_PPoly 1,
    Set.exists_of_ssubset (PWithAdvice_const_ssubset_succ 1)⟩

-- The zero-bit boundary agrees with the established ordinary P class.
example : P Turing.MultiTapeTM.encBits ⊂ PWithAdvice (fun _ => 1) := by
  rw [← PWithAdvice_zero_eq_P]
  exact PWithAdvice_const_ssubset_succ 0

-- Constant advice larger than the empty-input truth table is still allowed.
example : ∃ L, L ∈ PWithAdvice (fun _ => 5) ∧ L ∉ PWithAdvice (fun _ => 4) :=
  Set.exists_of_ssubset (PWithAdvice_const_ssubset_succ 4)

-- The maximal truth-table schedule is included, even though it is exponential in n.
example : PWithAdvice (fun n => 2 ^ n - 1) ⊂ PWithAdvice (fun n => 2 ^ n) :=
  PWithAdvice_pred_ssubset (fun n => Nat.two_pow_pos n)
    (Filter.Eventually.of_forall (fun _ => le_rfl))

-- Positivity is necessary when using natural-number predecessor.
example : ¬ (PWithAdvice (fun _ => 0 - 1) ⊂ PWithAdvice (fun _ => 0)) := by
  simp
