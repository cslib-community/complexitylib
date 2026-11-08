/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Parity of Boolean lists

Executable exclusive-or folding agrees with addition in the Boolean ring and with the existing
finite-tuple `Cslib.parityOn`. The empty word has parity zero. These bridges let list-based
programs reuse the finite-coordinate parity API without changing the mathematical relation.
-/

public section

namespace Cslib.BitString

/-- Exclusive or of every bit, with zero for the empty word. -/
@[expose] def wordParity (word : List Bool) : Bool := word.foldr Bool.xor false

@[simp] theorem wordParity_nil : wordParity [] = false := rfl

@[simp] theorem wordParity_cons (b : Bool) (word : List Bool) :
    wordParity (b :: word) = (b ^^ wordParity word) := rfl

/-- List parity is the sum in the existing Boolean ring. -/
theorem wordParity_eq_sum (word : List Bool) : wordParity word = word.sum := by
  induction word with
  | nil => rfl
  | cons b word ih => simp only [wordParity_cons, List.sum_cons, ih, Bool.add_eq_xor]

/-- Folding a finite tuple computes its existing finite-set parity. -/
theorem wordParity_ofFn {n : ℕ} (x : Fin n → Bool) :
    wordParity (List.ofFn x) = parityOn Finset.univ x := by
  induction n with
  | zero => simp [parityOn]
  | succ n ih =>
    rw [List.ofFn_succ, wordParity_cons, ih]
    simp only [parityOn_eq_sum, Fin.sum_univ_succ, Bool.add_eq_xor]

end Cslib.BitString
