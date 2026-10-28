/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite-function digit numbering

## Main results

* `Nat.ofDigits_ofFn`: a digit list as a finite sum of weighted digits.
* `Nat.ofDigits_finFunctionFinEquiv`: agreement with Mathlib's finite-function numbering.
-/

@[expose] public section

namespace Nat

/-- Interpreting a fixed-length tuple as a least-significant-first digit list. -/
theorem ofDigits_ofFn (b : ℕ) {L : ℕ} (f : Fin L → ℕ) :
    ofDigits b (List.ofFn f) = ∑ i, f i * b ^ i.val := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.ofFn_succ, ofDigits_cons, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ']
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- `finFunctionFinEquiv` uses exactly `ofDigits`'s least-significant-first convention. -/
theorem ofDigits_finFunctionFinEquiv {b L : ℕ} (f : Fin L → Fin b) :
    ofDigits b (List.ofFn fun i => (f i).val) = (finFunctionFinEquiv f).val :=
  ofDigits_ofFn b _

end Nat
