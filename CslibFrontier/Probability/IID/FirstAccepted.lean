/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The first accepted trial

Run `m` independent uniform trials `v : Fin m → T` and keep the first one accepted by `acc`
(`Cslib.Probability.firstAccepted`). Counting over all `m`-tuples:

* no trial is accepted for exactly `R ^ m` tuples, where `R` counts the rejected values
  (`Cslib.Probability.card_filter_forall_not_acc`);
* the first accepted trial is bad for at most `B N ^ m / A` tuples, where `N = #T`, `A` counts the
  accepted values and `B` the accepted bad ones
  (`Cslib.Probability.card_filter_firstAccepted_bad_mul_le`).

So the first accepted trial is bad with probability at most `Pr[bad | accepted]`, whatever `m`
is. The bound is the elementary fact behind rejection sampling with a timeout, as in the circuit
`C_{A,v}` of [Impagliazzo, Jaiswal, Kabanets and Wigderson, Section
3][ImpagliazzoJaiswalKabanetsWigderson2010].

## Main definitions

* `Cslib.Probability.firstAccepted`: the first accepted entry of a tuple, if any.

## Main results

* `Cslib.Probability.card_filter_forall_not_acc`: no trial is accepted.
* `Cslib.Probability.card_filter_firstAccepted_bad_mul_le`: the first accepted trial is bad.

## References

* [R. Impagliazzo, R. Jaiswal, V. Kabanets and A. Wigderson, *Uniform Direct Product Theorems:
  Simplified, Optimized, and Derandomized*][ImpagliazzoJaiswalKabanetsWigderson2010]
-/

public section

namespace Cslib.Probability

open Finset

variable {T : Type*}

/-- The first entry of `v` accepted by `acc`, if any. -/
def firstAccepted (acc : T → Bool) {m : ℕ} (v : Fin m → T) : Option T :=
  (List.ofFn v).find? acc

@[simp] theorem firstAccepted_zero (acc : T → Bool) (v : Fin 0 → T) :
    firstAccepted acc v = none := by
  simp [firstAccepted]

theorem firstAccepted_cons (acc : T → Bool) {m : ℕ} (a : T) (w : Fin m → T) :
    firstAccepted acc (Fin.cons a w : Fin (m + 1) → T) =
      if acc a then some a else firstAccepted acc w := by
  simp only [firstAccepted, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  cases h : acc a <;> simp [h]

/-- No trial is accepted exactly when the first accepted trial does not exist. -/
theorem firstAccepted_eq_none_iff (acc : T → Bool) {m : ℕ} (v : Fin m → T) :
    firstAccepted acc v = none ↔ ∀ i, acc (v i) = false := by
  simp [firstAccepted, List.find?_eq_none, List.mem_ofFn]

/-- The first accepted trial is accepted and is one of the trials. -/
theorem firstAccepted_eq_some {acc : T → Bool} {m : ℕ} {v : Fin m → T} {a : T}
    (h : firstAccepted acc v = some a) : acc a = true ∧ ∃ i, v i = a := by
  refine ⟨List.find?_some h, ?_⟩
  simpa [List.mem_ofFn] using List.mem_of_find?_eq_some h

variable [Fintype T]

/-- **No trial is accepted**: exactly `R ^ m` tuples have every entry rejected. -/
theorem card_filter_forall_not_acc (acc : T → Bool) (m : ℕ) :
    #{v : Fin m → T | ∀ i, acc (v i) = false} = #{a | acc a = false} ^ m := by
  rw [← Fintype.card_piFinset_const]
  congr 1
  ext v
  simp [Fintype.mem_piFinset]

/-- The tuples whose first accepted entry is bad, split along the first trial. -/
private theorem card_filter_firstAccepted_bad_succ (acc bad : T → Bool) (m : ℕ) :
    #{v : Fin (m + 1) → T | (firstAccepted acc v).any bad} =
      #{a | acc a ∧ bad a} * Fintype.card T ^ m +
        #{a | acc a = false} * #{w : Fin m → T | (firstAccepted acc w).any bad} := by
  classical
  rw [card_filter, ← (Fin.consEquiv fun _ => T).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, firstAccepted_cons]
  have hterm : ∀ a : T, (∑ w : Fin m → T,
      if (if acc a then some a else firstAccepted acc w).any bad then 1 else 0) =
      (if acc a ∧ bad a then Fintype.card T ^ m else 0) +
        (if acc a = false then #{w : Fin m → T | (firstAccepted acc w).any bad} else 0) := by
    intro a
    cases ha : acc a <;> cases hb : bad a <;> simp [*]
  rw [Finset.sum_congr rfl fun a _ => hterm a, sum_add_distrib, ← sum_filter, ← sum_filter,
    sum_const, sum_const, smul_eq_mul, smul_eq_mul]

/-- **The first accepted trial is bad** for at most a `B / A` fraction of the tuples, where `A`
counts the accepted values and `B` the accepted bad ones. -/
theorem card_filter_firstAccepted_bad_mul_le (acc bad : T → Bool) :
    ∀ m : ℕ, #{v : Fin m → T | (firstAccepted acc v).any bad} * #{a | acc a = true} ≤
      #{a | acc a ∧ bad a} * Fintype.card T ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := card_filter_firstAccepted_bad_mul_le acc bad m
    have hsplit : #{a | acc a = true} + #{a | acc a = false} = Fintype.card T := by
      simpa using card_filter_add_card_filter_not (s := univ) (p := fun a : T => acc a = true)
    rw [card_filter_firstAccepted_bad_succ, pow_succ]
    nlinarith [Nat.zero_le (#{a | acc a ∧ bad a} * Fintype.card T ^ m),
      Nat.zero_le #{a | acc a = false}]

end Cslib.Probability
