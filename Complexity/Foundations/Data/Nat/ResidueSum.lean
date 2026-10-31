/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Range
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact counts from streamed residues

A count `N` that is known to lie below a modulus `m` is recovered exactly from residues modulo
`m`: an accumulator that adds one term at a time and reduces modulo `m` ends at the sum of the terms
modulo `m` (`Nat.foldl_range_add_mod`), and if the terms are congruent to numbers summing to
`N < m`, it ends at `N` itself (`Nat.foldl_range_add_mod_eq_of_lt`). The accumulator is one
residue, however many terms are added.

This is how the deterministic counting simulations of #1833 obtain the exact number of accepting
choice strings, at most `2 ^ τ`, from contractions computed modulo `2 ^ (τ + 1)` and summed over
all movement schedules.

## Main results

* `Nat.foldl_range_add_mod`: streaming a sum modulo `m`.
* `Nat.foldl_range_add_mod_eq_of_lt`: exact recovery of a count below the modulus.
-/

public section

namespace Nat

/-- **Streaming a sum modulo `m`.** Adding the terms `f 0, …, f (n - 1)` one at a time to the
residue of `a` and reducing modulo `m` after each step gives `(a + ∑ f i) % m`. -/
theorem foldl_range_add_mod (f : ℕ → ℕ) (m a n : ℕ) :
    (List.range n).foldl (fun acc i => (acc + f i) % m) (a % m) =
      (a + ∑ i ∈ Finset.range n, f i) % m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, Nat.mod_add_mod, Nat.add_assoc]

/-- **Exact recovery of a count below the modulus.** If each term `f i` is congruent modulo `m`
to `g i`, and the `g i` sum to `N < m`, the streamed sum of the `f i` modulo `m`, from `0`, is
exactly `N`. -/
theorem foldl_range_add_mod_eq_of_lt {f g : ℕ → ℕ} {m n N : ℕ}
    (hfg : ∀ i < n, f i % m = g i % m) (hsum : ∑ i ∈ Finset.range n, g i = N) (hN : N < m) :
    (List.range n).foldl (fun acc i => (acc + f i) % m) 0 = N := by
  have h := foldl_range_add_mod f m 0 n
  rw [Nat.zero_mod, Nat.zero_add] at h
  rw [h, Finset.sum_nat_mod, Finset.sum_congr rfl fun i hi => hfg i (Finset.mem_range.mp hi),
    ← Finset.sum_nat_mod, hsum, Nat.mod_eq_of_lt hN]

end Nat
