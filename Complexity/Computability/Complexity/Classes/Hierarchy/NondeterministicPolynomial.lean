/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.NondeterministicTime
public import Complexity.Computability.Complexity.Classes.Padding.NondeterministicPolynomial
public import Complexity.Computability.Complexity.Classes.Time.Polynomial
import Mathlib.Tactic.Linarith

/-!
# The nondeterministic hierarchy at every integer polynomial degree

For integers `1 ≤ a < b`, `NTIME (n ^ a)` is strictly contained in `NTIME (n ^ b)` on bit
strings (`Cslib.Complexity.NTIME_pow_ssubset_NTIME_pow`). The result has the conventional native
multitape-machine semantics of `NTIME`: finite-state nondeterministic machines with a binary
alphabet, every computation path halting within the bound.

The proof amplifies a hypothetical collapse `NTIME ((n + 1) ^ b) ⊆ NTIME ((n + 1) ^ a)` by
polynomial padding (`Cslib.Complexity.NTIME_pow_mul_subset_of_subset`), which propagates it to
`NTIME ((n + 1) ^ (b * k)) ⊆ NTIME ((n + 1) ^ (a * (k + 1) + 1))` for every `k ≥ 1`. Once
`3 * a ≤ k`, the degree `a * (k + 3)` is at most `b * k`, and `a * (k + 1) + 1` is at most
`a * (k + 2)`. So each class at degree `a * (k + 3)` collapses to the class at degree
`a * (k + 2)`, and every class at a degree `a * j` with `j ≥ 3 * a + 2` collapses to the class at
degree `D = a * (3 * a + 2)`. This contradicts the coarse hierarchy obtained by lazy
diagonalization (`Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le`), which separates
degree `D` from degree `6 * D + 14`. Unlike the deterministic case
(`Cslib.Complexity.DTIME_pow_ssubset_DTIME_pow`), the linear degree `a = 1` needs no separate
argument: the transfer already loses a degree, and the amplification absorbs it.

The hierarchy is a classical consequence of the nondeterministic time hierarchy theorem
[Arora and Barak, Theorem 3.3][AroraBarak07]. The proof combines native polynomial padding with the
library's coarse lazy diagonal; the amplification is proved here. Arbitrary real exponents and the
textbook gap `f (n + 1) = o (g n)` are not claimed by this theorem.

## Main results

* `Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow`: strictness for `(n + 1)` powers.
* `Cslib.Complexity.NTIME_pow_ssubset_NTIME_pow`: strictness for the conventional `n` powers.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Every two distinct positive integer polynomial degrees give distinct nondeterministic time
classes.** Padding propagates a collapse to overlapping intervals of exponents, so all classes
above degree `a * (3 * a + 2)` would collapse to it, contradicting the coarse lazy-diagonal
hierarchy. -/
theorem NTIME_succ_pow_ssubset_NTIME_succ_pow {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    NTIME encBits (fun n => (n + 1) ^ a) ⊂ NTIME encBits (fun n => (n + 1) ^ b) := by
  have hsub {d e : ℕ} (h : d ≤ e) :
      NTIME encBits (fun n => (n + 1) ^ d) ⊆ NTIME encBits (fun n => (n + 1) ^ e) :=
    NTIME_mono fun n => Nat.pow_le_pow_right (by omega) h
  refine ⟨hsub hab.le, fun hcollapse => ?_⟩
  -- one step of the amplification, from degree `a * (k + 3)` down to `a * (k + 2)`
  have hstep (k : ℕ) (hk : 3 * a ≤ k) :
      NTIME encBits (fun n => (n + 1) ^ (a * (k + 3))) ⊆
        NTIME encBits (fun n => (n + 1) ^ (a * (k + 2))) := by
    have hup : a * (k + 3) ≤ b * k := by nlinarith
    have hdown : a * (k + 1) + 1 ≤ a * (k + 2) := by nlinarith
    exact (hsub hup).trans ((NTIME_pow_mul_subset_of_subset ha (by omega) (by omega)
      hcollapse).trans (hsub hdown))
  -- every degree `a * j` with `j ≥ 3 * a + 2` collapses to degree `a * (3 * a + 2)`
  have htail (j : ℕ) (hj : 3 * a + 2 ≤ j) :
      NTIME encBits (fun n => (n + 1) ^ (a * j)) ⊆
        NTIME encBits (fun n => (n + 1) ^ (a * (3 * a + 2))) := by
    induction j, hj using Nat.le_induction with
    | base => exact Set.Subset.refl _
    | succ j hj ih =>
      have h := hstep (j - 2) (by omega)
      rw [show j - 2 + 3 = j + 1 by omega, show j - 2 + 2 = j by omega] at h
      exact h.trans ih
  exact (NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le (d := a * (3 * a + 2))
    (e := a * (18 * a + 26)) (by nlinarith)).2 (htail _ (by omega))

/-- **Strict nondeterministic polynomial time levels.** For integers `1 ≤ a < b`, some binary
language is decidable in nondeterministic time `O(n ^ b)` but not `O(n ^ a)`, using the native
finite-state, binary-alphabet nondeterministic multitape machines and the usual additive
constants in `NTIME`. -/
theorem NTIME_pow_ssubset_NTIME_pow {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    NTIME encBits (fun n => n ^ a) ⊂ NTIME encBits (fun n => n ^ b) := by
  simpa only [NTIME_succ_pow_eq] using NTIME_succ_pow_ssubset_NTIME_succ_pow ha hab

end Cslib.Complexity
