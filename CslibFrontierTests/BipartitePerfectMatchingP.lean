/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.BipartitePerfectMatching.Membership
import CslibFrontier.Computability.Circuit.Monotone.BipartiteMatching.Separation

/-!
# Bipartite perfect matching in P

The polynomial-time decider for bipartite perfect matching on small adjacency matrices, among them
a `3 × 3` instance where the first greedy edge must be rerouted along an augmenting path, words of
non-square length, and the empty word (the graph `K_{0,0}`). The decider's verdicts transfer to
membership in the language through `decider_eq_true_iff`. Then the hypothesis of the monotone lower
bound is met at `n = 2 ^ 320`, and the separation theorem yields a concrete language.
-/

namespace ComplexityTests.BipartitePerfectMatchingP

open Cslib Cslib.Complexity Cslib.Complexity.BipartitePerfectMatching Cslib.Circuits
open Turing.MultiTapeTM (encBits)

/-! ### The decider on small matrices -/

-- The empty word is the `0 × 0` matrix, whose empty graph has the empty perfect matching.
example : decider [] = true := by decide +kernel

-- The `2 × 2` identity and anti-identity matrices have perfect matchings.
example : decider [true, false, false, true] = true := by decide +kernel
example : decider [false, true, true, false] = true := by decide +kernel

-- Left vertex `1` has no edges.
example : decider [true, true, false, false] = false := by decide +kernel

-- Words of non-square length are rejected, even when every bit is one.
example : decider [true, true, true] = false := by decide +kernel
example : decider [true, true, true, true, true] = false := by decide +kernel

/-- A `3 × 3` matrix where the first round matches `(0, 0)`, the second reroutes along the
augmenting path `1 → 0 → 0 → 1`, and the third adds `(2, 2)`. -/
def rerouted : List Bool := [true, true, false, true, false, false, false, false, true]

example : maximumMatching rerouted 3 = [(2, 2), (1, 0), (0, 1)] := by decide +kernel
example : decider rerouted = true := by decide +kernel

-- Left vertices `0` and `1` are adjacent only to right vertex `0`, violating Hall's condition.
example : decider [true, false, false, true, false, false, true, true, true] = false := by
  decide +kernel

/-! ### Membership in the language -/

example : rerouted ∈ BipartitePerfectMatching := (decider_eq_true_iff _).mp (by decide +kernel)

example : [true, true, false, false] ∉ BipartitePerfectMatching := by
  rw [← decider_eq_true_iff]
  decide +kernel

-- An explicit perfect matching certifies membership directly.
example : [false, true, true, false] ∈ BipartitePerfectMatching :=
  (mem_iff_of_length_eq (n := 2) rfl).mpr ⟨Equiv.swap 0 1, by decide⟩

/-! ### Slices -/

example : BipartitePerfectMatching.slice (3 * 3) = bipartitePerfectMatching 3 := slice_mul_self 3

example (x : Fin 3 → Bool) : BipartitePerfectMatching.slice 3 x = false := by
  refine slice_eq_false_of_ne (fun n hn => ?_) x
  have : n ≤ 2 := by nlinarith
  rcases (by omega : n ≤ 1 ∨ n = 2) with h | rfl
  · have := Nat.mul_le_mul h h
    omega
  · omega

/-! ### Monotone versus general circuits -/

-- The hypothesis `⌊log₂ n⌋ ≥ 320` of the lower bound holds at `n = 2 ^ 320`, where it gives more
-- than `2 ^ 400` gates.
example :
    ((2 ^ (20 ^ 2) : ℕ) : ℕ∞) <
      ecomplexity Monotone.interpretation
        (single (BipartitePerfectMatching.slice (2 ^ 320 * 2 ^ 320))) := by
  have h := two_pow_sq_lt_ecomplexity_slice (n := 2 ^ 320) (by rw [Nat.log_pow (by norm_num)])
  have e : (320 / 16) ^ 2 = 20 ^ 2 := by norm_num
  rw [Nat.log_pow (by norm_num), e] at h
  exact h

-- For every `k` some side length `n` makes the monotone circuit complexity exceed `(n * n) ^ k`.
example (k : ℕ) : ∃ n, (((n * n) ^ k : ℕ) : ℕ∞) <
    ecomplexity Monotone.interpretation (single (BipartitePerfectMatching.slice (n * n))) :=
  (eventually_pow_lt_ecomplexity_slice k).exists

-- The separation is witnessed by a language that is also in `P/poly`.
example : BipartitePerfectMatching ∈ Circuits.Boolean.PPoly := mem_PPoly

example : ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
    ∀ k, ∃ n, (((n * n) ^ k : ℕ) : ℕ∞) <
      ecomplexity Monotone.interpretation (single (L.slice (n * n))) := by
  obtain ⟨L, hL, -, h⟩ := exists_monotone_mem_P_superpolynomial_ecomplexity
  exact ⟨L, hL, fun k => (h k).exists⟩

end ComplexityTests.BipartitePerfectMatchingP
