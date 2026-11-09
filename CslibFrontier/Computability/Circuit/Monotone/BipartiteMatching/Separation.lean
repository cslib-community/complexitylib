/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Monotone.BipartiteMatching.Asymptotic
public import CslibFrontier.Computability.Complexity.Problems.BipartitePerfectMatching.Membership
public import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Monotone circuits versus polynomial time

Bipartite perfect matching separates monotone circuit size from general circuit size. The language
`Cslib.Complexity.BipartitePerfectMatching` of row-major adjacency matrices of subgraphs of
`K_{n,n}` with a perfect matching is in `P`
(`Cslib.Complexity.BipartitePerfectMatching.mem_P`), hence in `P/poly`
(`Cslib.Complexity.BipartitePerfectMatching.mem_PPoly`), and all its slices are monotone. Yet by
Razborov's theorem [Razborov1985a], [Jukna, Theorem 9.38][Jukna2012] its slice at length `n * n`
needs monotone circuits with more than `2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)` gates once `⌊log₂ n⌋ ≥ 320`
(`Cslib.Complexity.BipartitePerfectMatching.two_pow_sq_lt_ecomplexity_slice`), which is
`n ^ Ω(log n)` and eventually exceeds every polynomial in the input length `n * n`
(`Cslib.Complexity.BipartitePerfectMatching.eventually_pow_lt_ecomplexity_slice`). Together with
a polynomial-time matching algorithm, the lower bound shows that monotone circuits for a monotone
function can be superpolynomially larger than general circuits. The packaged statement is
`Cslib.Complexity.exists_monotone_mem_P_superpolynomial_ecomplexity`.

Monotone circuit complexity is `ecomplexity Monotone.interpretation`, the least number of gates of
a circuit over constants and binary AND and OR gates; `P/poly` is `Cslib.Circuits.Boolean.PPoly`,
over the De Morgan basis.
Only lengths `n * n` carry the lower bound: at the other lengths the slice is constantly false.

## Main results

* `Cslib.Complexity.BipartitePerfectMatching.mem_PPoly`: bipartite perfect matching has
  polynomial-size circuits.
* `Cslib.Complexity.BipartitePerfectMatching.two_pow_sq_lt_ecomplexity_slice`,
  `Cslib.Complexity.BipartitePerfectMatching.eventually_pow_lt_ecomplexity_slice`: the monotone
  circuit complexity of its slices.
* `Cslib.Complexity.exists_monotone_mem_P_superpolynomial_ecomplexity`: a language in `P` with
  monotone slices whose monotone circuit complexity is superpolynomial.

## References

* [A. A. Razborov, *Lower bounds on monotone complexity of the logical permanent*][Razborov1985a]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.11][Jukna2012]
-/

public section

namespace Cslib.Complexity

open Cslib.Circuits Turing.MultiTapeTM

namespace BipartitePerfectMatching

/-- **Bipartite perfect matching has polynomial-size circuits**, since it is in `P`. -/
theorem mem_PPoly : BipartitePerfectMatching ∈ Circuits.Boolean.PPoly :=
  Circuits.Boolean.mem_PPolyOn_encBits_iff.mp (Circuits.Boolean.P_subset_PPolyOn mem_P)

/-- **Razborov's lower bound for the language.** For `⌊log₂ n⌋ ≥ 320`, the monotone circuit
complexity of the slice of bipartite perfect matching at length `n * n` exceeds
`2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)` [Razborov1985a], [Jukna, Theorem 9.38][Jukna2012]. -/
theorem two_pow_sq_lt_ecomplexity_slice {n : ℕ} (hn : 320 ≤ Nat.log 2 n) :
    ((2 ^ ((Nat.log 2 n / 16) ^ 2) : ℕ) : ℕ∞) <
      ecomplexity Monotone.interpretation (single (BipartitePerfectMatching.slice (n * n))) := by
  rw [slice_mul_self]
  exact Circuits.Monotone.two_pow_sq_lt_ecomplexity_bipartitePerfectMatching hn

/-- **The monotone circuit complexity is superpolynomial**: for every `k`, the slice at length
`n * n` eventually needs monotone circuits with more than `(n * n) ^ k` gates. Explicitly, this
holds once `⌊log₂ n⌋ ≥ 16 (32 k + 20)`. -/
theorem eventually_pow_lt_ecomplexity_slice (k : ℕ) :
    ∀ᶠ n in Filter.atTop, (((n * n) ^ k : ℕ) : ℕ∞) <
      ecomplexity Monotone.interpretation (single (BipartitePerfectMatching.slice (n * n))) := by
  refine Filter.eventually_atTop.mpr ⟨2 ^ (16 * (32 * k + 20)), fun n hn => ?_⟩
  have hL : 16 * (32 * k + 20) ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hn
  refine lt_of_le_of_lt ?_ (two_pow_sq_lt_ecomplexity_slice (by omega))
  set L := Nat.log 2 n
  set q := L / 16
  have hq : 32 * k + 20 ≤ q := by omega
  have hL1 : L + 1 ≤ 16 * (q + 1) := by omega
  have hexp : 2 * k * (L + 1) ≤ q ^ 2 := by nlinarith
  have hn2 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hnn : (n * n) ^ k ≤ 2 ^ (2 * k * (L + 1)) := by
    calc (n * n) ^ k ≤ (2 ^ (L + 1) * 2 ^ (L + 1)) ^ k := by gcongr
      _ = 2 ^ (2 * k * (L + 1)) := by rw [← pow_add, ← pow_mul]; congr 1; ring
  exact_mod_cast hnn.trans (Nat.pow_le_pow_right (by norm_num) hexp)

end BipartitePerfectMatching

/-- **Monotone circuits versus polynomial time** [Razborov1985a]: some language is in `P` under
the plain bit encoding, has monotone slices, and has monotone circuit complexity exceeding every
polynomial in the input length infinitely often, along the lengths `n * n`. Bipartite perfect
matching (`BipartitePerfectMatching`) is such a language; being in `P`, it is also in `P/poly`
(`BipartitePerfectMatching.mem_PPoly`). -/
theorem exists_monotone_mem_P_superpolynomial_ecomplexity :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ (∀ m, Monotone (L.slice m)) ∧
      ∀ k, ∀ᶠ n in Filter.atTop, (((n * n) ^ k : ℕ) : ℕ∞) <
        ecomplexity Monotone.interpretation (single (L.slice (n * n))) :=
  ⟨BipartitePerfectMatching, BipartitePerfectMatching.mem_P,
    BipartitePerfectMatching.monotone_slice,
    BipartitePerfectMatching.eventually_pow_lt_ecomplexity_slice⟩

end Cslib.Complexity
