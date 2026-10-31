/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.BipartiteMatching.LowerBound
public import Cslib.Computability.Circuit.Complexity
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Combinatorics.SmallSubsets
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An `n ^ Ω(log n)` lower bound for monotone circuits computing perfect matchings

Let `L = ⌊log₂ n⌋` and take matchings of at most `s = ⌊L / 16⌋` edges, `q = 2 ^ s K` fresh
petals with `K = s ^ 2 + s + 2 + 2 s (L + 1)`, and closure under `r = (q s) ^ 2 + 1`-fold
implication in the explicit lower bound
(`Cslib.Circuits.Monotone.lt_size_of_computes_bipartitePerfectMatching`).

There are at most `(n ^ 2 + 1) ^ s ≤ 2 ^ (2 s (L + 1))` matchings of at most `s` edges
(`Cslib.Circuits.BipartiteMatching.Razborov.card_matchings_le`), and
`(1 - 2 ^ (-s)) ^ (2 ^ s) ≤ 1 / 2`, so the negative budget allows `2 ^ (s ^ 2)` gates. Since
`q s = 2 ^ s K s ≤ 4 ^ s` once `s ≥ 20`, a conjunction errs on at most a `2 ^ (8 s ^ 2)` multiple
of `(n - s - 1)!` of the `n!` perfect matchings, while `n! / (n - s - 1)! ≥ (n - s) ^ (s + 1)` and
`n - s ≥ 2 ^ (15 s)`; so the positive budget allows `2 ^ (s ^ 2)` gates too.

So for `⌊log₂ n⌋ ≥ 320`, that is `n ≥ 2 ^ 320`, every monotone circuit computing whether a
subgraph of `K_{n,n}` has a perfect matching has more than `2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)` gates
(`Cslib.Circuits.Monotone.two_pow_sq_lt_size_of_computes_bipartitePerfectMatching`), which is
`n ^ Ω(log n)`: Razborov's theorem [Razborov1985a], [Jukna, Theorem 9.38][Jukna2012]. The
constants are not optimized; Jukna takes `s = ⌊(log n) / 8⌋` and `r = ⌊n ^ (1/4) (log n) ^ 8⌋`.

## Main results

* `Cslib.Circuits.BipartiteMatching.Razborov.card_matchings_le`: there are at most
  `(n * n + 1) ^ s` matchings of at most `s` edges.
* `Cslib.Circuits.Monotone.two_pow_sq_lt_size_of_separates_ofPerm_ofColoring`,
  `Cslib.Circuits.Monotone.two_pow_sq_lt_size_of_computes_bipartitePerfectMatching`,
  `Cslib.Circuits.Monotone.two_pow_sq_lt_ecomplexity_bipartitePerfectMatching`: the
  `2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)` lower bound for separating circuits, for circuits computing perfect
  matching and for the monotone circuit complexity of perfect matching.

## References

* [A. A. Razborov, *Lower bounds on monotone complexity of the logical permanent*][Razborov1985a]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.11][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Finset BipartiteMatching
open Cslib.Circuits.Monotone (signature)
open scoped Nat

namespace BipartiteMatching.Razborov

/-- There are at most `(n * n + 1) ^ s` matchings with at most `s` edges. -/
theorem card_matchings_le (n s : ℕ) : (matchings n s).card ≤ (n * n + 1) ^ s := by
  calc (matchings n s).card ≤ #{E : Finset (Fin n × Fin n) | #E ≤ s} :=
        card_le_card fun E hE => mem_filter.2 ⟨mem_univ _, (mem_matchings.1 hE).2⟩
    _ ≤ (n * n + 1) ^ s := by
        rw [card_filter_card_le_eq_sum_choose, Fintype.card_prod, Fintype.card_fin, add_pow]
        refine sum_le_sum fun j hj => ?_
        rw [one_pow, mul_one]
        exact (Nat.choose_le_pow _ j).trans
          (Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.lt_succ_iff.1 (mem_range.1 hj))))

end BipartiteMatching.Razborov

namespace Monotone

open BipartiteMatching.Razborov

/-- `b ^ m (b + m) ≤ (b + 1) ^ m b`. -/
private theorem pow_mul_add_le (b : ℕ) : ∀ m, b ^ m * (b + m) ≤ (b + 1) ^ m * b
  | 0 => by simp
  | m + 1 => by
    have ih := pow_mul_add_le b m
    calc b ^ (m + 1) * (b + (m + 1)) = b ^ m * (b * (b + m + 1)) := by ring
      _ ≤ b ^ m * ((b + 1) * (b + m)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (b + 1) * (b ^ m * (b + m)) := by ring
      _ ≤ (b + 1) * ((b + 1) ^ m * b) := Nat.mul_le_mul_left _ ih
      _ = (b + 1) ^ (m + 1) * b := by ring

/-- `2 (a - 1) ^ a ≤ a ^ a` for `a ≥ 1`, that is `(1 - 1 / a) ^ a ≤ 1 / 2`. -/
private theorem two_mul_sub_one_pow_le {a : ℕ} (ha : 1 ≤ a) : 2 * (a - 1) ^ a ≤ a ^ a := by
  rcases a with _ | _ | b
  · omega
  · simp
  · simp only [Nat.add_sub_cancel]
    have h := pow_mul_add_le (b + 1) (b + 1 + 1)
    refine Nat.le_of_mul_le_mul_right (c := b + 1) ?_ (by omega)
    calc 2 * (b + 1) ^ (b + 1 + 1) * (b + 1) = (b + 1) ^ (b + 1 + 1) * (2 * b + 2) := by ring
      _ ≤ (b + 1) ^ (b + 1 + 1) * (b + 1 + (b + 1 + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (b + 1 + 1) ^ (b + 1 + 1) * (b + 1) := h

/-- `64 s ^ 3 ≤ 2 ^ s` for `s ≥ 20`. -/
private theorem sixtyFour_mul_pow_three_le_two_pow {s : ℕ} (hs : 20 ≤ s) : 64 * s ^ 3 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have h1 : 20 * s ^ 2 ≤ s ^ 3 := by
      have := Nat.mul_le_mul_left (s ^ 2) hs
      rw [show s ^ 3 = s ^ 2 * s by ring]
      linarith
    have h2 : 20 * s ≤ s ^ 2 := by
      have := Nat.mul_le_mul_left s hs
      rw [sq]
      linarith
    calc 64 * (s + 1) ^ 3 ≤ 2 * (64 * s ^ 3) := by nlinarith
      _ ≤ 2 * 2 ^ s := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (s + 1) := by ring

/-- **An `n ^ Ω(log n)` lower bound for separating circuits.** For `⌊log₂ n⌋ ≥ 320`, every monotone
circuit accepting the perfect matchings of permutations and rejecting the graphs of two-colourings
without a perfect matching has more than `2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)` gates. -/
theorem two_pow_sq_lt_size_of_separates_ofPerm_ofColoring {n : ℕ} (hn : 320 ≤ Nat.log 2 n)
    {C : Circuit signature (n * n) 1}
    (hC₁ : ∀ σ : Equiv.Perm (Fin n), C.eval Monotone.interpretation (ofPerm σ) 0 = true)
    (hC₂ : ∀ c : Coloring n, bipartitePerfectMatching n (ofColoring c) = false →
      C.eval Monotone.interpretation (ofColoring c) 0 = false) :
    2 ^ ((Nat.log 2 n / 16) ^ 2) < C.size := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hL : 320 ≤ Nat.log 2 n := hn
  have h2L : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hnL : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  obtain ⟨L, hLdef⟩ : ∃ L, Nat.log 2 n = L := ⟨_, rfl⟩
  rw [hLdef] at hL h2L hnL ⊢
  obtain ⟨s, hsdef⟩ : ∃ s, L / 16 = s := ⟨_, rfl⟩
  rw [hsdef]
  have hs : 20 ≤ s := by omega
  have hsL : 16 * s ≤ L := by omega
  have hLs : L + 1 ≤ 16 * s + 16 := by omega
  have h16 : 2 ^ (16 * s) ≤ n := (Nat.pow_le_pow_right two_pos hsL).trans h2L
  obtain ⟨K, hKdef⟩ : ∃ K, s ^ 2 + s + 2 + 2 * s * (L + 1) = K := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, 2 ^ s * K = q := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, (q * s) ^ 2 + 1 = r := ⟨_, rfl⟩
  have hKs : K * s ≤ 2 ^ s := by
    have h1 := Nat.mul_le_mul_left s hLs
    have h2 : s * 20 ≤ s * s := Nat.mul_le_mul_left _ hs
    have hK : K ≤ 35 * s ^ 2 := by rw [← hKdef, sq]; nlinarith
    calc K * s ≤ 35 * s ^ 2 * s := Nat.mul_le_mul_right _ hK
      _ ≤ 64 * s ^ 3 := by rw [pow_succ]; nlinarith
      _ ≤ 2 ^ s := sixtyFour_mul_pow_three_le_two_pow hs
  have hqs : 1 ≤ q * s := by
    rw [← hqdef]
    exact Nat.mul_pos (Nat.mul_pos (by positivity) (by rw [← hKdef]; positivity)) (by omega)
  have hr2 : 2 ≤ r := by
    have := Nat.one_le_pow 2 (q * s) hqs
    omega
  refine lt_size_of_separates_ofPerm_ofColoring (r := r) (s := s) (q := q) hr2
    (by omega) (by omega) ?_ ?_ (two_pow_mul_errorCap_mul_lt ?_) hC₁ hC₂
  · -- `4 ^ (s + 1) ≤ 2 n + 1`
    calc 4 ^ (s + 1) = 2 ^ (2 * s + 2) := by
          rw [show 2 * s + 2 = 2 * (s + 1) by ring, pow_mul]
          norm_num
      _ ≤ 2 ^ (16 * s) := Nat.pow_le_pow_right two_pos (by omega)
      _ ≤ 2 * n + 1 := by omega
  · -- the positive budget
    have hns : 2 ^ (15 * s) ≤ n - s := by
      have h1 : s ≤ 2 ^ (15 * s) :=
        (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right two_pos (by omega))
      have h2 : 2 ^ (15 * s) * 2 ≤ 2 ^ (16 * s) := by
        rw [← pow_succ]
        exact Nat.pow_le_pow_right two_pos (by omega)
      omega
    have hsn : s + 1 ≤ n :=
      (Nat.lt_two_pow_self).trans_le ((Nat.pow_le_pow_right two_pos (by omega)).trans h16)
    have hfact : (n - (s + 1))! * (n - s) ^ (s + 1) ≤ n ! := by
      have h := Nat.factorial_mul_pow_le_factorial (m := n - (s + 1)) (n := s + 1)
      rwa [show n - (s + 1) + 1 = n - s by omega, show n - (s + 1) + (s + 1) = n by omega] at h
    have hr : (r - 1) ^ (2 * s) ≤ 2 ^ (8 * s ^ 2) := by
      calc (r - 1) ^ (2 * s) = (2 ^ s * (K * s)) ^ (4 * s) := by
            rw [show r - 1 = (q * s) ^ 2 by omega, ← pow_mul, show q * s = 2 ^ s * (K * s) by
              rw [← hqdef]; ring, show 2 * (2 * s) = 4 * s by ring]
        _ ≤ (2 ^ s * 2 ^ s) ^ (4 * s) :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hKs) _
        _ = 2 ^ (8 * s ^ 2) := by rw [← pow_add, ← pow_mul]; ring_nf
    have hlt : 2 ^ (8 * s ^ 2) * 2 ^ (s ^ 2) < (n - s) ^ (s + 1) := by
      calc 2 ^ (8 * s ^ 2) * 2 ^ (s ^ 2) = 2 ^ (9 * s ^ 2) := by rw [← pow_add]; ring_nf
        _ < 2 ^ (15 * s * s) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
        _ = (2 ^ (15 * s)) ^ s := by rw [← pow_mul]
        _ ≤ (n - s) ^ s := Nat.pow_le_pow_left hns _
        _ ≤ (n - s) ^ (s + 1) :=
            Nat.pow_le_pow_right (by have := Nat.one_le_two_pow (n := 15 * s); omega) (by omega)
    calc Positive.errorCap n r s * 2 ^ (s ^ 2)
        = (r - 1) ^ (2 * s) * 2 ^ (s ^ 2) * (n - (s + 1))! := by rw [Positive.errorCap]; ring
      _ ≤ 2 ^ (8 * s ^ 2) * 2 ^ (s ^ 2) * (n - (s + 1))! :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr)
      _ < (n - s) ^ (s + 1) * (n - (s + 1))! :=
          Nat.mul_lt_mul_of_pos_right hlt (Nat.factorial_pos _)
      _ ≤ n ! := by rw [mul_comm]; exact hfact
  · -- the negative budget
    have hM : (matchings n s).card ≤ 2 ^ (2 * (L + 1) * s) := by
      refine (card_matchings_le n s).trans ?_
      rw [pow_mul]
      refine Nat.pow_le_pow_left ?_ s
      have : n * n < 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_self_lt_mul_self hnL
      rw [mul_comm 2 (L + 1), pow_mul, sq]
      omega
    have hB : (2 ^ s - 1) ^ q * 2 ^ K ≤ 2 ^ (s * q) := by
      have h := Nat.pow_le_pow_left (two_mul_sub_one_pow_le (a := 2 ^ s) Nat.one_le_two_pow) K
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at h
      calc (2 ^ s - 1) ^ q * 2 ^ K = 2 ^ K * (2 ^ s - 1) ^ (2 ^ s * K) := by
            rw [mul_comm, ← hqdef]
        _ ≤ 2 ^ (s * (2 ^ s * K)) := h
        _ = 2 ^ (s * q) := by rw [hqdef]
    refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ K) ?_
    calc 2 ^ (s + 1) * (matchings n s).card * (2 ^ s - 1) ^ q * 2 ^ (s ^ 2) * 2 ^ K
        = 2 ^ (s + 1) * (matchings n s).card * 2 ^ (s ^ 2) * ((2 ^ s - 1) ^ q * 2 ^ K) := by ring
      _ ≤ 2 ^ (s + 1) * 2 ^ (2 * (L + 1) * s) * 2 ^ (s ^ 2) * 2 ^ (s * q) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM)) hB
      _ = 2 ^ (s + 1 + 2 * (L + 1) * s + s ^ 2) * 2 ^ (s * q) := by rw [← pow_add, ← pow_add]
      _ < 2 ^ K * 2 ^ (s * q) :=
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) (by nlinarith))
            (by positivity)
      _ = 2 ^ (s * q) * 2 ^ K := mul_comm _ _

/-- **Razborov's `n ^ Ω(log n)` lower bound for perfect matching** [Razborov1985a],
[Jukna, Theorem 9.38][Jukna2012]. For `⌊log₂ n⌋ ≥ 320`, that is `n ≥ 2 ^ 320`, every monotone
circuit computing whether a subgraph of `K_{n,n}` has a perfect matching has more than
`2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)` gates, which is `n ^ Ω(log n)`. -/
theorem two_pow_sq_lt_size_of_computes_bipartitePerfectMatching {n : ℕ}
    (hn : 320 ≤ Nat.log 2 n)
    {C : Circuit signature (n * n) 1}
    (hC : C.Computes Monotone.interpretation (single (bipartitePerfectMatching n))) :
    2 ^ ((Nat.log 2 n / 16) ^ 2) < C.size := by
  have heval (x : BitString (n * n)) :
      C.eval Monotone.interpretation x 0 = bipartitePerfectMatching n x := by
    rw [hC, single_apply]
  refine two_pow_sq_lt_size_of_separates_ofPerm_ofColoring hn (fun σ => ?_) fun c hc => ?_
  · rw [heval, bipartitePerfectMatching_ofPerm]
  · rw [heval, hc]

/-- **The monotone circuit complexity of perfect matching.** For `⌊log₂ n⌋ ≥ 320`, the monotone
circuit complexity of perfect matching in subgraphs of `K_{n,n}` exceeds
`2 ^ (⌊⌊log₂ n⌋ / 16⌋ ^ 2)`. -/
theorem two_pow_sq_lt_ecomplexity_bipartitePerfectMatching {n : ℕ} (hn : 320 ≤ Nat.log 2 n) :
    ((2 ^ ((Nat.log 2 n / 16) ^ 2) : ℕ) : ℕ∞) <
      ecomplexity Monotone.interpretation (single (bipartitePerfectMatching n)) := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top _), le_ecomplexity_iff]
  intro C hC
  exact_mod_cast two_pow_sq_lt_size_of_computes_bipartitePerfectMatching hn hC

end Monotone

end Cslib.Circuits
