/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Closure.LowerBound
public import Complexity.Computability.Circuit.Monotone.Clique.LowerBound
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Combinatorics.SmallSubsets
import Complexity.Foundations.Data.Nat.Choose
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A `2 ^ l` lower bound for monotone clique separators

Take the closed approximators of width `l` closed under `r = l (⌊log₂ n⌋ + 2) + 2`-fold
implication. There are at most `(n + 1) ^ l ≤ 2 ^ (l (⌊log₂ n⌋ + 1))` sets of at most `l`
vertices, so the negative budget of the Alon–Boppana dichotomy
(`Cslib.Circuits.Monotone.Closure.lt_size_of_separates`) allows `2 ^ l` gates once there are
`g ≥ 2 l ^ 2` colours. A conjunction errs on at most a `2 l · 8 ^ -(l / 2 + 1)` fraction of the
`k`-sets once `8 (r - 1) k ≤ n`, so the positive budget allows `2 ^ l` gates too.

So for `2 ≤ l` with `2 l ^ 2 ≤ g < k` and `8 l (⌊log₂ n⌋ + 3) k ≤ n`, every monotone circuit
separating the graphs with a `k`-clique from the `g`-colourable graphs on `n` vertices has more
than `2 ^ l` gates (`Cslib.Circuits.Monotone.two_pow_lt_size_of_separates`). With `l ≈ √(g / 2)`
this is a bound `2 ^ Ω(√g)` under a hypothesis `√g · k = O(n / log n)`, the form of
[Alon and Boppana, Theorem 3.11][AlonBoppana1987] (their `s₁ - 1` and `s₂` are our `g` and `k`)
and of [Krajíček, Theorem 7.2][Krajicek1997], with different constants. The Razborov bound
(`Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_size_of_separates`) needs `k ^ 4 ≤ n`.

In particular, for `n ≥ 2 ^ 40` and `⌊√n⌋ < k ≤ ⌊√n⌋ + 2`, which covers Krajíček's `k = ⌈√n⌉ + 1`,
every monotone circuit separating the graphs with a `k`-clique from the `(k - 1)`-colourable graphs
has more than `2 ^ (⌊√⌊√n⌋⌋ / 2)` gates, where `⌊√⌊√n⌋⌋ = ⌊n ^ (1/4)⌋`
(`Cslib.Circuits.Monotone.two_pow_lt_size_of_separates_sqrt`).

## Main results

* `Cslib.Circuits.Monotone.Closure.card_smallSets_le`: there are at most `(n + 1) ^ l` sets of at
  most `l` vertices.
* `Cslib.Circuits.Monotone.two_pow_lt_size_of_separates`,
  `Cslib.Circuits.Monotone.two_pow_lt_size_of_computes_clique`: the `2 ^ l` lower bound for
  separating circuits and for circuits computing `k`-clique.
* `Cslib.Circuits.Monotone.two_pow_lt_size_of_separates_sqrt`: the `2 ^ Ω(n ^ (1/4))` bound for
  cliques of size about `√n`.

## References

* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]; Theorem 7.2 is numbered as in the author's preprint.
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Circuits.Clique Finset

namespace Closure

/-- There are at most `(n + 1) ^ l` sets of at most `l` vertices. -/
theorem card_smallSets_le (n l : ℕ) : (smallSets n l).card ≤ (n + 1) ^ l := by
  rw [smallSets, card_filter_card_le_eq_sum_choose, Fintype.card_fin, add_pow]
  refine sum_le_sum fun j hj => ?_
  rw [one_pow, mul_one]
  exact (Nat.choose_le_pow n j).trans
    (Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.lt_succ_iff.1 (mem_range.1 hj))))

/-- The positive budget: if `q (r - 1) k ≤ n` and `2 l t < q ^ (l / 2 + 1)`, a circuit with `t`
gates stays below the positive budget. -/
private theorem positive_budget {n k r l t q : ℕ} (hr : 2 ≤ r) (hlk : l ≤ k) (hq : 1 ≤ q)
    (hn : q * (r - 1) * k ≤ n) (ht : 2 * l * t < q ^ (l / 2 + 1)) :
    Positive.errorCap n k r l * t < n.choose k := by
  have hq' : 1 ≤ q * (r - 1) := Nat.mul_pos hq (by omega)
  have hkn : k ≤ n := (Nat.le_mul_of_pos_left k hq').trans hn
  have hsum : q ^ (l / 2 + 1) * ∑ j ∈ Icc (l / 2 + 1) l, (r - 1) ^ j * (n - j).choose (k - j) ≤
      l * n.choose k := by
    rw [mul_sum]
    calc ∑ j ∈ Icc (l / 2 + 1) l, q ^ (l / 2 + 1) * ((r - 1) ^ j * (n - j).choose (k - j))
        ≤ ∑ _j ∈ Icc (l / 2 + 1) l, n.choose k := sum_le_sum fun j hj => by
          obtain ⟨hj₁, hj₂⟩ := mem_Icc.1 hj
          calc q ^ (l / 2 + 1) * ((r - 1) ^ j * (n - j).choose (k - j))
              ≤ q ^ j * ((r - 1) ^ j * (n - j).choose (k - j)) :=
                Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hj₁)
            _ = (q * (r - 1)) ^ j * (n - j).choose (k - j) := by rw [mul_pow]; ring
            _ ≤ n.choose k := Nat.pow_mul_choose_sub_le_choose hq' (hj₂.trans hlk) hn
      _ ≤ l * n.choose k := by
        rw [sum_const, smul_eq_mul, Nat.card_Icc]
        exact Nat.mul_le_mul_right _ (by omega)
  have hchoose : 0 < n.choose k := Nat.choose_pos hkn
  refine Nat.lt_of_mul_lt_mul_left (a := q ^ (l / 2 + 1)) ?_
  calc q ^ (l / 2 + 1) * (Positive.errorCap n k r l * t)
      = (q ^ (l / 2 + 1) * ∑ j ∈ Icc (l / 2 + 1) l, (r - 1) ^ j * (n - j).choose (k - j)) *
          (2 * t) := by rw [Positive.errorCap]; ring
    _ ≤ l * n.choose k * (2 * t) := Nat.mul_le_mul_right _ hsum
    _ = (2 * l * t) * n.choose k := by ring
    _ < q ^ (l / 2 + 1) * n.choose k := Nat.mul_lt_mul_of_pos_right ht hchoose

/-- The negative budget: if `2 l ^ 2 ≤ g`, `r ≤ n` and `2 S t < 2 ^ r` for the number `S` of sets
of at most `l` vertices, a circuit with `t` gates stays below the negative budget. -/
private theorem negative_budget {n g r l t : ℕ} (hl : 1 ≤ l) (hg : 2 * l ^ 2 ≤ g) (hrn : r ≤ n)
    (ht : 2 * (smallSets n l).card * t < 2 ^ r) :
    2 * Negative.errorCap n g r l * t < g ^ n := by
  have hgpos : 0 < g := by
    have := one_le_pow₀ (n := 2) hl
    omega
  have hpos : 0 < (l ^ 2) ^ r * g ^ (n - r) := by positivity
  calc 2 * Negative.errorCap n g r l * t
      = (2 * (smallSets n l).card * t) * ((l ^ 2) ^ r * g ^ (n - r)) := by
        simp only [Negative.errorCap, Monotone.Negative.pluckErrorCap]
        ring
    _ < 2 ^ r * ((l ^ 2) ^ r * g ^ (n - r)) := Nat.mul_lt_mul_of_pos_right ht hpos
    _ = (2 * l ^ 2) ^ r * g ^ (n - r) := by rw [mul_pow]; ring
    _ ≤ g ^ r * g ^ (n - r) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hg r)
    _ = g ^ n := by rw [← pow_add, Nat.add_sub_cancel' hrn]

/-- `2 l 2 ^ l < 8 ^ (l / 2 + 1)`. -/
private theorem two_mul_mul_two_pow_lt (l : ℕ) : 2 * l * 2 ^ l < 8 ^ (l / 2 + 1) := by
  have hl : l ≤ 2 * (l / 2) + 1 := by omega
  have ha : l / 2 + 1 ≤ 2 ^ (l / 2) := Nat.lt_two_pow_self
  calc 2 * l * 2 ^ l ≤ 2 * (2 * (l / 2) + 1) * 2 ^ (2 * (l / 2) + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hl) (Nat.pow_le_pow_right (by omega) hl)
    _ < 4 * 2 ^ (l / 2) * 2 ^ (2 * (l / 2) + 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = 8 ^ (l / 2 + 1) := by rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul]; ring

end Closure

open Closure in
/-- **The Alon–Boppana lower bound for separating circuits.** For `2 ≤ l` with `2 l ^ 2 ≤ g < k`
and `8 l (⌊log₂ n⌋ + 3) k ≤ n`, every monotone circuit separating the graphs with a `k`-clique from
the `g`-colourable graphs on `n` vertices has more than `2 ^ l` gates
[Alon and Boppana, Theorem 3.11][AlonBoppana1987]. -/
theorem two_pow_lt_size_of_separates {n k g l : ℕ} (hl : 2 ≤ l) (hg : 2 * l ^ 2 ≤ g)
    (hgk : g < k) (hn : 8 * l * (Nat.log 2 n + 3) * k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k g fun x => C.eval interpretation x 0) : 2 ^ l < C.size := by
  have hb : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk1 : 1 ≤ k := by omega
  have hr1 : l * (Nat.log 2 n + 2) + 2 - 1 ≤ l * (Nat.log 2 n + 3) := by
    calc l * (Nat.log 2 n + 2) + 2 - 1 = l * (Nat.log 2 n + 2) + 1 := by omega
      _ ≤ l * (Nat.log 2 n + 2) + l := by omega
      _ = l * (Nat.log 2 n + 3) := by ring
  have hr : 8 * (l * (Nat.log 2 n + 2) + 2 - 1) * k ≤ n := by
    refine le_trans ?_ hn
    rw [mul_assoc 8 l]
    exact Nat.mul_le_mul_right k (Nat.mul_le_mul_left 8 hr1)
  have hrn : l * (Nat.log 2 n + 2) + 2 ≤ n := by
    have h8 : l * (Nat.log 2 n + 2) + 2 ≤ 8 * (l * (Nat.log 2 n + 2) + 2 - 1) := by omega
    exact h8.trans ((Nat.le_mul_of_pos_right _ hk1).trans hr)
  refine Closure.lt_size_of_separates (r := l * (Nat.log 2 n + 2) + 2) (by omega) hl hg hgk ?_ ?_
    hC
  · refine positive_budget (q := 8) (by omega) ?_ (by norm_num) hr (two_mul_mul_two_pow_lt l)
    have := Nat.le_self_pow two_ne_zero l
    omega
  · refine negative_budget (by omega) hg hrn ?_
    calc 2 * (smallSets n l).card * 2 ^ l ≤ 2 * (2 ^ (Nat.log 2 n + 1)) ^ l * 2 ^ l := by
          gcongr
          exact (card_smallSets_le n l).trans (Nat.pow_le_pow_left hb l)
      _ = 2 ^ (l * (Nat.log 2 n + 1) + l + 1) := by rw [← pow_mul]; ring
      _ < 2 ^ (l * (Nat.log 2 n + 2) + 2) := Nat.pow_lt_pow_right (by norm_num) (by ring_nf; omega)

/-- **The Alon–Boppana lower bound for cliques.** For `2 ≤ l` with `2 l ^ 2 ≤ k - 1` and
`8 l (⌊log₂ n⌋ + 3) k ≤ n`, every monotone circuit computing `k`-clique on `n` vertices has more
than `2 ^ l` gates. -/
theorem two_pow_lt_size_of_computes_clique {n k l : ℕ} (hl : 2 ≤ l) (hk : 2 * l ^ 2 ≤ k - 1)
    (hn : 8 * l * (Nat.log 2 n + 3) * k ≤ n) {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) : 2 ^ l < C.size := by
  have : 1 ≤ l ^ 2 := one_le_pow₀ (by omega)
  exact two_pow_lt_size_of_separates hl hk (by omega) hn
    (separates_of_computes_clique (by omega) hC)

/-- `32 c + 48 ≤ 2 ^ c` for `c ≥ 10`. -/
private theorem thirtyTwo_mul_add_le_two_pow {c : ℕ} (hc : 10 ≤ c) : 32 * c + 48 ≤ 2 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c _ ih => rw [pow_succ]; omega

/-- **The Alon–Boppana lower bound for cliques of size about `√n`.** For `n ≥ 2 ^ 40` and
`⌊√n⌋ < k ≤ ⌊√n⌋ + 2`, every monotone circuit separating the graphs with a `k`-clique from the
`(k - 1)`-colourable graphs on `n` vertices has more than `2 ^ (⌊√⌊√n⌋⌋ / 2)` gates, of order
`2 ^ (n ^ (1/4) / 2)`. Krajíček's `k = ⌈√n⌉ + 1` is in this range
[Krajíček, Theorem 7.2][Krajicek1997]. -/
theorem two_pow_lt_size_of_separates_sqrt {n k : ℕ} (hn : 2 ^ 40 ≤ n) (hk : n.sqrt < k)
    (hk' : k ≤ n.sqrt + 2) {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    2 ^ (n.sqrt.sqrt / 2) < C.size := by
  set a := n.sqrt.sqrt
  have ha : 1024 ≤ a := Nat.le_sqrt.2 (Nat.le_sqrt.2 (le_trans (by norm_num) hn))
  have ha2 : a ^ 2 ≤ n.sqrt := Nat.sqrt_le' _
  have ha4 : a ^ 4 ≤ n :=
    calc a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left ha2 2
      _ ≤ n := Nat.sqrt_le' n
  have hsqrt : n.sqrt < (a + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hc : 10 ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) (le_trans (by norm_num) ha)
  have hca : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
  have hlog : Nat.log 2 n < 4 * (Nat.log 2 a + 1) := by
    refine Nat.log_lt_of_lt_pow (by omega) ?_
    calc n < (n.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' n
      _ ≤ ((a + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ ((2 ^ (Nat.log 2 a + 1)) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) a) 2) 2
      _ = 2 ^ (4 * (Nat.log 2 a + 1)) := by rw [← pow_mul, ← pow_mul]; ring_nf
  have h8 : 8 * (Nat.log 2 n + 3) ≤ a := by
    have := thirtyTwo_mul_add_le_two_pow hc
    omega
  have hk2 : k ≤ 2 * a ^ 2 := by nlinarith
  refine two_pow_lt_size_of_separates (by omega) ?_ (by omega) ?_ hC
  · calc 2 * (a / 2) ^ 2 ≤ (2 * (a / 2)) ^ 2 := by nlinarith
      _ ≤ a ^ 2 := Nat.pow_le_pow_left (Nat.mul_div_le a 2) 2
      _ ≤ k - 1 := by omega
  · have h4 : 8 * (a / 2) ≤ 4 * a := by omega
    calc 8 * (a / 2) * (Nat.log 2 n + 3) * k ≤ 4 * a * (Nat.log 2 n + 3) * (2 * a ^ 2) := by
          gcongr
      _ = a * (8 * (Nat.log 2 n + 3)) * a ^ 2 := by ring
      _ ≤ a * a * a ^ 2 := by gcongr
      _ = a ^ 4 := by ring
      _ ≤ n := ha4

end Cslib.Circuits.Monotone
