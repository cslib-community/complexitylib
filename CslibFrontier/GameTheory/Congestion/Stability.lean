/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Affine
import CslibFrontier.GameTheory.Strategic.Stability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The price of stability of affine congestion games

Rosenthal's potential approximates the social cost of an atomic congestion game. With nondecreasing
latencies every summand `latency e (k + 1)`, `k < load s e`, is at most `latency e (load s e)`, so
`rosenthalPotential s ≤ socialCost s`. With nonnegative affine latencies
`latency e k = a e * k + b e`, the potential of a resource with load `n` is
`a e * n (n + 1) / 2 + b e * n ≥ n * latency e n / 2`, so `socialCost s ≤ 2 * rosenthalPotential s`.
These are the bounds `C(f) / 2 ≤ Φ(f) ≤ C(f)` of [Roughgarden2013CS364A], Exercise Set #7,
Exercise 55. By the potential function method ([TardosWexler2007], Theorem 19.13, as
`Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le` with
`A = 2` and `B = 1`), the price of stability of affine congestion games is at most `2`.

The bound `2` is not tight for affine congestion games; sharper bounds on their price of stability
are not formalized here.

## Main results

* `Cslib.GameTheory.CongestionGame.rosenthalPotential_le_socialCost`: with nondecreasing
  latencies, Rosenthal's potential is at most the social cost.
* `Cslib.GameTheory.CongestionGame.socialCost_le_two_mul_rosenthalPotential`
  ([Roughgarden2013CS364A], Exercise 55): with nonnegative affine latencies, the social cost is at
  most twice Rosenthal's potential.
* `Cslib.GameTheory.CongestionGame.exists_isPureNash_socialCost_le_two_mul`: **the price of
  stability of affine congestion games is at most `2`**.
* `Cslib.GameTheory.CongestionGame.exists_reflTransGen_isPureNash_socialCost_le_two_mul`:
  better-response dynamics started at any profile `s₀` reach a pure Nash equilibrium of social
  cost at most `2 * socialCost s₀`.

## References

* [Roughgarden2013CS364A]
* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory.CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq E]
  (C : CongestionGame ι S E)

/-- With nondecreasing latencies, **Rosenthal's potential is at most the social cost**: the
potential `∑ k < load s e, latency e (k + 1)` of each resource is at most
`load s e * latency e (load s e)`. -/
theorem rosenthalPotential_le_socialCost [Fintype E] (hmono : ∀ e, Monotone (C.latency e))
    (s : ∀ i, S i) : C.rosenthalPotential s ≤ C.toCostGame.socialCost s := by
  rw [socialCost_toCostGame, rosenthalPotential_def]
  refine Finset.sum_le_sum fun e _ => ?_
  calc ∑ k ∈ Finset.range (C.load s e), C.latency e (k + 1)
      ≤ ∑ _k ∈ Finset.range (C.load s e), C.latency e (C.load s e) :=
        Finset.sum_le_sum fun k hk => hmono e (Finset.mem_range.1 hk)
    _ = (C.load s e : ℝ) * C.latency e (C.load s e) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- With nonnegative affine latencies, **the social cost is at most twice Rosenthal's potential**
([Roughgarden2013CS364A], Exercise Set #7, Exercise 55, the inequality `C(f) ≤ 2 Φ(f)`): a
resource with load `n` and latency `a * k + b` contributes `n * (a * n + b)` to the social cost and
`a * n * (n + 1) / 2 + b * n` to the potential. -/
theorem socialCost_le_two_mul_rosenthalPotential [Fintype E] (h : C.HasAffineLatencies)
    (s : ∀ i, S i) : C.toCostGame.socialCost s ≤ 2 * C.rosenthalPotential s := by
  obtain ⟨a, b, ha, hb, hl⟩ := h
  rw [socialCost_toCostGame, rosenthalPotential_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have hsum : ∀ n : ℕ, 2 * ∑ k ∈ Finset.range n, C.latency e (k + 1)
      = a e * n * (n + 1) + 2 * b e * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, hl]
      push_cast
      ring
  rw [hsum, hl]
  have hn : (0 : ℝ) ≤ C.load s e := Nat.cast_nonneg _
  nlinarith [mul_nonneg (ha e) hn, mul_nonneg (hb e) hn]

variable [DecidableEq ι] [Finite E] [∀ i, Finite (S i)]

/-- **The price of stability of affine congestion games is at most `2`**: an atomic congestion
game with nonnegative affine latencies, finitely many resources and finitely many (and at least
one) strategies per player has a pure Nash equilibrium `s` with `socialCost s ≤ 2 * socialCost s'`
for every profile `s'`. This is the potential function method ([TardosWexler2007], Theorem 19.13)
with the bounds of [Roughgarden2013CS364A], Exercise 55; the equilibrium is a global minimizer of
Rosenthal's potential. -/
theorem exists_isPureNash_socialCost_le_two_mul [∀ i, Nonempty (S i)] (h : C.HasAffineLatencies) :
    ∃ s, C.toCostGame.IsPureNash s ∧
      ∀ s', C.toCostGame.socialCost s ≤ 2 * C.toCostGame.socialCost s' := by
  have := Fintype.ofFinite E
  obtain ⟨s, hs, hle⟩ := C.isExactPotential_rosenthalPotential.isGeneralizedOrdinalPotential
    |>.exists_isPureNash_socialCost_le zero_le_two (C.socialCost_le_two_mul_rosenthalPotential h)
      (fun s => by
        rw [one_mul]
        exact C.rosenthalPotential_le_socialCost h.monotone_latency s)
  exact ⟨s, hs, fun s' => by simpa only [mul_one] using hle s'⟩

/-- **Better-response dynamics from any profile reach a good equilibrium** in affine congestion
games: from every profile `s₀`, a finite sequence of improving unilateral deviations reaches a
pure Nash equilibrium `t` with `socialCost t ≤ 2 * socialCost s₀`. Started at a socially optimal
profile, this reaches an equilibrium within the price-of-stability bound `2`. -/
theorem exists_reflTransGen_isPureNash_socialCost_le_two_mul (h : C.HasAffineLatencies)
    (s₀ : ∀ i, S i) :
    ∃ t, Relation.ReflTransGen (flip C.toCostGame.Improves) s₀ t ∧ C.toCostGame.IsPureNash t ∧
      C.toCostGame.socialCost t ≤ 2 * C.toCostGame.socialCost s₀ := by
  have := Fintype.ofFinite E
  obtain ⟨t, hpath, ht, hle⟩ := C.isExactPotential_rosenthalPotential.isGeneralizedOrdinalPotential
    |>.exists_reflTransGen_isPureNash_socialCost_le zero_le_two
      (C.socialCost_le_two_mul_rosenthalPotential h)
      (fun s => by
        rw [one_mul]
        exact C.rosenthalPotential_le_socialCost h.monotone_latency s) s₀
  exact ⟨t, hpath, ht, by simpa only [mul_one] using hle⟩

end Cslib.GameTheory.CongestionGame
