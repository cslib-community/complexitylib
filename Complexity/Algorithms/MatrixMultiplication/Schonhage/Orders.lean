/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Levels
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Pruned
public import Complexity.Foundations.Combinatorics.FunctionPlaces
public import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Orders and counts of contributing leaves

## Main definitions

* `order`, `alpha`, `beta`: leaf order and its two counting distributions.

## Main results

* `card_contributing_of_order`, `card_filter_order_eq`, `card_outStr_of_leaf`: exact counts.
* `two_pow_mul_beta_le`: geometric decay when `L = 19m`.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The set of levels at which a leaf chooses `P₀`. -/
def P0Levels {L : ℕ} (τ : Leaf L) : Finset (Fin L) := univ.filter fun ℓ => τ ℓ = Term.P0

/-- The integer difference between `m` and the number of `P0` positions of a leaf. It can be
negative for arbitrary leaves; nonnegativity is proved for leaves contributing to an
output with `m` inner positions. -/
def order {L : ℕ} (m : ℕ) (τ : Leaf L) : ℤ := (m : ℤ) - ((P0Levels τ).card : ℤ)

/-- The quantity `m.choose d * 9 ^ d`, counting order-`d` leaves contributing to one output
with `m` inner positions. -/
def alpha (m d : ℕ) : ℕ := m.choose d * 9 ^ d

/-- The quantity `L.choose (m - d) * 9 ^ (L - m + d)`, using natural-number subtraction. Its
interpretation as the number of order-`d` leaves requires `d ≤ m ≤ L`. -/
def beta (L m d : ℕ) : ℕ := L.choose (m - d) * 9 ^ (L - m + d)

/-! ### One level: which terms contribute to which variables -/

/-- The private term of `z` is `P₀` exactly if `z = z₀`. -/
theorem OutVar.privateTerm_eq_P0_iff (z : OutVar) : z.privateTerm = Term.P0 ↔ z.IsInner := by
  cases z <;> simp [OutVar.IsInner, OutVar.privateTerm]

/-- One term is `P₀`. -/
private theorem card_term_P0 : (univ.filter fun lam : Term => lam = Term.P0).card = 1 := by decide

/-- Nine terms are different from `P₀`. -/
private theorem card_term_ne_P0 : (univ.filter fun lam : Term => ¬ lam = Term.P0).card = 9 := by
  decide

/-- Among the terms contributing to `z`, the number of those equal to `P₀`: one if `z = z₀`, none if
`z = z_ij`. -/
private theorem card_contributing_P0 (z : OutVar) :
    ((univ.filter fun lam : Term => lam.Contributes z).filter fun lam => lam = Term.P0).card
      = if z.IsInner then 1 else 0 := by
  decide +revert

/-- Among the terms contributing to `z`, the number of those different from `P₀`: nine if `z = z₀`,
one if `z = z_ij`. -/
private theorem card_contributing_ne_P0 (z : OutVar) :
    ((univ.filter fun lam : Term => lam.Contributes z).filter fun lam => ¬ lam = Term.P0).card
      = if z.IsInner then 9 else 1 := by
  decide +revert

/-- The number of terms contributing to `z`: ten if `z = z₀`, one if `z = z_ij`. -/
private theorem card_contributing_term (z : OutVar) :
    (univ.filter fun lam : Term => lam.Contributes z).card = if z.IsInner then 10 else 1 := by
  decide +revert

/-- Among the output variables to which `lam` contributes, exactly one is inner. -/
private theorem card_contributed_inner (lam : Term) :
    ((univ.filter fun z : OutVar => lam.Contributes z).filter fun z => z.IsInner).card = 1 := by
  decide +revert

/-- Among the output variables to which `lam` contributes, the number of outer ones: none if
`lam = P₀`, one if `lam = P_ij`. -/
private theorem card_contributed_outer (lam : Term) :
    ((univ.filter fun z : OutVar => lam.Contributes z).filter fun z => ¬ z.IsInner).card
      = if lam = Term.P0 then 0 else 1 := by
  decide +revert

/-! ### The order of a leaf -/

/-- Membership in the set of levels at which a leaf chooses `P₀`. -/
@[simp]
theorem mem_P0Levels {L : ℕ} {τ : Leaf L} {ℓ : Fin L} : ℓ ∈ P0Levels τ ↔ τ ℓ = Term.P0 := by
  simp [P0Levels]

/-- Membership in the inner set of an output string. -/
@[simp]
theorem mem_innerSetO {L : ℕ} {η : OutStr L} {ℓ : Fin L} : ℓ ∈ innerSetO η ↔ (η ℓ).IsInner := by
  simp [innerSetO]

/-- A contributing leaf can use `P0` only at an inner position of the output string. -/
theorem P0Levels_subset {L : ℕ} {τ : Leaf L} {w : OutStr L} (h : Leaf.Contributes τ w) :
    P0Levels τ ⊆ innerSetO w := by
  intro ℓ hℓ
  rw [mem_P0Levels] at hℓ
  rw [mem_innerSetO]
  rcases (Term.contributes_iff _ _).mp (h ℓ) with hinner | hprivate
  · exact hinner
  · exact (OutVar.privateTerm_eq_P0_iff _).mp (hprivate.symm.trans hℓ)

/-- A leaf contributing to a string with exactly `m` inner positions has nonnegative order
relative to `m`. -/
theorem order_nonneg {L m : ℕ} {w : OutStr L} (hw : (innerSetO w).card = m) {τ : Leaf L}
    (h : Leaf.Contributes τ w) : 0 ≤ order m τ := by
  have hc := card_le_card (P0Levels_subset h)
  unfold order
  omega

/-- The order relative to `m` of any leaf is at most `m`, regardless of which outputs it
contributes to. -/
theorem order_le {L : ℕ} (m : ℕ) (τ : Leaf L) : order m τ ≤ m := by
  unfold order
  omega

/-- A leaf has order `d` exactly if it chooses `P₀` at `m - d` levels. -/
theorem order_eq_iff {L : ℕ} (m d : ℕ) (τ : Leaf L) :
    order m τ = d ↔ (P0Levels τ).card + d = m := by
  unfold order
  omega

/-! ### The counts -/

/-- Exactly `10 ^ m` leaves contribute to an output string with `m` inner positions. -/
theorem card_filter_contributes {L m : ℕ} (w : OutStr L) (hw : (innerSetO w).card = m) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w).card = 10 ^ m := by
  -- Ten terms contribute to `z₀` and one to `z_ij`.
  simp only [Leaf.filter_contributes_eq_piFinset, Fintype.card_piFinset,
    card_contributing_term]
  rw [prod_ite, prod_const, prod_const_one, mul_one, ← hw]
  rfl

/-- For a string with `m` inner positions, `alpha m d` leaves of order `d` contribute to it.
The natural parameter `d` is unrestricted; for `d > m` both sides are zero. -/
theorem card_contributing_of_order {L m : ℕ} (w : OutStr L) (hw : (innerSetO w).card = m)
    (d : ℕ) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w ∧ order m τ = d).card = alpha m d := by
  by_cases hd : d ≤ m
  · -- Sort the strings of terms that contribute to `w` level by level and have `P₀` at exactly
    -- `m - d` levels by the set `S` of these levels.
    have hcount := Finset.card_pi_places_card
      (fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ)) (fun lam => lam = Term.P0)
      (m - d)
    simp only [card_contributing_P0, card_contributing_ne_P0] at hcount
    -- Given `S`, there is no such string unless `S ⊆ Q`.  Then there are nine choices at each of
    -- the `|Q| - |S| = d` levels of `Q` outside `S`, and one choice at every other level.
    have hgiven : ∀ S ∈ powersetCard (m - d) (univ : Finset (Fin L)),
        (∏ ℓ, if ℓ ∈ S then (if (w ℓ).IsInner then 1 else 0) else (if (w ℓ).IsInner then 9 else 1))
          = if S ⊆ innerSetO w then 9 ^ d else 0 := by
      intro S hS
      have hQS := prod_ite_ite_subset (innerSetO w) S 9
      rw [hw, (mem_powersetCard.mp hS).2, Nat.sub_sub_self hd] at hQS
      rw [← hQS]
      exact prod_congr rfl fun ℓ _ => by simp
    -- There are `binom(m, m - d) = binom(m, d)` sets `S ⊆ Q`.
    rw [sum_congr rfl hgiven, sum_powersetCard_ite_subset, hw, Nat.choose_symm hd] at hcount
    -- These strings are the leaves of order `d` that contribute to `w`.
    rw [alpha, ← hcount]
    refine congrArg card (Finset.ext fun τ => ?_)
    simp only [mem_filter, mem_univ, true_and, order_eq_iff]
    exact and_congr Iff.rfl (by unfold P0Levels; omega)
  · -- No leaf has order more than `m`.
    rw [alpha, Nat.choose_eq_zero_of_lt (by omega), zero_mul, card_eq_zero]
    refine filter_eq_empty_iff.mpr fun τ _ h => ?_
    have hle := order_le m τ
    omega

/-- If `d ≤ m ≤ L`, the full leaf index type contains exactly `beta L m d` leaves of order
`d`. -/
theorem card_filter_order_eq {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd : d ≤ m) :
    (univ.filter fun τ : Leaf L => order m τ = d).card = beta L m d := by
  -- The leaves of order `d` are the strings of terms with `P₀` at exactly `m - d` levels.
  have hsort : (univ.filter fun τ : Leaf L => order m τ = d)
      = univ.filter fun τ : Leaf L => (univ.filter fun ℓ => τ ℓ = Term.P0).card = m - d := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, order_eq_iff]
    unfold P0Levels
    omega
  rw [hsort, Finset.card_places_card (fun lam : Term => lam = Term.P0) (m - d), card_term_P0,
    card_term_ne_P0, one_pow, one_mul, Fintype.card_fin, beta,
    show L - (m - d) = L - m + d by omega]

/-- Evaluate `beta` at order zero. -/
theorem beta_zero (L m : ℕ) : beta L m 0 = L.choose m * 9 ^ (L - m) := by
  simp [beta]

/-- The order-zero count formula equals `M L m`. -/
theorem beta_zero_eq_M (L m : ℕ) : beta L m 0 = M L m := by
  rw [beta_zero, M, K, N0, ← pow_mul, mul_comm (L - m) 2, pow_mul]
  norm_num

/-- Assuming `m ≤ L`, a leaf of natural order `d` contributes to exactly `(L - m + d).choose
d` output strings with `m` inner positions. The order hypothesis forces `d ≤ m`. -/
theorem card_outStr_of_leaf {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (τ : Leaf L)
    (hτ : order m τ = d) :
    (univ.filter fun w : OutStr L => (innerSetO w).card = m ∧ Leaf.Contributes τ w).card
      = (L - m + d).choose d := by
  have hP0 : (P0Levels τ).card + d = m := (order_eq_iff m d τ).mp hτ
  -- Sort the output strings to which `τ` contributes level by level, with `z₀` at exactly `m`
  -- levels, by the set `S` of these levels, which is their inner set.
  have hcount := Finset.card_pi_places_card
    (fun ℓ => univ.filter fun z : OutVar => (τ ℓ).Contributes z) (fun z => z.IsInner) m
  simp only [card_contributed_inner, card_contributed_outer] at hcount
  -- Given `S`, there is one such string if `S` contains the levels at which `τ` chooses `P₀`, and
  -- none otherwise.
  have hgiven : ∀ S ∈ powersetCard m (univ : Finset (Fin L)),
      (∏ ℓ, if ℓ ∈ S then 1 else (if τ ℓ = Term.P0 then 0 else 1))
        = if P0Levels τ ⊆ S then 1 else 0 := by
    intro S _
    rw [← prod_ite_ite_superset]
    exact prod_congr rfl fun ℓ _ => by simp
  -- A set of `m` levels that contains these `m - d` levels is given by the `L - m` levels outside
  -- it, among the other `L - m + d` levels.
  rw [sum_congr rfl hgiven, ← card_filter,
    card_powersetCard_superset _ (by simpa using hmL), Fintype.card_fin,
    show L - (P0Levels τ).card = L - m + d by omega, Nat.choose_symm_add] at hcount
  rw [← hcount]
  refine congrArg card (Finset.ext fun w => ?_)
  simp only [mem_filter, mem_univ, true_and]
  exact and_comm

/-- `β_d` is positive when `m ≤ L`. -/
theorem beta_pos {L m : ℕ} (hmL : m ≤ L) (d : ℕ) : 0 < beta L m d :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (by positivity)

/-- For `1 ≤ d ≤ m ≤ L`, consecutive values of `beta` satisfy the displayed multiplication
identity, without division (cf. [AlmanWilliams2026, equation (5)]). -/
theorem Equation5.ratio_nat {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    beta L m d * (L - m + d) = 9 * (m - d + 1) * beta L m (d - 1) := by
  -- With `k = m - d` this is `binom(L, k) (L - k) = binom(L, k + 1) (k + 1)`, times a power of 9.
  have hchoose : L.choose (m - d + 1) * (m - d + 1) = L.choose (m - d) * (L - m + d) := by
    rw [Nat.choose_succ_right_eq, show L - (m - d) = L - m + d by omega]
  have hpow : 9 ^ (L - m + d) = 9 * 9 ^ (L - m + (d - 1)) := by
    rw [show L - m + d = L - m + (d - 1) + 1 by omega, pow_succ, mul_comm]
  rw [beta, beta, show m - (d - 1) = m - d + 1 by omega, hpow]
  calc L.choose (m - d) * (9 * 9 ^ (L - m + (d - 1))) * (L - m + d)
      = 9 * 9 ^ (L - m + (d - 1)) * (L.choose (m - d) * (L - m + d)) := by ring
    _ = 9 * 9 ^ (L - m + (d - 1)) * (L.choose (m - d + 1) * (m - d + 1)) := by rw [hchoose]
    _ = 9 * (m - d + 1) * (L.choose (m - d + 1) * 9 ^ (L - m + (d - 1))) := by ring

/-- For `1 ≤ d ≤ m ≤ L`, the ratio of consecutive `beta` values is `9 * (m - d + 1) / (L - m +
d)`, with the ratio and subtractions interpreted in `ℚ`. This extends the parameter ranges
used in [AlmanWilliams2026, equations (5) and (7)]. -/
theorem beta_ratio {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    (beta L m d : ℚ) / (beta L m (d - 1) : ℚ)
      = 9 * ((m : ℚ) - (d : ℚ) + 1) / ((L : ℚ) - (m : ℚ) + (d : ℚ)) := by
  have hm : (m : ℚ) ≤ L := by exact_mod_cast hmL
  have hd0 : (1 : ℚ) ≤ d := by exact_mod_cast hd1
  have hbeta : (0 : ℚ) < beta L m (d - 1) := by exact_mod_cast beta_pos hmL (d - 1)
  have hnat := congrArg (Nat.cast : ℕ → ℚ) (Equation5.ratio_nat hmL d hd1 hd)
  push_cast [Nat.cast_sub hmL, Nat.cast_sub hd] at hnat
  rw [div_eq_div_iff hbeta.ne' (by linarith), hnat]

/-- At `L = 19 * m` and `1 ≤ d ≤ m`, the ratio of consecutive `beta` values is bounded above
by `9 * m / (18 * m + 1)`, which is strictly below `1 / 2`. All divisions here are in `ℚ`. -/
theorem beta_ratio_lt_half (m d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    (beta (19 * m) m d : ℚ) / (beta (19 * m) m (d - 1) : ℚ) ≤ 9 * (m : ℚ) / (18 * (m : ℚ) + 1)
      ∧ 9 * (m : ℚ) / (18 * (m : ℚ) + 1) < 1 / 2 := by
  have hm : (1 : ℚ) ≤ m := by exact_mod_cast hd1.trans hd
  have hd0 : (1 : ℚ) ≤ d := by exact_mod_cast hd1
  refine ⟨?_, ?_⟩
  · -- The numerator is at most `9m` and the denominator at least `18m + 1`, because `d ≥ 1`.
    rw [beta_ratio (by omega) d hd1 hd]
    push_cast
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) (by linarith)
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith

/-- For `d ≤ m` and `L = 19 * m`, the order count satisfies `2 ^ d * beta L m d ≤ M L m`. This
is the division-free geometric bound from [AlmanWilliams2026, equation (5)]. -/
theorem two_pow_mul_beta_le (m d : ℕ) (hd : d ≤ m) : 2 ^ d * beta (19 * m) m d ≤ M (19 * m) m := by
  induction d with
  | zero => simp [beta_zero_eq_M]
  | succ d ih =>
    -- By the two inequalities of (5), `β_{d+1} < β_d / 2`.
    obtain ⟨hle, hlt⟩ := beta_ratio_lt_half m (d + 1) (by omega) hd
    rw [Nat.add_sub_cancel] at hle
    have hbeta : (0 : ℚ) < beta (19 * m) m d := by exact_mod_cast beta_pos (by omega) d
    have hhalf : 2 * beta (19 * m) m (d + 1) ≤ beta (19 * m) m d := by
      have hq := (div_lt_iff₀ hbeta).mp (hle.trans_lt hlt)
      exact_mod_cast (by linarith : (2 * beta (19 * m) m (d + 1) : ℚ) ≤ beta (19 * m) m d)
    calc 2 ^ (d + 1) * beta (19 * m) m (d + 1) = 2 ^ d * (2 * beta (19 * m) m (d + 1)) := by ring
      _ ≤ 2 ^ d * beta (19 * m) m d := Nat.mul_le_mul_left _ hhalf
      _ ≤ M (19 * m) m := ih (by omega)


end Cslib.Algorithms.MatrixMultiplication.Schonhage
