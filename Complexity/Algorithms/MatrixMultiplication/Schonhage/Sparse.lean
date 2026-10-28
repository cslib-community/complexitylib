/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Orders
public import Complexity.Foundations.Algebra.GeometricTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sparse query bounds

## Main definitions

* `saving`: the factor `D^(-1/18)` for `D = 4^m`.

## Main results

* `card_leaves_le_sum_min`: sum the two order-wise bounds.
* `card_leaves_le_saving`: explicit sparse leaf bound, with no assumed sparse solver.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-! ### Specialization to `L = 19 * m` -/

/-- At `L = 19 * m`, the outer dimension is `3 ^ (18 * m)`. -/
theorem N0_nineteen_mul (m : ℕ) : N0 (19 * m) m = 3 ^ (18 * m) := by
  unfold N0
  congr 1
  omega

/-- `M` is positive when `m ≤ L`. -/
theorem M_pos {L m : ℕ} (hmL : m ≤ L) : 0 < M L m :=
  Nat.mul_pos (Nat.choose_pos hmL) (Nat.pow_pos (Nat.pow_pos (by decide)))

/-- `D = 4^m = 2^{2m}`. -/
private theorem D_eq_two_pow (m : ℕ) : (D m : ℝ) = (2 : ℝ) ^ (2 * m) := by
  rw [D, pow_mul]
  norm_num

/-- The real square root of `D m` is `2 ^ m`. -/
theorem two_pow_eq_sqrt_D (m : ℕ) : (2 : ℝ) ^ m = Real.sqrt (D m) := by
  rw [D_eq_two_pow, pow_mul', Real.sqrt_sq (by positivity)]

/-- The positive real factor `2 ^ (-m / 9)`, used in the finite leaf and encoding count
bounds. -/
noncomputable def saving (m : ℕ) : ℝ := (2 : ℝ) ^ (-(m : ℝ) / 9)

/-- `2^{-m/9}` is positive. -/
theorem saving_pos (m : ℕ) : 0 < saving m :=
  Real.rpow_pos_of_pos two_pos _

/-- `2^{-m/9} ≤ 1`. -/
theorem saving_le_one (m : ℕ) : saving m ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr m.cast_nonneg) (by norm_num))

/-- `2^{-m/9} · 2^{m/9} = 1`. -/
theorem saving_mul_two_rpow (m : ℕ) : saving m * (2 : ℝ) ^ ((m : ℝ) / 9) = 1 := by
  rw [saving, ← Real.rpow_add two_pos, show -(m : ℝ) / 9 + (m : ℝ) / 9 = 0 by ring, Real.rpow_zero]

/-- Express `saving m` as the real power `D^(-1/18)` for `D = D m`. -/
theorem saving_eq_D_rpow (m : ℕ) : saving m = (D m : ℝ) ^ (-(1 / 18 : ℝ)) := by
  rw [saving, D_eq_two_pow, ← Real.rpow_natCast 2 (2 * m), ← Real.rpow_mul two_pos.le]
  congr 1
  push_cast
  ring

/-! ### The first inequality -/

/-- If every string in `U` has `m` inner positions, its contributing leaves of natural order
`d` are bounded both by `U.card * alpha m d` and by `beta L m d`. The minimum combines
these bounds without counting a shared leaf more than once. -/
theorem card_leaves_filter_order_le {L m : ℕ} (U : Finset (OutStr L))
    (hU : ∀ w ∈ U, (innerSetO w).card = m) (d : ℕ) :
    ((leaves U).filter fun τ => order m τ = d).card ≤ min (U.card * alpha m d) (beta L m d) := by
  refine le_min ?_ ?_
  · -- Charge each output string of U for its leaves of order d.
    calc _ ≤ (U.biUnion fun w =>
            univ.filter fun τ : Leaf L => Leaf.Contributes τ w ∧ order m τ = d).card := by
          refine card_le_card fun τ hτ => ?_
          obtain ⟨hτU, hτd⟩ := mem_filter.mp hτ
          obtain ⟨w, hw, hc⟩ := mem_leaves.mp hτU
          exact mem_biUnion.mpr ⟨w, hw, mem_filter.mpr ⟨mem_univ _, hc, hτd⟩⟩
      _ ≤ U.card * alpha m d :=
          card_biUnion_le_card_mul _ _ _ fun w hw =>
            (card_contributing_of_order w (hU w hw) d).le
  · -- There are only β_d leaves of order d in all.
    rcases U.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
    · simp [leaves]
    have hmL : m ≤ L := by
      have h := card_le_univ (innerSetO w₀)
      rwa [hU w₀ hw₀, Fintype.card_fin] at h
    rcases le_or_gt d m with hd | hd
    · rw [← card_filter_order_eq hmL d hd]
      exact card_le_card (filter_subset_filter _ (subset_univ _))
    · -- No leaf has an order above m.
      have hempty : ((leaves U).filter fun τ => order m τ = d) = ∅ := by
        refine filter_false_of_mem fun τ _ h => ?_
        have hle := order_le m τ
        omega
      rw [hempty]
      exact Nat.zero_le _

/-- Bound the cardinality of `leaves U` by summing the smaller of the per-output bound and the
full leaf count over natural orders `0` through `m`. Every string in `U` must have exactly
`m` inner positions; the empty set is permitted (cf. [AlmanWilliams2026, Lemma 11]). -/
theorem card_leaves_le_sum_min {L m : ℕ} (U : Finset (OutStr L))
    (hU : ∀ w ∈ U, (innerSetO w).card = m) :
    (leaves U).card ≤ ∑ d ∈ range (m + 1), min (U.card * alpha m d) (beta L m d) := by
  -- Every leaf of `leaves(U)` has an order between 0 and m.
  have hord : ∀ τ ∈ leaves U, 0 ≤ order m τ := by
    intro τ hτ
    obtain ⟨w, hw, hc⟩ := mem_leaves.mp hτ
    exact order_nonneg (hU w hw) hc
  have hmaps : ∀ τ ∈ leaves U, (order m τ).toNat ∈ range (m + 1) := by
    intro τ _
    have hle := order_le m τ
    rw [mem_range]
    omega
  -- Sum the smaller of the two bounds over the orders.
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_le_sum fun d _ => le_trans ?_ (card_leaves_filter_order_le U hU d)
  refine card_le_card fun τ hτ => ?_
  obtain ⟨hτU, hτd⟩ := mem_filter.mp hτ
  have hnonneg := hord τ hτU
  exact mem_filter.mpr ⟨hτU, by omega⟩

/-! ### The second inequality -/

/-- Equation (5) over the reals: `β_d ≤ M 2^{-d}` for `0 ≤ d ≤ m` and `L = 19m`. -/
private theorem beta_le_M_mul (m d : ℕ) (hd : d ≤ m) :
    (beta (19 * m) m d : ℝ) ≤ (M (19 * m) m : ℝ) * (1 / 2 : ℝ) ^ d := by
  have h : (2 : ℝ) ^ d * (beta (19 * m) m d : ℝ) ≤ (M (19 * m) m : ℝ) := by
    exact_mod_cast two_pow_mul_beta_le m d hd
  rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- By (5), the orders `d ≥ a` contribute `∑ β_d ≤ M ∑_{d ≥ a} 2^{-d} < 2 · 2^{-a} M`. -/
private theorem sum_beta_lt_of_subset (m a : ℕ) (s : Finset ℕ) (hs : s ⊆ Ico a (m + 1)) :
    ((∑ d ∈ s, beta (19 * m) m d : ℕ) : ℝ) < 2 * (1 / 2 : ℝ) ^ a * (M (19 * m) m : ℝ) := by
  have hM : (0 : ℝ) < (M (19 * m) m : ℝ) := by exact_mod_cast M_pos (show m ≤ 19 * m by omega)
  push_cast
  calc ∑ d ∈ s, (beta (19 * m) m d : ℝ)
      ≤ ∑ d ∈ s, (M (19 * m) m : ℝ) * (1 / 2 : ℝ) ^ d :=
        sum_le_sum fun d hd =>
          beta_le_M_mul m d (by have := mem_Ico.mp (hs hd); omega)
    _ ≤ ∑ d ∈ Ico a (m + 1), (M (19 * m) m : ℝ) * (1 / 2 : ℝ) ^ d :=
        sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => by positivity
    _ = (M (19 * m) m : ℝ) * ∑ d ∈ Ico a (m + 1), (1 / 2 : ℝ) ^ d := (mul_sum _ _ _).symm
    _ < (M (19 * m) m : ℝ) * (2 * (1 / 2 : ℝ) ^ a) :=
        mul_lt_mul_of_pos_left
          ((geom_sum_Ico_lt_of_lt_one (by norm_num) (by norm_num) a _).trans_eq (by ring)) hM
    _ = 2 * (1 / 2 : ℝ) ^ a * (M (19 * m) m : ℝ) := by ring

/-- At `L = 19 * m`, the sum of `beta L m d` over `0 ≤ d ≤ m` with `m < 9 * d` is strictly
below `2 * saving m * M L m`. This includes `m = 0`, when the sum is empty. -/
theorem sum_beta_large_orders_lt (m : ℕ) :
    ((∑ d ∈ (range (m + 1)).filter (fun d => m < 9 * d), beta (19 * m) m d : ℕ) : ℝ)
      < 2 * saving m * (M (19 * m) m : ℝ) := by
  -- The orders d > m/9 are the orders d ≥ ⌊m/9⌋ + 1.
  have hs : (range (m + 1)).filter (fun d => m < 9 * d) ⊆ Ico (m / 9 + 1) (m + 1) := by
    intro d hd
    obtain ⟨hdm, hd9⟩ := mem_filter.mp hd
    rw [mem_range] at hdm
    rw [mem_Ico]
    omega
  refine (sum_beta_lt_of_subset m (m / 9 + 1) _ hs).trans_le ?_
  have hpow : (1 / 2 : ℝ) ^ (m / 9 + 1) ≤ saving m := by
    have hfloor : (m : ℝ) ≤ 9 * ((m / 9 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m ≤ 9 * (m / 9 + 1))
    rw [show (1 / 2 : ℝ) ^ (m / 9 + 1) = (2 : ℝ) ^ (-((m / 9 + 1 : ℕ) : ℝ)) by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- Multiply `hpow` by `2` and by `M`.
  gcongr

/-- One term of the display in the proof of Lemma 11: `binom(m, d) 9^d = binom(m, d) 72^d 8^{-d}`,
which is at most `72^{m/9} binom(m, d) 8^{-d}` for `d ≤ m/9`.  The factor `1^{m-d}` makes the right
side a term of the expansion of `(1/8 + 1)^m`. -/
private theorem alpha_le (m d : ℕ) (hd : 9 * d ≤ m) :
    (alpha m d : ℝ)
      ≤ (72 : ℝ) ^ ((m : ℝ) / 9) * ((1 / 8 : ℝ) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
  have hd' : (9 : ℝ) * d ≤ m := by exact_mod_cast hd
  have hpow : (72 : ℝ) ^ d ≤ (72 : ℝ) ^ ((m : ℝ) / 9) := by
    rw [← Real.rpow_natCast (72 : ℝ) d]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc (alpha m d : ℝ) = (72 : ℝ) ^ d * ((1 / 8 : ℝ) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
        rw [alpha, one_pow, mul_one, ← mul_assoc, ← mul_pow]
        push_cast
        norm_num [mul_comm]
    _ ≤ _ := by gcongr

/-- The first two steps of the display in the proof of Lemma 11:
`∑_{d ≤ m/9} binom(m, d) 9^d ≤ 72^{m/9} ∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^{m/9} (9/8)^m`. -/
private theorem sum_alpha_small_orders_le_aux (m : ℕ) :
    ((∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m), alpha m d : ℕ) : ℝ)
      ≤ (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m := by
  push_cast
  calc ∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m), (alpha m d : ℝ)
      ≤ ∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m),
          (72 : ℝ) ^ ((m : ℝ) / 9) * ((1 / 8 : ℝ) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum fun d hd => alpha_le m d (mem_filter.mp hd).2
    _ ≤ ∑ d ∈ range (m + 1),
          (72 : ℝ) ^ ((m : ℝ) / 9) * ((1 / 8 : ℝ) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m := by
        rw [← mul_sum, ← add_pow]
        norm_num

/-- For `m ≥ 1`, the sum of `alpha m d` over `0 ≤ d ≤ m` with `9 * d ≤ m` is strictly below `2
^ m * saving m`. For `m = 0`, the two quantities are equal, so the strict inequality needs
the stated positivity hypothesis. -/
theorem sum_alpha_small_orders_lt (m : ℕ) (hm : 1 ≤ m) :
    ((∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m), alpha m d : ℕ) : ℝ)
      < (2 : ℝ) ^ m * saving m := by
  have hm9 : (0 : ℝ) < (m : ℝ) / 9 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  refine (sum_alpha_small_orders_le_aux m).trans_lt ?_
  -- 72^{m/9} (9/8)^m = (72 · (9/8)^9)^{m/9}
  have hleft : (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m
      = (72 * (9 / 8 : ℝ) ^ 9) ^ ((m : ℝ) / 9) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (9 / 8 : ℝ) 9,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (9 / 8 : ℝ) m]
    congr 2
    push_cast
    ring
  -- 256^{m/9} = 2^m · 2^{-m/9}
  have hright : (256 : ℝ) ^ ((m : ℝ) / 9) = (2 : ℝ) ^ m * saving m := by
    rw [saving, show (256 : ℝ) = (2 : ℝ) ^ ((8 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hleft, ← hright]
  -- `72 · (9/8)^9 < 208 < 256`.
  exact Real.rpow_lt_rpow (by positivity) (by norm_num) hm9

/-- The bound of `sum_alpha_small_orders_lt` with `≤`, which also holds for `m = 0`. -/
private theorem sum_alpha_small_orders_le (m : ℕ) :
    ((∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m), alpha m d : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ m * saving m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [alpha, saving]
  · exact (sum_alpha_small_orders_lt m hm).le

/-- Split the order sum at `m / 9`, applying the query-dependent estimate below the cutoff
and the layout-dependent estimate above it. -/
private theorem card_leaves_le_split {L m : ℕ} (U : Finset (OutStr L))
    (hU : ∀ w ∈ U, (innerSetO w).card = m) :
    (leaves U).card
      ≤ U.card * ∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m), alpha m d
        + ∑ d ∈ (range (m + 1)).filter (fun d => m < 9 * d), beta L m d := by
  refine (card_leaves_le_sum_min U hU).trans ?_
  rw [← sum_filter_add_sum_filter_not (range (m + 1)) (fun d => 9 * d ≤ m), mul_sum]
  refine add_le_add (sum_le_sum fun d _ => min_le_left _ _) ?_
  rw [filter_congr fun d _ => (not_le (a := 9 * d) (b := m))]
  exact sum_le_sum fun d _ => min_le_right _ _

/-- For strings of length `19 * m`, each with `m` inner positions, the contributing leaf set
has cardinality at most `saving m * (2 ^ m * U.card + 2 * M (19 * m) m)`. This real bound
permits `m = 0` and `U = ∅`; it makes no execution-cost claim (cf. [AlmanWilliams2026,
Lemma 11]). -/
theorem card_leaves_le_saving {m : ℕ} (U : Finset (OutStr (19 * m)))
    (hU : ∀ w ∈ U, (innerSetO w).card = m) :
    ((leaves U).card : ℝ) ≤ saving m * ((2 : ℝ) ^ m * (U.card : ℝ) + 2 * (M (19 * m) m : ℝ)) := by
  have hsplit : ((leaves U).card : ℝ)
      ≤ (U.card : ℝ) * ((∑ d ∈ (range (m + 1)).filter (fun d => 9 * d ≤ m), alpha m d : ℕ) : ℝ)
        + ((∑ d ∈ (range (m + 1)).filter (fun d => m < 9 * d), beta (19 * m) m d : ℕ) : ℝ) := by
    exact_mod_cast card_leaves_le_split U hU
  have hsmall :=
    mul_le_mul_of_nonneg_left (sum_alpha_small_orders_le m) (Nat.cast_nonneg (α := ℝ) U.card)
  have hlarge := (sum_beta_large_orders_lt m).le
  calc ((leaves U).card : ℝ) ≤ _ := hsplit
    _ ≤ (U.card : ℝ) * ((2 : ℝ) ^ m * saving m) + 2 * saving m * (M (19 * m) m : ℝ) :=
        add_le_add hsmall hlarge
    _ = _ := by ring

/-- Combine the order-wise minimum bound on `leaves U` with the explicit real bound available
when `L = 19 * m`. Both conclusions assume only that each requested string has `m` inner
positions; the specialization is conditional on the displayed equality of parameters. -/
theorem sparse_leaf_bounds {L m : ℕ} (U : Finset (OutStr L)) (hU : ∀ w ∈ U, (innerSetO w).card =
  m) :
    (leaves U).card ≤ ∑ d ∈ range (m + 1), min (U.card * alpha m d) (beta L m d)
      ∧ (L = 19 * m →
          ((leaves U).card : ℝ)
            ≤ (2 : ℝ) ^ (-(m : ℝ) / 9) * ((2 : ℝ) ^ m * (U.card : ℝ) + 2 * (M L m : ℝ))) := by
  refine ⟨card_leaves_le_sum_min U hU, ?_⟩
  rintro rfl
  exact card_leaves_le_saving U hU

end Cslib.Algorithms.MatrixMultiplication.Schonhage
