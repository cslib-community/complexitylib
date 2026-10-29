/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.ThinProduct
public import Complexity.Foundations.Algebra.FiniteMagnitude

/-!
# Magnitudes of specified integer values and auxiliary counts

## Main results

* `abs_bandArrayL_le`, `abs_bandArrayR_le`: input entries are unchanged or zero.
* `abs_encodingL_le`, `abs_encodingR_le`, `Pruned.abs_result_le`: explicit integer magnitude bounds.
* `minutiae_total_le`: bound on layout subsets, tiles and wanted positions.

The magnitude bounds concern band-array values, encoded values and returned pruned
values. They do not bound every intermediate state of a native implementation or certify
a machine word width.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-! ### Auxiliary finite counts -/

/-- `2^{m/9} ≤ 2^m`. -/
private theorem two_rpow_ninth_le (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (2 : ℝ) ^ m := by
  rw [← Real.rpow_natCast]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- A number that is at least `2^{m/9}` is at least 1 after multiplication by `2^{-m/9}`. -/
private theorem one_le_saving_mul {m : ℕ} {x : ℝ} (hx : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ x) :
    1 ≤ saving m * x := by
  rw [← saving_mul_two_rpow m]
  exact mul_le_mul_of_nonneg_left hx (saving_pos m).le

/-- When `D m ^ 18 ≤ N`, the number `K (19 * m) m` of size-`m` level sets is at most `N`. -/
theorem K_le_of_D_pow_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : K (19 * m) m ≤ N :=
  (Nat.le_mul_of_pos_right _ (N0_pos _ _)).trans (K_mul_N0_le m N hN)

/-- For `m ≤ L`, the tile count multiplied by `N0 L m` is at most four times the square of the
padded dimension `padN L m N`. -/
theorem card_tiles_mul_N0_le {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    (tiles L m N).card * N0 L m ≤ 4 * padN L m N ^ 2 := by
  -- `N₀ ≤ K N₀² = M`, and there are at most `4N²/M` tiles.
  refine le_trans (Nat.mul_le_mul_left _ ?_) (card_tiles_mul_M_le L m N)
  calc N0 L m = 1 * N0 L m ^ 1 := by ring
    _ ≤ K L m * N0 L m ^ 2 :=
        Nat.mul_le_mul (Nat.choose_pos hmL) (Nat.pow_le_pow_right (N0_pos L m) (by norm_num))

/-- The size condition `D m ^ 18 ≤ N` implies the real bound `2 ^ (m / 9) ≤ N`. -/
theorem two_rpow_le_of_D_pow_le (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (N : ℝ) := by
  -- `2^{m/9} ≤ 2^m ≤ 4^{18m} = D^18 ≤ N`.
  have hpow : 2 ^ m ≤ N :=
    calc 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ ≤ (4 ^ m) ^ 18 := Nat.le_self_pow (by norm_num) _
      _ ≤ N := hN
  exact (two_rpow_ninth_le m).trans (by exact_mod_cast hpow)

/-- At `L = 19 * m`, the outer dimension is at least the real power `2 ^ (m / 9)`. -/
theorem two_rpow_le_N0 (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (N0 (19 * m) m : ℝ) := by
  -- `2^{m/9} ≤ 2^m ≤ 3^{18m} = N₀`.
  have hpow : 2 ^ m ≤ N0 (19 * m) m :=
    calc 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
      _ ≤ 3 ^ (19 * m - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (two_rpow_ninth_le m).trans (by exact_mod_cast hpow)

/-- The three counts of the remaining minutiae (Section 2.4.4), one by one: the subsets in the
table, the tiles, and the positions of `W`. -/
private theorem minutiae_parts (m N : ℕ) (W : Finset (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    (K (19 * m) m : ℝ) ≤ saving m * (N : ℝ) ^ 2
      ∧ ((tiles (19 * m) m N).card : ℝ) ≤ 4 * saving m * (padN (19 * m) m N : ℝ) ^ 2
      ∧ (W.card : ℝ) ≤ saving m * (N : ℝ) ^ 2 := by
  have hc := saving_pos m
  refine ⟨?_, ?_, ?_⟩
  · -- The subsets in the table: `K ≤ N ≤ 2^{-m/9} N²`.
    calc (K (19 * m) m : ℝ) ≤ N := by exact_mod_cast K_le_of_D_pow_le m N hN
      _ ≤ saving m * N * N :=
          le_mul_of_one_le_left N.cast_nonneg (one_le_saving_mul (two_rpow_le_of_D_pow_le m N hN))
      _ = saving m * (N : ℝ) ^ 2 := by ring
  · -- The tiles: at most `4N²/N₀ ≤ 4 · 2^{-m/9} N²`.
    have hT : ((tiles (19 * m) m N).card : ℝ) * N0 (19 * m) m
        ≤ 4 * (padN (19 * m) m N : ℝ) ^ 2 := by
      exact_mod_cast card_tiles_mul_N0_le (show m ≤ 19 * m by omega) N
    calc ((tiles (19 * m) m N).card : ℝ)
        ≤ (tiles (19 * m) m N).card * (saving m * N0 (19 * m) m) :=
          le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_saving_mul (two_rpow_le_N0 m))
      _ = saving m * ((tiles (19 * m) m N).card * N0 (19 * m) m) := by ring
      _ ≤ saving m * (4 * (padN (19 * m) m N : ℝ) ^ 2) := by gcongr
      _ = 4 * saving m * (padN (19 * m) m N : ℝ) ^ 2 := by ring
  · -- The positions: `|W| ≤ 2^{-m} N² ≤ 2^{-m/9} N²`.
    have hW' : (W.card : ℝ) * (2 : ℝ) ^ m ≤ (N : ℝ) ^ 2 := by exact_mod_cast hW
    calc (W.card : ℝ) = saving m * (W.card * (2 : ℝ) ^ ((m : ℝ) / 9)) := by
          rw [mul_left_comm, saving_mul_two_rpow, mul_one]
      _ ≤ saving m * (W.card * (2 : ℝ) ^ m) := by gcongr; exact two_rpow_ninth_le m
      _ ≤ saving m * (N : ℝ) ^ 2 := by gcongr

/-- At `L = 19 * m`, the sum of `K L m`, the tile count and `W.card` is at most `18 *
D^(-1/18) * N²`, where `D = D m` and `N` is the original matrix dimension. The hypotheses
are `D m ^ 18 ≤ N` and `W.card * 2 ^ m ≤ N ^ 2`. This counts finite objects; it does not
count operations on them. -/
theorem minutiae_total_le (m N : ℕ) (W : Finset (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    ((K (19 * m) m + (tiles (19 * m) m N).card + W.card : ℕ) : ℝ)
      ≤ 18 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  obtain ⟨hK, hT, hW'⟩ := minutiae_parts m N W hN hW
  have hc := saving_pos m
  have hpad : (padN (19 * m) m N : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast padN_le_two_mul_of_D_pow_le m N hN
  have hsq : saving m * (padN (19 * m) m N : ℝ) ^ 2 ≤ saving m * (2 * (N : ℝ)) ^ 2 := by gcongr
  rw [← saving_eq_D_rpow]
  push_cast
  -- `K + |tiles| + |W| ≤ c N² + 4 c (2N)² + c N² = 18 c N²` with `c = 2^{-m/9}`.
  linarith [hK, hT, hW', hsq]

/-! ### Bounds on specified integer values -/

/-- The subsets in the table are distinct (Section 2.3.4), so a sum over the table that selects the
subset `Q` is one of its terms or 0. -/
private theorem sum_table_eq_zero_or {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (Q : Finset (Fin L)) :
    (∑ gh, if lay.table gh = Q then F gh else 0) = 0
      ∨ ∃ gh, (∑ gh', if lay.table gh' = Q then F gh' else 0) = F gh := by
  by_cases hQ : ∃ gh, lay.table gh = Q
  · obtain ⟨gh, rfl⟩ := hQ
    exact .inr ⟨gh, by simp [lay.table_injective.eq_iff]⟩
  · exact .inl (sum_eq_zero fun gh _ => ite_eq_right (not_exists.mp hQ gh))

/-- A nonnegative bound `A` on the absolute values of all entries of `X` also bounds every
value of its left band arrays, for every band index. Zero padding and unused strings are
included; `0 ≤ A` remains required when `N = 0`. -/
theorem abs_bandArrayL_le {L m N : ℕ} (lay : Layout L m) {X : Matrix (Fin N) (Fin (D m)) ℤ} {A : ℤ}
    (hA : 0 ≤ A) (hX : ∀ I k, |X I k| ≤ A) (β : ℕ) (u : LeftStr L) :
    |bandArrayL lay X β u| ≤ A := by
  unfold bandArrayL arrayL bandFamilyL
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => rowBlock lay X (β * K0 L m + gh.1)) (innerSetL u)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hA
    · rw [hgh]
      unfold rowBlock padRows
      split_ifs
      · exact hX _ _
      · simpa using hA
  · simpa using hA

/-- A nonnegative bound `B` on the absolute values of all entries of `Y` also bounds every
value of its right band arrays, for every band index. Zero padding and unused strings are
included; `0 ≤ B` remains required when `N = 0`. -/
theorem abs_bandArrayR_le {L m N : ℕ} (lay : Layout L m) {Y : Matrix (Fin (D m)) (Fin N) ℤ} {B : ℤ}
    (hB : 0 ≤ B) (hY : ∀ k J, |Y k J| ≤ B) (β : ℕ) (v : RightStr L) :
    |bandArrayR lay Y β v| ≤ B := by
  unfold bandArrayR arrayR bandFamilyR
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => colBlock lay Y (β * K0 L m + gh.2)) (innerSetR v)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hB
    · rw [hgh]
      unfold colBlock padCols
      split_ifs
      · exact hY _ _
      · simpa using hB
  · simpa using hB

/-- If every coefficient has absolute value at most one and every array entry has absolute
value at most `A`, then an encoded value has absolute value at most the array index type's
cardinality times `A`. This bounds the value of the finite sum defining `encodeWith`. -/
theorem abs_encodeWith_le {α : Type} [Fintype α] {c : Term → α → ℤ} (hc : ∀ lam s, |c lam s| ≤ 1)
    {L : ℕ} {a : (Fin L → α) → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodeWith c τ a| ≤ Fintype.card (Fin L → α) * A := by
  have h := abs_sum_mul_le univ (c := fun u => ∏ ℓ, c (τ ℓ) (u ℓ))
    (fun u _ => abs_prod_le_one _ fun ℓ _ => hc _ _) fun u _ => ha u
  simpa only [encodeWith, mul_comm, card_univ] using h

/-- An absolute bound `A` on the left array entries gives the bound `7 ^ L * A` on each value
of `encodingL`. -/
theorem abs_encodingL_le {L : ℕ} {a : LeftStr L → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodingL a τ| ≤ 7 ^ L * A := by
  have h := abs_encodeWith_le abs_phi_le_one ha τ
  rw [card_leftStr] at h
  exact_mod_cast h

/-- An absolute bound `B` on the right array entries gives the bound `7 ^ L * B` on each value
of `encodingR`. -/
theorem abs_encodingR_le {L : ℕ} {b : RightStr L → ℤ} {B : ℤ} (hb : ∀ v, |b v| ≤ B) (τ : Leaf L) :
    |encodingR b τ| ≤ 7 ^ L * B := by
  have h := abs_encodeWith_le abs_psi_le_one hb τ
  rw [card_rightStr] at h
  exact_mod_cast h

/-- If `encA` and `encB` are bounded in absolute value by `A` and `B`, every value returned by
`Pruned.result` is bounded by `10 ^ n * (A * B)`. This holds for every request set `S` and
output string `w`, including unrequested strings, whose returned value is zero. It bounds
the specified mathematical result, not native scratch states or machine word width. -/
theorem Pruned.abs_result_le {n : ℕ} (encA encB : Leaf n → ℤ) (A B : ℤ) (hA : ∀ τ, |encA τ| ≤ A)
    (hB : ∀ τ, |encB τ| ≤ B) (S : Finset (OutStr n)) (w : OutStr n) :
    |Pruned.result n encA encB S w| ≤ 10 ^ n * (A * B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA fun _ => Term.P0)
  have hAB : 0 ≤ A * B := mul_nonneg hA0 ((abs_nonneg _).trans (hB fun _ => Term.P0))
  -- The value is 0, or the sum over some of the `10^n` leaves of the product of the two numbers
  -- looked up there.
  rw [Pruned.result_eq_piecewise_sum]
  simp only [Finset.piecewise]
  split_ifs
  · calc |∑ τ : Leaf n with Leaf.Contributes τ w, encA τ * encB τ|
        ≤ (univ.filter fun τ : Leaf n => Leaf.Contributes τ w).card * (A * B) :=
          abs_sum_le_card_mul _ fun τ _ => by
            rw [abs_mul]
            exact mul_le_mul (hA τ) (hB τ) (abs_nonneg _) hA0
      _ ≤ 10 ^ n * (A * B) := by
          gcongr
          exact_mod_cast (card_le_univ _).trans_eq (card_vertex n)
  · simp only [Pi.zero_apply, abs_zero]
    positivity

/-- Under `D m ^ 18 ≤ N`, the number `10 ^ (19 * m)` of leaf indices is at most `N ^ 2`. -/
theorem ten_pow_le_sq (m N : ℕ) (hN : D m ^ 18 ≤ N) : 10 ^ (19 * m) ≤ N ^ 2 := by
  -- `N₀ ≤ K N₀ ≤ N` and `2^{-m/9} ≤ 1`, so equation (6) gives `10^L ≤ N N₀ ≤ N²`.
  have hN0 : (N0 (19 * m) m : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_mul_of_pos_left _ (Nat.choose_pos (by omega))).trans
      (K_mul_N0_le m N hN)
  have hc := saving_le_one m
  have hreal : (10 : ℝ) ^ (19 * m) ≤ (N : ℝ) ^ 2 :=
    calc (10 : ℝ) ^ (19 * m) ≤ saving m * N * N0 (19 * m) m := encoding_size_le m N hN
      _ ≤ 1 * N * N := by gcongr
      _ = (N : ℝ) ^ 2 := by ring
  exact_mod_cast hreal

end Cslib.Algorithms.MatrixMultiplication.Schonhage
