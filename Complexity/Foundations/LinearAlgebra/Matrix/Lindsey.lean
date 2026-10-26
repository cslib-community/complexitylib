/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lindsey's lemma over `𝔽₂`

Read an element `z` of `𝔽₂ = ZMod 2` as the sign `(-1) ^ z`. For a matrix `B` over `𝔽₂` with
rows indexed by `α` and columns by `β`, sets `P` and `Q` of vectors, and weights `g` and `h` of
absolute value at most one,

`(∑_{p ∈ P} ∑_{q ∈ Q} g(p) h(q) (-1)^{p ⬝ᵥ B q})² · 2^{rank B} ≤ |P| |Q| 2^{|α|} 2^{|β|}`

(`Matrix.sq_sum_bilinear_mul_two_pow_rank_le`). This is Lindsey's lemma: a bilinear form of large
rank is nearly balanced on every large combinatorial rectangle [Jukna, Ch. 14][Jukna2011]. For a
square `B` of full rank the sign matrix `(-1)^{p ⬝ᵥ B q}` is a Hadamard matrix, and the bound is
Lindsey's bound `|P| |Q| 2^{|α|}` on its sums over rectangles; the rank refines it.

The proof is Cauchy–Schwarz over `p`, character orthogonality
`∑_p (-1)^{p ⬝ᵥ v} = 2^{|α|} [v = 0]` (`Matrix.sum_neg_one_pow_val_dotProduct`), and the count
`|{q' : B q' = B q}| = 2^{|β| - rank B}` of a fibre of `B` (`Matrix.card_ker_mul_two_pow_rank`).

## Main results

* `ZMod.neg_one_pow_val_add`: the sign of a sum in `𝔽₂` is the product of the signs.
* `Matrix.sum_neg_one_pow_val_dotProduct`: character orthogonality.
* `Matrix.card_ker_mul_two_pow_rank`: the kernel of a matrix over `𝔽₂` has `2^{|β| - rank}`
  elements.
* `Matrix.sq_sum_bilinear_mul_two_pow_rank_le`: Lindsey's lemma.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
-/

@[expose] public section

/-- The sign of a sum in `𝔽₂` is the product of the signs. -/
theorem ZMod.neg_one_pow_val_add {R : Type*} [Ring R] (a b : ZMod 2) :
    (-1 : R) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

namespace Matrix

open Finset

variable {α β : Type*}

/-- **Character orthogonality over `𝔽₂`.** The signs `(-1)^{p ⬝ᵥ v}` cancel over all `p` unless
`v = 0`. -/
theorem sum_neg_one_pow_val_dotProduct [Fintype α] [DecidableEq α] (v : α → ZMod 2) :
    ∑ p : α → ZMod 2, (-1 : ℝ) ^ (p ⬝ᵥ v).val = if v = 0 then (2 : ℝ) ^ Fintype.card α else 0 := by
  split_ifs with hv
  · subst hv
    simp [ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    have hvi : v i = 1 := by
      revert hi
      generalize v i = z
      decide +revert
    -- Flipping the coordinate `i` negates every sign.
    set S := ∑ p : α → ZMod 2, (-1 : ℝ) ^ (p ⬝ᵥ v).val
    have hS : S = -S := by
      calc S = ∑ p : α → ZMod 2, (-1 : ℝ) ^ ((p + Pi.single i 1) ⬝ᵥ v).val :=
            (Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ fun _ => rfl).symm
        _ = ∑ p : α → ZMod 2, -(-1 : ℝ) ^ (p ⬝ᵥ v).val := by
            refine Fintype.sum_congr _ _ fun p => ?_
            rw [add_dotProduct, single_dotProduct, hvi, one_mul, ZMod.neg_one_pow_val_add,
              show (1 : ZMod 2).val = 1 from rfl, pow_one, mul_neg_one]
        _ = -S := by rw [Finset.sum_neg_distrib]
    linarith

/-- All fibres of a linear map have the size of its kernel. -/
theorem card_filter_mulVec_eq [Fintype α] [Fintype β] [DecidableEq β] (B : Matrix α β (ZMod 2))
    (q : β → ZMod 2) :
    #{z : β → ZMod 2 | B *ᵥ z = B *ᵥ q} = #{z : β → ZMod 2 | B *ᵥ z = 0} := by
  refine Finset.card_bij' (fun z _ => z - q) (fun z _ => z + q) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [mulVec_sub, hz, sub_self]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [mulVec_add, hz, zero_add]
  · intro z _
    simp
  · intro z _
    simp

/-- The kernel of a matrix over `𝔽₂` has `2^{|β| - rank B}` elements. -/
theorem card_ker_mul_two_pow_rank [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β (ZMod 2)) :
    #{z : β → ZMod 2 | B *ᵥ z = 0} * 2 ^ B.rank = 2 ^ Fintype.card β := by
  classical
  have hker : #{z : β → ZMod 2 | B *ᵥ z = 0} = Fintype.card (LinearMap.ker B.mulVecLin) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun z => by simp)
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker B.mulVecLin)
  have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  rw [hker, hcard, ZMod.card, rank, ← pow_add, ← hrn, add_comm]

/-- Cauchy–Schwarz bound for a subset `P` when `|g p| ≤ 1`. -/
private theorem sq_sum_mul_le_card_mul_sum_sq [Fintype α] (P : Finset α) (g H : α → ℝ)
    (hg : ∀ p, |g p| ≤ 1) :
    (∑ p ∈ P, g p * H p) ^ 2 ≤ #P * ∑ p, H p ^ 2 := by
  classical
  -- Cauchy–Schwarz over `p`.
  refine (Finset.sum_mul_sq_le_sq_mul_sq P g H).trans ?_
  have hg2 : ∑ p ∈ P, g p ^ 2 ≤ #P := by
    calc ∑ p ∈ P, g p ^ 2 ≤ ∑ _p ∈ P, (1 : ℝ) := Finset.sum_le_sum fun p _ => by
          have := hg p
          nlinarith [abs_nonneg (g p), sq_abs (g p)]
      _ = #P := by simp
  have hH2 : ∑ p ∈ P, H p ^ 2 ≤ ∑ p, H p ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ P) fun p _ _ => sq_nonneg _
  have := Finset.sum_nonneg fun p (_ : p ∈ P) => sq_nonneg (H p)
  calc (∑ p ∈ P, g p ^ 2) * ∑ p ∈ P, H p ^ 2 ≤ #P * ∑ p ∈ P, H p ^ 2 :=
        mul_le_mul_of_nonneg_right hg2 this
    _ ≤ #P * ∑ p, H p ^ 2 := mul_le_mul_of_nonneg_left hH2 (Nat.cast_nonneg _)

/-- Expanding the squared inner sum over all `p : α → ZMod 2` leaves only pairs `(q, q')` in the
same fibre of `B *ᵥ ·`. -/
private theorem sum_sq_sum_bilinear_eq [Fintype α] [Fintype β] [DecidableEq α]
    (B : Matrix α β (ZMod 2)) (Q : Finset (β → ZMod 2)) (h : (β → ZMod 2) → ℝ) :
    (∑ p : α → ZMod 2, (∑ q ∈ Q, h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val) ^ 2) =
      ∑ q ∈ Q, ∑ q' ∈ Q, h q * h q' *
        (if B *ᵥ q + B *ᵥ q' = 0 then (2 : ℝ) ^ Fintype.card α else 0) := by
  -- Expanding the square and summing over `p` first.
  calc ∑ p : α → ZMod 2, (∑ q ∈ Q, h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val) ^ 2
      = ∑ p, ∑ q ∈ Q, ∑ q' ∈ Q, h q * h q' *
          (-1 : ℝ) ^ (p ⬝ᵥ (B *ᵥ q + B *ᵥ q')).val := by
        refine Fintype.sum_congr _ _ fun p => ?_
        simp only [sq, Finset.sum_mul_sum, dotProduct_add, ZMod.neg_one_pow_val_add]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
        ring
    _ = ∑ q ∈ Q, ∑ q' ∈ Q, ∑ p, h q * h q' *
          (-1 : ℝ) ^ (p ⬝ᵥ (B *ᵥ q + B *ᵥ q')).val := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
        rw [← Finset.mul_sum, sum_neg_one_pow_val_dotProduct]

/-- Each row of the fibre-diagonalized sum is bounded by `#(ker B) · 2 ^ |α|`. -/
private theorem sum_fibre_row_le [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β (ZMod 2)) (Q : Finset (β → ZMod 2)) (h : (β → ZMod 2) → ℝ)
    (hh : ∀ q, |h q| ≤ 1) (q : β → ZMod 2) :
    ∑ q' ∈ Q, h q * h q' *
      (if B *ᵥ q + B *ᵥ q' = 0 then (2 : ℝ) ^ Fintype.card α else 0) ≤
      #{z : β → ZMod 2 | B *ᵥ z = 0} * (2 : ℝ) ^ Fintype.card α := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card α := by positivity
  calc ∑ q' ∈ Q, h q * h q' *
        (if B *ᵥ q + B *ᵥ q' = 0 then (2 : ℝ) ^ Fintype.card α else 0)
      ≤ ∑ q' ∈ Q, (if B *ᵥ q' = B *ᵥ q then (2 : ℝ) ^ Fintype.card α else 0) := by
        refine Finset.sum_le_sum fun q' _ => ?_
        -- Over `𝔽₂`, two vectors sum to zero exactly when they are equal.
        have heq : B *ᵥ q + B *ᵥ q' = 0 ↔ B *ᵥ q' = B *ᵥ q := by
          rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self, eq_comm]
        have hhh : |h q * h q'| ≤ 1 := by
          rw [abs_mul]
          nlinarith [abs_nonneg (h q), abs_nonneg (h q'), hh q, hh q']
        rw [if_congr heq rfl rfl]
        split_ifs
        · nlinarith [le_abs_self (h q * h q')]
        · simp
    _ = #{q' ∈ Q | B *ᵥ q' = B *ᵥ q} * (2 : ℝ) ^ Fintype.card α := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ #{z : β → ZMod 2 | B *ᵥ z = 0} * (2 : ℝ) ^ Fintype.card α := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        have hle : #{q' ∈ Q | B *ᵥ q' = B *ᵥ q} ≤ #{z : β → ZMod 2 | B *ᵥ z = 0} :=
          calc _ ≤ #{z : β → ZMod 2 | B *ᵥ z = B *ᵥ q} :=
                Finset.card_le_card fun z hz => by
                  simp only [mem_filter, mem_univ, true_and] at hz ⊢
                  exact hz.2
            _ = _ := card_filter_mulVec_eq B q
        exact_mod_cast hle

/-- **Lindsey's lemma over `𝔽₂`.** For a matrix `B` over `𝔽₂`, sets `P` and `Q` of vectors, and
weights `g` and `h` of absolute value at most one,
`(∑_{p ∈ P} ∑_{q ∈ Q} g(p) h(q) (-1)^{p ⬝ᵥ B q})² · 2^{rank B} ≤ |P| |Q| 2^{|α|} 2^{|β|}`. -/
theorem sq_sum_bilinear_mul_two_pow_rank_le [Fintype α] [Fintype β]
    (B : Matrix α β (ZMod 2)) (P : Finset (α → ZMod 2))
    (Q : Finset (β → ZMod 2)) (g : (α → ZMod 2) → ℝ) (h : (β → ZMod 2) → ℝ)
    (hg : ∀ p, |g p| ≤ 1) (hh : ∀ q, |h q| ≤ 1) :
    (∑ p ∈ P, ∑ q ∈ Q, g p * h q * (-1) ^ (p ⬝ᵥ B *ᵥ q).val) ^ 2 * 2 ^ B.rank ≤
      #P * #Q * 2 ^ Fintype.card α * 2 ^ Fintype.card β := by
  classical
  set H : (α → ZMod 2) → ℝ := fun p => ∑ q ∈ Q, h q * (-1) ^ (p ⬝ᵥ B *ᵥ q).val
  set K := #{z : β → ZMod 2 | B *ᵥ z = 0}
  have hsum : ∑ p ∈ P, ∑ q ∈ Q, g p * h q * (-1 : ℝ) ^ (p ⬝ᵥ B *ᵥ q).val =
      ∑ p ∈ P, g p * H p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [H, Finset.mul_sum, mul_assoc]
  have hCS : (∑ p ∈ P, g p * H p) ^ 2 ≤ #P * ∑ p, H p ^ 2 :=
    sq_sum_mul_le_card_mul_sum_sq P g H hg
  -- Only pairs in a common fibre survive, and fibres have the size of the kernel.
  have hfibre : ∑ p, H p ^ 2 ≤ #Q * K * (2 : ℝ) ^ Fintype.card α := by
    rw [sum_sq_sum_bilinear_eq B Q h]
    calc _ ≤ ∑ _q ∈ Q, K * (2 : ℝ) ^ Fintype.card α :=
          Finset.sum_le_sum fun q _ => sum_fibre_row_le B Q h hh q
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hK : (K : ℝ) * 2 ^ B.rank = 2 ^ Fintype.card β := by
    exact_mod_cast card_ker_mul_two_pow_rank B
  rw [hsum]
  have hpow : (0 : ℝ) ≤ 2 ^ B.rank := by positivity
  calc (∑ p ∈ P, g p * H p) ^ 2 * 2 ^ B.rank
      ≤ #P * (#Q * K * (2 : ℝ) ^ Fintype.card α) * 2 ^ B.rank := by
        refine mul_le_mul_of_nonneg_right (hCS.trans ?_) hpow
        exact mul_le_mul_of_nonneg_left hfibre (Nat.cast_nonneg _)
    _ = #P * #Q * 2 ^ Fintype.card α * ((K : ℝ) * 2 ^ B.rank) := by ring
    _ = _ := by rw [hK]

end Matrix
