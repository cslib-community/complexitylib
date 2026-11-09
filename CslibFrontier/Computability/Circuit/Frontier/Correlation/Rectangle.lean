/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Foundations.BooleanAnalysis.QuadraticForm
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Correlation with quadratic forms through rectangles

The *correlation* of two sets of inputs `S` and `T` is the fraction of inputs on which membership in
`S` and in `T` agree, minus the fraction on which it differs: in terms of the agreement of the
frontier method, `correlation S T = 2 · agreement S T - 1`
(`Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one`). For Boolean functions `f`
and `g` it is `E[(-1)^{f + g}]`.

**Quadratic forms are balanced on rectangles** (`sq_signedCount_quadForm_rectangle_mul_le`). Let
`S` be the set where the quadratic form of a matrix `Q` over `𝔽₂` is true, and cut the coordinates
into `X` and `Xᶜ`. On an input glued from a part `p` on `X` and a part `q` off `X`, the form is a
form in `p`, plus a form in `q`, plus the bilinear pairing `p ⬝ᵥ C q` of the block `C` of the polar
matrix `Q + Qᵀ` with rows `X` and columns `Xᶜ`, whose rank is the cut rank `ρ(X)`. Lindsey's lemma
then bounds the signed count of `S` on every rectangle `R` for the cut `X`:

`signedCount S R ² · 2^{ρ(X)} ≤ |R| · 2^n`.

**Correlation through rectangle classes** (`sq_correlation_quadForm_mul_le`). Partition the inputs
into classes on which membership in `T` is constant and each of which is a rectangle for the cut
`X`. Lindsey's lemma on every class and Cauchy–Schwarz over the classes give

`correlation S T ² · 2^{ρ(X)} ≤ #classes`.

## Main results

* `Cslib.Circuits.Frontier.sq_signedCount_quadForm_rectangle_mul_le`: quadratic forms are balanced
  on rectangles of large cut rank.
* `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le`: correlation through rectangle classes.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset

variable {ι : Type*}

/-! ### Quadratic forms on rectangles -/

variable [Fintype ι]

/-- **Quadratic forms are balanced on rectangles.** Let `S` be the set where the quadratic form of
`Q` over `𝔽₂` is true. On every rectangle `R` for the cut `X`, the signed count of `S` satisfies
`signedCount S R ² · 2^{ρ(X)} ≤ |R| · 2^n`, where `ρ(X)` is the cut rank of the polar matrix
`Q + Qᵀ` at `X`.

On an input glued from `p` on `X` and `q` off `X`, the sign of the form is the sign of a form in
`p`, times the sign of a form in `q`, times the sign of the pairing of `p` and `q` through the
block of `Q + Qᵀ` with rows `X` and columns `Xᶜ`; this is Lindsey's lemma for that block. -/
theorem sq_signedCount_quadForm_rectangle_mul_le (Q : Matrix ι ι (ZMod 2)) (X : Set ι)
    (A : Set (X → Bool)) (B : Set (↥Xᶜ → Bool)) :
    signedCount {x | BitString.quadForm Q x} (rectangle X A B) ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
      (rectangle X A B).ncard * 2 ^ Fintype.card ι := by
  classical
  set S := {x | BitString.quadForm Q x}
  let e := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool
  let bit := BitString.bitVal (ZMod 2)
  -- The sides, read as vectors over `𝔽₂`.
  let eX : (X → Bool) ↪ (X → ZMod 2) := ⟨fun p i => bit (p i),
    BitString.bitVal_zmod_two_injective.comp_left⟩
  let eY : (↥Xᶜ → Bool) ↪ (↥Xᶜ → ZMod 2) := ⟨fun q i => bit (q i),
    BitString.bitVal_zmod_two_injective.comp_left⟩
  let C := (Q + Qᵀ).submatrix ((↑) : X → ι) ((↑) : ↥Xᶜ → ι)
  let g : (X → ZMod 2) → ℝ := fun u =>
    (-1) ^ (u ⬝ᵥ Q.submatrix ((↑) : X → ι) ((↑) : X → ι) *ᵥ u).val
  let h : (↥Xᶜ → ZMod 2) → ℝ := fun w =>
    (-1) ^ (w ⬝ᵥ Q.submatrix ((↑) : ↥Xᶜ → ι) ((↑) : ↥Xᶜ → ι) *ᵥ w).val
  -- The signed count as a double sum over the sides.
  have hsum : signedCount S (rectangle X A B) =
      -∑ u ∈ A.toFinset.map eX, ∑ w ∈ B.toFinset.map eY,
        g u * h w * (-1) ^ (u ⬝ᵥ C *ᵥ w).val := by
    rw [signedCount_eq_sum, Finset.sum_map, ← Finset.sum_neg_distrib]
    simp only [Finset.sum_map, ← Finset.sum_neg_distrib]
    rw [← Finset.sum_product']
    refine Finset.sum_equiv e (fun x => ?_) fun x _ => ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        mem_toFinset]
      exact Iff.rfl
    · -- The sign of the form at an input splits along the cut.
      have hq := dotProduct_mulVec_self_eq_add Q X fun i => bit (x i)
      have hS : (if x ∈ S then (1 : ℝ) else -1) =
          -(-1) ^ ((fun i => bit (x i)) ⬝ᵥ Q *ᵥ fun i => bit (x i)).val := by
        rw [BitString.neg_one_pow_val_eq]
        simp only [S, mem_ofPred_eq]
        split_ifs <;> simp
      rw [hS, hq, ZMod.neg_one_pow_val_add, ZMod.neg_one_pow_val_add]
      rfl
  have hL := sq_sum_bilinear_mul_two_pow_rank_le C (A.toFinset.map eX) (B.toFinset.map eY) g h
    (fun _ => by simp [g]) (fun _ => by simp [h])
  have hC : C.rank = (Q + Qᵀ).cutRank X := ((Q + Qᵀ).cutRank_eq_rank X).symm
  rw [hC, Finset.card_map, Finset.card_map, ← ncard_eq_toFinset_card',
    ← ncard_eq_toFinset_card'] at hL
  have hn : Fintype.card X + Fintype.card ↥Xᶜ = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact ncard_add_ncard_compl X
  rw [hsum, neg_sq, ncard_rectangle, ← hn, pow_add]
  push_cast
  linarith

/-- **Correlation through rectangle classes.** Let `S` be the set where the quadratic form of `Q`
over `𝔽₂` is true. Let membership in `T` be constant on the classes of `msg`, and let every class
be a rectangle for the cut `X`. Then

`correlation S T ² · 2^{ρ(X)} ≤ #classes`,

where `ρ(X)` is the cut rank of the polar matrix `Q + Qᵀ` at `X`. This is Lindsey's lemma on each
class and Cauchy–Schwarz over the classes. -/
theorem sq_correlation_quadForm_mul_le (Q : Matrix ι ι (ZMod 2)) (T : Set (ι → Bool))
    {M : Type*} (msg : (ι → Bool) → M) (X : Set ι)
    (hT : ∀ x y, msg x = msg y → (x ∈ T ↔ y ∈ T))
    (hrect : ∀ x, ∃ (A : Set (X → Bool)) (B : Set (↥Xᶜ → Bool)),
      {y | msg y = msg x} = rectangle X A B) :
    correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
      (range msg).ncard := by
  classical
  set S := {x | BitString.quadForm Q x}
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ)
  set ρ := (Q + Qᵀ).cutRank X
  have hN : (0 : ℝ) < N := by positivity
  have hNn : N = 2 ^ Fintype.card ι := by simp [N, Fintype.card_bool]
  have hρ : (0 : ℝ) < 2 ^ ρ := by positivity
  set w : (ι → Bool) → ℝ := fun x => if (x ∈ S ↔ x ∈ T) then 1 else -1
  set cls : Finset M := Finset.univ.image msg
  -- The sum over each class is, up to sign, the signed count of `S` on a rectangle.
  have hclass : ∀ μ ∈ cls, (∑ x with msg x = μ, w x) ^ 2 * 2 ^ ρ ≤
      #{x | msg x = μ} * N := by
    intro μ hμ
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hμ
    obtain ⟨A, B, hAB⟩ := hrect x₀
    have hsign : ∑ x with msg x = msg x₀, w x =
        (if x₀ ∈ T then 1 else -1) * signedCount S (rectangle X A B) := by
      rw [signedCount_eq_sum, Finset.mul_sum]
      have hfilter : (Finset.univ.filter fun x => x ∈ rectangle X A B) =
          Finset.univ.filter fun x => msg x = msg x₀ := by
        ext x
        rw [Finset.mem_filter, Finset.mem_filter, ← hAB]
        rfl
      rw [hfilter]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxT := hT x x₀ (Finset.mem_filter.mp hx).2
      simp only [w]
      by_cases hx₀ : x₀ ∈ T <;> by_cases hxS : x ∈ S <;> simp_all
    have hcard : (#{x | msg x = msg x₀} : ℝ) = (rectangle X A B).ncard := by
      rw [ncard_eq_toFinset_card']
      congr 2
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_toFinset, ← hAB,
        mem_ofPred_eq]
    have hL := sq_signedCount_quadForm_rectangle_mul_le Q X A B
    rw [hsign, mul_pow, hcard, hNn]
    have hsq : ((if x₀ ∈ T then 1 else -1 : ℝ)) ^ 2 = 1 := by split_ifs <;> norm_num
    rw [hsq, one_mul]
    exact_mod_cast hL
  -- Cauchy–Schwarz over the classes.
  have htotal : correlation S T * N = ∑ μ ∈ cls, ∑ x with msg x = μ, w x := by
    rw [correlation_mul_card_eq_sum, Finset.sum_fiberwise_of_maps_to
      fun x _ => Finset.mem_image_of_mem msg (Finset.mem_univ x)]
  have hCS := sq_sum_le_card_mul_sum_sq (s := cls) (f := fun μ => ∑ x with msg x = μ, w x)
  have hsumcls : ∑ μ ∈ cls, ((#{x | msg x = μ} : ℕ) : ℝ) = N := by
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (f := msg) (t := cls) fun x _ => Finset.mem_image_of_mem msg (Finset.mem_univ x),
      Finset.card_univ]
  have hbound : (∑ μ ∈ cls, ∑ x with msg x = μ, w x) ^ 2 * 2 ^ ρ ≤ #cls * (N * N) := by
    calc (∑ μ ∈ cls, ∑ x with msg x = μ, w x) ^ 2 * 2 ^ ρ
        ≤ #cls * ∑ μ ∈ cls, (∑ x with msg x = μ, w x) ^ 2 * 2 ^ ρ := by
          rw [← Finset.sum_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hCS hρ.le
      _ ≤ #cls * ∑ μ ∈ cls, (#{x | msg x = μ} : ℝ) * N :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hclass) (Nat.cast_nonneg _)
      _ = #cls * (N * N) := by rw [← Finset.sum_mul, hsumcls]
  have hcls : (#cls : ℝ) = (range msg).ncard := by
    rw [ncard_eq_toFinset_card']
    congr 2
    ext μ
    simp [cls]
  rw [← htotal, mul_pow, hcls] at hbound
  have hNN : 0 < N * N := by positivity
  nlinarith

end Cslib.Circuits.Frontier
