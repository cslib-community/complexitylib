/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Degeneration
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Polynomial

/-!
# The primal packing

The primal packing of [Pass][Pass2026], Theorem 3.1, generalizing the three-for-one
degeneration of OpenAI's proof of `ω ≤ 9/4`: for `c t ≥ a + 2 b - 1`, the `c + 1` full
products `Full_{a,b}` of one polynomial `A` of length `a` with polynomials `P₁, …, P_{c+1}` of
length `b`, together with one middle product `Mid_{a,b}` of `A` with a polynomial `Q`, are
computed modulo `ε` from the `c` full products of `A` with the encoded polynomials
`E_ν = P_ν - z ^ t P_{ν+1} + ε z ^ b Q^{(ν)}`, where `Q^{(ν)}` is the `ν`-th block of `t`
consecutive coefficients of `Q`. The telescoping sum
`∑ z ^ (t ν) A E_ν = A P₁ + ε z ^ b A Q - z ^ (c t) A P_{c+1}` exposes the middle coefficients
of `A Q` in the gap between the two endpoint products, and the successive differences recover
the full products.

In the language of degenerations, this is a shared-left degeneration of order `1` of the sum of
the `c` sources `Full_{a,b+t}` to the shared-left sum of the `c + 2` targets, along the
inclusion of the padded index sets (`Tensor.isSLDegen_primal`). Each coefficient of the decoded
output is `ε` times the target plus `ε ^ 2` times an error.

## Main definitions

* `Cslib.Tensor.primalTargets`: the `c + 2` targets, `c + 1` full products and a middle product.

## Main results

* `Cslib.Tensor.isSLDegen_primal`: the primal packing, [Pass][Pass2026], Theorem 3.1.

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], Theorem 3.1
-/

@[expose] public section

namespace Cslib.Tensor

open Finset Polynomial

variable {K : Type*} [CommRing K]

/-- The targets of the primal packing: `c + 1` copies of the full product `Full_{a,b}` followed
by one middle product `Mid_{a,b}`. -/
def primalTargets (a b c : ℕ) (j : Fin (c + 2)) :
    Tensor K (Fin (a + b - 1)) (Fin (a + b - 1)) (Fin (a + b - 1)) :=
  if j.val ≤ c then full a b else mid a b

/-! ### The encoder, the decoder and the decoded entries

The right encoder and the decoder are given by their entries as functions of the index values,
`ε`-free parts and `ε`-parts separately; the decoded entries are computed as double sums over the
source indices, and the three coefficient identities below are the telescoping argument. -/

private theorem restrict_incl_slSum_apply {U V W U' V' W' ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype U'] [Fintype V'] [Fintype W'] [DecidableEq U'] (f : U → U')
    (β : Matrix (ι × V') (κ × V) K[X]) (γ : Matrix (κ × W) (ι × W') K[X])
    (G : ι → Tensor K U' V' W') (x : U) (j : κ) (y : V) (j' : κ) (z : W) :
    restrict (incl f) β γ ((slSum G).map C) x (j, y) (j', z) =
      ∑ ν, ∑ y', ∑ ℓ, β (ν, y') (j, y) * γ (j', z) (ν, ℓ) * C (G ν (f x) y' ℓ) := by
  simp only [restrict, incl_apply, Tensor.map_apply, slSum_apply, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul, apply_ite C, map_zero, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The `ε`-free part of the right encoder: `P_ν - z ^ t P_{ν+1}`, source `(ν, y')`, target
`(j, y)`. -/
private def primalBeta₀ (b t : ℕ) (ν y' j y : ℕ) : K :=
  (if j = ν ∧ y' = y ∧ y < b then 1 else 0) -
    (if j - 1 = ν ∧ 1 ≤ j ∧ y' = y + t ∧ y < b then 1 else 0)

/-- The `ε`-part of the right encoder: the `ν`-th block of the reversed `Q`, shifted by `z ^ b`. -/
private def primalBeta₁ (b c t s : ℕ) (ν y' j y : ℕ) : K :=
  if j = c + 1 ∧ b ≤ y' ∧ y' < b + t ∧ t * ν + y' + y + 1 = s + b then 1 else 0

/-- The decoder of the full targets `j ≤ c`, up to the factor `ε`. -/
private def primalGamma₁ (t s : ℕ) (j' k ν ℓ : ℕ) : K :=
  if ℓ + t * ν = k + t * j' then (if k + t * j' < s then 1 else 0) - (if ν < j' then 1 else 0)
  else 0

/-- The decoder of the middle target. -/
private def primalGamma₀ (b t s : ℕ) (k ν ℓ : ℕ) : K :=
  if k < b ∧ ℓ + t * ν + k + 1 = s + b then 1 else 0

private noncomputable def primalBeta (b c t s : ℕ) (ν y' j y : ℕ) : K[X] :=
  C (primalBeta₀ b t ν y' j y) + Polynomial.X * C (primalBeta₁ b c t s ν y' j y)

private noncomputable def primalGamma (b c t s : ℕ) (j' k ν ℓ : ℕ) : K[X] :=
  if j' ≤ c then Polynomial.X * C (primalGamma₁ t s j' k ν ℓ) else C (primalGamma₀ b t s k ν ℓ)

/-- Collapse the sum over the output index of a full product. -/
private theorem sum_fin_mul_ite_eq {n : ℕ} (F : Fin n → K[X]) (P Q : Prop) [Decidable P]
    [Decidable Q] (m : ℕ) :
    ∑ ℓ : Fin n, F ℓ * C (if P ∧ Q ∧ m = ℓ.val then 1 else 0) =
      if h : P ∧ Q ∧ m < n then F ⟨m, h.2.2⟩ else 0 := by
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨m, h.2.2⟩]
    · simp [h.1, h.2.1]
    · intro ℓ hℓ
      have : m ≠ ℓ.val := fun hm => hℓ (Fin.ext hm.symm)
      simp [this]
  · refine Finset.sum_eq_zero fun ℓ _ => ?_
    have : ¬ (P ∧ Q ∧ m = ℓ.val) := fun h' => h ⟨h'.1, h'.2.1, h'.2.2 ▸ ℓ.isLt⟩
    simp [this]

/-- The entries of the restriction, as a double sum over the source indices. -/
private theorem primal_entry (a b c t : ℕ) (h : a + b - 1 ≤ a + (b + t) - 1)
    (x : Fin (a + b - 1)) (j j' : Fin (c + 2)) (y k : Fin (a + b - 1)) :
    restrict (incl (Fin.castLE h))
      (Matrix.of fun p q => primalBeta (K := K) b c t (a + b - 1) p.1.val p.2.val q.1.val q.2.val)
      (Matrix.of fun q p => primalGamma (K := K) b c t (a + b - 1) q.1.val q.2.val p.1.val p.2.val)
      ((slSum fun _ : Fin c => (full a (b + t) : Tensor K _ _ _)).map C) x (j, y) (j', k) =
      ∑ ν ∈ range c, ∑ y' ∈ range (a + (b + t) - 1),
        primalBeta b c t (a + b - 1) ν y' j y *
          (if x < a ∧ y' < b + t ∧ x + y' < a + (b + t) - 1 then
            primalGamma b c t (a + b - 1) j' k ν (x + y') else 0) := by
  rw [restrict_incl_slSum_apply]
  simp only [Matrix.of_apply, full_apply, Fin.val_castLE]
  simp only [sum_fin_mul_ite_eq, dite_eq_ite]
  simp only [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [dite_eq_left (Finset.mem_range.1 hν)]
  refine Finset.sum_congr rfl fun y' hy' => ?_
  rw [dite_eq_left (Finset.mem_range.1 hy')]
  simp only [mul_ite, mul_zero]

/-- The entries decoding a full target `j' ≤ c`: `ε` times the `ε`-free part plus `ε ^ 2` times
the rest. -/
private theorem sum_primalBeta_mul_le (b c t s : ℕ) {j' : ℕ} (hj' : j' ≤ c) (x j y k : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (n m : ℕ) :
    ∑ ν ∈ range n, ∑ y' ∈ range m, primalBeta (K := K) b c t s ν y' j y *
        (if P y' then primalGamma b c t s j' k ν (x + y') else 0) =
      Polynomial.X * C (∑ ν ∈ range n, ∑ y' ∈ range m, primalBeta₀ b t ν y' j y *
          (if P y' then primalGamma₁ t s j' k ν (x + y') else 0)) +
        Polynomial.X ^ 2 * C (∑ ν ∈ range n, ∑ y' ∈ range m, primalBeta₁ b c t s ν y' j y *
          (if P y' then primalGamma₁ t s j' k ν (x + y') else 0)) := by
  simp only [primalBeta, primalGamma, ite_eq_left hj', map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y' _ => ?_
  split_ifs
  · simp only [map_mul]
    ring
  · simp

/-- The entries decoding the middle target `j' = c + 1`. -/
private theorem sum_primalBeta_mul_not_le (b c t s : ℕ) {j' : ℕ} (hj' : ¬ j' ≤ c) (x j y k : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (n m : ℕ) :
    ∑ ν ∈ range n, ∑ y' ∈ range m, primalBeta (K := K) b c t s ν y' j y *
        (if P y' then primalGamma b c t s j' k ν (x + y') else 0) =
      C (∑ ν ∈ range n, ∑ y' ∈ range m, primalBeta₀ b t ν y' j y *
          (if P y' then primalGamma₀ b t s k ν (x + y') else 0)) +
        Polynomial.X * C (∑ ν ∈ range n, ∑ y' ∈ range m, primalBeta₁ b c t s ν y' j y *
          (if P y' then primalGamma₀ b t s k ν (x + y') else 0)) := by
  simp only [primalBeta, primalGamma, ite_eq_right hj', map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y' _ => ?_
  split_ifs
  · simp only [map_mul]
    ring
  · simp


/-- The `ε`-free part decoding a full target `j' ≤ c` is that target. -/
private theorem primal_key_full {a b c t : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : a + b - 1 + b ≤ t * c) {x j y j' k : ℕ} (hj : j < c + 2) (hj' : j' ≤ c)
    (hk : k < a + b - 1) :
    ∑ ν ∈ range c, ∑ y' ∈ range (a + (b + t) - 1), primalBeta₀ (K := K) b t ν y' j y *
        (if x < a ∧ y' < b + t ∧ x + y' < a + (b + t) - 1 then
          primalGamma₁ t (a + b - 1) j' k ν (x + y') else 0) =
      if j = j' ∧ x < a ∧ y < b ∧ x + y = k then 1 else 0 := by
  have hc0 : 1 ≤ c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc; omega)
  simp only [primalBeta₀, sub_mul, Finset.sum_sub_distrib, ite_and, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_range]
  by_cases hxa : x < a
  swap
  · simp [hxa]
  by_cases hyb : y < b
  swap
  · simp [hyb]
  simp only [hxa, hyb, (by omega : y < a + (b + t) - 1), (by omega : y < b + t),
    (by omega : x + y < a + (b + t) - 1), (by omega : y + t < a + (b + t) - 1),
    (by omega : y + t < b + t), (by omega : x + (y + t) < a + (b + t) - 1), ite_true,
    primalGamma₁]
  rcases Nat.lt_or_ge j c with hjc | hjc
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have h10 : ¬ (1 : ℕ) ≤ 0 := by omega
      simp only [(by omega : (0 : ℕ) - 1 < c), h10, ite_true, ite_false, mul_zero, add_zero,
        sub_zero]
      rcases Nat.eq_zero_or_pos j' with rfl | hj'0
      · simp [hk]
      · rw [ite_eq_right (by omega : ¬ (0 = j'))]
        split_ifs <;> first | omega | simp
    · obtain ⟨j₁, rfl⟩ : ∃ j₁, j = j₁ + 1 := ⟨j - 1, by omega⟩
      simp only [hjc, Nat.add_sub_cancel, (by omega : j₁ < c), (by omega : 1 ≤ j₁ + 1), ite_true,
        mul_add_one]
      have hf : j' = j₁ + 1 → t * j' = t * j₁ + t := fun h => by subst h; ring
      split_ifs <;> first | omega | norm_num
  · obtain rfl | rfl : c = j ∨ c + 1 = j := by omega
    · simp only [lt_irrefl, ite_false, (by omega : c - 1 < c), hc0, ite_true, zero_sub]
      have hf : t * (c - 1) + t = t * c := by
        rw [← mul_add_one, Nat.sub_add_cancel hc0]
      have hf2 : j' = c → t * j' = t * c := fun h => by subst h; rfl
      split_ifs <;> first | omega | norm_num
    · have hcc : ¬ c + 1 < c := by omega
      simp only [hcc, Nat.add_sub_cancel, lt_irrefl, ite_false, sub_zero]
      rw [ite_eq_right (by omega : ¬ (c + 1 = j'))]

/-- The `ε`-free part decoding the middle target vanishes. -/
private theorem primal_key_mid_zero {a b c t : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : a + b - 1 + b ≤ t * c) {x j y k : ℕ} (hj : j < c + 2) (hk : k < a + b - 1) :
    ∑ ν ∈ range c, ∑ y' ∈ range (a + (b + t) - 1), primalBeta₀ (K := K) b t ν y' j y *
        (if x < a ∧ y' < b + t ∧ x + y' < a + (b + t) - 1 then
          primalGamma₀ b t (a + b - 1) k ν (x + y') else 0) = 0 := by
  have hc0 : 1 ≤ c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc; omega)
  simp only [primalBeta₀, sub_mul, Finset.sum_sub_distrib, ite_and, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_range]
  by_cases hxa : x < a
  swap
  · simp [hxa]
  by_cases hyb : y < b
  swap
  · simp [hyb]
  simp only [hxa, hyb, (by omega : y < a + (b + t) - 1), (by omega : y < b + t),
    (by omega : x + y < a + (b + t) - 1), (by omega : y + t < a + (b + t) - 1),
    (by omega : y + t < b + t), (by omega : x + (y + t) < a + (b + t) - 1), ite_true,
    primalGamma₀]
  rcases Nat.lt_or_ge j c with hjc | hjc
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have h10 : ¬ (1 : ℕ) ≤ 0 := by omega
      simp only [hjc, h10, ite_true, ite_false, mul_zero, add_zero, sub_zero]
      split_ifs <;> first | omega | rfl
    · obtain ⟨j₁, rfl⟩ : ∃ j₁, j = j₁ + 1 := ⟨j - 1, by omega⟩
      simp only [hjc, Nat.add_sub_cancel, (by omega : j₁ < c), (by omega : 1 ≤ j₁ + 1), ite_true,
        mul_add_one]
      split_ifs <;> first | omega | norm_num
  · obtain rfl | rfl : c = j ∨ c + 1 = j := by omega
    · simp only [lt_irrefl, ite_false, (by omega : c - 1 < c), hc0, ite_true, zero_sub]
      have hf : t * (c - 1) + t = t * c := by
        rw [← mul_add_one, Nat.sub_add_cancel hc0]
      split_ifs <;> first | omega | norm_num
    · have hcc : ¬ c + 1 < c := by omega
      simp only [hcc, Nat.add_sub_cancel, lt_irrefl, ite_false, sub_zero]

/-- The `ε`-part decoding the middle target is the middle target. -/
private theorem primal_key_mid {a b c t : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ht : 1 ≤ t)
    (hc : a + b - 1 + b ≤ t * c) {x j y k : ℕ} :
    ∑ ν ∈ range c, ∑ y' ∈ range (a + (b + t) - 1), primalBeta₁ (K := K) b c t (a + b - 1) ν y' j y *
        (if x < a ∧ y' < b + t ∧ x + y' < a + (b + t) - 1 then
          primalGamma₀ b t (a + b - 1) k ν (x + y') else 0) =
      if j = c + 1 ∧ x < a ∧ k < b ∧ x + k = y then 1 else 0 := by
  obtain ⟨m, hm⟩ : ∃ m, m = a + b - 2 - x - k := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod m t
  have hml := Nat.mod_lt m ht
  have key : ∀ ν y', ((j = c + 1 ∧ b ≤ y' ∧ y' < b + t ∧ t * ν + y' + y + 1 = a + b - 1 + b) ∧
      (x < a ∧ y' < b + t ∧ x + y' < a + (b + t) - 1) ∧
        (k < b ∧ x + y' + t * ν + k + 1 = a + b - 1 + b)) ↔
      (m / t = ν ∧ b + m % t = y' ∧ (j = c + 1 ∧ x < a ∧ k < b ∧ x + k = y)) := by
    intro ν y'
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩⟩
      obtain ⟨hd, hmod⟩ := (Nat.div_mod_unique ht).2
        ⟨(by omega : (y' - b) + t * ν = m), (by omega : y' - b < t)⟩
      exact ⟨hd, by omega, h1, h5, h8, by omega⟩
    · rintro ⟨rfl, rfl, h1, h5, h8, h9⟩
      omega
  simp only [primalBeta₁, primalGamma₀, ite_mul, one_mul, zero_mul, ← ite_and]
  simp only [key, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_range]
  have h1 : m / t < c := Nat.div_lt_of_lt_mul (by omega)
  have h2 : b + m % t < a + (b + t) - 1 := by omega
  simp only [h1, h2, ite_true]


/-- The `ε ^ 2`-remainder of a decoded entry: the `ε`-part of the encoder against the decoder of
a full target. -/
private noncomputable def primalRem (a b c t : ℕ) (x : ℕ) (y z : ℕ × ℕ) : K[X] :=
  if z.1 ≤ c then
    C (∑ ν ∈ range c, ∑ y' ∈ range (a + (b + t) - 1), primalBeta₁ b c t (a + b - 1) ν y' y.1 y.2 *
      (if x < a ∧ y' < b + t ∧ x + y' < a + (b + t) - 1 then
        primalGamma₁ t (a + b - 1) z.1 z.2 ν (x + y') else 0))
  else 0

/-- The target entries, in terms of the index values. -/
private theorem slSum_primalTargets_apply (a b c : ℕ) (x : Fin (a + b - 1)) (j j' : Fin (c + 2))
    (y k : Fin (a + b - 1)) :
    slSum (primalTargets a b c) x (j, y) (j', k) =
      if j'.val ≤ c then
        (if j.val = j'.val ∧ x.val < a ∧ y.val < b ∧ x.val + y.val = k.val then (1 : K) else 0)
      else
        (if j.val = c + 1 ∧ x.val < a ∧ k.val < b ∧ x.val + k.val = y.val then 1 else 0) := by
  simp only [slSum_apply, primalTargets, ite_apply, full_apply, mid_apply]
  by_cases hjj : j = j'
  · subst hjj
    by_cases hj : j.val ≤ c
    · simp [hj]
    · simp [show j.val = c + 1 by omega]
  · have h1 : j.val ≠ j'.val := fun h => hjj (Fin.ext h)
    have h2 : ¬ j'.val ≤ c → j.val ≠ c + 1 := fun hj' h => hjj (Fin.ext (by omega))
    rw [ite_eq_right hjj]
    split_ifs with hj' h3 h4
    · exact absurd h3.1 h1
    · rfl
    · exact absurd h4.1 (h2 hj')
    · rfl

/-- Each decoded entry is `ε` times the target entry plus `ε ^ 2` times the remainder. -/
private theorem primal_entry_eq {a b c t : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ht : 1 ≤ t)
    (hc : a + b - 1 + b ≤ t * c) (h : a + b - 1 ≤ a + (b + t) - 1) (x : Fin (a + b - 1))
    (j j' : Fin (c + 2)) (y k : Fin (a + b - 1)) :
    restrict (incl (Fin.castLE h))
      (Matrix.of fun p q => primalBeta (K := K) b c t (a + b - 1) p.1.val p.2.val q.1.val q.2.val)
      (Matrix.of fun q p => primalGamma (K := K) b c t (a + b - 1) q.1.val q.2.val p.1.val p.2.val)
      ((slSum fun _ : Fin c => (full a (b + t) : Tensor K _ _ _)).map C) x (j, y) (j', k) =
      Polynomial.X * C (slSum (primalTargets a b c) x (j, y) (j', k)) +
        Polynomial.X ^ 2 * primalRem a b c t x.val (j.val, y.val) (j'.val, k.val) := by
  rw [primal_entry, slSum_primalTargets_apply]
  by_cases hj' : j'.val ≤ c
  · rw [sum_primalBeta_mul_le b c t (a + b - 1) hj', primal_key_full ha hb hc j.isLt hj' k.isLt]
    simp only [primalRem, hj', ite_true]
  · rw [sum_primalBeta_mul_not_le b c t (a + b - 1) hj',
      primal_key_mid_zero ha hb hc j.isLt k.isLt, primal_key_mid ha hb ht hc, map_zero, zero_add]
    simp only [primalRem, hj', ite_false, mul_zero, add_zero]

/-- **The primal packing** ([Pass][Pass2026], Theorem 3.1): for `a, b, t ≥ 1` and
`c t ≥ a + 2 b - 1`, the shared-left sum of `c + 1` full products `Full_{a,b}` and one middle
product `Mid_{a,b}` is a shared-left degeneration of order `1` of the shared-left sum of `c`
full products `Full_{a,b+t}`, along the inclusion `Fin (a + b - 1) → Fin (a + (b + t) - 1)` of
the padded index sets. -/
theorem isSLDegen_primal {a b c t : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ht : 1 ≤ t)
    (hc : a + 2 * b - 1 ≤ c * t) :
    IsSLDegen (Fin.castLE (by omega : a + b - 1 ≤ a + (b + t) - 1)) 1
      (slSum (primalTargets a b c : Fin (c + 2) → Tensor K _ _ _))
      (slSum fun _ : Fin c => full a (b + t)) := by
  have hc' : a + b - 1 + b ≤ t * c := by rw [mul_comm]; omega
  refine ⟨Matrix.of fun p q => primalBeta b c t (a + b - 1) p.1.val p.2.val q.1.val q.2.val,
    Matrix.of fun q p => primalGamma b c t (a + b - 1) q.1.val q.2.val p.1.val p.2.val,
    fun x y z => primalRem a b c t x.val (y.1.val, y.2.val) (z.1.val, z.2.val), ?_⟩
  funext x y z
  obtain ⟨j, y⟩ := y
  obtain ⟨j', k⟩ := z
  rw [primal_entry_eq ha hb ht hc']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply, pow_one]

end Cslib.Tensor
