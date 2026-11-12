/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ROABP
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Pi

/-!
# The monomials and coefficients of a segment of a branching program

For a list `L` of variables, `monomialsLE L δ` is the set of exponent vectors of the monomials
in the variables of `L` of individual degree at most `δ`, and `segmentCoeff M L m` is the product
of the coefficient matrices of the layers of `L` at the exponents of `m`. For two disjoint lists
the monomials of `L₁ ++ L₂` are the sums of a monomial of `L₁` and a monomial of `L₂`
(`monomialsLE_append`), and the coefficient is the product of the two
coefficients (`segmentCoeff_append_add`). This is the product structure that Agrawal, Gurjar,
Korwar and Saxena [AgrawalGurjarKorwarSaxena2015] use for the coefficients of a product of
polynomials over the matrix algebra in disjoint sets of variables.

## Main definitions

* `monomialsLE`: exponent vectors supported in a list, with entries at most `δ`.
* `segmentCoeff`: the product of the coefficient matrices of the layers of a list.

## Main results

* `monomialsLE_append`, `segmentCoeff_append_add`.
* `weight_le_of_mem_monomialsLE`: a bound on the weight of such a monomial.

## References

* [M. Agrawal, R. Gurjar, A. Korwar, N. Saxena, *Hitting-sets for ROABP and sum of
  set-multilinear circuits*][AgrawalGurjarKorwarSaxena2015], §3, proof of Lemma 8
-/

public section

open scoped Polynomial Pointwise

namespace Cslib.Circuits.Arithmetic

open Finset

variable {F : Type*} [Field F] {n w : ℕ}

open scoped Classical in
/-- The exponent vectors with entries at most `δ` that vanish outside the list `L`. -/
noncomputable def monomialsLE (L : List (Fin n)) (δ : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Fintype.piFinset fun i : Fin n => if i ∈ L then range (δ + 1) else {0}).map
    Finsupp.equivFunOnFinite.symm.toEmbedding

theorem mem_monomialsLE {L : List (Fin n)} {δ : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ monomialsLE L δ ↔ (∀ i, m i ≤ δ) ∧ ∀ i ∉ L, m i = 0 := by
  classical
  rw [monomialsLE, mem_map_equiv, Fintype.mem_piFinset]
  refine ⟨fun h => ⟨fun i => ?_, fun i hi => ?_⟩, fun h i => ?_⟩
  · have hi := h i
    split_ifs at hi with hL
    · exact Nat.lt_succ_iff.1 (mem_range.1 hi)
    · rw [show m i = 0 from mem_singleton.1 hi]
      exact Nat.zero_le δ
  · have h' := h i
    simp only [hi, ↓reduceIte] at h'
    exact mem_singleton.1 h'
  · split_ifs with hL
    · exact mem_range.2 (Nat.lt_succ_of_le (h.1 i))
    · exact mem_singleton.2 (h.2 i hL)

/-- The monomials of two disjoint lists: sums of a monomial of each. -/
theorem monomialsLE_append {L₁ L₂ : List (Fin n)} (hd : L₁.Disjoint L₂) (δ : ℕ) :
    monomialsLE (L₁ ++ L₂) δ = monomialsLE L₁ δ + monomialsLE L₂ δ := by
  classical
  ext m
  rw [mem_add]
  constructor
  · intro hm
    obtain ⟨h1, h2⟩ := mem_monomialsLE.1 hm
    refine ⟨m.filter (· ∈ L₁), mem_monomialsLE.2 ⟨fun i => ?_, fun i hi => ?_⟩,
      m.filter (· ∉ L₁), mem_monomialsLE.2 ⟨fun i => ?_, fun i hi => ?_⟩,
      Finsupp.filter_add_filter_not m _⟩
    · rw [Finsupp.filter_apply]
      split_ifs <;> first | exact h1 i | exact Nat.zero_le _
    · exact Finsupp.filter_apply_neg _ m hi
    · rw [Finsupp.filter_apply]
      split_ifs <;> first | exact h1 i | exact Nat.zero_le _
    · by_cases hi1 : i ∈ L₁
      · exact Finsupp.filter_apply_neg _ m (not_not.2 hi1)
      · rw [Finsupp.filter_apply_pos _ m hi1]
        exact h2 i fun h => (List.mem_append.1 h).elim hi1 hi
  · rintro ⟨m₁, hm₁, m₂, hm₂, rfl⟩
    obtain ⟨h1, h1'⟩ := mem_monomialsLE.1 hm₁
    obtain ⟨h2, h2'⟩ := mem_monomialsLE.1 hm₂
    refine mem_monomialsLE.2 ⟨fun i => ?_, fun i hi => ?_⟩
    · rw [Finsupp.add_apply]
      by_cases hi : i ∈ L₁
      · rw [h2' i fun h => hd hi h, add_zero]
        exact h1 i
      · rw [h1' i hi, zero_add]
        exact h2 i
    · rw [Finsupp.add_apply, h1' i fun h => hi (List.mem_append_left _ h),
        h2' i fun h => hi (List.mem_append_right _ h)]

/-- The product of the coefficient matrices of the layers of the list `L` at the exponents of
`m`: the coefficient of the monomial `m` in the product of the layers, as a matrix. -/
@[expose] def segmentCoeff (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (L : List (Fin n))
    (m : Fin n →₀ ℕ) : Matrix (Fin w) (Fin w) F :=
  (L.map fun i => layerCoeff M i (m i)).prod

/-- The coefficient of a sum of monomials of two disjoint lists is the product of the
coefficients. -/
theorem segmentCoeff_append_add (M : Fin n → Matrix (Fin w) (Fin w) F[X]) {L₁ L₂ : List (Fin n)}
    (hd : L₁.Disjoint L₂) {δ : ℕ} {m₁ m₂ : Fin n →₀ ℕ} (hm₁ : m₁ ∈ monomialsLE L₁ δ)
    (hm₂ : m₂ ∈ monomialsLE L₂ δ) :
    segmentCoeff M (L₁ ++ L₂) (m₁ + m₂) = segmentCoeff M L₁ m₁ * segmentCoeff M L₂ m₂ := by
  rw [segmentCoeff, List.map_append, List.prod_append, segmentCoeff, segmentCoeff]
  congr 2
  · refine List.map_congr_left fun i hi => ?_
    rw [Finsupp.add_apply, (mem_monomialsLE.1 hm₂).2 i fun h => hd hi h, add_zero]
  · refine List.map_congr_left fun i hi => ?_
    rw [Finsupp.add_apply, (mem_monomialsLE.1 hm₁).2 i fun h => hd h hi, zero_add]

/-- The weight of a monomial of individual degree at most `δ`, for weights at most `N`. -/
theorem weight_le_of_mem_monomialsLE {L : List (Fin n)} {δ N : ℕ} {c : Fin n → ℕ}
    (hc : ∀ i, c i ≤ N) {m : Fin n →₀ ℕ} (hm : m ∈ monomialsLE L δ) :
    Finsupp.weight c m ≤ n * δ * N := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ fun i => zero_smul ℕ (c i)]
  calc ∑ i, m i • c i ≤ ∑ _i : Fin n, δ * N :=
        sum_le_sum fun i _ => Nat.mul_le_mul ((mem_monomialsLE.1 hm).1 i) (hc i)
    _ = n * δ * N := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

/-- The weight for `B * c + c'` is `B` times the weight for `c` plus the weight for `c'`. -/
theorem weight_mul_add (B : ℕ) (c c' : Fin n → ℕ) (m : Fin n →₀ ℕ) :
    Finsupp.weight (fun i => B * c i + c' i) m =
      B * Finsupp.weight c m + Finsupp.weight c' m := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum,
    Finsupp.sum, Finsupp.sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by
    simp only [smul_eq_mul]
    ring

end Cslib.Circuits.Arithmetic
