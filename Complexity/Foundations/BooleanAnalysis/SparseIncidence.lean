/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.IncidenceExpansion
public import Complexity.Foundations.BooleanAnalysis.SparseEquations
import Complexity.Foundations.BooleanAnalysis.SparseEquations.Degree
import Mathlib.Algebra.BigOperators.ModEq

/-!
# The incidence polynomial of a sparse system over `𝔽₂`

This file proves the congruence (D.2) in the proof of Lemma D.2 of [OpenAI2026ETH] (pp. 54–56).
That lemma counts the common zeros of a sparse polynomial system over `𝔽₂` by contracting tensor
networks over `(ℤ / 2 ^ p)[V] / (V ^ ℓ)`.

Equation `P i` is a family of monomials (`Finset (Finset ι)`). At the indicator `1_T` of a set
`T`, its integer lift counts the monomials inside `T`. Its parity factor is
`B_i(1_T, V) = ∑_{j < ℓ} e_j(y) h(y) ^ j V ^ j`, with `y` that count, `h(Y) = Y (Y - 1)` and `e_j`
from Lemma 5.1 (`Polynomial.parityFactor`). Its **incidence coefficient** at `S`
(`Cslib.BitString.parityCoeff`) is the subset inversion `∑_{T ⊆ S} (-1) ^ (|S| - |T|) B_i(1_T, V)`
in `ℤ[V]`. This is the coefficient `[z_{i,S}] B̄_i` of the multilinear factor on p. 56.

* **The per-factor degree bound** (p. 55, just before (D.1)): if every monomial has at most `k`
  variables, the `V ^ j` coefficient of `parityCoeff ℓ (P i) S` vanishes once `#S > k (1 + 2 j)`
  (`Cslib.BitString.coeff_parityCoeff_eq_zero`). The reason is that `e_j(y) h(y) ^ j` has degree at
  most `k (1 + 2 j)` on the cube (`Cslib.BitString.coeff_parityFactor_mem_lowDegree`). Over the
  `a` equations this gives the bound (D.1): below `V ^ ℓ`, every term of the product has at most
  `K = k (a + 2 (ℓ - 1))` incidences (`Cslib.BitString.coeff_incidenceSum_eq_of_le`).
* **(D.2)**: for `a` equations, scopes `I i` containing the variables of `P i`, `ℓ ≥ 1` and
  `K ≥ k (a + 2 (ℓ - 1))`, the number of common zeros is congruent modulo `2 ^ ℓ` to the sum of the
  coefficients below `V ^ ℓ` of the incidence sum of these coefficients
  (`Cslib.BitString.commonZeroCount_modEq_sumCoeffsBelow_incidenceSum`). The incidence sum is
  `Cslib.BitString.incidenceSum I (fun i => parityCoeff ℓ (P i)) K`. The proof combines Lemma 5.2
  (`Cslib.BitString.sum_sumCoeffsBelow_prod_parityFactor_modEq_commonZeroCount`), the incidence
  expansion (`Cslib.BitString.sum_prod_eq_incidenceSum`) and the truncation
  (`Cslib.BitString.coeff_incidenceSum_eq_of_le`).
* **Exact recovery**: for `n < ℓ` variables, any integers congruent to the coefficients below
  `V ^ ℓ` sum, modulo `2 ^ ℓ`, to the count
  (`Cslib.BitString.emod_sum_eq_commonZeroCount_of_modEq`). These integers can be the coefficients
  of a contraction in `(ℤ / 2 ^ ℓ)[V] / (V ^ ℓ)`.

The paper writes (D.2) with the incidence polynomial `F(z, V) = ∏_i B̄_i(z_i, V)` summed at
`z_{iv} = x_v` over the cube. The incidence sum is that cube sum written as its monomial
expansion: the monomial of a set of incidences `(S i)_i` has coefficient `∏_i [z_{i,S_i}] B̄_i`, and
its cube sum is the weight `2 ^ |{v : b_v = 0}|`. The lemma's networks contract exactly this sum,
one network per degree array.

## Main definitions

* `Cslib.BitString.parityCoeff`: the incidence coefficient `[z_S] B̄` of an equation.

## Main results

* `Cslib.BitString.monomialSum_indicator`: the integer lift at an indicator counts the monomials
  inside the set.
* `Cslib.BitString.coeff_parityCoeff_eq_zero`: the per-factor degree bound preceding (D.1).
* `Cslib.BitString.commonZeroCount_modEq_sumCoeffsBelow_incidenceSum`: the congruence (D.2).
* `Cslib.BitString.emod_sum_eq_commonZeroCount_of_modEq`: exact recovery of the count.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemmas 5.1 and 5.2
  (pp. 36–37) and the proof of Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.BitString

open Finset Polynomial

variable {ι κ : Type*} [DecidableEq ι]

/-- **The incidence coefficient** `[z_S] B̄` of an equation `P` (a family of monomials) at a set
`S`, for truncation order `ℓ`: the subset Möbius transform at `S` of
`T ↦ parityFactor ℓ #{M ∈ P | M ⊆ T}`. Here `#{M ∈ P | M ⊆ T}` is the integer lift of `P` at the
indicator of `T` (`Cslib.BitString.monomialSum_indicator`). -/
@[expose] noncomputable def parityCoeff (ℓ : ℕ) (P : Finset (Finset ι)) (S : Finset ι) : ℤ[X] :=
  subsetMobius (fun T => parityFactor ℓ (#{M ∈ P | M ⊆ T} : ℤ)) S

/-- **The integer lift at an indicator** counts the monomials inside the set. -/
theorem monomialSum_indicator (R : Type*) [CommRing R] (P : Finset (Finset ι)) (T : Finset ι) :
    monomialSum R P (fun v => decide (v ∈ T)) = (#{M ∈ P | M ⊆ T} : R) := by
  rw [monomialSum_eq_card_filter]
  congr 2
  ext M
  simp only [mem_filter, decide_eq_true_eq, subset_iff]

/-- The `V ^ j` coefficient of the incidence coefficient is the subset Möbius transform of the
`V ^ j` coefficients. -/
theorem coeff_parityCoeff (ℓ : ℕ) (P : Finset (Finset ι)) (S : Finset ι) (j : ℕ) :
    (parityCoeff ℓ P S).coeff j =
      subsetMobius (fun T => (parityFactor ℓ (#{M ∈ P | M ⊆ T} : ℤ)).coeff j) S :=
  map_subsetMobius (lcoeff ℤ j).toAddMonoidHom _ S

/-- **The per-factor degree bound**: if every monomial of `P` has at most `k` variables, the
`V ^ j` coefficient of the incidence coefficient at `S` vanishes once `#S > k (1 + 2 j)`. This is
the bound on `B̄_i` stated just before (D.1) on p. 55. -/
theorem coeff_parityCoeff_eq_zero {ℓ k : ℕ} {P : Finset (Finset ι)} (hk : ∀ M ∈ P, #M ≤ k)
    {S : Finset ι} {j : ℕ} (hS : k * (1 + 2 * j) < #S) : (parityCoeff ℓ P S).coeff j = 0 := by
  rw [coeff_parityCoeff]
  have h := subsetMobius_eq_zero_of_mem_lowDegree (coeff_parityFactor_mem_lowDegree ℓ hk j) hS
  simpa only [monomialSum_indicator] using h

/-- The integer lift of an equation depends only on the variables of its scope. -/
theorem monomialSum_congr_of_eqOn {P : Finset (Finset ι)} {I : Finset ι}
    (hI : equationScope P ⊆ I) {x y : ι → Bool} (h : ∀ v ∈ I, x v = y v) :
    monomialSum ℤ P x = monomialSum ℤ P y := by
  simp only [monomialSum, monomial]
  refine sum_congr rfl fun M hM => prod_congr rfl fun v hv => ?_
  rw [h v (hI (mem_biUnion.mpr ⟨M, hM, hv⟩))]

variable [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The congruence (D.2)**: for scopes `I i` containing the variables of the equations `P i`
with monomials of at most `k` variables, `ℓ ≥ 1` and `K ≥ k (#κ + 2 (ℓ - 1))`, the number of
common zeros is congruent modulo `2 ^ ℓ` to the sum of the coefficients below `V ^ ℓ` of the
incidence sum of the incidence coefficients. -/
theorem commonZeroCount_modEq_sumCoeffsBelow_incidenceSum (P : κ → Finset (Finset ι))
    {I : κ → Finset ι} (hI : ∀ i, equationScope (P i) ⊆ I i) {k ℓ K : ℕ}
    (hk : ∀ i, ∀ M ∈ P i, #M ≤ k) (hℓ : 1 ≤ ℓ) (hK : k * (Fintype.card κ + 2 * (ℓ - 1)) ≤ K) :
    (commonZeroCount univ P : ℤ) ≡
      sumCoeffsBelow ℓ (incidenceSum I (fun i => parityCoeff ℓ (P i)) K) [ZMOD 2 ^ ℓ] := by
  have h52 := sum_sumCoeffsBelow_prod_parityFactor_modEq_commonZeroCount univ P hℓ
  rw [← sumCoeffsBelow_sum] at h52
  have hexp := sum_prod_eq_incidenceSum I (fun i x => parityFactor ℓ (monomialSum ℤ (P i) x))
    (fun i x y h => by rw [monomialSum_congr_of_eqOn (hI i) h]) (le_max_right K (∑ i, #(I i)))
  simp only [monomialSum_indicator] at hexp
  change _ = incidenceSum I (fun i => parityCoeff ℓ (P i)) _ at hexp
  have htrunc : sumCoeffsBelow ℓ
      (incidenceSum I (fun i => parityCoeff ℓ (P i)) (max K (∑ i, #(I i)))) =
      sumCoeffsBelow ℓ (incidenceSum I (fun i => parityCoeff ℓ (P i)) K) :=
    sum_congr rfl fun t ht => coeff_incidenceSum_eq_of_le I _
      (fun i S j hj => coeff_parityCoeff_eq_zero (hk i) hj) hK (le_max_left _ _) (mem_range.mp ht)
  rw [hexp, htrunc] at h52
  exact h52.symm

/-- **Exact recovery of the count.** For `n < ℓ` variables and integers `q j` congruent modulo
`2 ^ ℓ` to the coefficients below `V ^ ℓ` of the incidence sum, the sum of the `q j` modulo `2 ^ ℓ`
is the number of common zeros. -/
theorem emod_sum_eq_commonZeroCount_of_modEq (P : κ → Finset (Finset ι)) {I : κ → Finset ι}
    (hI : ∀ i, equationScope (P i) ⊆ I i) {k ℓ K : ℕ} (hk : ∀ i, ∀ M ∈ P i, #M ≤ k)
    (hℓ : Fintype.card ι < ℓ) (hK : k * (Fintype.card κ + 2 * (ℓ - 1)) ≤ K) (q : ℕ → ℤ)
    (hq : ∀ j < ℓ,
      q j ≡ (incidenceSum I (fun i => parityCoeff ℓ (P i)) K).coeff j [ZMOD 2 ^ ℓ]) :
    (∑ j ∈ range ℓ, q j) % 2 ^ ℓ = commonZeroCount univ P := by
  have hsum : (∑ j ∈ range ℓ, q j) ≡ (commonZeroCount univ P : ℤ) [ZMOD 2 ^ ℓ] :=
    (Int.ModEq.sum fun j hj => hq j (mem_range.mp hj)).trans
      (commonZeroCount_modEq_sumCoeffsBelow_incidenceSum P hI hk (by omega) hK).symm
  rw [hsum, Int.emod_eq_of_lt (Nat.cast_nonneg _)]
  have hle : (commonZeroCount univ P : ℤ) ≤ 2 ^ Fintype.card ι := by
    exact_mod_cast commonZeroCount_le_two_pow univ P
  have hlt : (2 : ℤ) ^ Fintype.card ι < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hℓ
  omega

end Cslib.BitString
