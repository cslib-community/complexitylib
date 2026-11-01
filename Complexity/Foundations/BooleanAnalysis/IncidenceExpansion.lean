/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Mobius
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Fintype.Pi
import Complexity.Foundations.Data.Polynomial.CoeffProd
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Expanding a product of local functions on the cube by incidences

Let every factor `g i` of a product of functions on the cube `ι → Bool` depend only on the
coordinates in a scope `I i`. Expand each factor in the monomials of its scope, with the subset
Möbius transform `c i = subsetMobius (T ↦ g i 1_T)` as coefficients. Summing the product over the
cube then gives a sum over the choices of one set `S i ⊆ I i` for every factor
(`Cslib.BitString.sum_prod_eq_incidenceSum`):
$$\sum_x \prod_i g_i(x) = \sum_{S_i \subseteq I_i} \Big(\prod_i c_i(S_i)\Big)
  \prod_v \begin{cases} 1 & v \in \bigcup_i S_i \\ 2 & \text{otherwise.} \end{cases}$$
The weight (`Cslib.BitString.incidenceWeight`) is the cube sum of the monomial of the union: a
coordinate in some `S i` must be `1`, and any other coordinate is free.

A choice `(S i)_i` is a set of incidences `(i, v)` with `v ∈ S i ⊆ I i`. The incidence sum
(`Cslib.BitString.incidenceSum`) adds only the choices with at most `K` incidences. This is the
monomial expansion of the incidence polynomial in the proof of Lemma D.2 of [OpenAI2026ETH]
(pp. 54–56). There, test `i` has incidence indeterminates `z_{iv}`, `v ∈ I_i`. The coefficient of
the monomial `z_{i,S}` in the multilinear factor `B̄_i` is the subset inversion
`∑_{T ⊆ S} (-1) ^ (|S| - |T|) B_i(1_T, V)`, which is `c i S`. The variable-group entry
`2 ^ |{v : b_v = 0}|` is a factor of the weight.

When the coefficients are polynomials whose `V ^ j` coefficient vanishes on sets of more than
`k (1 + 2 j)` elements, a product of `a` of them has a nonzero `V ^ t` coefficient only on choices
with at most `k (a + 2 t)` incidences (`Polynomial.coeff_prod_eq_zero_of_lt`). So below
`V ^ ℓ` the incidence sum does not change once `K ≥ k (a + 2 (ℓ - 1))`
(`Cslib.BitString.coeff_incidenceSum_eq_of_le`). This is the degree bound (D.1) on p. 55.

## Main definitions

* `Cslib.BitString.incidenceWeight`: `2` for each coordinate in no chosen set.
* `Cslib.BitString.incidenceSum`: the sum over the choices with at most `K` incidences.

## Main results

* `Cslib.BitString.sum_prod_eq_incidenceSum`: the cube sum of a product of local functions is
  the incidence sum of their subset Möbius transforms.
* `Cslib.BitString.map_incidenceSum`: ring homomorphisms commute with the incidence sum.
* `Cslib.BitString.coeff_incidenceTerm_eq_zero`: a choice with too many incidences has no low
  coefficient.
* `Cslib.BitString.coeff_incidenceSum_eq_of_le`: below `V ^ ℓ`, enough incidences are counted
  once `K ≥ k (a + 2 (ℓ - 1))`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], proof of Lemma D.2,
  pp. 54–56.
-/

public section

namespace Cslib.BitString

open Finset Polynomial

variable {ι κ R : Type*}

/-! ### The incidence sum -/

section Defs

variable [CommRing R] [Fintype ι] [Fintype κ]

/-- **The weight of a choice of incidences** `(S i)_i`: the product over the coordinates of `1`
for a coordinate in some `S i` and `2` for any other. It is the sum over the cube of the monomial
of `⋃ i, S i` (`Cslib.BitString.sum_ite_forall_eq_incidenceWeight`). -/
@[expose] def incidenceWeight [DecidableEq ι] (S : κ → Finset ι) : R :=
  ∏ v, if ∃ i, v ∈ S i then 1 else 2

/-- **The incidence sum** of coefficients `c i S` for scopes `I i`, up to `K` incidences: the sum
over the choices of `S i ⊆ I i` for every `i` with `∑ i, #(S i) ≤ K` of
`(∏ i, c i (S i)) * incidenceWeight S`. -/
@[expose] def incidenceSum [DecidableEq ι] [DecidableEq κ] (I : κ → Finset ι)
    (c : κ → Finset ι → R) (K : ℕ) : R :=
  ∑ S ∈ (Fintype.piFinset fun i => (I i).powerset) with ∑ i, #(S i) ≤ K,
    (∏ i, c i (S i)) * incidenceWeight S

variable [DecidableEq ι]

/-- A ring homomorphism fixes the weight of a choice of incidences. -/
theorem map_incidenceWeight {R' : Type*} [CommRing R'] (φ : R →+* R') (S : κ → Finset ι) :
    φ (incidenceWeight S) = incidenceWeight S := by
  simp only [incidenceWeight, map_prod]
  refine prod_congr rfl fun v _ => ?_
  split_ifs
  · exact map_one φ
  · exact map_ofNat φ 2

/-- **Ring homomorphisms commute with the incidence sum.** -/
theorem map_incidenceSum [DecidableEq κ] {R' : Type*} [CommRing R'] (φ : R →+* R')
    (I : κ → Finset ι) (c : κ → Finset ι → R) (K : ℕ) :
    φ (incidenceSum I c K) = incidenceSum I (fun i S => φ (c i S)) K := by
  simp only [incidenceSum, map_sum, map_mul, map_prod, map_incidenceWeight]

omit [Fintype ι] [DecidableEq ι] in
/-- A product of indicators is the indicator of the conjunction. -/
private theorem prod_ite_one_zero {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    [Decidable (∀ a, p a)] : (∏ a, if p a then (1 : R) else 0) = if ∀ a, p a then 1 else 0 := by
  by_cases h : ∀ a, p a
  · rw [ite_eq_left h]
    exact prod_eq_one fun a _ => ite_eq_left (h a)
  · rw [ite_eq_right h]
    obtain ⟨a, ha⟩ := not_forall.mp h
    exact prod_eq_zero (mem_univ a) (ite_eq_right ha)

/-- **The weight is a cube sum**: summing over the cube the indicator that every chosen set lies
in the support gives the weight of the choice. -/
theorem sum_ite_forall_eq_incidenceWeight (S : κ → Finset ι) :
    (∑ x : ι → Bool, if ∀ i, ∀ v ∈ S i, x v = true then (1 : R) else 0) =
      incidenceWeight S := by
  have hprod : ∀ x : ι → Bool, (if ∀ i, ∀ v ∈ S i, x v = true then (1 : R) else 0) =
      ∏ v, if (∃ i, v ∈ S i) → x v = true then 1 else 0 := by
    intro x
    rw [prod_ite_one_zero]
    refine if_congr ⟨fun h v hv => ?_, fun h i v hv => h v ⟨i, hv⟩⟩ rfl rfl
    obtain ⟨i, hi⟩ := hv
    exact h i v hi
  simp_rw [hprod]
  calc (∑ x : ι → Bool, ∏ v, if (∃ i, v ∈ S i) → x v = true then (1 : R) else 0)
      = ∏ v, ∑ b : Bool, if (∃ i, v ∈ S i) → b = true then (1 : R) else 0 :=
        (Fintype.prod_sum fun v (b : Bool) =>
          if (∃ i, v ∈ S i) → b = true then (1 : R) else 0).symm
    _ = incidenceWeight S := by
        refine prod_congr rfl fun v _ => ?_
        rw [Fintype.sum_bool]
        by_cases hv : ∃ i, v ∈ S i
        · simp only [hv, forall_const, Bool.false_eq_true, ↓reduceIte, add_zero]
        · simp only [hv, IsEmpty.forall_iff, ↓reduceIte]
          exact one_add_one_eq_two

end Defs

/-! ### The expansion -/

section Expansion

variable [CommRing R] [Fintype ι] [DecidableEq ι]

/-- **A local function in the monomials of its scope**: if `g` depends only on the coordinates in
`I`, then `g x` is the sum over the subsets `S ⊆ I` of the subset Möbius transform of
`T ↦ g 1_T` at `S`, times the monomial of `S` at `x`. -/
theorem eq_sum_subsetMobius_of_local {I : Finset ι} {g : (ι → Bool) → R}
    (hg : ∀ x y : ι → Bool, (∀ v ∈ I, x v = y v) → g x = g y) (x : ι → Bool) :
    g x = ∑ S ∈ I.powerset, subsetMobius (fun T => g fun v => decide (v ∈ T)) S *
      if ∀ v ∈ S, x v = true then 1 else 0 := by
  set W := I.filter fun v => x v = true
  have hgx : g x = g fun v => decide (v ∈ W) :=
    hg _ _ fun v hv => by simp only [W, mem_filter, hv, true_and, Bool.decide_eq_true]
  rw [hgx, ← sum_powerset_subsetMobius (fun T => g fun v => decide (v ∈ T)) W]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext S
  simp only [mem_powerset, mem_filter, W, subset_iff]
  exact ⟨fun h => ⟨fun v hv => (h hv).1, fun v hv => (h hv).2⟩,
    fun h v hv => ⟨h.1 hv, h.2 v hv⟩⟩

variable [Fintype κ] [DecidableEq κ]

/-- **The incidence expansion of a cube sum.** If every `g i` depends only on the coordinates in
`I i`, the sum over the cube of `∏ i, g i x` is the incidence sum of the subset Möbius transforms
`T ↦ g i 1_T`, for every `K` at least the total size of the scopes. -/
theorem sum_prod_eq_incidenceSum (I : κ → Finset ι) (g : κ → (ι → Bool) → R)
    (hg : ∀ i x y, (∀ v ∈ I i, x v = y v) → g i x = g i y) {K : ℕ}
    (hK : ∑ i, #(I i) ≤ K) :
    ∑ x : ι → Bool, ∏ i, g i x =
      incidenceSum I (fun i => subsetMobius fun T => g i fun v => decide (v ∈ T)) K := by
  set c : κ → Finset ι → R := fun i => subsetMobius fun T => g i fun v => decide (v ∈ T)
  have hfilter : ((Fintype.piFinset fun i => (I i).powerset).filter
      fun S => ∑ i, #(S i) ≤ K) = Fintype.piFinset fun i => (I i).powerset := by
    refine filter_true_of_mem fun S hS => ?_
    rw [Fintype.mem_piFinset] at hS
    exact (sum_le_sum fun i _ => card_le_card (mem_powerset.mp (hS i))).trans hK
  rw [incidenceSum, hfilter]
  calc ∑ x : ι → Bool, ∏ i, g i x
      = ∑ x : ι → Bool, ∏ i, ∑ S ∈ (I i).powerset,
          c i S * if ∀ v ∈ S, x v = true then 1 else 0 :=
        sum_congr rfl fun x _ => prod_congr rfl fun i _ => eq_sum_subsetMobius_of_local (hg i) x
    _ = ∑ x : ι → Bool, ∑ S ∈ Fintype.piFinset fun i => (I i).powerset,
          (∏ i, c i (S i)) * if ∀ i, ∀ v ∈ S i, x v = true then 1 else 0 := by
        refine sum_congr rfl fun x _ => ?_
        rw [prod_univ_sum]
        refine sum_congr rfl fun S _ => ?_
        rw [prod_mul_distrib, prod_ite_one_zero]
    _ = ∑ S ∈ Fintype.piFinset fun i => (I i).powerset, (∏ i, c i (S i)) * incidenceWeight S := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        rw [← mul_sum, sum_ite_forall_eq_incidenceWeight]

end Expansion

/-! ### Truncation below `V ^ ℓ` -/

section Truncation

variable {A : Type*} [CommRing A]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **A choice with too many incidences has no low coefficient.** If the `V ^ j` coefficient of
every `c i S` vanishes on sets of more than `k (1 + 2 j)` elements, then the term of a choice with
more than `k (#κ + 2 t)` incidences has zero `V ^ t` coefficient. -/
theorem coeff_incidenceTerm_eq_zero (c : κ → Finset ι → A[X]) {k t : ℕ}
    (hc : ∀ i S j, k * (1 + 2 * j) < #S → (c i S).coeff j = 0) {S : κ → Finset ι}
    (hS : k * (Fintype.card κ + 2 * t) < ∑ i, #(S i)) :
    ((∏ i, c i (S i)) * incidenceWeight S).coeff t = 0 := by
  have hC : (incidenceWeight S : A[X]) = C (incidenceWeight S) := (map_incidenceWeight C S).symm
  rw [hC, coeff_mul_C, coeff_prod_eq_zero_of_lt univ (fun i => c i (S i)) (fun i => #(S i)) k
    (fun i _ j hj => hc i (S i) j hj) (by rwa [card_univ]), zero_mul]

/-- **Truncating the incidence sum below `V ^ ℓ`.** If the `V ^ j` coefficient of every `c i S`
vanishes on sets of more than `k (1 + 2 j)` elements, then below `V ^ ℓ` the incidence sum up to
`K'` incidences equals that up to `K`, for `k (#κ + 2 (ℓ - 1)) ≤ K ≤ K'`. -/
theorem coeff_incidenceSum_eq_of_le (I : κ → Finset ι) (c : κ → Finset ι → A[X]) {k ℓ K K' : ℕ}
    (hc : ∀ i S j, k * (1 + 2 * j) < #S → (c i S).coeff j = 0)
    (hK : k * (Fintype.card κ + 2 * (ℓ - 1)) ≤ K) (hKK' : K ≤ K') {t : ℕ} (ht : t < ℓ) :
    (incidenceSum I c K').coeff t = (incidenceSum I c K).coeff t := by
  have hsplit := sum_filter_add_sum_filter_not
    ((Fintype.piFinset fun i => (I i).powerset).filter fun S => ∑ i, #(S i) ≤ K')
    (fun S => ∑ i, #(S i) ≤ K) (fun S => (∏ i, c i (S i)) * incidenceWeight S)
  rw [filter_filter, filter_congr (q := fun S => ∑ i, #(S i) ≤ K)
    fun S _ => ⟨fun h => h.2, fun h => ⟨h.trans hKK', h⟩⟩] at hsplit
  rw [incidenceSum, incidenceSum, ← hsplit, coeff_add, finsetSum_coeff, finsetSum_coeff,
    add_eq_left]
  refine sum_eq_zero fun S hS => coeff_incidenceTerm_eq_zero c hc ?_
  have hlt : K < ∑ i, #(S i) := Nat.lt_of_not_le (mem_filter.mp hS).2
  have hmono : k * (Fintype.card κ + 2 * t) ≤ k * (Fintype.card κ + 2 * (ℓ - 1)) :=
    Nat.mul_le_mul_left k (by omega)
  omega

end Truncation

end Cslib.BitString
