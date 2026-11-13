/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.SubsetZeta

/-!
# Covering product and subset convolution

For `f g : Finset ι → R`, the **subset convolution** at `X` is `∑_{A ⊆ X} f A * g (X \ A)`, the
sum over the ordered partitions of `X` into two parts, and the **covering product** at `X` is the
sum of `f A * g B` over the pairs `A, B ⊆ X` with `A ∪ B = X`.

The zeta transform turns the covering product into the pointwise product
(`subsetZeta_coveringProduct`), so by Möbius inversion the covering product is the Möbius transform
of the pointwise product of the zeta transforms (`coveringProduct_eq_subsetMobius`); this is the
inclusion–exclusion identity of [BjorklundHusfeldtKaskiKoivisto2007], quoted as the identity before
the preprocessing algorithm in the proof of [ChanItakuraMaYu2026], Theorem 2.2. In the *ranked*
case, where `f` is supported on sets with `t₁` elements, `g` on sets with `t₂` elements and
`#X = t₁ + t₂`, every covering pair is a partition, so the two products agree at `X`
(`coveringProduct_eq_subsetConvolution`). That is the reduction of [ChanItakuraMaYu2026],
Problem 2.1, to covering products.

The algorithm computing selected entries is in `CslibFrontier.Algorithms.Lean.TrimmedYates`.

## Main definitions

* `Cslib.BitString.subsetConvolution`: the subset convolution.
* `Cslib.BitString.coveringProduct`: the covering product.

## Main results

* `Cslib.BitString.subsetZeta_coveringProduct`: the zeta transform of the covering product is the
  product of the zeta transforms.
* `Cslib.BitString.coveringProduct_eq_subsetMobius`: the inclusion–exclusion formula for the
  covering product.
* `Cslib.BitString.coveringProduct_eq_subsetConvolution`: ranked inputs.

## References

* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Fourier meets Möbius: fast subset
  convolution*][BjorklundHusfeldtKaskiKoivisto2007]
* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

open Finset

namespace Cslib.BitString

variable {ι R : Type*} [DecidableEq ι]

section Semiring

variable [CommSemiring R]

/-- The **subset convolution**: the value at `X` is `∑_{A ⊆ X} f A * g (X \ A)`. -/
@[expose] def subsetConvolution (f g : Finset ι → R) (X : Finset ι) : R :=
  ∑ A ∈ X.powerset, f A * g (X \ A)

/-- The **covering product**: the value at `X` is the sum of `f A * g B` over the pairs of subsets
`A, B ⊆ X` with `A ∪ B = X`. -/
@[expose] def coveringProduct (f g : Finset ι → R) (X : Finset ι) : R :=
  ∑ A ∈ X.powerset, ∑ B ∈ X.powerset, if A ∪ B = X then f A * g B else 0

/-- The covering product at `U ⊆ S` sums over the pairs of subsets of `S` whose union is `U`. -/
theorem coveringProduct_eq_sum_of_subset (f g : Finset ι → R) {U S : Finset ι} (hU : U ⊆ S) :
    coveringProduct f g U =
      ∑ A ∈ S.powerset, ∑ B ∈ S.powerset, if A ∪ B = U then f A * g B else 0 := by
  have hpow : U.powerset ⊆ S.powerset := powerset_mono.mpr hU
  rw [coveringProduct]
  refine (sum_subset hpow fun A _ hA => sum_eq_zero fun B _ => ite_eq_right ?_).trans
    (sum_congr rfl fun A _ => sum_subset hpow fun B _ hB => ite_eq_right ?_)
  · exact fun h => hA (mem_powerset.mpr (h ▸ subset_union_left))
  · exact fun h => hB (mem_powerset.mpr (h ▸ subset_union_right))

/-- **The zeta transform turns the covering product into the pointwise product.** -/
theorem subsetZeta_coveringProduct (f g : Finset ι → R) (S : Finset ι) :
    subsetZeta (coveringProduct f g) S = subsetZeta f S * subsetZeta g S := by
  rw [subsetZeta, subsetZeta, subsetZeta, sum_mul_sum,
    sum_congr rfl fun U hU => coveringProduct_eq_sum_of_subset f g (mem_powerset.mp hU)]
  rw [sum_comm]
  refine sum_congr rfl fun A hA => ?_
  rw [sum_comm, sum_congr rfl fun B hB => sum_ite_eq S.powerset (A ∪ B) fun _ => f A * g B]
  refine sum_congr rfl fun B hB => ite_eq_left ?_
  exact mem_powerset.mpr (union_subset (mem_powerset.mp hA) (mem_powerset.mp hB))

end Semiring

section Ring

variable [CommRing R]

/-- **Inclusion–exclusion for the covering product** ([BjorklundHusfeldtKaskiKoivisto2007]): the
covering product is the Möbius transform of the pointwise product of the zeta transforms,
`(f *_c g) X = ∑_{S ⊆ X} (-1) ^ #(X \ S) * f̂ S * ĝ S`. -/
theorem coveringProduct_eq_subsetMobius (f g : Finset ι → R) :
    coveringProduct f g = subsetMobius fun S => subsetZeta f S * subsetZeta g S := by
  rw [← subsetMobius_subsetZeta (coveringProduct f g)]
  congr 1
  funext S
  exact subsetZeta_coveringProduct f g S

end Ring

section Ranked

variable [CommSemiring R]

/-- **Ranked inputs.** If `f` is supported on sets with `t₁` elements, `g` on sets with `t₂`
elements and `#X = t₁ + t₂`, then the covering product at `X` is the subset convolution at `X`:
a cover of `X` by a `t₁`-set and a `t₂`-set is a partition. -/
theorem coveringProduct_eq_subsetConvolution {f g : Finset ι → R} {t₁ t₂ : ℕ}
    (hf : ∀ A, f A ≠ 0 → #A = t₁) (hg : ∀ B, g B ≠ 0 → #B = t₂) {X : Finset ι}
    (hX : #X = t₁ + t₂) : coveringProduct f g X = subsetConvolution f g X := by
  rw [coveringProduct, subsetConvolution]
  refine sum_congr rfl fun A hA => ?_
  have hAX : A ⊆ X := mem_powerset.mp hA
  refine (sum_eq_single (X \ A) (fun B hB hne => ?_) fun h =>
    absurd (mem_powerset.mpr sdiff_subset) h).trans (ite_eq_left (union_sdiff_of_subset hAX))
  split_ifs with hU
  · by_cases hfA : f A = 0
    · rw [hfA, zero_mul]
    by_cases hgB : g B = 0
    · rw [hgB, mul_zero]
    refine absurd ?_ hne
    have hcard := card_union_add_card_inter A B
    rw [hU, hX, hf A hfA, hg B hgB] at hcard
    have hdisj : Disjoint A B := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
    rw [← hU, union_sdiff_cancel_left hdisj]
  · rfl

end Ranked

end Cslib.BitString
