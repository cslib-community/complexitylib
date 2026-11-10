/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Data.Finset.Powerset

/-!
# Binomial coefficients of the number of true bits

The number of `r`-element sets of true positions is a sum of monomials: for `s` a finite set of
positions, `∑_{S ⊆ s, #S = r} ∏_{i ∈ S} x_i = C(#{i ∈ s | x_i}, r)`
(`Cslib.BitString.sum_powersetCard_monomial`). It is a function of degree at most `r`
(`Cslib.BitString.sum_powersetCard_monomial_mem_lowDegree`). Modulo a prime `p`, the case
`r = p ^ i` reads the `i`-th base-`p` digit of the number of true bits
(`Nat.pow_dvd_iff_forall_dvd_choose`), which is how `MOD_m` gates become polynomials of degree
below `m` [BeigelTarui1994, Lemma 2.1].

## Main results

* `Cslib.BitString.sum_powersetCard_monomial`: the sum of the `r`-element monomials is the binomial
  coefficient of the number of true bits.
* `Cslib.BitString.sum_powersetCard_monomial_mem_lowDegree`: it has degree at most `r`.

## References

* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Cslib.BitString

open Finset

variable {R : Type*} [CommRing R] {ι : Type*}

/-- **The `r`-element monomials count the `r`-element sets of true bits.** Over `s`, the sum of the
monomials of the `r`-element subsets of `s` is `C(#{i ∈ s | x i}, r)`. -/
theorem sum_powersetCard_monomial (s : Finset ι) (r : ℕ) (x : ι → Bool) :
    ∑ S ∈ s.powersetCard r, monomial R S x = ((#{i ∈ s | x i = true}).choose r : R) := by
  classical
  simp only [monomial_apply]
  rw [sum_boole, ← card_powersetCard]
  congr 2
  ext S
  simp only [mem_filter, mem_powersetCard, subset_iff]
  constructor
  · rintro ⟨⟨hs, hr⟩, hx⟩
    exact ⟨fun i hi => ⟨hs hi, hx i hi⟩, hr⟩
  · rintro ⟨hs, hr⟩
    exact ⟨⟨fun i hi => (hs hi).1, hr⟩, fun i hi => (hs hi).2⟩

/-- The sum of the `r`-element monomials over `s` has degree at most `r`. -/
theorem sum_powersetCard_monomial_mem_lowDegree (s : Finset ι) (r : ℕ) :
    (fun x => ∑ S ∈ s.powersetCard r, monomial R S x) ∈ lowDegree R ι r := by
  have h : (fun x => ∑ S ∈ s.powersetCard r, monomial R S x) =
      ∑ S ∈ s.powersetCard r, monomial R S := by
    funext x
    rw [Finset.sum_apply]
  rw [h]
  exact sum_mem_lowDegree _ fun S hS => monomial_mem_lowDegree (mem_powersetCard.1 hS).2.le

end Cslib.BitString
