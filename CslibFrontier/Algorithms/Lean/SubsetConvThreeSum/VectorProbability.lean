/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Probability
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorTrial
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The success probability of a base-`r` hashing trial

The error analysis of [ChanItakuraMaYu2026], Theorem 3.4, for a fixed prime `p`, as counts over
the uniform seeds `seeds p`, following the base-`2` analysis of
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Probability`.

Let `P` be the ordered pairs `(x, y)` of numbers below `r ^ d` whose digit vectors add up to a
balanced vector (`balancedPairs`). For a witness `c = a + b` with `a`, `b` isolated, a seed hashing
`a` to `x` and `b` to `y` with `(x, y) ∈ P` either accepts `c` or hashes the left element of a false
pair to a number whose digit vector is dominated by the balanced vector `π x + π y`
(`dominated`). A balanced vector `z` dominates at most `∏ j, (z j + 1) = (r !) ^ (d / r)` digit
vectors (`card_dominated_le`, `prod_add_one_of_balancedVec`), the paper's `(r!)^{d/r}` replacing
`(2t choose t)` of Theorem 2.3. Hence (`card_vaccepts_add_ge`)

`#P (p - 1) ≤ #accepting seeds + #P · #L · (r !) ^ (d / r)`,

and for a good prime, `4 #L (r !) ^ (d / r) ≤ p - 1`, a trial accepts `c` with probability at least
`(3/4) #P / p ^ 2` (`four_mul_card_vaccepts_ge`): inequality (2) as modified in the proof of
Theorem 3.4. The counting argument itself is shared with Theorem 2.3
(`card_mul_le_card_filter_add`).

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.balancedPairs`: the pairs `P`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.dominated`: numbers with dominated digit vectors.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_dominated_le`,
  `prod_add_one_of_balancedVec`: at most `(r !) ^ (d / r)` dominated numbers.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_vaccepts_add_ge`: the success count of one trial.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.four_mul_card_vaccepts_ge`: a good prime.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Nat

/-- The ordered pairs of numbers below `r ^ d` whose digit vectors add up to a balanced vector. -/
@[expose] def balancedPairs (r d : ℕ) : Finset (ℕ × ℕ) :=
  (range (r ^ d) ×ˢ range (r ^ d)).filter fun xy =>
    BalancedVec r (digitVec r d xy.1 + digitVec r d xy.2)

/-- The numbers below `r ^ d` whose digit vector is dominated by `z`. -/
@[expose] def dominated (r d : ℕ) (z : Fin d → ℕ) : Finset ℕ :=
  (range (r ^ d)).filter fun x => digitVec r d x ≤ z

/-- A vector `z` dominates at most `∏ j, (z j + 1)` digit vectors of numbers below `r ^ d`. -/
theorem card_dominated_le (r d : ℕ) (z : Fin d → ℕ) : #(dominated r d z) ≤ ∏ j, (z j + 1) := by
  have h : #(dominated r d z) ≤ #(Fintype.piFinset fun j => range (z j + 1)) := by
    refine card_le_card_of_injOn (digitVec r d) ?_ ?_
    · intro x hx
      have hle := (mem_filter.mp hx).2
      exact Fintype.mem_piFinset.mpr fun j => mem_range.mpr (Nat.lt_succ_of_le (hle j))
    · intro x hx y hy hxy
      rw [← digitVal_digitVec (mem_range.mp (mem_filter.mp hx).1),
        ← digitVal_digitVec (mem_range.mp (mem_filter.mp hy).1)]
      exact congrArg (digitVal r) hxy
  simpa [Fintype.card_piFinset] using h

/-- A balanced vector dominates `∏ j, (z j + 1) = (r !) ^ (d / r)` vectors. -/
theorem prod_add_one_of_balancedVec {r d : ℕ} {v : Fin d → ℕ} (hv : BalancedVec r v) :
    ∏ j, (v j + 1) = (r !) ^ (d / r) := by
  rw [← prod_fiberwise_of_maps_to (g := v) (t := range r) fun j _ => mem_range.mpr (hv.1 j),
    Nat.factorial_eq_prod_range_add_one, ← prod_pow]
  refine prod_congr rfl fun k hk => ?_
  rw [prod_congr rfl fun j hj => by rw [(mem_filter.mp hj).2], prod_const,
    hv.2 k (mem_range.mp hk)]

variable {p : ℕ} [Fact p.Prime]

/-- **The success count of one base-`r` trial** ([ChanItakuraMaYu2026], Theorem 3.4, the
modified inequalities (1) and (2)): if `c = a + b` with `a ∈ Ag ⊆ A` and `b ∈ Bg ⊆ B` isolated in
`A` and `B`, and `r ^ d ≤ p`, then
`#balancedPairs · (p - 1) ≤ #accepting seeds + #balancedPairs · #L · (r !) ^ (d / r)`. -/
theorem card_vaccepts_add_ge {r d : ℕ} (hp : r ^ d ≤ p) {A B Ag Bg : List ℕ}
    (hAg : ∀ x ∈ Ag, x ∈ A) (hBg : ∀ x ∈ Bg, x ∈ B) {a b c : ℕ} (ha : a ∈ Ag) (hb : b ∈ Bg)
    (hia : Isolated p A a) (hib : Isolated p B b) (habc : a + b = c) :
    #(balancedPairs r d) * (p - 1) ≤ #((seeds p).filter fun s => VAccepts r d s Ag Bg c) +
      #(balancedPairs r d) * (#(falsePairs p c Ag Bg) * (r !) ^ (d / r)) := by
  refine card_mul_le_card_filter_add hAg hBg ha hb hia hib habc _ (fun xy hxy => ?_)
    (fun xy => dominated r d (digitVec r d xy.1 + digitVec r d xy.2)) (fun xy hxy => ?_) ?_
  · obtain ⟨hmem, -⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hmem
    exact ⟨(mem_range.mp hx).trans_le hp, (mem_range.mp hy).trans_le hp⟩
  · rw [← prod_add_one_of_balancedVec (mem_filter.mp hxy).2]
    exact card_dominated_le r d _
  intro xy hxy s hseed hfa hgb hrej
  obtain ⟨hmem, hbal⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hmem
  have hξ := mem_seeds.mp hseed
  have hx' : s.left a < r ^ d := hfa ▸ mem_range.mp hx
  have hy' : s.right b < r ^ d := hgb ▸ mem_range.mp hy
  rw [← hfa, ← hgb] at hbal
  obtain hacc | ⟨a', ha', b', hb', hcov, hne⟩ :=
    vaccepts_or_exists_vcovers_ne hp ha hb habc hx' hy' hbal
  · exact absurd hacc hrej
  obtain ⟨hlt, hdig⟩ := add_lt_and_digitVec_add hx' hy' hbal.1
  have htarget := target_eq_add (s := s) habc (hlt.trans_le hp)
  have hcong := natCast_add_eq_of_vcovers hξ (htarget ▸ hlt) hcov
  refine ⟨(a', b'), ?_, ?_⟩
  · exact mem_filter.mpr ⟨mem_product.mpr ⟨List.mem_toFinset.mpr (List.mem_of_mem_filter ha'),
      List.mem_toFinset.mpr (List.mem_of_mem_filter hb')⟩, hcong, hne⟩
  · refine mem_filter.mpr ⟨mem_range.mpr hcov.1, fun j => ?_⟩
    have := congrFun hcov.2.2 j
    rw [htarget, hdig] at this
    rw [← hfa, ← hgb]
    simp only [Pi.add_apply] at this ⊢
    omega

/-- **A good prime** for a base-`r` trial: if moreover `4 #L (r !) ^ (d / r) ≤ p - 1`, a trial
accepts `c` with probability at least `(3/4) #P / p ^ 2`, that is,
`3 #balancedPairs (p - 1) ≤ 4 #accepting seeds`. -/
theorem four_mul_card_vaccepts_ge {r d : ℕ} (hp : r ^ d ≤ p) {A B Ag Bg : List ℕ}
    (hAg : ∀ x ∈ Ag, x ∈ A) (hBg : ∀ x ∈ Bg, x ∈ B) {a b c : ℕ} (ha : a ∈ Ag) (hb : b ∈ Bg)
    (hia : Isolated p A a) (hib : Isolated p B b) (habc : a + b = c)
    (hgood : 4 * (#(falsePairs p c Ag Bg) * (r !) ^ (d / r)) ≤ p - 1) :
    3 * (#(balancedPairs r d) * (p - 1)) ≤
      4 * #((seeds p).filter fun s => VAccepts r d s Ag Bg c) :=
  three_mul_le_four_mul_of_le_add (card_vaccepts_add_ge hp hAg hBg ha hb hia hib habc) hgood

end Cslib.Algorithms.Lean.SubsetConvThreeSum
