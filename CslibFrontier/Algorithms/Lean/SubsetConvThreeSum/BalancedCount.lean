/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorProbability
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Int.CardIntervalMod

/-!
# Counting balanced pairs

The exact number of pairs in the success analysis of the base-`r` trial
([ChanItakuraMaYu2026], proof of Theorem 3.4, p. 13): the pairs `(x, y)` of numbers below `r ^ d`
whose digit vectors add up to a balanced vector (`balancedPairs`).

* A digit vector `z` with digits below `r` dominates exactly `∏ j, (z j + 1)` digit vectors of
  numbers below `r ^ d` (`card_dominated`); for a balanced `z` this is `(r !) ^ (d / r)`.
* Fibring the pairs by the sum of their digit vectors, `#balancedPairs` is the number of balanced
  vectors times `(r !) ^ (d / r)` (`card_balancedPairs_eq`).
* **The balanced vectors** (`balancedVecs`): for `0 < r` and `r ∣ d`, their number times
  `((d / r)!) ^ r` is `d !` (`card_balancedVecs_mul`), i.e. the multinomial coefficient
  `d! / ((d/r)!)^r` of the paper. The permutations of the `d` positions act transitively on
  balanced vectors (`Equiv.ofFiberEquiv` matches the fibres of two balanced vectors), and the
  stabilizer of one of them has `((d / r)!) ^ r` elements (`DomMulAct.stabilizer_card`).
* Hence `#balancedPairs · ((d / r)!) ^ r = d! (r!) ^ (d / r)` (`card_balancedPairs_mul`) and
  `#balancedPairs = d! / ((d/r)!)^r · (r!)^(d/r)` (`card_balancedPairs`). If `r ∤ d` there are
  no balanced vectors (`balancedVecs_eq_empty`).

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.balancedVecs`: the balanced digit vectors.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_dominated`,
  `card_balancedPairs_eq`, `card_balancedVecs_mul`, `card_balancedPairs_mul`,
  `card_balancedPairs`, `balancedVecs_eq_empty`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Nat

/-! ### Dominated vectors -/

/-- A vector `z` with digits below `r` dominates exactly `∏ j, (z j + 1)` digit vectors of numbers
below `r ^ d`. -/
theorem card_dominated {r d : ℕ} {z : Fin d → ℕ} (hz : ∀ j, z j < r) :
    #(dominated r d z) = ∏ j, (z j + 1) := by
  have h : #(dominated r d z) = #(Fintype.piFinset fun j => range (z j + 1)) := by
    refine card_bij (fun x _ => digitVec r d x) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
      (fun v hv => ?_)
    · have hle := (mem_filter.mp hx).2
      exact Fintype.mem_piFinset.mpr fun j => mem_range.mpr (Nat.lt_succ_of_le (hle j))
    · rw [← digitVal_digitVec (mem_range.mp (mem_filter.mp hx).1),
        ← digitVal_digitVec (mem_range.mp (mem_filter.mp hy).1), hxy]
    · have hv' : ∀ j, v j ≤ z j := fun j =>
        Nat.lt_succ_iff.mp (mem_range.mp (Fintype.mem_piFinset.mp hv j))
      obtain ⟨hlt, hdig⟩ := digitVal_lt_and_digitVec (r := r) (v := v)
        fun j => (hv' j).trans_lt (hz j)
      exact ⟨digitVal r v, mem_filter.mpr ⟨mem_range.mpr hlt, by rw [hdig]; exact hv'⟩, hdig⟩
  simpa [Fintype.card_piFinset] using h

/-! ### Balanced pairs by the sum of their digit vectors -/

/-- The balanced digit vectors of length `d`. -/
@[expose] def balancedVecs (r d : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ => range r).filter fun v => BalancedVec r v

theorem mem_balancedVecs {r d : ℕ} {v : Fin d → ℕ} : v ∈ balancedVecs r d ↔ BalancedVec r v := by
  simp only [balancedVecs, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  exact fun h => h.1

/-- The pairs whose digit vectors add up to a balanced `z` correspond to the numbers whose digit
vector `z` dominates. -/
private theorem card_fiber_balancedPairs {r d : ℕ} {z : Fin d → ℕ} (hz : BalancedVec r z) :
    #((balancedPairs r d).filter fun xy => digitVec r d xy.1 + digitVec r d xy.2 = z) =
      #(dominated r d z) := by
  refine card_bij' (fun xy _ => xy.1) (fun x _ => (x, digitVal r (z - digitVec r d x)))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hmem, hsum⟩ := mem_filter.mp hxy
    obtain ⟨hpr, -⟩ := mem_filter.mp hmem
    refine mem_filter.mpr ⟨(mem_product.mp hpr).1, fun j => ?_⟩
    rw [← hsum]
    exact Nat.le_add_right _ _
  · intro x hx
    obtain ⟨hxr, hle⟩ := mem_filter.mp hx
    have hlt : ∀ j, (z - digitVec r d x) j < r := fun j =>
      (Nat.sub_le _ _).trans_lt (hz.1 j)
    obtain ⟨hylt, hydig⟩ := digitVal_lt_and_digitVec hlt
    have hsum : digitVec r d x + digitVec r d (digitVal r (z - digitVec r d x)) = z := by
      rw [hydig]
      funext j
      have h1 : digitVec r d x j ≤ z j := hle j
      simp only [Pi.add_apply, Pi.sub_apply]
      omega
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hxr, mem_range.mpr hylt⟩, ?_⟩, hsum⟩
    rw [hsum]
    exact hz
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hmem, hsum⟩ := mem_filter.mp hxy
    obtain ⟨hpr, -⟩ := mem_filter.mp hmem
    have hy := mem_range.mp (mem_product.mp hpr).2
    have : z - digitVec r d x = digitVec r d y := by
      rw [← hsum]
      funext j
      simp
    simp only [this, digitVal_digitVec hy]
  · intro x _
    rfl

/-- **Balanced pairs by their sum**: `#balancedPairs` is the number of balanced vectors times
`(r !) ^ (d / r)`. -/
theorem card_balancedPairs_eq (r d : ℕ) :
    #(balancedPairs r d) = #(balancedVecs r d) * (r !) ^ (d / r) := by
  rw [card_eq_sum_card_fiberwise (f := fun xy : ℕ × ℕ => digitVec r d xy.1 + digitVec r d xy.2)
    (s := balancedPairs r d) (t := balancedVecs r d) fun xy hxy => mem_balancedVecs.mpr (by
      unfold balancedPairs at hxy; exact (mem_filter.mp hxy).2)]
  rw [sum_congr rfl fun z hz => by
    rw [card_fiber_balancedPairs (mem_balancedVecs.mp hz),
      card_dominated (mem_balancedVecs.mp hz).1,
      prod_add_one_of_balancedVec (mem_balancedVecs.mp hz)], sum_const, smul_eq_mul]

/-! ### Balanced vectors -/

/-- The digit vectors with values in `Fin r` in which every value occurs `d / r` times. -/
private abbrev finBalanced (r d : ℕ) : Finset (Fin d → Fin r) :=
  univ.filter fun v => ∀ k, #(univ.filter fun j => v j = k) = d / r

private theorem card_balancedVecs_eq_finBalanced {r d : ℕ} :
    #(balancedVecs r d) = #(finBalanced r d) := by
  symm
  refine card_bij (fun v _ => fun j => (v j : ℕ)) (fun v hv => ?_) (fun v _ w _ h => ?_)
    (fun u hu => ?_)
  · refine mem_balancedVecs.mpr ⟨fun j => (v j).is_lt, fun k hk => ?_⟩
    have := (mem_filter.mp hv).2 ⟨k, hk⟩
    rw [← this]
    congr 1
  · funext j; exact Fin.ext (congrFun h j)
  · have hu' := mem_balancedVecs.mp hu
    refine ⟨fun j => ⟨u j, hu'.1 j⟩, mem_filter.mpr ⟨mem_univ _, fun k => ?_⟩, rfl⟩
    refine (?_ : _ = #(univ.filter fun j => u j = k)).trans (hu'.2 k k.is_lt)
    congr 1

/-- The vector `j ↦ j mod r` is balanced when `r ∣ d`. -/
private theorem mod_mem_finBalanced {r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    (fun j : Fin d => (⟨j % r, Nat.mod_lt _ hr⟩ : Fin r)) ∈ finBalanced r d := by
  refine mem_filter.mpr ⟨mem_univ _, fun k => ?_⟩
  have hcount := Nat.count_modEq_card (b := d) (r := r) hr k
  rw [Nat.mod_eq_zero_of_dvd hrd] at hcount
  simp only [Nat.not_lt_zero, ite_false, add_zero] at hcount
  rw [← hcount, Nat.count_eq_card_filter_range, card_filter, card_filter,
    ← Fin.sum_univ_eq_sum_range (fun j => if j ≡ (k : ℕ) [MOD r] then 1 else 0) d]
  refine sum_congr rfl fun j _ => ?_
  have : ((⟨j % r, Nat.mod_lt _ hr⟩ : Fin r) = k) ↔ (j : ℕ) ≡ (k : ℕ) [MOD r] := by
    rw [Fin.ext_iff, Nat.ModEq, Nat.mod_eq_of_lt k.is_lt]
  simp only [this]

/-- **The number of balanced vectors** (the multinomial coefficient `d! / ((d/r)!)^r` of
[ChanItakuraMaYu2026], p. 13): for `0 < r` and `r ∣ d`,
`#balancedVecs r d · ((d / r)!) ^ r = d !`. -/
theorem card_balancedVecs_mul {r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    #(balancedVecs r d) * ((d / r)!) ^ r = d ! := by
  classical
  rw [card_balancedVecs_eq_finBalanced]
  set v₀ : Fin d → Fin r := fun j => ⟨j % r, Nat.mod_lt _ hr⟩
  have hv₀ := mod_mem_finBalanced hr hrd
  -- every balanced vector is `v₀ ∘ σ` for a permutation `σ`
  have hfib : ∀ v ∈ finBalanced r d, ∃ σ : Equiv.Perm (Fin d), v₀ ∘ σ = v := by
    intro v hv
    have e : ∀ k, {a // v a = k} ≃ {b // v₀ b = k} := fun k =>
      Fintype.equivOfCardEq (by
        rw [Fintype.card_subtype, Fintype.card_subtype, (mem_filter.mp hv).2 k,
          (mem_filter.mp hv₀).2 k])
    exact ⟨Equiv.ofFiberEquiv e, funext fun a => Equiv.ofFiberEquiv_map e a⟩
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin d))), v₀ ∘ σ ∈ finBalanced r d := by
    intro σ _
    refine mem_filter.mpr ⟨mem_univ _, fun k => ?_⟩
    rw [← (mem_filter.mp hv₀).2 k]
    refine card_bij (fun j _ => σ j) (fun j hj => ?_) (fun _ _ _ _ h => σ.injective h)
      (fun j hj => ⟨σ.symm j, ?_, by simp⟩)
    · simpa using hj
    · simpa using hj
  -- the stabilizer of `v₀`
  have hstab : #((univ : Finset (Equiv.Perm (Fin d))).filter
      fun g : Equiv.Perm (Fin d) => v₀ ∘ ⇑g = v₀) =
      ((d / r)!) ^ r := by
    rw [← Fintype.card_subtype, DomMulAct.stabilizer_card]
    rw [prod_congr rfl fun k _ => by
      rw [Fintype.card_subtype, (mem_filter.mp hv₀).2 k], prod_const, Finset.card_univ,
      Fintype.card_fin]
  -- each fibre of `σ ↦ v₀ ∘ σ` is a coset of the stabilizer
  have hcoset : ∀ v ∈ finBalanced r d,
      #((univ : Finset (Equiv.Perm (Fin d))).filter
        fun σ : Equiv.Perm (Fin d) => v₀ ∘ ⇑σ = v) = ((d / r)!) ^ r := by
    intro v hv
    obtain ⟨τ, hτ⟩ := hfib v hv
    rw [← hstab]
    refine card_bij' (fun σ _ => τ.symm.trans σ) (fun g _ => τ.trans g) ?_ ?_ ?_ ?_
    · intro σ hσ
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      have h := (mem_filter.mp hσ).2
      funext a
      have := congrFun h (τ.symm a)
      have h2 := congrFun hτ (τ.symm a)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this h2
      simp only [Function.comp_apply, Equiv.coe_trans]
      rw [this, ← h2]
    · intro g hg
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      have h := (mem_filter.mp hg).2
      funext a
      have := congrFun h (τ a)
      simp only [Function.comp_apply, Equiv.coe_trans] at this ⊢
      rw [this, ← hτ]
      rfl
    · intro σ _; ext a; simp
    · intro g _; ext a; simp
  have htotal := card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin d) => v₀ ∘ σ)
    (s := univ) (t := finBalanced r d) hmaps
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, sum_congr rfl hcoset, sum_const,
    smul_eq_mul] at htotal
  exact htotal.symm

/-- **The number of balanced pairs**: for `0 < r` and `r ∣ d`,
`#balancedPairs r d · ((d / r)!) ^ r = d ! (r !) ^ (d / r)`. -/
theorem card_balancedPairs_mul {r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    #(balancedPairs r d) * ((d / r)!) ^ r = d ! * (r !) ^ (d / r) := by
  rw [card_balancedPairs_eq, mul_right_comm, card_balancedVecs_mul hr hrd]

/-- **The number of balanced pairs**, as in [ChanItakuraMaYu2026], p. 13:
`#balancedPairs r d = d! / ((d/r)!)^r · (r!)^(d/r)` for `0 < r` and `r ∣ d`. -/
theorem card_balancedPairs {r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    #(balancedPairs r d) = d ! / ((d / r)!) ^ r * (r !) ^ (d / r) := by
  rw [card_balancedPairs_eq, ← card_balancedVecs_mul hr hrd,
    Nat.mul_div_cancel _ (pow_pos (Nat.factorial_pos _) _)]

/-- Without `r ∣ d` there are no balanced vectors. -/
theorem balancedVecs_eq_empty {r d : ℕ} (hrd : ¬ r ∣ d) : balancedVecs r d = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => hrd ?_
  have hb := mem_balancedVecs.mp hv
  have hsum : ∑ k ∈ range r, #(univ.filter fun j => v j = k) = d := by
    have := card_eq_sum_card_fiberwise (f := v) (s := univ) (t := range r)
      fun j _ => mem_range.mpr (hb.1 j)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  rw [sum_congr rfl fun k hk => hb.2 k (mem_range.mp hk), sum_const, card_range,
    smul_eq_mul] at hsum
  exact ⟨d / r, hsum.symm⟩

end Cslib.Algorithms.Lean.SubsetConvThreeSum
