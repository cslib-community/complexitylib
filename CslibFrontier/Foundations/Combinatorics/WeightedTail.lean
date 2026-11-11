/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weighted tails for independent coordinates

Draw a function `f : ∀ i, α i` uniformly, so that its coordinates are independent and uniform. The
coordinates where it hits a fixed set `C i ⊆ α i` form a set `{i | f i ∈ C i}`. Any property of
that set has probability at most the sum, over the sets `S` with the property, of the probability
of hitting at every coordinate of `S`. As a count (`card_filter_pi_le_sum_prod`):
`#{f | P {i | f i ∈ C i}} ≤ ∑_{S with P S} ∏_{i ∈ S} #(C i) ∏_{i ∉ S} #(α i)`.

If coordinate `i` carries weight `w i` and hits with probability at most `exp (-w i)`, then the
hits have total weight at least `T` with probability at most `2 ^ |ι| exp (-T)`
(`card_filter_le_sum_weight_le`). Every set `S` of weight at least `T` is hit everywhere with
probability at most `exp (-T)`, and there are at most `2 ^ |ι|` such sets. This is the crude union
bound over sets of coordinates. It loses the factor `2 ^ |ι|` that a Chernoff-type bound avoids,
but it needs no independence beyond the product structure and no bound on the weights.

## Main results

* `Cslib.card_filter_pi_le_sum_prod`: the hits satisfy `P` for at most
  `∑_{S with P S} ∏_{i ∈ S} #(C i) ∏_{i ∉ S} #(α i)` functions.
* `Cslib.card_filter_le_sum_weight_le`: the hits have weight at least `T` for at most a
  `2 ^ |ι| exp (-T)` fraction of the functions, when `#(C i) ≤ exp (-w i) #(α i)`.
-/

public section

namespace Cslib

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)]

/-- **Union bound over the sets of hit coordinates.** The functions `f : ∀ i, α i` whose hit set
`{i | f i ∈ C i}` has property `P` number at most the sum, over the sets `S` with property `P`, of
the number of functions hitting at every coordinate of `S`. -/
theorem card_filter_pi_le_sum_prod (C : ∀ i, Finset (α i)) (P : Finset ι → Prop)
    [DecidablePred P] :
    #{f : ∀ i, α i | P {i | f i ∈ C i}} ≤
      ∑ S with P S, (∏ i ∈ S, #(C i)) * ∏ i ∈ Sᶜ, Fintype.card (α i) := by
  classical
  calc #{f : ∀ i, α i | P {i | f i ∈ C i}}
      ≤ #(({S | P S} : Finset (Finset ι)).biUnion fun S =>
          Fintype.piFinset fun i => if i ∈ S then C i else univ) := by
        refine card_le_card fun f hf => ?_
        rw [mem_filter] at hf
        refine mem_biUnion.2 ⟨({i | f i ∈ C i} : Finset ι), mem_filter.2 ⟨mem_univ _, hf.2⟩, ?_⟩
        refine Fintype.mem_piFinset.2 fun i => ?_
        by_cases h : f i ∈ C i <;> simp [h]
    _ ≤ ∑ S with P S, #(Fintype.piFinset fun i => if i ∈ S then C i else univ) :=
        card_biUnion_le
    _ = ∑ S with P S, (∏ i ∈ S, #(C i)) * ∏ i ∈ Sᶜ, Fintype.card (α i) := by
        refine sum_congr rfl fun S _ => ?_
        rw [Fintype.card_piFinset, ← prod_mul_prod_compl S]
        congr 1
        · exact prod_congr rfl fun i hi => by simp [hi]
        · exact prod_congr rfl fun i hi => by simp [mem_compl.1 hi]

/-- **Weighted tail by a union bound.** If coordinate `i` hits `C i` with probability at most
`exp (-w i)`, then the coordinates hit by `f` have total weight at least `T` for at most a
`2 ^ |ι| exp (-T)` fraction of the functions `f`. -/
theorem card_filter_le_sum_weight_le (C : ∀ i, Finset (α i)) (w : ι → ℝ)
    (hC : ∀ i, (#(C i) : ℝ) ≤ Real.exp (-w i) * Fintype.card (α i)) (T : ℝ) :
    (#{f : ∀ i, α i | T ≤ ∑ i with f i ∈ C i, w i} : ℝ) ≤
      2 ^ Fintype.card ι * Real.exp (-T) * Fintype.card (∀ i, α i) := by
  classical
  have hterm (S : Finset ι) (hS : T ≤ ∑ i ∈ S, w i) :
      ((∏ i ∈ S, #(C i)) * ∏ i ∈ Sᶜ, Fintype.card (α i) : ℕ) ≤
        Real.exp (-T) * Fintype.card (∀ i, α i) := by
    push_cast
    calc (∏ i ∈ S, (#(C i) : ℝ)) * ∏ i ∈ Sᶜ, (Fintype.card (α i) : ℝ)
        ≤ (∏ i ∈ S, Real.exp (-w i) * Fintype.card (α i)) *
            ∏ i ∈ Sᶜ, (Fintype.card (α i) : ℝ) := by
          gcongr with i
          exact hC i
      _ = Real.exp (-∑ i ∈ S, w i) * ∏ i, (Fintype.card (α i) : ℝ) := by
          rw [prod_mul_distrib, mul_assoc, prod_mul_prod_compl, ← Real.exp_sum, sum_neg_distrib]
      _ ≤ Real.exp (-T) * Fintype.card (∀ i, α i) := by
          rw [Fintype.card_pi]
          push_cast
          gcongr
  calc (#{f : ∀ i, α i | T ≤ ∑ i with f i ∈ C i, w i} : ℝ)
      ≤ ∑ S with T ≤ ∑ i ∈ S, w i,
          ((∏ i ∈ S, #(C i)) * ∏ i ∈ Sᶜ, Fintype.card (α i) : ℕ) := by
        exact_mod_cast card_filter_pi_le_sum_prod C fun S => T ≤ ∑ i ∈ S, w i
    _ = ∑ S with T ≤ ∑ i ∈ S, w i,
          (((∏ i ∈ S, #(C i)) * ∏ i ∈ Sᶜ, Fintype.card (α i) : ℕ) : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ _S with T ≤ ∑ i ∈ _S, w i, Real.exp (-T) * Fintype.card (∀ i, α i) :=
        sum_le_sum fun S hS => hterm S (mem_filter.1 hS).2
    _ ≤ ∑ _S : Finset ι, Real.exp (-T) * Fintype.card (∀ i, α i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = 2 ^ Fintype.card ι * Real.exp (-T) * Fintype.card (∀ i, α i) := by
        rw [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul]
        push_cast
        ring

end Cslib
