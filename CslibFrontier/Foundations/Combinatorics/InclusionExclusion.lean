/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice

/-!
# Inclusion–exclusion for injective self-maps

On a finite type `V`, a self-map `w : V → V` is injective iff it is surjective
(`Finite.injective_iff_surjective`), that is, it misses no element of `V`. Applying the
inclusion–exclusion principle for an intersection of complements
(`Finset.inclusion_exclusion_sum_inf_compl`; see also [FominKratsch2010], Section 4.1, Theorem 4.2)
to the sets of maps missing each `v : V` expresses the count of injective self-maps satisfying any
decidable predicate `P : (V → V) → Prop` as an alternating sum over subsets `S ⊆ V` of the counts
of maps satisfying `P` with range in `S` (`Finset.card_filter_injective_eq_sum_powerset`).

## Main results

* `Finset.card_filter_injective_eq_sum_powerset`: inclusion–exclusion over `S ⊆ V` for injective
  self-maps `w : V → V` satisfying `P w`.

## References

* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 4.1,
  Theorem 4.2
-/

public section

namespace Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Inclusion–exclusion for injective self-maps.** On a finite type `V`, a map `w : V → V` is
injective iff it is surjective, i.e., misses no element of `V`. Filtering by any predicate `P` and
applying inclusion–exclusion over the sets of maps missing each `v : V` expresses the count of
injective maps satisfying `P` as an alternating sum over subsets `S ⊆ V` of the counts of maps
satisfying `P` with range in `S`. -/
theorem card_filter_injective_eq_sum_powerset (P : (V → V) → Prop) [DecidablePred P] :
    (#(univ.filter fun w : V → V => P w ∧ Function.Injective w) : ℤ) =
      ∑ S : Finset V, (-1 : ℤ) ^ (Fintype.card V - #S) *
        #(univ.filter fun w : V → V => P w ∧ ∀ i, w i ∈ S) := by
  let miss : V → Finset (V → V) := fun v => univ.filter fun w => ∀ i, w i ≠ v
  let f : (V → V) → ℤ := fun w => if P w then 1 else 0
  have hIE := Finset.inclusion_exclusion_sum_inf_compl (univ : Finset V) miss f
  have hLHS : ∑ w ∈ (univ : Finset V).inf (fun v => (miss v)ᶜ), f w =
      (#(univ.filter fun w : V → V => P w ∧ Function.Injective w) : ℤ) := by
    have hset : ((univ : Finset V).inf fun v => (miss v)ᶜ) =
        univ.filter (fun w : V → V => Function.Injective w) := by
      ext w
      simp only [Finset.mem_inf, Finset.mem_univ, forall_true_left, Finset.mem_compl,
        Finset.mem_filter, true_and, miss, not_forall, not_ne_iff]
      exact Finite.injective_iff_surjective.symm
    rw [hset, ← Finset.sum_filter]
    simp only [Finset.filter_filter, and_comm, Finset.sum_const, nsmul_one]
  have hRHS_term : ∀ T : Finset V, ∑ w ∈ T.inf miss, f w =
      (#(univ.filter fun w : V → V => P w ∧ ∀ i, w i ∈ Tᶜ) : ℤ) := by
    intro T
    have hset : T.inf miss = univ.filter (fun w : V → V => ∀ i, w i ∈ Tᶜ) := by
      ext w
      simp only [Finset.mem_inf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
        miss]
      exact ⟨fun h i hiT => h (w i) hiT i rfl, fun h v hvT i hwi => h i (hwi ▸ hvT)⟩
    rw [hset, ← Finset.sum_filter]
    simp only [Finset.filter_filter, and_comm, Finset.sum_const, nsmul_one]
  rw [hLHS] at hIE
  rw [hIE, Finset.powerset_univ]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hRHS_term]
  refine Finset.sum_bij (fun T _ => Tᶜ) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro T₁ _ T₂ _ h
    exact compl_involutive.injective h
  · intro S _
    exact ⟨Sᶜ, Finset.mem_univ _, compl_compl S⟩
  · intro T _
    have hcard : #T = Fintype.card V - #Tᶜ := by
      rw [Finset.card_compl, Nat.sub_sub_self (Finset.card_le_univ T)]
    rw [hcard]

end Finset
