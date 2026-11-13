/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Thinning

/-!
# Regression examples for independent thinning

A parent uniformly supported on the two singleton subsets of `Bool` is a correlated,
nonempty probability law with spread parameter `1/2`. The exact boundary case
`t = q = 1/2`, `p = 1/3` exercises the domination theorem. Further examples exercise
the signed kernel and the universal `α = 1/2` corollary.
-/

namespace Cslib.Probability.Thinning

open Finset

private theorem sum_containment_delta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s j : Finset ι) (c : ℝ) :
    (∑ k : Finset ι, if s ⊆ k then (if k = j then c else 0) else 0) =
      if s ⊆ j then c else 0 := by
  rw [sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [hkj]
  · simp

/-- A genuinely correlated parent: choose exactly one of the two coordinates uniformly. -/
private noncomputable def singletonLaw (j : Finset Bool) : ℝ :=
  (if j = {false} then 1 / 2 else 0) + (if j = {true} then 1 / 2 else 0)

private theorem singletonLaw_nonneg (j : Finset Bool) : 0 ≤ singletonLaw j := by
  unfold singletonLaw
  split_ifs <;> norm_num

/-- The parent masses sum to one. In particular this is not just a subprobability example. -/
private theorem singletonLaw_sum : (∑ j : Finset Bool, singletonLaw j) = 1 := by
  norm_num [singletonLaw, sum_add_distrib]

private theorem singletonLaw_spread : IsSpread (1 / 2) singletonLaw := by
  intro s
  have he (k : Finset Bool) :
      (if s ⊆ k then singletonLaw k else 0) =
      (if s ⊆ k then (if k = {false} then (1 / 2 : ℝ) else 0) else 0) +
      (if s ⊆ k then (if k = {true} then (1 / 2 : ℝ) else 0) else 0) := by
    unfold singletonLaw
    split_ifs <;> ring
  simp_rw [he, sum_add_distrib, sum_containment_delta]
  by_cases hs : s = ∅
  · subst s
    norm_num
  · have hf : s ⊆ {false} ↔ s = {false} := by
      simp only [subset_singleton_iff, hs, false_or]
    have ht : s ⊆ {true} ↔ s = {true} := by
      simp only [subset_singleton_iff, hs, false_or]
    simp only [hf, ht]
    by_cases hsf : s = {false}
    · subst s
      norm_num
    · by_cases hst : s = {true}
      · subst s
        norm_num
      · simp only [hsf, hst, ite_false, zero_add]
        positivity

/-- The exact boundary case `t = q = 1/2`, `p = 1/3` has a nonempty correlated parent. -/
example {U : Set (Finset Bool)} (hU : IsUpperSet U) :
    (∑ j : Finset Bool, singletonLaw j * BitString.bernoulliAverage (1 / 2)
      (fun x => U.indicator (1 : Finset Bool → ℝ) (retain j x))) ≤
      BitString.bernoulliAverage (1 / 3) (fun w =>
        U.indicator (1 : Finset Bool → ℝ) (univ.filter fun i => w i)) :=
  thinning_le_bernoulli (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) singletonLaw singletonLaw_nonneg singletonLaw_spread hU

/-- The signed-kernel argument really includes negative entries. -/
public theorem signed_kernel_negative : coordinateKernel (3 / 4) (1 / 4) false true < 0 := by
  norm_num [coordinateKernel]

/-- The row normalization remains valid in that signed regime. -/
example (x : Bool) :
    (1 - (1 / 4 : ℝ)) * coordinateKernel (3 / 4) (1 / 4) x false +
      (1 / 4 : ℝ) * coordinateKernel (3 / 4) (1 / 4) x true = 1 :=
  coordinateKernel_average (by norm_num) (by norm_num) x

/-- The conjecture corollary applies at the universal constant `α = 1/2`, for every ground set
and every increasing event. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (μ : Finset ι → ℝ) (hμ : ∀ j, 0 ≤ μ j) (hs : IsSpread (p / 2) μ)
    {U : Set (Finset ι)} (hU : IsUpperSet U) :
    (∑ j : Finset ι, μ j * BitString.bernoulliAverage (1 / 2)
      (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x))) ≤
      BitString.bernoulliAverage p (fun w =>
        U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i)) := by
  apply thinning_le_bernoulli_of_alpha (by norm_num) (by norm_num) (by norm_num) hp hp' μ hμ
  · simpa only [one_div, inv_mul_eq_div] using hs
  · exact hU

/-- The mask law uses the two-coordinate product mass, including endpoint densities. -/
example (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (BitString.bernoulliPMF (ι := Fin 2) p hp hp' (fun _ => true)).toReal = p ^ 2 := by
  simp [BitString.bernoulliWeight, pow_two]

/-- The correlated parent as an actual PMF, rather than only real-valued weights. -/
private noncomputable def singletonPMF : PMF (Finset Bool) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (singletonLaw j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => singletonLaw_nonneg j),
      singletonLaw_sum, ENNReal.ofReal_one])

private theorem singletonPMF_mass (j : Finset Bool) : (singletonPMF j).toReal = singletonLaw j :=
  ENNReal.toReal_ofReal (singletonLaw_nonneg j)

/-- At the exact boundary, the joint law has the actual thinning/product marginals and puts
zero mass on a retained singleton paired with the empty target. -/
example : ∃ γ : PMF (Finset Bool × Finset Bool),
    γ.map Prod.fst = thin singletonPMF (1 / 2) (by norm_num) (by norm_num) ∧
    γ.map Prod.snd = bernoulliSet (1 / 3) (by norm_num) (by norm_num) ∧
    γ ({false}, ∅) = 0 := by
  obtain ⟨γ, hl, hr, hs⟩ := exists_thinning_coupling
    (t := 1 / 2) (p := 1 / 3) (q := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) singletonPMF (by
      simpa only [singletonPMF_mass] using singletonLaw_spread)
  refine ⟨γ, hl, hr, ?_⟩
  by_contra hn
  have hh := hs ({false}, ∅) hn
  simp at hh

/-- The exact-density endpoint on a correlated parent gives density `1/3`. -/
example : ∃ γ : PMF (Finset Bool × Finset Bool),
    γ.map Prod.fst = thin singletonPMF (1 / 2) (by norm_num) (by norm_num) ∧
    γ.map Prod.snd = bernoulliSet (1 / 3) (by norm_num) (by norm_num) ∧
    ∀ z ∈ γ.support, z.1 ⊆ z.2 := by
  obtain ⟨hp, hp', γ, hl, hr, hs⟩ := exists_thinning_coupling_explicit_density
    (t := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    singletonPMF (by simpa only [singletonPMF_mass] using singletonLaw_spread)
  refine ⟨γ, hl, ?_, hs⟩
  convert hr using 1
  norm_num

/-- A nonempty correlated parent also exercises Corollary 1.3 at `α = 3/5`, `p = 5/6`.
Here `α p = 1/2` and the golden-ratio inequality is strict. -/
example : ∃ γ : PMF (Finset Bool × Finset Bool),
    γ.map Prod.fst = thin singletonPMF (3 / 5) (by norm_num) (by norm_num) ∧
    γ.map Prod.snd = bernoulliSet (5 / 6) (by norm_num) (by norm_num) ∧
    ∀ z ∈ γ.support, z.1 ⊆ z.2 := by
  apply exists_thinning_coupling_of_alpha (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  convert singletonLaw_spread using 1
  · norm_num
  · funext j
    exact singletonPMF_mass j

/-- Empty ground sets and zero retention are included in the actual coupling theorem. -/
example : ∃ γ : PMF (Finset (Fin 0) × Finset (Fin 0)),
    γ.map Prod.fst = thin (PMF.pure ∅) 0 (by norm_num) (by norm_num) ∧
    γ.map Prod.snd = bernoulliSet (1 / 2) (by norm_num) (by norm_num) ∧
    ∀ z ∈ γ.support, z.1 ⊆ z.2 := by
  apply exists_thinning_coupling (q := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro s
  have hs : s = ∅ := Subsingleton.elim _ _
  subst s
  simp only [empty_subset, ite_true, card_empty, pow_zero, PMF.sum_toReal, le_refl]

end Cslib.Probability.Thinning
