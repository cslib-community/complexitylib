/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Linarith

/-!
# Method of conditional expectations on finite product spaces

For an independent product distribution `PMF.pi p` on `∀ i : ι, α i`, fixing the coordinates in
`fixed : Finset ι` to the values of `x` and drawing the remaining coordinates independently from
`p` gives the product law `fixedPi p fixed x`. When `x` is supported on `fixed`, this coincides
with conditioning `PMF.pi p` on the cylinder event `{y | ∀ i ∈ fixed, y i = x i}`
(`filter_pi_cylinder`).

The conditional expectation `condExpect p f fixed x` of `f : (∀ i, α i) → ℝ` satisfies:
* `condExpect_empty`: at `fixed = ∅`, it equals the full expectation `∑ y, (pi p y).toReal * f y`;
* `condExpect_univ`: at `fixed = Finset.univ`, it equals `f x`;
* `sum_mul_condExpect_insert`: for any free coordinate `i ∉ fixed`, the `p i`-weighted average of
  `condExpect p f (insert i fixed) (Function.update x i a)` equals `condExpect p f fixed x`.

Consequently, every free coordinate admits a supported value not increasing `condExpect`
(`exists_condExpect_insert_le`) and a supported value not decreasing it
(`exists_le_condExpect_insert`).

## Main definitions

* `Cslib.Probability.PMF.fixedPi`: product law with `fixed` coordinates pinned to `x`.
* `Cslib.Probability.PMF.condExpect`: conditional expectation of `f` given `fixed` pinned to `x`.

## Main results

* `Cslib.Probability.PMF.condExpect_empty`, `Cslib.Probability.PMF.condExpect_univ`: boundary
  values at no fixed coordinates and all coordinates fixed.
* `Cslib.Probability.PMF.filter_pi_cylinder`: agreement with `PMF.filter` on positive-mass
  cylinder events.
* `Cslib.Probability.PMF.sum_mul_condExpect_insert`: coordinate-averaging / tower law for
  `i ∉ fixed`.
* `Cslib.Probability.PMF.exists_condExpect_insert_le`,
  `Cslib.Probability.PMF.exists_le_condExpect_insert`: existence of minimizing and maximizing
  coordinate choices in `(p i).support`.
* `Cslib.Probability.PMF.condExpect_uniform_bool_add`: two-branch sum identity on the uniform
  Boolean cube.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Chapter 16][AlonSpencer2016]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*,
  Section 5.2][WilliamsonShmoys2011]
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.Probability.PMF

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- Product distribution where coordinates in `fixed` are pinned to `x` and coordinates outside
`fixed` are drawn independently from `p`. -/
@[expose] noncomputable def fixedPi (p : ∀ i, PMF (α i)) (fixed : Finset ι) (x : ∀ i, α i) :
    PMF (∀ i, α i) :=
  pi fun j => if j ∈ fixed then PMF.pure (x j) else p j

/-- Conditional expectation of `f` under `PMF.pi p` given that coordinates in `fixed` take the
values `x i`. -/
@[expose] noncomputable def condExpect (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    (fixed : Finset ι) (x : ∀ i, α i) : ℝ :=
  ∑ y, (fixedPi p fixed x y).toReal * f y

@[simp]
theorem fixedPi_empty (p : ∀ i, PMF (α i)) (x : ∀ i, α i) :
    fixedPi p ∅ x = pi p := by
  simp [fixedPi]

@[simp]
theorem condExpect_empty (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ) (x : ∀ i, α i) :
    condExpect p f ∅ x = ∑ y, (pi p y).toReal * f y := by
  simp [condExpect]

@[simp]
theorem fixedPi_univ (p : ∀ i, PMF (α i)) (x : ∀ i, α i) :
    fixedPi p Finset.univ x = PMF.pure x := by
  ext y
  rw [fixedPi, pi_apply, PMF.pure_apply]
  by_cases hy : y = x
  · subst hy
    simp
  · rw [ite_eq_right hy]
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ x j := by
      simpa only [funext_iff, not_forall] using hy
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

@[simp]
theorem condExpect_univ (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ) (x : ∀ i, α i) :
    condExpect p f Finset.univ x = f x := by
  rw [condExpect, fixedPi_univ, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ x))

theorem fixedPi_congr (p : ∀ i, PMF (α i)) (fixed : Finset ι) {x x' : ∀ i, α i}
    (hx : ∀ i ∈ fixed, x i = x' i) :
    fixedPi p fixed x = fixedPi p fixed x' := by
  unfold fixedPi
  congr 1
  funext j
  by_cases hj : j ∈ fixed
  · simp [hj, hx j hj]
  · simp [hj]

theorem condExpect_congr (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ) (fixed : Finset ι)
    {x x' : ∀ i, α i} (hx : ∀ i ∈ fixed, x i = x' i) :
    condExpect p f fixed x = condExpect p f fixed x' := by
  rw [condExpect, condExpect, fixedPi_congr p fixed hx]

/-- When `x` has positive probability on every coordinate in `fixed`, conditioning `pi p` on the
cylinder `{y | ∀ i ∈ fixed, y i = x i}` yields `fixedPi p fixed x`. -/
theorem filter_pi_cylinder (p : ∀ i, PMF (α i)) (fixed : Finset ι) (x : ∀ i, α i)
    (hx : ∀ i ∈ fixed, x i ∈ (p i).support)
    (hsupp : ∃ y ∈ {y : ∀ i, α i | ∀ i ∈ fixed, y i = x i}, y ∈ (pi p).support) :
    (pi p).filter {y | ∀ i ∈ fixed, y i = x i} hsupp = fixedPi p fixed x := by
  classical
  set c : ℝ≥0∞ := ∏ i ∈ fixed, p i (x i)
  have hc0 : c ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (PMF.mem_support_iff _ _).mp (hx i hi)
  have hctop : c ≠ ⊤ := ENNReal.prod_ne_top fun i _ => PMF.apply_ne_top _ _
  have hpt : ∀ z : ∀ i, α i,
      Set.indicator {w : ∀ i, α i | ∀ i ∈ fixed, w i = x i} (pi p) z =
        c * fixedPi p fixed x z := by
    intro z
    by_cases hz : ∀ i ∈ fixed, z i = x i
    · rw [Set.indicator_of_mem hz, fixedPi, pi_apply, pi_apply,
        ← Finset.prod_sdiff (Finset.subset_univ fixed),
        ← Finset.prod_sdiff (s₁ := fixed) (Finset.subset_univ fixed)]
      have hfix1 : ∏ i ∈ fixed, p i (z i) = c :=
        Finset.prod_congr rfl fun i hi => by rw [hz i hi]
      have hfix2 : ∏ i ∈ fixed, (if i ∈ fixed then PMF.pure (x i) else p i) (z i) = 1 :=
        Finset.prod_eq_one fun i hi => by simp [hi, hz i hi]
      have hfree : ∏ i ∈ Finset.univ \ fixed,
          (if i ∈ fixed then PMF.pure (x i) else p i) (z i) =
          ∏ i ∈ Finset.univ \ fixed, p i (z i) :=
        Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.mp hi).2]
      rw [hfix1, hfix2, hfree, mul_one, mul_comm]
    · rw [Set.indicator_of_notMem hz]
      simp only [not_forall] at hz
      obtain ⟨i, hi, hne⟩ := hz
      have hzero : fixedPi p fixed x z = 0 := by
        rw [fixedPi, pi_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hne])
      rw [hzero, mul_zero]
  have hsum : (∑' a' : ∀ i, α i,
      Set.indicator {w : ∀ i, α i | ∀ i ∈ fixed, w i = x i} (pi p) a') = c := by
    simp_rw [hpt]
    rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  ext y
  rw [PMF.filter_apply, hpt y, hsum, mul_right_comm, ENNReal.mul_inv_cancel hc0 hctop, one_mul]

/-- **Coordinate averaging (tower law)**: for any free coordinate `i ∉ fixed`, the `p i`-weighted
average of `condExpect p f (insert i fixed) (Function.update x i a)` equals
`condExpect p f fixed x`. -/
theorem sum_mul_condExpect_insert (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {fixed : Finset ι} {i : ι} (hi : i ∉ fixed) (x : ∀ i, α i) :
    ∑ a : α i, (p i a).toReal * condExpect p f (insert i fixed) (Function.update x i a) =
      condExpect p f fixed x := by
  let q : ∀ j, PMF (α j) := fun j => if j ∈ fixed then PMF.pure (x j) else p j
  have hqi : q i = p i := by simp [q, hi]
  have hupd : ∀ a : α i,
      Function.update q i (PMF.pure a) =
        fun j => if j ∈ insert i fixed then PMF.pure (Function.update x i a j) else p j := by
    intro a
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [q, hji]
  have hbind := pi_bind_update q i
  have hexp := congrArg (fun μ : PMF (∀ j, α j) => ∑ y, (μ y).toReal * f y) hbind
  rw [sum_bind_mul] at hexp
  change _ = ∑ y, ((pi q) y).toReal * f y
  rw [← hexp, hqi]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [condExpect, fixedPi, hupd a]

/-- **Method of conditional expectations (minimization step)**: for any free coordinate `i ∉ fixed`,
some supported value `a ∈ (p i).support` satisfies
`condExpect p f (insert i fixed) (Function.update x i a) ≤ condExpect p f fixed x`. -/
theorem exists_condExpect_insert_le (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {fixed : Finset ι} {i : ι} (hi : i ∉ fixed) (x : ∀ i, α i) :
    ∃ a ∈ (p i).support,
      condExpect p f (insert i fixed) (Function.update x i a) ≤ condExpect p f fixed x := by
  obtain ⟨a, ha_supp, hle⟩ := Convexity.StdSimplex.exists_mem_support_le_sum_mul
    (toStdSimplex (p i)) (fun b => condExpect p f (insert i fixed) (Function.update x i b))
  have ha : a ∈ (p i).support := by
    rw [Finsupp.mem_support_iff, weights_toStdSimplex] at ha_supp
    by_contra hnot
    exact ha_supp (by simp [(PMF.apply_eq_zero_iff (p i) a).mpr hnot])
  refine ⟨a, ha, hle.trans_eq ?_⟩
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [weights_toStdSimplex]
  exact sum_mul_condExpect_insert p f hi x

/-- **Method of conditional expectations (maximization step)**: for any free coordinate `i ∉ fixed`,
some supported value `a ∈ (p i).support` satisfies
`condExpect p f fixed x ≤ condExpect p f (insert i fixed) (Function.update x i a)`. -/
theorem exists_le_condExpect_insert (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {fixed : Finset ι} {i : ι} (hi : i ∉ fixed) (x : ∀ i, α i) :
    ∃ a ∈ (p i).support,
      condExpect p f fixed x ≤ condExpect p f (insert i fixed) (Function.update x i a) := by
  have hneg : ∀ fixed' y, condExpect p (fun z => -f z) fixed' y = -condExpect p f fixed' y := by
    intro fixed' y
    simp only [condExpect, mul_neg, Finset.sum_neg_distrib]
  obtain ⟨a, ha, hle⟩ := exists_condExpect_insert_le p (fun z => -f z) hi x
  rw [hneg, hneg] at hle
  exact ⟨a, ha, by linarith⟩

end General

section UniformBool

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On the uniform Boolean cube `ι → Bool`, fixing a free coordinate `i ∉ fixed` to `true` and
`false` splits `condExpect` into two halves summing to `2 * condExpect`. -/
theorem condExpect_uniform_bool_add (f : (ι → Bool) → ℝ) {fixed : Finset ι} {i : ι}
    (hi : i ∉ fixed) (x : ι → Bool) :
    condExpect (fun _ => PMF.uniformOfFintype Bool) f (insert i fixed)
        (Function.update x i true) +
      condExpect (fun _ => PMF.uniformOfFintype Bool) f (insert i fixed)
        (Function.update x i false) =
      2 * condExpect (fun _ => PMF.uniformOfFintype Bool) f fixed x := by
  have h := sum_mul_condExpect_insert (fun _ : ι => PMF.uniformOfFintype Bool) f hi x
  rw [Fintype.sum_bool] at h
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat] at h
  linarith

end UniformBool

end Cslib.Probability.PMF
