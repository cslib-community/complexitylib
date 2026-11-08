/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.MarkovChain.Mixing
public import Mathlib.InformationTheory.Hamming
import Complexity.Foundations.Data.Hamming
import Complexity.Probability.PMF.Expect
import Complexity.Probability.StatisticalDistance

/-!
# Path coupling

Path coupling ([LevinPeres2017], Section 14.2, after Bubley and Dyer) bounds mixing by
coupling only *neighboring* states. Suppose `ρ` behaves like the path metric of a neighbor
relation `N` with edge lengths at least one ([LevinPeres2017], (14.5)): it is at least one off the
diagonal and every pair has a geodesic step to a neighbor
(`Cslib.Probability.MarkovChain.IsPathMetric`; symmetry and the triangle inequality are not
needed). Suppose also that every neighboring pair `x, y` admits a coupling of
`P x` and `P y` under which `ρ` contracts in expectation by a factor `κ` ((14.8) with
`κ = e^{-α}`). Then `t` steps contract `ρ` by `κ ^ t` in statistical distance:
`‖Pᵗ(x, ·) - Pᵗ(y, ·)‖_TV ≤ κ ^ t ρ(x, y)`
(`Cslib.Probability.MarkovChain.dist_pow_le_of_pathCoupling`). Hence `d(t) ≤ κ ^ t diam` and
`t_mix(ε) ≤ ⌈(log diam - log ε) / α⌉` ([LevinPeres2017], Corollary 14.8).

The source proves Theorem 14.6 through the transportation metric `ρ_K` and an optimal transport
plan. This module uses the dual statement instead: one coupled step multiplies the
`ρ`-Lipschitz constant of any function by `κ`
(`Cslib.Probability.MarkovChain.lipschitz_sum_pow`), and statistical distance is the largest gap
in expectation of a `{0, 1}`-valued function, which is `1`-Lipschitz because `ρ ≥ 1` off the
diagonal. A Lipschitz bound along neighbors extends to all pairs along a geodesic
(`Cslib.Probability.MarkovChain.IsPathMetric.lipschitz`), which plays the role of the triangle
inequality for `ρ_K`. No optimal transport plan or gluing of couplings is needed.

Every result also has a form relative to a set `C` of states that is closed under `P`
(suffix `_on`, with `Cslib.Probability.MarkovChain.IsPathMetricOn`): the hypotheses are needed
only for states in `C`, and the conclusion holds for chains started in `C`. This is the form for
a chain that does not mix on all of `S`, such as Glauber dynamics with a frozen boundary
([LevinPeres2017], Section 14.4.2), and the global results are its case `C = univ`.

Hamming distance is the path metric of the relation "at Hamming distance one"
(`Cslib.Probability.MarkovChain.isPathMetric_hammingDist`), and also relative to any set closed
under copying one coordinate (`Cslib.Probability.MarkovChain.isPathMetricOn_hammingDist`). This
is the setting of the coloring application in `Complexity.Probability.MarkovChain.Coloring`.

Expectations are written as finite sums `∑ a, (μ a).toReal * f a`.

## Main definitions

* `Cslib.Probability.MarkovChain.IsPathMetric`: the conditions that path coupling uses on `ρ`
  and `N`, satisfied by the path metric of `N` with edge lengths at least one.
* `Cslib.Probability.MarkovChain.IsPathMetricOn`: the same conditions relative to a set `C`.

## Main results

* `Cslib.Probability.MarkovChain.isPathMetric_hammingDist`,
  `Cslib.Probability.MarkovChain.isPathMetricOn_hammingDist`: Hamming distance is a path metric.
* `Cslib.Probability.MarkovChain.lipschitz_sum_pow`: `t` coupled steps contract Lipschitz
  constants by `κ ^ t`.
* `Cslib.Probability.MarkovChain.dist_pow_le_of_pathCoupling`,
  `Cslib.Probability.MarkovChain.dist_pow_le_of_pathCoupling_on`: [LevinPeres2017],
  Theorem 14.6 with (14.7).
* `Cslib.Probability.MarkovChain.IsStationary.distToStationary_le_of_pathCoupling`,
  `Cslib.Probability.MarkovChain.IsStationary.mixingTime_le_of_pathCoupling`,
  `Cslib.Probability.MarkovChain.IsStationary.dist_le_of_pathCoupling_on`:
  [LevinPeres2017], Corollary 14.8.

## References

* [LevinPeres2017], Sections 14.1 and 14.2.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF

variable {S : Type*}

/-! ### Path metrics -/

/-- The conditions on `ρ` and the neighbor relation `N` that path coupling uses: `ρ` vanishes on
the diagonal, is at least one off it, and every `x ≠ y` has a neighbor `z ≠ x` of `x` with
`ρ x z + ρ z y ≤ ρ x y` (a geodesic step). The path metric of `N` with edge lengths at least one
([LevinPeres2017], (14.5)) satisfies them, taking for `z` the second vertex of a shortest path,
but they do not require `ρ` to be symmetric or to satisfy the triangle inequality. -/
structure IsPathMetric (N : S → S → Prop) (ρ : S → S → ℝ) : Prop where
  self : ∀ x, ρ x x = 0
  one_le : ∀ x y, x ≠ y → 1 ≤ ρ x y
  exists_step : ∀ x y, x ≠ y → ∃ z, N x z ∧ x ≠ z ∧ ρ x z + ρ z y ≤ ρ x y

/-- `IsPathMetric` relative to a set `C` of states: the conditions are required only for states
in `C`, and the geodesic steps stay in `C`. This is the form needed for a chain that is confined
to a closed set `C`. -/
structure IsPathMetricOn (C : Set S) (N : S → S → Prop) (ρ : S → S → ℝ) : Prop where
  self : ∀ x ∈ C, ρ x x = 0
  one_le : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 1 ≤ ρ x y
  exists_step : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
    ∃ z ∈ C, N x z ∧ x ≠ z ∧ ρ x z + ρ z y ≤ ρ x y

variable {N : S → S → Prop} {ρ : S → S → ℝ}

theorem isPathMetricOn_univ : IsPathMetricOn Set.univ N ρ ↔ IsPathMetric N ρ :=
  ⟨fun h => ⟨fun x => h.self x trivial, fun x y => h.one_le x trivial y trivial,
      fun x y hxy => by
        obtain ⟨z, -, hz⟩ := h.exists_step x trivial y trivial hxy
        exact ⟨z, hz⟩⟩,
    fun h => ⟨fun x _ => h.self x, fun x _ y _ => h.one_le x y,
      fun x _ y _ hxy => by
        obtain ⟨z, hz⟩ := h.exists_step x y hxy
        exact ⟨z, trivial, hz⟩⟩⟩

namespace IsPathMetricOn

variable {C : Set S}

theorem nonneg (h : IsPathMetricOn C N ρ) {x y : S} (hx : x ∈ C) (hy : y ∈ C) : 0 ≤ ρ x y := by
  by_cases hxy : x = y
  · rw [hxy, h.self y hy]
  · linarith [h.one_le x hx y hy hxy]

/-- A Lipschitz bound along neighbors in `C` extends to all pairs in `C`. -/
theorem lipschitz (h : IsPathMetricOn C N ρ) {f : S → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hN : ∀ x ∈ C, ∀ z ∈ C, N x z → |f x - f z| ≤ L * ρ x z) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : |f x - f y| ≤ L * ρ x y := by
  suffices H : ∀ n : ℕ, ∀ x ∈ C, ρ x y < n → |f x - f y| ≤ L * ρ x y from
    H (⌊ρ x y⌋₊ + 1) x hx (by exact_mod_cast Nat.lt_floor_add_one (ρ x y))
  intro n
  induction n with
  | zero => intro x hx hxy; exact absurd hxy (not_lt.mpr (by exact_mod_cast h.nonneg hx hy))
  | succ n ih =>
    intro x hx hxy
    by_cases hne : x = y
    · rw [hne, sub_self, abs_zero, h.self y hy, mul_zero]
    obtain ⟨z, hzC, hNz, hxz, hle⟩ := h.exists_step x hx y hy hne
    have h1 := h.one_le x hx z hzC hxz
    have hzy : ρ z y < n := by push_cast at hxy; linarith
    calc |f x - f y| = |(f x - f z) + (f z - f y)| := by ring_nf
      _ ≤ |f x - f z| + |f z - f y| := abs_add_le _ _
      _ ≤ L * ρ x z + L * ρ z y := add_le_add (hN x hx z hzC hNz) (ih z hzC hzy)
      _ ≤ L * ρ x y := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hle hL

end IsPathMetricOn

namespace IsPathMetric

theorem isPathMetricOn (h : IsPathMetric N ρ) : IsPathMetricOn Set.univ N ρ :=
  isPathMetricOn_univ.2 h

theorem nonneg (h : IsPathMetric N ρ) (x y : S) : 0 ≤ ρ x y :=
  h.isPathMetricOn.nonneg trivial trivial

/-- A Lipschitz bound along neighbors extends to all pairs. -/
theorem lipschitz (h : IsPathMetric N ρ) {f : S → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hN : ∀ x z, N x z → |f x - f z| ≤ L * ρ x z) (x y : S) : |f x - f y| ≤ L * ρ x y :=
  h.isPathMetricOn.lipschitz hL (fun x _ z _ => hN x z) trivial trivial

end IsPathMetric

/-- Hamming distance is a path metric, relative to any set `C` closed under copying one
coordinate between two of its members: to move from `x` toward `y ≠ x`, change one coordinate where
they differ to its value in `y`. -/
theorem isPathMetricOn_hammingDist {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, DecidableEq (β i)] [DecidableEq ι] {C : Set (∀ i, β i)}
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ i, Function.update x i (y i) ∈ C) :
    IsPathMetricOn C (fun x y : ∀ i, β i => hammingDist x y = 1)
      fun x y => (hammingDist x y : ℝ) where
  self x _ := by rw [hammingDist_self, Nat.cast_zero]
  one_le x _ y _ hxy := by exact_mod_cast hammingDist_pos.2 hxy
  exists_step x hx y hy hxy := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    have h1 : hammingDist x (Function.update x i (y i)) = 1 := hammingDist_update_of_ne hi
    refine ⟨Function.update x i (y i), hC x hx y hy i, h1, fun h => hi ?_, ?_⟩
    · have := congrFun h i
      rwa [Function.update_self] at this
    · have := hammingDist_update_update x y i (y i) (y i)
      rw [Function.update_eq_self, ite_eq_left hi, ite_eq_right (not_not.2 rfl)] at this
      rw [h1]
      exact_mod_cast (by omega : 1 + hammingDist (Function.update x i (y i)) y ≤ hammingDist x y)

/-- Hamming distance is the path metric of the relation "at Hamming distance one". -/
theorem isPathMetric_hammingDist {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, DecidableEq (β i)] :
    IsPathMetric (fun x y : ∀ i, β i => hammingDist x y = 1) fun x y => (hammingDist x y : ℝ) := by
  classical
  exact isPathMetricOn_univ.1 (isPathMetricOn_hammingDist fun _ _ _ _ _ => trivial)

/-! ### Path coupling -/

variable [Fintype S] {P : MarkovChain S}

/-- One coupled step contracts a function that is Lipschitz on a set `C` containing the supports
of `P x` and `P y`: if `ω` couples `P x` with `P y` and `E_ω ρ ≤ κ ρ(x, y)`, then the expectations
of `f` differ by at most `L κ ρ(x, y)`. -/
theorem lipschitz_sum_of_coupling_on {C : Set S} {f : S → ℝ} {L κ : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a ∈ C, ∀ b ∈ C, |f a - f b| ≤ L * ρ a b) {x y : S} (hxC : (P x).support ⊆ C)
    (hyC : (P y).support ⊆ C) (ω : PMF (S × S))
    (h1 : ω.map Prod.fst = P x) (h2 : ω.map Prod.snd = P y)
    (hω : ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y) :
    |∑ a, (P x a).toReal * f a - ∑ a, (P y a).toReal * f a| ≤ L * κ * ρ x y := by
  rw [← h1, ← h2, sum_map_mul, sum_map_mul, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p, |(ω p).toReal * f p.1 - (ω p).toReal * f p.2|
      ≤ ∑ p, (ω p).toReal * (L * ρ p.1 p.2) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        by_cases hp : p ∈ ω.support
        · have hp1 : p.1 ∈ C := hxC (h1 ▸ (PMF.mem_support_map_iff _ _ _).2 ⟨p, hp, rfl⟩)
          have hp2 : p.2 ∈ C := hyC (h2 ▸ (PMF.mem_support_map_iff _ _ _).2 ⟨p, hp, rfl⟩)
          exact mul_le_mul_of_nonneg_left (hf p.1 hp1 p.2 hp2) ENNReal.toReal_nonneg
        · rw [PMF.apply_eq_zero_iff _ _ |>.2 hp, ENNReal.toReal_zero, zero_mul, zero_mul]
    _ = L * ∑ p, (ω p).toReal * ρ p.1 p.2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ L * (κ * ρ x y) := mul_le_mul_of_nonneg_left hω hL
    _ = L * κ * ρ x y := by ring

/-- One coupled step contracts a Lipschitz function: if `ω` couples `P x` with `P y` and
`E_ω ρ ≤ κ ρ(x, y)`, then the expectations of an `L`-Lipschitz `f` differ by at most
`L κ ρ(x, y)`. -/
theorem lipschitz_sum_of_coupling {f : S → ℝ} {L κ : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * ρ a b) {x y : S} (ω : PMF (S × S))
    (h1 : ω.map Prod.fst = P x) (h2 : ω.map Prod.snd = P y)
    (hω : ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y) :
    |∑ a, (P x a).toReal * f a - ∑ a, (P y a).toReal * f a| ≤ L * κ * ρ x y :=
  lipschitz_sum_of_coupling_on (C := Set.univ) hL (fun a _ b _ => hf a b)
    (Set.subset_univ _) (Set.subset_univ _) ω h1 h2 hω

/-- **Path coupling on a closed set, Lipschitz form.** Let `C` be closed under `P`. If every
neighboring pair in `C` admits a one-step coupling that contracts `ρ` in expectation by `κ`, then
`t` steps multiply Lipschitz constants on `C` by `κ ^ t`. -/
theorem lipschitz_sum_pow_on {C : Set S} (hρ : IsPathMetricOn C N ρ)
    (hP : ∀ x ∈ C, (P x).support ⊆ C) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x ∈ C, ∀ y ∈ C, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧
      ω.map Prod.snd = P y ∧ ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    {f : S → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a ∈ C, ∀ b ∈ C, |f a - f b| ≤ L * ρ a b) (t : ℕ)
    {x y : S} (hx : x ∈ C) (hy : y ∈ C) :
    |∑ a, ((P ^ t) x a).toReal * f a - ∑ a, ((P ^ t) y a).toReal * f a| ≤
      L * κ ^ t * ρ x y := by
  classical
  induction t generalizing x y with
  | zero =>
    have hpure (z : S) : ∑ a, ((P ^ 0) z a).toReal * f a = f z := by
      rw [Finset.sum_eq_single z]
      · simp
      · intro b _ hb
        simp [PMF.pure_apply_of_ne _ _ hb]
      · simp
    rw [hpure, hpure, pow_zero, mul_one]
    exact hf x hx y hy
  | succ t ih =>
    have hstep : ∀ a ∈ C, ∀ b ∈ C, N a b →
        |∑ c, ((P ^ (t + 1)) a c).toReal * f c - ∑ c, ((P ^ (t + 1)) b c).toReal * f c| ≤
          (L * κ ^ (t + 1)) * ρ a b := by
      intro a ha b hb hab
      obtain ⟨ω, h1, h2, hω⟩ := hc a ha b hb hab
      rw [pow_succ_apply', pow_succ_apply', sum_bind_mul, sum_bind_mul]
      calc _ ≤ L * κ ^ t * κ * ρ a b :=
            lipschitz_sum_of_coupling_on (P := P) (by positivity)
              (fun a' ha' b' hb' => ih ha' hb') (hP a ha) (hP b hb) ω h1 h2 hω
        _ = L * κ ^ (t + 1) * ρ a b := by ring
    exact hρ.lipschitz (by positivity) hstep hx hy

/-- **Path coupling, Lipschitz form.** If every neighboring pair admits a one-step coupling that
contracts `ρ` in expectation by `κ`, then `t` steps multiply `ρ`-Lipschitz constants by
`κ ^ t`. This is the dual form of [LevinPeres2017], Theorem 14.6. -/
theorem lipschitz_sum_pow (hρ : IsPathMetric N ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x y, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧ ω.map Prod.snd = P y ∧
      ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    {f : S → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * ρ a b) (t : ℕ) (x y : S) :
    |∑ a, ((P ^ t) x a).toReal * f a - ∑ a, ((P ^ t) y a).toReal * f a| ≤
      L * κ ^ t * ρ x y :=
  lipschitz_sum_pow_on hρ.isPathMetricOn (fun _ _ => Set.subset_univ _) hκ
    (fun x _ y _ => hc x y) hL (fun a _ b _ => hf a b) t trivial trivial

/-- **Path coupling on a closed set** ([LevinPeres2017], Theorem 14.6 with (14.7), for a chain
confined to a closed set `C`): if every neighboring pair in `C` admits a one-step coupling that
contracts `ρ` in expectation by `κ`, then after `t` steps the chains started at any `x, y ∈ C` are
within statistical distance `κ ^ t ρ(x, y)`. -/
theorem dist_pow_le_of_pathCoupling_on {C : Set S} (hρ : IsPathMetricOn C N ρ)
    (hP : ∀ x ∈ C, (P x).support ⊆ C) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x ∈ C, ∀ y ∈ C, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧
      ω.map Prod.snd = P y ∧ ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    (t : ℕ) {x y : S} (hx : x ∈ C) (hy : y ∈ C) :
    dist ((P ^ t) x) ((P ^ t) y) ≤ κ ^ t * ρ x y := by
  classical
  set p := (P ^ t) x
  set q := (P ^ t) y
  set f : S → ℝ := fun a => if (q a).toReal < (p a).toReal then 1 else 0
  have hf : ∀ a ∈ C, ∀ b ∈ C, |f a - f b| ≤ 1 * ρ a b := by
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab, sub_self, abs_zero, hρ.self b hb, mul_zero]
    · rw [one_mul]
      refine le_trans ?_ (hρ.one_le a ha b hb hab)
      simp only [f]
      split_ifs <;> norm_num
  have hd : dist p q = ∑ a, (p a).toReal * f a - ∑ a, (q a).toReal * f a := by
    rw [dist_eq_sum_filter_lt, ← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [f]
    split_ifs <;> ring
  rw [hd]
  have := lipschitz_sum_pow_on (P := P) hρ hP hκ hc zero_le_one hf t hx hy
  rw [one_mul] at this
  exact (le_abs_self _).trans this

/-- **Path coupling** ([LevinPeres2017], Theorem 14.6 with (14.7), after Bubley and Dyer): if
every neighboring pair admits a one-step coupling that contracts `ρ` in expectation by `κ`, then
after `t` steps the chains started at any `x` and `y` are within statistical distance
`κ ^ t ρ(x, y)`. -/
theorem dist_pow_le_of_pathCoupling (hρ : IsPathMetric N ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x y, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧ ω.map Prod.snd = P y ∧
      ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    (t : ℕ) (x y : S) : dist ((P ^ t) x) ((P ^ t) y) ≤ κ ^ t * ρ x y :=
  dist_pow_le_of_pathCoupling_on hρ.isPathMetricOn (fun _ _ => Set.subset_univ _) hκ
    (fun x _ y _ => hc x y) t trivial trivial

/-- Path coupling bounds `d̄(t) ≤ κ ^ t diam`. -/
theorem distPair_le_of_pathCoupling [Nonempty S] (hρ : IsPathMetric N ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x y, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧ ω.map Prod.snd = P y ∧
      ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    {D : ℝ} (hD : ∀ x y, ρ x y ≤ D) (t : ℕ) : P.distPair t ≤ κ ^ t * D := by
  have hD0 : 0 ≤ D := by
    obtain ⟨x⟩ := ‹Nonempty S›
    simpa [hρ.self] using hD x x
  refine P.distPair_le (fun x y => (dist_pow_le_of_pathCoupling hρ hκ hc t x y).trans ?_)
    (by positivity)
  exact mul_le_mul_of_nonneg_left (hD x y) (pow_nonneg hκ t)

/-- **Path coupling bound on mixing from a closed set** ([LevinPeres2017], Corollary 14.8, for a
chain confined to a closed set `C` that contains the support of the stationary `π`): from any
`x ∈ C`, `‖Pᵗ(x, ·) - π‖_TV ≤ κ ^ t diam(C)`. -/
theorem IsStationary.dist_le_of_pathCoupling_on {π : PMF S} (hπ : P.IsStationary π) {C : Set S}
    (hπC : π.support ⊆ C) (hρ : IsPathMetricOn C N ρ) (hP : ∀ x ∈ C, (P x).support ⊆ C)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x ∈ C, ∀ y ∈ C, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧
      ω.map Prod.snd = P y ∧ ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    {D : ℝ} (hD : ∀ x ∈ C, ∀ y ∈ C, ρ x y ≤ D) (t : ℕ) {x : S} (hx : x ∈ C) :
    dist ((P ^ t) x) π ≤ κ ^ t * D :=
  hπ.dist_le_of_forall_mem_support fun y hy =>
    (dist_pow_le_of_pathCoupling_on hρ hP hκ hc t (hπC hy) hx).trans
      (mul_le_mul_of_nonneg_left (hD y (hπC hy) x hx) (pow_nonneg hκ t))

/-- **Path coupling bound on mixing** ([LevinPeres2017], Corollary 14.8): `d(t) ≤ κ ^ t diam`. -/
theorem IsStationary.distToStationary_le_of_pathCoupling {π : PMF S} (hπ : P.IsStationary π)
    (hρ : IsPathMetric N ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ x y, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧ ω.map Prod.snd = P y ∧
      ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    {D : ℝ} (hD : ∀ x y, ρ x y ≤ D) (t : ℕ) : P.distToStationary π t ≤ κ ^ t * D := by
  have : Nonempty S := ⟨π.support_nonempty.some⟩
  exact (hπ.distToStationary_le_distPair t).trans (distPair_le_of_pathCoupling hρ hκ hc hD t)

/-- **Path coupling bound on the mixing time** ([LevinPeres2017], Corollary 14.8): if the
contraction factor is at most `e^{-α}` with `α > 0` and `ρ ≤ D`, then
`t_mix(ε) ≤ ⌈(log D - log ε) / α⌉`. -/
theorem IsStationary.mixingTime_le_of_pathCoupling {π : PMF S} (hπ : P.IsStationary π)
    (hρ : IsPathMetric N ρ) {κ α : ℝ} (hκ : 0 ≤ κ)
    (hα : 0 < α) (hκα : κ ≤ Real.exp (-α))
    (hc : ∀ x y, N x y → ∃ ω : PMF (S × S), ω.map Prod.fst = P x ∧ ω.map Prod.snd = P y ∧
      ∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y)
    {D : ℝ} (hD0 : 0 < D) (hD : ∀ x y, ρ x y ≤ D) {ε : ℝ} (hε : 0 < ε) :
    P.mixingTime π ε ≤ (⌈(Real.log D - Real.log ε) / α⌉₊ : ℕ) := by
  set t := ⌈(Real.log D - Real.log ε) / α⌉₊
  refine mixingTime_le_of_distToStationary_le ?_
  refine (hπ.distToStationary_le_of_pathCoupling hρ hκ hc hD t).trans ?_
  have ht : (Real.log D - Real.log ε) / α ≤ t := Nat.le_ceil _
  have ht' : Real.log D - Real.log ε ≤ α * t := by
    rwa [div_le_iff₀ hα, mul_comm] at ht
  calc κ ^ t * D ≤ Real.exp (-α) ^ t * D :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hκ hκα t) hD0.le
    _ = Real.exp (-(α * t) + Real.log D) := by
        rw [← Real.exp_nat_mul, Real.exp_add, Real.exp_log hD0]; ring_nf
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith)
    _ = ε := Real.exp_log hε

end Cslib.Probability.MarkovChain
