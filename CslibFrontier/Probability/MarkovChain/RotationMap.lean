/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.HittingTime
public import CslibFrontier.Foundations.Combinatorics.Expander.Harmonic
public import CslibFrontier.Foundations.Combinatorics.Expander.Walk
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Hitting and return times of random walks on regular multigraphs

The random walk on a `D`-regular multigraph `G` (a `Cslib.RotationMap V D`, with parallel edges and
self-loops allowed) moves from `x` along a uniformly random edge label
(`Cslib.RotationMap.randomWalk`). Its transition probabilities are `edgeCount x y / |D|`
(`randomWalk_apply`), and the `t`-step probability of avoiding a vertex is the fraction of the
`|D| ^ t` label sequences whose walk (`Cslib.RotationMap.walkAt`) avoids it
(`survival_randomWalk_mul_pow`).

These are the facts of [Arora and Barak, Chapter 7, Exercise 9][AroraBarak07]:

* **(b)(i)** On a connected regular multigraph, the uniform distribution is the unique stationary
  distribution (`isStationary_randomWalk_iff`). The proof is the maximum principle
  `Cslib.RotationMap.eq_of_forall_sum_edgeCount_mul_eq` of `Expander.Harmonic`.
* **(c)** The expected return time to `u` equals the number of vertices of the connected component
  of `u` (`returnTime_randomWalk_eq_card`); in a connected graph on `n` vertices it is `n`, so at
  most `10 n²`. This is Kac's formula for the uniform measure on the component.
* **(d)** If `u` and `v` are joined by a path of length at most `k`, then `E_u[τ_v] ≤ k |D| n`
  (`hittingTime_randomWalk_le_length_mul`), hence `E_u[τ_v] ≤ 100 k n²` when `|D| ≤ n`
  (`hittingTime_randomWalk_le_hundred_mul`). For vertices `s`, `t` in the same component, a walk
  of `1000 n³` steps from `s` misses `t` with probability at most `1 / 10`
  (`ten_mul_card_filter_walkAt_ne_le`), which counts label sequences.

The edge bound comes from the first-step equation of the return time: if `x` is a neighbor of `y`,
then `(1 / |D|) E_x[τ_y] ≤ E_y[τ⁺_y] ≤ n`. The triangle inequality for hitting times sums it along
a path, and Markov's inequality turns the expectation into the miss probability. Arora and Barak
state (d) for `d`-regular graphs with `d ≤ n`; with unbounded edge multiplicity the bound in `n`
alone fails, so the hypothesis `|D| ≤ n` is kept.

## Main definitions

* `Cslib.RotationMap.randomWalk`: the random walk on a regular multigraph, as a `MarkovChain`.

## Main results

* `Cslib.RotationMap.randomWalk_apply`: its transition probabilities.
* `Cslib.RotationMap.survival_randomWalk_mul_pow`: survival probabilities count label sequences.
* `Cslib.RotationMap.isStationary_randomWalk_iff`: exercise 7.9(b)(i).
* `Cslib.RotationMap.returnTime_randomWalk_eq_card`,
  `Cslib.RotationMap.returnTime_randomWalk_eq_card_of_connected`,
  `Cslib.RotationMap.returnTime_randomWalk_le_ten_mul_sq`: exercise 7.9(c).
* `Cslib.RotationMap.hittingTime_randomWalk_le_length_mul`,
  `Cslib.RotationMap.hittingTime_randomWalk_le_hundred_mul`,
  `Cslib.RotationMap.ten_mul_card_filter_walkAt_ne_le`: exercise 7.9(d).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [D. A. Levin, Y. Peres, *Markov Chains and Mixing Times*][LevinPeres2017]
-/

public section

namespace Cslib.RotationMap

open Finset Cslib.Probability Cslib.Probability.MarkovChain
open scoped ENNReal

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [Nonempty D] (G : RotationMap V D)

/-- The **random walk** on a regular multigraph: from `x`, follow a uniformly random edge
label. -/
noncomputable def randomWalk : MarkovChain V where
  step x := (PMF.uniformOfFintype D).map (G.neighbor x)

omit [Fintype V] in
/-- The transition probabilities of the random walk are the edge multiplicities divided by the
degree. -/
theorem randomWalk_apply (x y : V) :
    G.randomWalk x y = G.edgeCount x y / Fintype.card D := by
  change ((PMF.uniformOfFintype D).map (G.neighbor x)) y = _
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv, edgeCount_eq_card_filter]
  simp_rw [eq_comm (a := y)]

variable {G}

omit [Fintype V] in
theorem randomWalk_ne_zero_iff {x y : V} : G.randomWalk x y ≠ 0 ↔ G.edgeCount x y ≠ 0 := by
  rw [randomWalk_apply, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  simp [ENNReal.natCast_ne_top]

/-! ### Kac's formula on a component -/

omit [DecidableEq V] in
open Classical in
/-- The uniform measure on the connected component of `u` is stationary. -/
theorem sum_component_mul_randomWalk (u y : V) :
    ∑ x, (if G.toSimpleGraph.Reachable u x then 1 else 0) * G.randomWalk x y =
      if G.toSimpleGraph.Reachable u y then 1 else 0 := by
  classical
  by_cases hy : G.toSimpleGraph.Reachable u y
  · rw [ite_eq_left hy]
    have : ∀ x, (if G.toSimpleGraph.Reachable u x then 1 else 0) * G.randomWalk x y =
        G.randomWalk y x := by
      intro x
      by_cases hc : G.edgeCount x y = 0
      · have h1 : G.randomWalk x y = 0 := by rw [randomWalk_apply, hc]; simp
        have h0 : G.randomWalk y x = 0 := by
          rw [randomWalk_apply, G.edgeCount_comm, hc]; simp
        rw [h0, h1, mul_zero]
      · rw [ite_eq_left (hy.trans (reachable_of_edgeCount_ne_zero hc).symm), one_mul,
          randomWalk_apply, randomWalk_apply, G.edgeCount_comm]
    simp_rw [this]
    exact sum_apply _ y
  · rw [ite_eq_right hy]
    refine sum_eq_zero fun x _ => ?_
    by_cases hx : G.toSimpleGraph.Reachable u x
    · have : G.edgeCount x y = 0 := by
        by_contra hc; exact hy (hx.trans (reachable_of_edgeCount_ne_zero hc))
      rw [randomWalk_apply, this]; simp
    · simp [hx]

/-- In a regular multigraph, every vertex reaches every vertex of its component along transitions
of positive probability, so expected hitting times within a component are finite. -/
theorem hittingTime_randomWalk_ne_top {u x : V} (hx : G.toSimpleGraph.Reachable u x) :
    hittingTime G.randomWalk u x ≠ ⊤ := by
  refine hittingTime_ne_top (S := {x | G.toSimpleGraph.Reachable u x}) (fun a ha b hab => ?_)
    (fun y hy => ?_) hx
  · exact (ha : G.toSimpleGraph.Reachable u a).trans
      (reachable_of_edgeCount_ne_zero (randomWalk_ne_zero_iff.1 hab))
  · refine Relation.ReflTransGen.mono (fun a b h => randomWalk_ne_zero_iff.2
      (edgeCount_ne_zero_of_adj h)) _ _ ((SimpleGraph.reachable_iff_reflTransGen y u).1 ?_)
    exact (hy : G.toSimpleGraph.Reachable u y).symm

/-- **Arora–Barak, Exercise 7.9(c).** The expected return time of the random walk to `u` is the
number of vertices of the connected component of `u`. -/
theorem returnTime_randomWalk_eq_card (u : V) :
    returnTime G.randomWalk u = Nat.card {x // G.toSimpleGraph.Reachable u x} := by
  classical
  have h := mul_returnTime_eq (π := fun x => if G.toSimpleGraph.Reachable u x then 1 else 0)
    (sum_component_mul_randomWalk u) u ?_
  · rw [ite_eq_left (SimpleGraph.Reachable.refl u), one_mul] at h
    rw [h, sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · refine (ENNReal.sum_lt_top.2 fun x _ => ?_).ne
    by_cases hx : G.toSimpleGraph.Reachable u x
    · simpa [hx] using (hittingTime_randomWalk_ne_top hx).lt_top
    · simp [hx]

/-- **Arora–Barak, Exercise 7.9(c).** On a connected regular multigraph, the expected return time
to every vertex is the number of vertices. -/
theorem returnTime_randomWalk_eq_card_of_connected (hG : G.toSimpleGraph.Connected) (u : V) :
    returnTime G.randomWalk u = Fintype.card V := by
  rw [returnTime_randomWalk_eq_card, Nat.card_congr (Equiv.subtypeUnivEquiv fun x => hG u x),
    Nat.card_eq_fintype_card]

theorem returnTime_randomWalk_le_card (u : V) : returnTime G.randomWalk u ≤ Fintype.card V := by
  rw [returnTime_randomWalk_eq_card]
  exact_mod_cast Nat.card_le_card_of_injective _ Subtype.val_injective |>.trans
    (Nat.card_eq_fintype_card).le

/-- **Arora–Barak, Exercise 7.9(c)**, as stated: `E_u ≤ 10 n²`. -/
theorem returnTime_randomWalk_le_ten_mul_sq (u : V) :
    returnTime G.randomWalk u ≤ 10 * (Fintype.card V : ℝ≥0∞) ^ 2 := by
  refine (returnTime_randomWalk_le_card u).trans ?_
  have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
  exact_mod_cast (show Fintype.card V ≤ 10 * Fintype.card V ^ 2 by nlinarith)

/-! ### Hitting times along paths -/

/-- If `x` is a neighbor of `y`, the expected hitting time of `y` from `x` is at most `|D| n`. -/
theorem hittingTime_randomWalk_le_of_edgeCount_ne_zero {x y : V} (h : G.edgeCount y x ≠ 0) :
    hittingTime G.randomWalk y x ≤ Fintype.card D * Fintype.card V := by
  have hP : (Fintype.card D : ℝ≥0∞)⁻¹ ≤ G.randomWalk y x := by
    rw [randomWalk_apply, div_eq_mul_inv]
    exact le_mul_of_one_le_left (zero_le) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 h)
  have hle : (Fintype.card D : ℝ≥0∞)⁻¹ * hittingTime G.randomWalk y x ≤ Fintype.card V := by
    refine le_trans ?_ (returnTime_randomWalk_le_card (G := G) y)
    rw [returnTime_eq]
    refine le_trans ?_ le_add_self
    exact (by gcongr : (Fintype.card D : ℝ≥0∞)⁻¹ * hittingTime G.randomWalk y x ≤
        G.randomWalk y x * hittingTime G.randomWalk y x).trans
      (single_le_sum (f := fun z => G.randomWalk y z * hittingTime G.randomWalk y z)
        (fun _ _ => zero_le) (mem_univ x))
  calc hittingTime G.randomWalk y x
      = Fintype.card D * ((Fintype.card D : ℝ≥0∞)⁻¹ * hittingTime G.randomWalk y x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel
          (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
          one_mul]
    _ ≤ Fintype.card D * Fintype.card V := by gcongr

/-- Along a path of length `ℓ` in the simple graph of `G` from `u` to `v`,
`E_u[τ_v] ≤ ℓ |D| n`. -/
theorem hittingTime_randomWalk_le_length_mul {u v : V} (p : G.toSimpleGraph.Walk u v) :
    hittingTime G.randomWalk v u ≤ p.length * (Fintype.card D * Fintype.card V) := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    calc hittingTime G.randomWalk z x
        ≤ hittingTime G.randomWalk y x + hittingTime G.randomWalk z y :=
          hittingTime_le_add y z x
      _ ≤ Fintype.card D * Fintype.card V + p.length * (Fintype.card D * Fintype.card V) :=
          add_le_add (hittingTime_randomWalk_le_of_edgeCount_ne_zero
            (edgeCount_ne_zero_of_adj hxy.symm)) ih
      _ = (SimpleGraph.Walk.cons hxy p).length * (Fintype.card D * Fintype.card V) := by
          rw [SimpleGraph.Walk.length_cons]; push_cast; ring

/-- **Arora–Barak, Exercise 7.9(d).** If `u` and `v` are joined by a path of length at most `k`
in a `d`-regular multigraph on `n` vertices with `d ≤ n`, then `E_u[τ_v] ≤ 100 k n²`. -/
theorem hittingTime_randomWalk_le_hundred_mul (hD : Fintype.card D ≤ Fintype.card V) {k : ℕ}
    {u v : V} (p : G.toSimpleGraph.Walk u v) (hk : p.length ≤ k) :
    hittingTime G.randomWalk v u ≤ 100 * k * (Fintype.card V : ℝ≥0∞) ^ 2 := by
  refine (hittingTime_randomWalk_le_length_mul p).trans ?_
  have : p.length * (Fintype.card D * Fintype.card V) ≤ 100 * k * Fintype.card V ^ 2 := by
    calc p.length * (Fintype.card D * Fintype.card V)
        ≤ k * (Fintype.card V * Fintype.card V) := by gcongr
      _ ≤ 100 * k * Fintype.card V ^ 2 := by nlinarith
  exact_mod_cast this

/-- For vertices `s`, `t` in the same component of a `d`-regular multigraph on `n` vertices,
`E_s[τ_t] ≤ (n - 1) d n`: a path has fewer than `n` edges. -/
theorem hittingTime_randomWalk_le_of_reachable {s t : V} (h : G.toSimpleGraph.Reachable s t) :
    hittingTime G.randomWalk t s ≤
      (Fintype.card V - 1 : ℕ) * (Fintype.card D * Fintype.card V) := by
  classical
  obtain ⟨p, hp⟩ := h.exists_isPath
  refine (hittingTime_randomWalk_le_length_mul p).trans ?_
  have := hp.length_lt
  gcongr
  exact_mod_cast Nat.le_sub_one_of_lt this

/-! ### Survival probabilities count label sequences -/

/-- The number of label sequences of length `T` whose walk from `s` avoids `t` at all times
`0, …, T`, as a fraction of `|D| ^ T`, is the survival probability `P_s(τ_t > T)`. -/
theorem survival_randomWalk_mul_pow (t : V) :
    ∀ (T : ℕ) (s : V), survival G.randomWalk t T s * (Fintype.card D : ℝ≥0∞) ^ T =
      #{k : Fin T → D | ∀ i ≤ T, G.walkAt (s, k) i ≠ t}
  | 0, s => by
    by_cases hs : s = t
    · subst hs; simp
    · rw [survival_zero_of_ne hs]
      simp [hs]
  | T + 1, s => by
    by_cases hs : s = t
    · subst hs
      have : ∀ k : Fin (T + 1) → D, ¬ ∀ i ≤ T + 1, G.walkAt (s, k) i ≠ s :=
        fun k h => h 0 (Nat.zero_le _) rfl
      simp [this]
    rw [survival_succ_of_ne hs, sum_mul]
    have hcount : #{k : Fin (T + 1) → D | ∀ i ≤ T + 1, G.walkAt (s, k) i ≠ t} =
        ∑ a, #{k : Fin T → D | ∀ i ≤ T, G.walkAt (G.neighbor s a, k) i ≠ t} := by
      rw [← card_sigma]
      refine card_bij' (fun k _ => ⟨k 0, Fin.tail k⟩) (fun p _ => Fin.cons p.1 p.2)
        (fun k hk => ?_) (fun p hp => ?_) (fun k _ => Fin.cons_self_tail k)
        (fun p _ => by simp)
      · simp only [mem_filter, mem_univ, true_and, mem_sigma] at hk ⊢
        intro i hi
        have := hk (i + 1) (by omega)
        rwa [← Fin.cons_self_tail k, walkAt_cons_succ] at this
      · simp only [mem_filter, mem_univ, true_and, mem_sigma] at hp ⊢
        intro i hi
        cases i with
        | zero => exact hs
        | succ i => rw [walkAt_cons_succ]; exact hp i (by omega)
    rw [hcount, Nat.cast_sum, G.sum_comp_neighbor s (fun y => (#{k : Fin T → D |
      ∀ i ≤ T, G.walkAt (y, k) i ≠ t} : ℝ≥0∞))]
    refine sum_congr rfl fun y _ => ?_
    rw [← survival_randomWalk_mul_pow t T y, randomWalk_apply, nsmul_eq_mul, pow_succ]
    rw [div_eq_mul_inv]
    calc (G.edgeCount s y : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ * survival G.randomWalk t T y *
          ((Fintype.card D : ℝ≥0∞) ^ T * Fintype.card D)
        = G.edgeCount s y * (survival G.randomWalk t T y * (Fintype.card D : ℝ≥0∞) ^ T) *
          ((Fintype.card D : ℝ≥0∞)⁻¹ * Fintype.card D) := by ring
      _ = _ := by
        rw [ENNReal.inv_mul_cancel
          (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), mul_one]

/-- **Arora–Barak, Exercise 7.9(d), miss probability.** In a `d`-regular multigraph on `n`
vertices with `d ≤ n`, if `s` and `t` are connected, at most a tenth of the label sequences of
length `1000 n³` give a walk from `s` that never visits `t`. -/
theorem ten_mul_card_filter_walkAt_ne_le (hD : Fintype.card D ≤ Fintype.card V) {s t : V}
    (h : G.toSimpleGraph.Reachable s t) :
    10 * #{k : Fin (1000 * Fintype.card V ^ 3) → D |
        ∀ i ≤ 1000 * Fintype.card V ^ 3, G.walkAt (s, k) i ≠ t} ≤
      Fintype.card D ^ (1000 * Fintype.card V ^ 3) := by
  set n := Fintype.card V
  set T := 1000 * n ^ 3
  have hn : 1 ≤ n := Fintype.card_pos_iff.2 ⟨s⟩
  -- the survival probability is at most `1 / 10`
  have hsurv : 10 * survival G.randomWalk t T s ≤ 1 := by
    have hM := mul_survival_le_hittingTime (P := G.randomWalk) t T s
    have hH := hittingTime_randomWalk_le_of_reachable h
    have hnum : ((n - 1 : ℕ) : ℝ≥0∞) * (Fintype.card D * n) ≤ (n : ℝ≥0∞) ^ 3 := by
      have : (n - 1) * (Fintype.card D * n) ≤ n ^ 3 := by
        calc (n - 1) * (Fintype.card D * n) ≤ n * (n * n) := by gcongr; omega
          _ = n ^ 3 := by ring
      exact_mod_cast this
    have hT : (10 : ℝ≥0∞) * (n : ℝ≥0∞) ^ 3 ≤ (T : ℝ≥0∞) + 1 := by
      have : 10 * n ^ 3 ≤ T + 1 := by omega
      exact_mod_cast this
    have hn3 : (n : ℝ≥0∞) ^ 3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
    have hn3' : (n : ℝ≥0∞) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    have key : 10 * survival G.randomWalk t T s * (n : ℝ≥0∞) ^ 3 ≤ 1 * (n : ℝ≥0∞) ^ 3 := by
      calc 10 * survival G.randomWalk t T s * (n : ℝ≥0∞) ^ 3
          = (10 * (n : ℝ≥0∞) ^ 3) * survival G.randomWalk t T s := by ring
        _ ≤ ((T : ℝ≥0∞) + 1) * survival G.randomWalk t T s := by gcongr
        _ ≤ (n : ℝ≥0∞) ^ 3 := hM.trans (hH.trans hnum)
        _ = 1 * (n : ℝ≥0∞) ^ 3 := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left hn3 hn3').1 key
  have hc := survival_randomWalk_mul_pow (G := G) t T s
  have : (10 * #{k : Fin T → D | ∀ i ≤ T, G.walkAt (s, k) i ≠ t} : ℝ≥0∞) ≤
      (Fintype.card D : ℝ≥0∞) ^ T := by
    rw [← hc, ← mul_assoc]
    calc 10 * survival G.randomWalk t T s * (Fintype.card D : ℝ≥0∞) ^ T
        ≤ 1 * (Fintype.card D : ℝ≥0∞) ^ T := by gcongr
      _ = _ := one_mul _
  exact_mod_cast this

/-! ### Uniqueness of the stationary distribution -/

omit [DecidableEq V] in
/-- The uniform distribution is stationary for the random walk on a regular multigraph. -/
theorem isStationary_uniform_randomWalk [Nonempty V] :
    G.randomWalk.IsStationary (PMF.uniformOfFintype V) := by
  classical
  ext y
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← mul_sum]
  simp_rw [randomWalk_apply, G.edgeCount_comm _ y, div_eq_mul_inv, ← sum_mul]
  rw [← Nat.cast_sum, G.sum_edgeCount,
    ENNReal.mul_inv_cancel
          (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), mul_one]

omit [DecidableEq V] in
/-- **Arora–Barak, Exercise 7.9(b)(i).** On a connected regular multigraph, the uniform
distribution is the unique stationary distribution of the random walk. -/
theorem isStationary_randomWalk_iff (hG : G.toSimpleGraph.Connected) (π : PMF V) :
    G.randomWalk.IsStationary π ↔ π = @PMF.uniformOfFintype V _ hG.nonempty := by
  classical
  have := hG.nonempty
  refine ⟨fun h => ?_, fun h => h ▸ isStationary_uniform_randomWalk⟩
  -- stationarity as an averaging identity in `ℝ≥0∞`
  have hst : ∀ y, ∑ x, (G.edgeCount y x : ℝ≥0∞) * π x = Fintype.card D * π y := by
    intro y
    have hy : ∑ x, π x * G.randomWalk x y = π y := by
      rw [← tsum_fintype (L := .unconditional V), ← PMF.bind_apply]
      exact congrArg (· y) h
    rw [← hy, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [randomWalk_apply, G.edgeCount_comm x y, mul_comm (π x), ← mul_assoc,
      ENNReal.mul_div_cancel
          (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
  set f : V → ℝ := fun x => (π x).toReal
  have hf : ∀ y, ∑ x, (G.edgeCount y x : ℝ) * f x = Fintype.card D * f y := by
    intro y
    have := congrArg ENNReal.toReal (hst y)
    rw [ENNReal.toReal_sum fun x _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (π.apply_ne_top x), ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
    simpa [f, ENNReal.toReal_mul] using this
  obtain ⟨u⟩ := hG.nonempty
  have hconst : ∀ x, π x = π u := fun x =>
    (ENNReal.toReal_eq_toReal_iff' (π.apply_ne_top x) (π.apply_ne_top u)).1
      (eq_of_forall_sum_edgeCount_mul_eq hG.preconnected hf x u)
  have hsum : (Fintype.card V : ℝ≥0∞) * π u = 1 := by
    rw [← π.tsum_coe, tsum_fintype]
    simp [hconst]
  ext x
  rw [PMF.uniformOfFintype_apply, hconst x]
  exact (ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at hsum))

end Cslib.RotationMap
