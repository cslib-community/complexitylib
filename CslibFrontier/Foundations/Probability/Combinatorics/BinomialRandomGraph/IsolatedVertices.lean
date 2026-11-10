/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.Connectivity
import Mathlib.Probability.Moments.Variance

/-!
# Isolated vertices of binomial random graphs and disconnection below the threshold

The binomial random graph `G(n, p)` (Mathlib's `SimpleGraph.binomialRandom`) has an isolated vertex
with probability tending to `1` when `n p - log n → -∞` and to `0` when `n p - log n → ∞`. This is
the sharp threshold for isolated vertices, in the `G(n, p)` form of
[Frieze and Karoński, Lemma 1.11][FriezeKaronski2016] (stated there for `G(n, m)`). A connected
graph on `n ≥ 2` vertices has no isolated vertex, so `G(n, p)` is disconnected with probability
tending to `1` when `n p - log n → -∞`. This is the `c_n → -∞` case of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016] in `G(n, p)`. The `c_n → ∞` case is in
`CslibFrontier/Foundations/Probability/Combinatorics/BinomialRandomGraph/Connectivity.lean`.

Let `X` count the isolated vertices and `μ = n (1 - p) ^ (n - 1)`. A fixed vertex is isolated when
its `n - 1` possible edges are absent, and two distinct vertices are both isolated when the
`2 n - 3` possible edges at either are absent (both through
`SimpleGraph.binomialRandom_real_disjoint_edgeSet`). Hence `E[X] = μ` and
`E[X ^ 2] = μ + n (n - 1) (1 - p) ^ (2 n - 3)`. The union bound gives `P(X > 0) ≤ μ`. Chebyshev's
inequality (Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq`) gives
`P(X = 0) ≤ Var[X] / μ ^ 2 ≤ 1 / μ + p / (1 - p)` for `n ≥ 1` and `p < 1`. Below the threshold,
`p ≤ log n / n` eventually, so `p / (1 - p) → 0`, and `log (1 - p) ≥ -p / (1 - p)` gives
`1 / μ ≤ exp (n p - log n + 2 (log n) ^ 2 / n) → 0`.

The source computes the second moment the same way and concludes through
`P(X > 0) ≥ (E X) ^ 2 / E[X ^ 2]`; Chebyshev's inequality gives the same conclusion here. The
Poisson limit `P(X = 0) → e ^ (-e ^ (-c))` at `n p - log n → c`, and with it the constant case of
Theorem 4.1, is not formalized.

## Main results

* `SimpleGraph.binomialRandom_real_isIsolated`, `SimpleGraph.binomialRandom_real_isIsolated_and`:
  one vertex, respectively two distinct vertices, are isolated with probability
  `(1 - p) ^ (n - 1)`, respectively `(1 - p) ^ (2 n - 3)`.
* `SimpleGraph.integral_natCard_isIsolated`, `SimpleGraph.integral_natCard_isIsolated_sq`: the
  first two moments of the number of isolated vertices.
* `SimpleGraph.binomialRandom_real_exists_isIsolated_le`: `P(X > 0) ≤ n (1 - p) ^ (n - 1)`.
* `SimpleGraph.binomialRandom_real_forall_not_isIsolated_le`,
  `SimpleGraph.binomialRandom_real_connected_le`: `P(X = 0)` and `P(connected)` are at most
  `1 / μ + p / (1 - p)`.
* `SimpleGraph.tendsto_binomialRandom_real_exists_isIsolated_atTop`,
  `SimpleGraph.tendsto_binomialRandom_real_exists_isIsolated_atBot`: the sharp threshold for
  isolated vertices.
* `SimpleGraph.tendsto_binomialRandom_real_connected_atBot`: disconnection with high probability
  when `n p - log n → -∞`.

## References

* [A. Frieze, M. Karoński, *Introduction to Random Graphs*, Sections 1.2, 3.1 and
  4.1][FriezeKaronski2016]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V : Type*}

/-- The `|V| - 1` possible edges at `v`. -/
private noncomputable def incidentPairs [Fintype V] [DecidableEq V] (v : V) : Finset (Sym2 V) :=
  (univ.erase v).image fun w => s(v, w)

/-- There are `|V| - 1` possible edges at `v`. -/
private theorem card_incidentPairs [Fintype V] [DecidableEq V] (v : V) :
    #(incidentPairs v) = Fintype.card V - 1 := by
  rw [incidentPairs, card_image_of_injective _ (fun _ _ h => Sym2.congr_right.1 h),
    card_erase_of_mem (mem_univ _), card_univ]

/-- No possible edge at `v` is a loop. -/
private theorem not_isDiag_of_mem_incidentPairs [Fintype V] [DecidableEq V] {v : V} {e : Sym2 V}
    (he : e ∈ incidentPairs v) : ¬e.IsDiag := by
  simp only [incidentPairs, mem_image, mem_erase, mem_univ, and_true] at he
  obtain ⟨w, hw, rfl⟩ := he
  simpa using Ne.symm hw

/-- `v` is isolated exactly when no possible edge at `v` is present. -/
private theorem isIsolated_iff_disjoint_incidentPairs [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    G.IsIsolated v ↔ Disjoint (incidentPairs v : Set (Sym2 V)) G.edgeSet := by
  simp only [IsIsolated, Set.disjoint_left, incidentPairs, coe_image, coe_erase, coe_univ,
    Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  constructor
  · rintro h _ ⟨w, -, rfl⟩ hw
    exact h w hw
  · intro h w hw
    exact h ⟨w, hw.ne', rfl⟩ hw

/-- A fixed vertex of `G(V, p)` is isolated with probability `(1 - p) ^ (|V| - 1)`. -/
theorem binomialRandom_real_isIsolated [Fintype V] (p : I) (v : V) :
    G(V, p).real {G | G.IsIsolated v} = (1 - p : ℝ) ^ (Fintype.card V - 1) := by
  classical
  have : {G : SimpleGraph V | G.IsIsolated v} =
      {G | Disjoint (incidentPairs v : Set (Sym2 V)) G.edgeSet} := by
    ext G
    exact isIsolated_iff_disjoint_incidentPairs G v
  rw [this, binomialRandom_real_disjoint_edgeSet p _
    (fun _ => not_isDiag_of_mem_incidentPairs), card_incidentPairs]

/-- The possible edges at two distinct vertices share only the edge between them. -/
private theorem incidentPairs_inter [Fintype V] [DecidableEq V] {u v : V} (huv : u ≠ v) :
    incidentPairs u ∩ incidentPairs v = {s(u, v)} := by
  ext e
  simp only [incidentPairs, mem_inter, mem_image, mem_erase, mem_univ, and_true,
    mem_singleton]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, ⟨w', hw', h⟩⟩
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1 huv.symm
    · rw [h1]
  · rintro rfl
    exact ⟨⟨v, huv.symm, rfl⟩, ⟨u, huv, Sym2.eq_swap⟩⟩

/-- Two distinct fixed vertices of `G(V, p)` are both isolated with probability
`(1 - p) ^ (2 |V| - 3)`: the `2 (|V| - 2) + 1` possible edges at `u` or `v` are all absent. -/
theorem binomialRandom_real_isIsolated_and [Fintype V] (p : I) {u v : V} (huv : u ≠ v) :
    G(V, p).real {G | G.IsIsolated u ∧ G.IsIsolated v} =
      (1 - p : ℝ) ^ (2 * Fintype.card V - 3) := by
  classical
  have : {G : SimpleGraph V | G.IsIsolated u ∧ G.IsIsolated v} =
      {G | Disjoint ((incidentPairs u ∪ incidentPairs v : Finset (Sym2 V)) : Set (Sym2 V))
        G.edgeSet} := by
    ext G
    simp only [Set.mem_ofPred_eq, isIsolated_iff_disjoint_incidentPairs, coe_union,
      Set.disjoint_union_left]
  have h2 : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.2 ⟨u, v, huv⟩
  rw [this, binomialRandom_real_disjoint_edgeSet p _ (fun e he => by
    rcases mem_union.1 he with he | he <;> exact not_isDiag_of_mem_incidentPairs he)]
  have hc := card_union_add_card_inter (incidentPairs u) (incidentPairs v)
  rw [incidentPairs_inter huv, card_singleton, card_incidentPairs, card_incidentPairs] at hc
  congr 1
  omega


/-! ### Moments of the number of isolated vertices -/

/-- The number of isolated vertices is a sum of indicators. -/
private theorem natCard_isIsolated_eq_sum [Fintype V] (G : SimpleGraph V) :
    (Nat.card {v // G.IsIsolated v} : ℝ) =
      ∑ v, {G' : SimpleGraph V | G'.IsIsolated v}.indicator 1 G := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, natCast_card_filter]
  refine sum_congr rfl fun v _ => ?_
  by_cases h : G.IsIsolated v <;> simp [h]

/-- **First moment**: `G(V, p)` has `|V| (1 - p) ^ (|V| - 1)` isolated vertices on average. -/
theorem integral_natCard_isIsolated [Fintype V] (p : I) :
    ∫ G, (Nat.card {v // G.IsIsolated v} : ℝ) ∂G(V, p) =
      Fintype.card V * (1 - p : ℝ) ^ (Fintype.card V - 1) := by
  simp_rw [natCard_isIsolated_eq_sum]
  rw [integral_finsetSum _ fun v _ => Integrable.of_finite]
  simp_rw [integral_indicator_one MeasurableSet.of_discrete, binomialRandom_real_isIsolated]
  simp

/-- **Second moment** of the number `X` of isolated vertices of `G(V, p)`:
`E[X ^ 2] = |V| (1 - p) ^ (|V| - 1) + |V| (|V| - 1) (1 - p) ^ (2 |V| - 3)`. -/
theorem integral_natCard_isIsolated_sq [Fintype V] (p : I) :
    ∫ G, (Nat.card {v // G.IsIsolated v} : ℝ) ^ 2 ∂G(V, p) =
      Fintype.card V * (1 - p : ℝ) ^ (Fintype.card V - 1) +
        Fintype.card V * (Fintype.card V - 1) * (1 - p : ℝ) ^ (2 * Fintype.card V - 3) := by
  classical
  have hmul : ∀ (s t : Set (SimpleGraph V)) (G : SimpleGraph V),
      s.indicator (1 : SimpleGraph V → ℝ) G * t.indicator 1 G = (s ∩ t).indicator 1 G := by
    intro s t G
    rw [Set.inter_indicator_one, Pi.mul_apply]
  simp_rw [natCard_isIsolated_eq_sum, sq, sum_mul_sum, hmul]
  rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => Integrable.of_finite]
  simp_rw [integral_finsetSum _ fun v _ => Integrable.of_finite,
    integral_indicator_one MeasurableSet.of_discrete]
  have hrow : ∀ u : V, ∑ v, G(V, p).real ({G | G.IsIsolated u} ∩ {G | G.IsIsolated v}) =
      (1 - p : ℝ) ^ (Fintype.card V - 1) +
        (Fintype.card V - 1) * (1 - p : ℝ) ^ (2 * Fintype.card V - 3) := by
    intro u
    rw [← add_sum_erase _ _ (mem_univ u), Set.inter_self, binomialRandom_real_isIsolated]
    rw [sum_congr rfl fun v hv => by
      rw [← Set.ofPred_and, binomialRandom_real_isIsolated_and p (ne_of_mem_erase hv).symm]]
    rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
      Nat.cast_sub (Fintype.card_pos_iff.2 ⟨u⟩), Nat.cast_one]
  simp_rw [hrow]
  rw [sum_const, card_univ, nsmul_eq_mul]
  ring


/-! ### Explicit bounds -/

/-- **First moment method**: `G(V, p)` has an isolated vertex with probability at most
`|V| (1 - p) ^ (|V| - 1)`. -/
theorem binomialRandom_real_exists_isIsolated_le [Fintype V] (p : I) :
    G(V, p).real {G | ∃ v, G.IsIsolated v} ≤
      Fintype.card V * (1 - p : ℝ) ^ (Fintype.card V - 1) := by
  have : {G : SimpleGraph V | ∃ v, G.IsIsolated v} = ⋃ v, {G | G.IsIsolated v} := by
    ext G
    simp
  rw [this]
  refine (measureReal_iUnion_fintype_le _).trans_eq ?_
  simp_rw [binomialRandom_real_isIsolated]
  simp

/-- The algebra behind the second-moment bound: with `μ = n (1 - p) ^ (n - 1)`,
`(n (n - 1) (1 - p) ^ (2 n - 3) + μ - μ ^ 2) / μ ^ 2 ≤ 1 / μ + p / (1 - p)`. -/
private theorem variance_div_sq_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 1) :
    (n * (n - 1) * (1 - p) ^ (2 * n - 3) + n * (1 - p) ^ (n - 1) - (n * (1 - p) ^ (n - 1)) ^ 2) /
      (n * (1 - p) ^ (n - 1)) ^ 2 ≤ 1 / (n * (1 - p) ^ (n - 1)) + p / (1 - p) := by
  have hq : 0 < 1 - p := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · norm_num
    have := div_nonneg hp0 hq.le
    linarith
  · rw [show 2 * (m + 1 + 1) - 3 = 2 * m + 1 by omega, show m + 1 + 1 - 1 = m + 1 by omega]
    push_cast
    have hN : (m + 1 + 1 : ℝ) ≠ 0 := by positivity
    have hq' : (1 - p) ≠ 0 := hq.ne'
    calc _ = 1 / ((m + 1 + 1 : ℝ) * (1 - p) ^ (m + 1)) + p / (1 - p) -
          1 / ((m + 1 + 1 : ℝ) * (1 - p)) := by
          field_simp
          ring
      _ ≤ _ := by
          have : 0 < 1 / ((m + 1 + 1 : ℝ) * (1 - p)) := by positivity
          linarith

/-- **Second moment method**: if `|V| ≥ 1` and `p < 1`, then `G(V, p)` has no isolated vertex with
probability at most `1 / μ + p / (1 - p)`, where `μ = |V| (1 - p) ^ (|V| - 1)` is the expected
number of isolated vertices. -/
theorem binomialRandom_real_forall_not_isIsolated_le [Fintype V] [Nonempty V] (p : I)
    (hp : (p : ℝ) < 1) :
    G(V, p).real {G | ∀ v, ¬G.IsIsolated v} ≤
      1 / (Fintype.card V * (1 - p : ℝ) ^ (Fintype.card V - 1)) + p / (1 - p) := by
  set n := Fintype.card V with hn
  set X : SimpleGraph V → ℝ := fun G => (Nat.card {v // G.IsIsolated v} : ℝ) with hX
  set μ : ℝ := n * (1 - p : ℝ) ^ (n - 1) with hμ
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hq0 : (0 : ℝ) < 1 - p := by linarith
  have hμ0 : 0 < μ := by
    rw [hμ]
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    positivity
  have hE : ∫ G, X G ∂G(V, p) = μ := integral_natCard_isIsolated p
  have hE2 : ∫ G, X G ^ 2 ∂G(V, p) = μ + n * (n - 1) * (1 - p : ℝ) ^ (2 * n - 3) :=
    integral_natCard_isIsolated_sq p
  have hmem : MemLp X 2 G(V, p) := MemLp.of_discrete
  have hsub : {G : SimpleGraph V | ∀ v, ¬G.IsIsolated v} ⊆
      {G | μ ≤ |X G - ∫ G, X G ∂G(V, p)|} := by
    intro G hG
    have : X G = 0 := by
      simp only [hX, Nat.cast_eq_zero]
      exact Nat.card_eq_zero.2 (Or.inl ⟨fun v => hG v.1 v.2⟩)
    simp only [Set.mem_ofPred_eq, this, hE, zero_sub, abs_neg, abs_of_pos hμ0, le_refl]
  have hvar : variance X G(V, p) = n * (n - 1) * (1 - p : ℝ) ^ (2 * n - 3) + μ - μ ^ 2 := by
    rw [variance_eq_sub hmem, ← hE]
    change ∫ G, X G ^ 2 ∂G(V, p) - _ = _
    rw [hE2, hE]
    ring
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [measureReal_def]
  refine (ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))
    (meas_ge_le_variance_div_sq hmem hμ0)).trans ?_
  rw [hvar]
  exact variance_div_sq_le hn1 (unitInterval.nonneg p) hp

/-- A connected graph on at least two vertices has no isolated vertex. -/
private theorem setOf_connected_subset [Nontrivial V] :
    {G : SimpleGraph V | G.Connected} ⊆ {G | ∀ v, ¬G.IsIsolated v} :=
  fun _ hG v => (Connected.preconnected hG).not_isIsolated v

/-- If `|V| ≥ 2` and `p < 1`, then `G(V, p)` is connected with probability at most
`1 / μ + p / (1 - p)`, where `μ = |V| (1 - p) ^ (|V| - 1)`. -/
theorem binomialRandom_real_connected_le [Fintype V] [Nontrivial V] (p : I) (hp : (p : ℝ) < 1) :
    G(V, p).real {G | G.Connected} ≤
      1 / (Fintype.card V * (1 - p : ℝ) ^ (Fintype.card V - 1)) + p / (1 - p) :=
  (measureReal_mono setOf_connected_subset (measure_ne_top _ _)).trans
    (binomialRandom_real_forall_not_isIsolated_le p hp)

/-! ### Asymptotics -/

/-- The numerical inequality behind the lower half: if `n ≥ 1`, `0 ≤ p ≤ 1 / 2` and
`n p ≤ log n`, then `1 / (n (1 - p) ^ (n - 1)) ≤ exp (n p - log n + 2 (log n) ^ 2 / n)`. -/
private theorem one_div_mul_one_sub_pow_le {n : ℕ} (hn : 0 < n) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p ≤ 1 / 2) (hL : n * p ≤ Real.log n) :
    1 / (n * (1 - p) ^ (n - 1)) ≤ Real.exp (n * p - Real.log n + 2 * (Real.log n ^ 2 / n)) := by
  have hq : 0 < 1 - p := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : -(p / (1 - p)) ≤ Real.log (1 - p) := by
    have := Real.one_sub_inv_le_log_of_pos hq
    rwa [show 1 - (1 - p)⁻¹ = -(p / (1 - p)) by field_simp; ring] at this
  have h1' : Real.exp (-(p / (1 - p))) ≤ 1 - p :=
    (Real.exp_le_exp.2 h1).trans_eq (Real.exp_log hq)
  have h2 : p / (1 - p) ≤ p + 2 * p ^ 2 := by
    rw [div_le_iff₀ hq]
    nlinarith [sq_nonneg p]
  have h3 : n * p ^ 2 ≤ Real.log n ^ 2 / n := by
    rw [le_div_iff₀ hn0]
    have := mul_self_le_mul_self (mul_nonneg hn0.le hp0) hL
    nlinarith
  have h4 : Real.exp (-(n * (p / (1 - p)))) ≤ (1 - p) ^ (n - 1) := by
    have hr : 0 ≤ p / (1 - p) := div_nonneg hp0 hq.le
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc Real.exp (-(n * (p / (1 - p)))) ≤ Real.exp (-((n - 1 : ℕ) * (p / (1 - p)))) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = Real.exp (-(p / (1 - p))) ^ (n - 1) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (1 - p) ^ (n - 1) := pow_le_pow_left₀ (Real.exp_pos _).le h1' _
  have h5 : Real.exp (-(n * p + 2 * (Real.log n ^ 2 / n))) ≤ (1 - p) ^ (n - 1) := by
    refine le_trans (Real.exp_le_exp.2 ?_) h4
    have := mul_le_mul_of_nonneg_left h2 hn0.le
    nlinarith
  have e : Real.exp (n * p - Real.log n + 2 * (Real.log n ^ 2 / n)) * n =
      Real.exp (n * p + 2 * (Real.log n ^ 2 / n)) := by
    rw [show n * p - Real.log n + 2 * (Real.log n ^ 2 / n) =
        (n * p + 2 * (Real.log n ^ 2 / n)) + -Real.log n by ring, Real.exp_add, Real.exp_neg,
      Real.exp_log hn0]
    field_simp
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = Real.exp (n * p + 2 * (Real.log n ^ 2 / n)) *
        Real.exp (-(n * p + 2 * (Real.log n ^ 2 / n))) := by rw [← Real.exp_add]; simp
    _ ≤ Real.exp (n * p + 2 * (Real.log n ^ 2 / n)) * (1 - p) ^ (n - 1) := by gcongr
    _ = _ := by rw [← e]; ring

/-- **Isolated vertices above the threshold**, the `G(n, p)` form of
[Frieze and Karoński, Lemma 1.11][FriezeKaronski2016]: if `n p(n) - log n → ∞`, then `G(n, p(n))`
has an isolated vertex with probability tending to `0`. -/
theorem tendsto_binomialRandom_real_exists_isIsolated_atTop {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n) atTop atTop) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∃ v, G.IsIsolated v}) atTop (𝓝 0) := by
  have hy : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(n * (p n : ℝ)))) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hp).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply, neg_sub]
    rw [Real.exp_sub, Real.exp_log hn0, Real.exp_neg, div_eq_mul_inv]
  have h := hy.const_mul (Real.exp 1)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => measureReal_nonneg) (fun n => ?_)
  refine (binomialRandom_real_exists_isIsolated_le (p n)).trans ?_
  rw [Fintype.card_fin]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hp1 : (p n : ℝ) ≤ 1 := unitInterval.le_one (p n)
  have h1 : (1 - p n : ℝ) ^ (n - 1) ≤ Real.exp (-(p n * ((n : ℝ) - 1))) := by
    calc (1 - p n : ℝ) ^ (n - 1) ≤ Real.exp (-(p n : ℝ)) ^ (n - 1) :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _
      _ = _ := by rw [← Real.exp_nat_mul, Nat.cast_sub hn, Nat.cast_one]; congr 1; ring
  have h2 : Real.exp (-(p n * ((n : ℝ) - 1))) ≤ Real.exp 1 * Real.exp (-(n * p n)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc (n : ℝ) * (1 - p n) ^ (n - 1) ≤ n * (Real.exp 1 * Real.exp (-(n * p n))) := by
        gcongr
        exact h1.trans h2
    _ = _ := by ring

/-- **No isolated vertex is unlikely below the threshold**: if `n p(n) - log n → -∞`, then
`G(n, p(n))` has no isolated vertex with probability tending to `0`. -/
theorem tendsto_binomialRandom_real_forall_not_isIsolated {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n) atTop atBot) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ v, ¬G.IsIsolated v}) atTop (𝓝 0) := by
  have hle : ∀ᶠ n : ℕ in atTop, (n : ℝ) * p n ≤ Real.log n := by
    filter_upwards [hp.eventually (eventually_le_atBot 0)] with n hn
    linarith
  have hlog1 : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hlog2 : Tendsto (fun n : ℕ => Real.log n ^ 2 / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hp0 : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog1
      (Eventually.of_forall fun n => unitInterval.nonneg (p n)) ?_
    filter_upwards [hle, eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [le_div_iff₀ this]
    linarith
  have hhalf : ∀ᶠ n in atTop, (p n : ℝ) ≤ 1 / 2 :=
    hp0.eventually (eventually_le_nhds (by norm_num))
  have hratio : Tendsto (fun n => (p n : ℝ) / (1 - p n)) atTop (𝓝 0) := by
    have := hp0.div ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp0)
      (by norm_num)
    rw [sub_zero, div_one] at this
    exact this
  have hexp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n + 2 * (Real.log n ^ 2 / n))
      atTop atBot := by
    have := hp.atBot_add (hlog2.const_mul 2)
    simpa using this
  have hinv : Tendsto (fun n : ℕ => 1 / (n * (1 - p n : ℝ) ^ (n - 1))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (Real.tendsto_exp_atBot.comp hexp) ?_ ?_
    · filter_upwards [hhalf] with n hn
      have : (0 : ℝ) < 1 - p n := by linarith
      positivity
    · filter_upwards [hle, hhalf, eventually_gt_atTop 0] with n hn hn' hn0
      exact one_div_mul_one_sub_pow_le hn0 (unitInterval.nonneg (p n)) hn' hn
  have hsum := hinv.add hratio
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => measureReal_nonneg) ?_
  filter_upwards [hhalf, eventually_gt_atTop 0] with n hn hn0
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have h := binomialRandom_real_forall_not_isIsolated_le (V := Fin n) (p n) (by linarith)
  rwa [Fintype.card_fin] at h

/-- **Isolated vertices below the threshold**, the `G(n, p)` form of
[Frieze and Karoński, Lemma 1.11][FriezeKaronski2016]: if `n p(n) - log n → -∞`, then
`G(n, p(n))` has an isolated vertex with probability tending to `1`. -/
theorem tendsto_binomialRandom_real_exists_isIsolated_atBot {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n) atTop atBot) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∃ v, G.IsIsolated v}) atTop (𝓝 1) := by
  have h := (tendsto_binomialRandom_real_forall_not_isIsolated hp).const_sub 1
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [← probReal_compl_eq_one_sub .of_discrete]
  congr 1
  ext G
  simp

/-- **Disconnection below the threshold**, the `G(n, p)` form of the case `c_n → -∞` of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016]: if `n p(n) - log n → -∞`, then
`G(n, p(n))` is connected with probability tending to `0`. -/
theorem tendsto_binomialRandom_real_connected_atBot {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n) atTop atBot) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | G.Connected}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_binomialRandom_real_forall_not_isIsolated hp)
    (Eventually.of_forall fun n => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  exact measureReal_mono setOf_connected_subset (measure_ne_top _ _)

end SimpleGraph
