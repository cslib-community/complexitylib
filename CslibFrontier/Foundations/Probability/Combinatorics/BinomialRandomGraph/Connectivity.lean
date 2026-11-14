/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.MeasureTheory.Constructions.SimpleGraph
public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgePattern
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Connectivity of binomial random graphs above the threshold

The binomial random graph `G(n, p)` (Mathlib's `SimpleGraph.binomialRandom`) is connected with
probability tending to `1` once `n p - log n → ∞`: this is the upper half of the Erdős–Rényi
connectivity threshold `p = log n / n`, in the `G(n, p)` form proved in the proof of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016] and cited in their Section 4.2.

The proof is a union bound over vertex cuts. A graph on `n ≥ 1` vertices that is not connected
has a vertex set `S` with `1 ≤ |S| ≤ n / 2` and no edge between `S` and its complement
(`SimpleGraph.exists_forall_not_adj_of_not_connected`, in
`CslibFrontier/Foundations/Combinatorics/SimpleGraph/Connectivity/Connected.lean`). In `G(V, p)`
none of the edges in a fixed set `t` of non-diagonal edges is present with probability
`(1 - p) ^ |t|` (`SimpleGraph.binomialRandom_real_disjoint_edgeSet`), so a fixed cut is empty
with probability `(1 - p) ^ (|S| (n - |S|))` (`SimpleGraph.binomialRandom_real_forall_not_adj`),
and

`P(G(n, p) is not connected) ≤ ∑_{k = 1}^{⌊n / 2⌋} C(n, k) (1 - p) ^ (k (n - k))`

(`SimpleGraph.binomialRandom_real_not_connected_le_sum`). Bounding the terms by
`C(n, k) ≤ n ^ k / k!`, `k ^ k / k! ≤ e ^ k` and `1 - p ≤ exp (-p)` turns this into an explicit
bound: if `n ≥ 1` and `n exp (-(n p)) ≤ 1 / 64`, then `G(n, p)` is disconnected with probability
at most `35 n exp (-(n p))` (`SimpleGraph.binomialRandom_real_not_connected_le`). For small `p`
the quantity `n exp (-(n p))` is close to `n (1 - p) ^ (n - 1)`, the expected number of isolated
vertices. The asymptotic forms are `SimpleGraph.tendsto_binomialRandom_real_not_connected` and
`SimpleGraph.tendsto_binomialRandom_real_connected`.

The source proof bounds the number of components of each order through their spanning trees;
the cut-based union bound used here is a standard simplification, and the constants `1 / 64` and
`35` are ours. The lower half (`n p - log n → -∞`) is in
`CslibFrontier/Foundations/Probability/Combinatorics/BinomialRandomGraph/IsolatedVertices.lean`,
and the threshold limit `e ^ (-e ^ (-c))` at `p = (log n + c) / n` is in the sibling module
`BinomialRandomGraph.ConnectivityThreshold`.

Measurability comes from `CslibFrontier/Foundations/MeasureTheory/Constructions/SimpleGraph.lean`:
for finite `V` the measurable space on `SimpleGraph V` is discrete, so every event about a random
graph on finitely many vertices is measurable.

## Main results

* `SimpleGraph.binomialRandom_real_forall_not_adj`: a fixed vertex cut is empty with probability
  `(1 - p) ^ (|S| (|V| - |S|))`.
* `SimpleGraph.binomialRandom_real_not_connected_le_sum`: the union bound over cuts.
* `SimpleGraph.binomialRandom_real_not_connected_le`: the explicit bound
  `35 n exp (-(n p))`.
* `SimpleGraph.tendsto_binomialRandom_real_not_connected`,
  `SimpleGraph.tendsto_binomialRandom_real_connected`: connectivity with high probability when
  `n p - log n → ∞`.

## References

* [A. Frieze, M. Karoński, *Introduction to Random Graphs*, Section 4.1][FriezeKaronski2016]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V : Type*}

/-- `G(V, p)` has no edge between a vertex set `S` and its complement with probability
`(1 - p) ^ (|S| (|V| - |S|))`. -/
theorem binomialRandom_real_forall_not_adj [Fintype V] (p : I) (S : Finset V) :
    G(V, p).real {G | ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
      (1 - p : ℝ) ^ (#S * (Fintype.card V - #S)) := by
  classical
  let t : Finset (Sym2 V) := (S ×ˢ Sᶜ).image Sym2.mk.uncurry
  have hset : {G : SimpleGraph V | ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
      {G | Disjoint (t : Set (Sym2 V)) G.edgeSet} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.disjoint_left, Finset.mem_coe, t, Finset.mem_image,
      Finset.mem_product, Finset.mem_compl]
    constructor
    · rintro h _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
      exact h u hu v hv
    · intro h u hu v hv huv
      exact h ⟨(u, v), ⟨hu, hv⟩, rfl⟩ huv
  have hdiag : ∀ e ∈ t, ¬e.IsDiag := by
    simp only [t, Finset.mem_image, Finset.mem_product, Finset.mem_compl]
    rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ huv
    exact hv (Sym2.mk_isDiag_iff.1 huv ▸ hu)
  have hcard : #t = #S * (Fintype.card V - #S) := by
    have hinj : Set.InjOn Sym2.mk.uncurry (↑(S ×ˢ Sᶜ) : Set (V × V)) := by
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_compl] at huv huv'
      have heq : s(u, v) = s(u', v') := h
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd huv.1 huv'.2
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_compl]
  rw [hset, binomialRandom_real_disjoint_edgeSet p t hdiag, hcard]

/-- **Union bound over cuts**: `G(V, p)` on `n ≥ 1` vertices is disconnected with probability at
most `∑_{k = 1}^{⌊n / 2⌋} C(n, k) (1 - p) ^ (k (n - k))`. -/
theorem binomialRandom_real_not_connected_le_sum [Fintype V] [Nonempty V] (p : I) :
    G(V, p).real {G | ¬G.Connected} ≤
      ∑ k ∈ Icc 1 (Fintype.card V / 2),
        ((Fintype.card V).choose k : ℝ) * (1 - p : ℝ) ^ (k * (Fintype.card V - k)) := by
  classical
  set n := Fintype.card V
  have hsub : {G : SimpleGraph V | ¬G.Connected} ⊆
      ⋃ k ∈ Icc 1 (n / 2), ⋃ S ∈ powersetCard k (univ : Finset V),
        {G | ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} := by
    intro G hG
    obtain ⟨S, hS1, hS2, hS⟩ := exists_forall_not_adj_of_not_connected hG
    simp only [Set.mem_iUnion, mem_Icc, mem_powersetCard, subset_univ, true_and,
      Set.mem_ofPred_eq, exists_prop]
    exact ⟨#S, ⟨hS1, by omega⟩, S, rfl, hS⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun k _ => ?_)
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  rw [sum_congr rfl fun S hS => by
    rw [binomialRandom_real_forall_not_adj, (mem_powersetCard.1 hS).2]]
  rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul]

/-! ### Explicit bound -/

/-- `(1 - p) ^ m ≤ exp (-(p m))`. -/
private theorem one_sub_pow_le_exp (p : I) (m : ℕ) :
    (1 - p : ℝ) ^ m ≤ Real.exp (-(p * m)) :=
  Real.one_sub_pow_le_exp (unitInterval.le_one p) (by rw [mul_comm])

/-- The `k`-th term of the union bound is at most `(n e exp (-(p (n - k))) / k) ^ k`. -/
private theorem choose_mul_pow_le {n k : ℕ} (hkn : k ≤ n) (p : I) :
    (n.choose k : ℝ) * (1 - p : ℝ) ^ (k * (n - k)) ≤
      ((n : ℝ) * Real.exp 1 * Real.exp (-(p * ((n : ℝ) - k))) / k) ^ k := by
  have hq : (1 - p : ℝ) ^ (n - k) ≤ Real.exp (-(p * ((n : ℝ) - k))) := by
    have := one_sub_pow_le_exp p (n - k)
    rwa [Nat.cast_sub hkn] at this
  have hp0 : (0 : ℝ) ≤ 1 - p := by linarith [unitInterval.le_one p]
  calc (n.choose k : ℝ) * (1 - p : ℝ) ^ (k * (n - k))
      ≤ ((n : ℝ) * Real.exp 1 / k) ^ k * ((1 - p : ℝ) ^ (n - k)) ^ k := by
        rw [← pow_mul, mul_comm (n - k) k]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_comm (n : ℝ)] using Nat.choose_le_exp_mul_div_pow n k)
          (by positivity)
    _ ≤ ((n : ℝ) * Real.exp 1 / k) ^ k * Real.exp (-(p * ((n : ℝ) - k))) ^ k := by
        gcongr
    _ = ((n : ℝ) * Real.exp 1 * Real.exp (-(p * ((n : ℝ) - k))) / k) ^ k := by
        rw [← mul_pow, div_mul_eq_mul_div]

/-- The numerical inequality behind the explicit bound: for `1 ≤ K`, `2 K ≤ N` and
`log N ≤ N p`, `N e ^ 2 exp (-(p (N - 2 K))) ≤ 16 K ^ 2`. -/
private theorem mul_exp_two_mul_exp_le {N K p : ℝ} (hK : 1 ≤ K) (hNK : 2 * K ≤ N)
    (hL : Real.log N ≤ N * p) :
    N * Real.exp 2 * Real.exp (-(p * (N - 2 * K))) ≤ 16 * K ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hE := Real.exp_one_gt_d9
  have hl2 := Real.log_two_gt_d9
  have h1 : Real.log (N / (K * Real.exp 1)) ≤ N / (K * Real.exp 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hN0.ne' (by positivity), Real.log_mul hK0.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at h1
  have h2 : K * (Real.log N - Real.log K) ≤ N / Real.exp 1 := by
    have h := mul_le_mul_of_nonneg_left h1 hK0.le
    have e1 : K * (N / (K * Real.exp 1) - 1) = N / Real.exp 1 - K := by
      field_simp
    linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have h3 : K * Real.log N ≤ N / Real.exp 1 + N * Real.log K := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ N - K) hlogK]
  have hp : Real.log N / N ≤ p := by rw [div_le_iff₀ hN0]; linarith
  have h4 : Real.log N - p * (N - 2 * K) ≤ 2 * K * Real.log N / N := by
    have h := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ N - 2 * K)
    have e2 : Real.log N / N * (N - 2 * K) = Real.log N - 2 * K * Real.log N / N := by
      field_simp
    linarith
  have h5 : 2 * K * Real.log N / N ≤ 2 / Real.exp 1 + 2 * Real.log K := by
    rw [div_le_iff₀ hN0]
    linear_combination 2 * h3
  have hinv : 2 / Real.exp 1 < 0.74 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]; norm_num at hE ⊢; linarith
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hK2 : Real.log (K ^ 2) = 2 * Real.log K := by rw [Real.log_pow]; norm_num
  have h6 : Real.log N + 2 - p * (N - 2 * K) ≤ Real.log 16 + Real.log (K ^ 2) := by
    rw [h16, hK2]; norm_num at hl2; linarith
  calc N * Real.exp 2 * Real.exp (-(p * (N - 2 * K)))
      = Real.exp (Real.log N + 2 - p * (N - 2 * K)) := by
        rw [show Real.log N + 2 - p * (N - 2 * K) = Real.log N + 2 + -(p * (N - 2 * K)) by ring,
          Real.exp_add, Real.exp_add, Real.exp_log hN0]
    _ ≤ Real.exp (Real.log 16 + Real.log (K ^ 2)) := Real.exp_le_exp.2 h6
    _ = 16 * K ^ 2 := by
        rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by positivity)]

/-- **Connectivity above the threshold, explicit form**: if `n ≥ 1` and
`n exp (-(n p)) ≤ 1 / 64`, then `G(n, p)` is disconnected with probability at most
`35 n exp (-(n p))`. -/
theorem binomialRandom_real_not_connected_le {n : ℕ} (hn : 0 < n) (p : I)
    (hy : n * Real.exp (-(n * p)) ≤ 1 / 64) :
    G(Fin n, p).real {G | ¬G.Connected} ≤ 35 * (n * Real.exp (-(n * p))) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set y : ℝ := n * Real.exp (-(n * p)) with hydef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 ≤ y := by positivity
  have hL : Real.log n ≤ n * p := by
    have h : Real.log y ≤ 0 := Real.log_nonpos hy0 (by linarith)
    rw [hydef, Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
  refine (binomialRandom_real_not_connected_le_sum p).trans ?_
  rw [Fintype.card_fin]
  set m := n / 2 with hm
  let r : ℕ → ℝ := fun k => (n : ℝ) * Real.exp 1 * Real.exp (-(p * ((n : ℝ) - k))) / k
  have hterm : ∀ k ∈ Icc 1 m, (n.choose k : ℝ) * (1 - p : ℝ) ^ (k * (n - k)) ≤ r k ^ k :=
    fun k hk => choose_mul_pow_le (by rw [mem_Icc] at hk; omega) p
  have hr : ∀ k ∈ Icc 1 m, r k ^ 2 ≤ 16 * y := by
    intro k hk
    rw [mem_Icc] at hk
    have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hNK : 2 * (k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
    have key := mul_exp_two_mul_exp_le hK hNK hL
    have hk0 : (0 : ℝ) < k := by linarith
    have e1 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    have e2 : Real.exp (-(p * ((n : ℝ) - k))) ^ 2 =
        Real.exp (-(n * p)) * Real.exp (-(p * (n - 2 * k))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    change ((n : ℝ) * Real.exp 1 * Real.exp (-(p * ((n : ℝ) - k))) / k) ^ 2 ≤ 16 * y
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc ((n : ℝ) * Real.exp 1 * Real.exp (-(p * ((n : ℝ) - k)))) ^ 2
        = y * (n * Real.exp 2 * Real.exp (-(p * (n - 2 * k)))) := by
          rw [mul_pow, mul_pow, e1, e2, hydef]; ring
      _ ≤ y * (16 * k ^ 2) := mul_le_mul_of_nonneg_left key hy0
      _ = 16 * y * k ^ 2 := by ring
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · rw [hm0, Icc_eq_empty (by norm_num), sum_empty]; positivity
  have h1mem : 1 ∈ Icc 1 m := mem_Icc.2 ⟨le_rfl, hm0⟩
  have hrest : (Icc 1 m).erase 1 = Icc 2 m := by
    ext k
    simp only [mem_erase, mem_Icc]
    omega
  rw [← add_sum_erase _ _ h1mem, hrest]
  -- the term `k = 1`
  have hone : (n.choose 1 : ℝ) * (1 - p : ℝ) ^ (1 * (n - 1)) ≤ Real.exp 1 * y := by
    rw [Nat.choose_one_right, one_mul]
    have h := one_sub_pow_le_exp p (n - 1)
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
    have hp1 : (p : ℝ) ≤ 1 := unitInterval.le_one p
    calc (n : ℝ) * (1 - p : ℝ) ^ (n - 1) ≤ n * Real.exp (-(p * ((n : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left h hn0.le
      _ = Real.exp p * y := by
          rw [hydef, ← mul_assoc, mul_comm (Real.exp _) (n : ℝ), mul_assoc, ← Real.exp_add]
          congr 2; ring
      _ ≤ Real.exp 1 * y := by gcongr
  -- the terms `k ≥ 2`
  have hgeom : ∀ k ∈ Icc 2 m, (n.choose k : ℝ) * (1 - p : ℝ) ^ (k * (n - k)) ≤
      64 * y * (1 / 2) ^ k := by
    intro k hk
    have hk' : k ∈ Icc 1 m := by rw [mem_Icc] at hk ⊢; omega
    refine (hterm k hk').trans ?_
    have h2 := hr k hk'
    have hk0 : (0 : ℝ) < k := by rw [mem_Icc] at hk'; exact_mod_cast hk'.1
    have hr0 : 0 ≤ r k := by positivity
    have hhalf : r k ≤ 1 / 2 := by nlinarith
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by rw [mem_Icc] at hk; omega⟩
    calc r (j + 2) ^ (j + 2) = r (j + 2) ^ 2 * r (j + 2) ^ j := by ring
      _ ≤ 16 * y * (1 / 2) ^ j := by gcongr
      _ = 64 * y * (1 / 2) ^ (j + 2) := by ring
  have hsum : ∑ k ∈ Icc 2 m, 64 * y * (1 / 2 : ℝ) ^ k ≤ 32 * y := by
    rw [← mul_sum, ← Finset.Ico_add_one_right_eq_Icc]
    have := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℝ)) (m := 2) (n := m + 1)
      (by norm_num) (by norm_num)
    nlinarith
  have hE := Real.exp_one_lt_d9
  nlinarith [sum_le_sum hgeom]

/-- **Connectivity above the threshold**, the `G(n, p)` form from the proof of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016]: if `n p(n) - log n → ∞`, then
`G(n, p(n))` is disconnected with probability tending to `0`. -/
theorem tendsto_binomialRandom_real_not_connected {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n) atTop atTop) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ¬G.Connected}) atTop (𝓝 0) := by
  have hy : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(n * (p n : ℝ)))) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hp).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply, neg_sub]
    rw [Real.exp_sub, Real.exp_log hn0, Real.exp_neg, div_eq_mul_inv]
  have h35 := hy.const_mul 35
  rw [mul_zero] at h35
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h35
    (Eventually.of_forall fun n => measureReal_nonneg) ?_
  filter_upwards [hy.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
    eventually_gt_atTop 0] with n hn hn0
  exact binomialRandom_real_not_connected_le hn0 (p n) hn

/-- **Connectivity above the threshold**, the `G(n, p)` form from the proof of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016]: if `n p(n) - log n → ∞`, then
`G(n, p(n))` is connected with probability tending to `1`. -/
theorem tendsto_binomialRandom_real_connected {p : ℕ → I}
    (hp : Tendsto (fun n : ℕ => n * (p n : ℝ) - Real.log n) atTop atTop) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | G.Connected}) atTop (𝓝 1) := by
  have h := (tendsto_binomialRandom_real_not_connected hp).const_sub 1
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [← probReal_compl_eq_one_sub .of_discrete]
  congr 1
  ext G
  simp

end SimpleGraph
