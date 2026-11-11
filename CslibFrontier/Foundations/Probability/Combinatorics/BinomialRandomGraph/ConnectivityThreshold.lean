/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Combinatorics/BinomialRandomGraph/`)

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.IsolatedVertices
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Probability.Bonferroni
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgePattern
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Topology.Algebra.Monoid

/-!
# Connectivity threshold limit for binomial random graphs

At the Erdős–Rényi connectivity threshold `n p(n) - log n → c` (`c : ℝ`), the number `X_n` of
isolated vertices in Mathlib's binomial random graph `G(Fin n, p n)` (`SimpleGraph.binomialRandom`)
converges in distribution to `Poisson(exp (-c))`, and the connectivity probability converges to
`exp (-exp (-c))`. This completes the constant-`c` case of
[Frieze and Karoński, Theorem 4.1][FriezeKaronski2016] in `G(n, p)` (whose `c_n → ∞` and
`c_n → -∞` halves are in `BinomialRandomGraph.Connectivity` and
`BinomialRandomGraph.IsolatedVertices`).

* `SimpleGraph.binomialRandom_real_forall_isIsolated`: any fixed `r`-subset `S` of vertices is
  all isolated with probability `(1 - p) ^ (|S| |V| - |S| (|S| + 1) / 2)`.
* `SimpleGraph.tendsto_mul_one_sub_pow_sub_one`: the expected number of isolated vertices satisfies
  `n (1 - p(n)) ^ (n - 1) → exp (-c)` when `n p(n) - log n → c`.
* `SimpleGraph.tendsto_binomialRandom_real_natCard_isIsolated_eq`: by Brun's sieve
  (`ProbabilityTheory.tendsto_measureReal_natCard_eq_poisson_of_factorialMoments`),
  `P(X_n = k) → exp (-exp (-c)) * (exp (-c) ^ k / k!)` for every `k : ℕ`, with `k = 0`
  specialized to `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_nhds`.
* `SimpleGraph.binomialRandom_real_forall_not_isIsolated_and_not_connected_le` and
  `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected`: a graph with
  no isolated vertex that is still disconnected contains a connected component of size `2 ≤ k ≤ n/2`
  with a spanning tree of `k - 1` internal edges and an empty cut of `k (n - k)` edges; the
  resulting union bound vanishes when `n p(n) - log n → c`.
* `SimpleGraph.tendsto_binomialRandom_real_connected_nhds`: combining `k = 0` with the component
  gap gives `P(G(n, p(n)) is connected) → exp (-exp (-c))`.

## Main results

* `SimpleGraph.binomialRandom_real_forall_isIsolated`
* `SimpleGraph.tendsto_mul_one_sub_pow_sub_one`
* `SimpleGraph.tendsto_binomialRandom_real_natCard_isIsolated_eq`
* `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_nhds`
* `SimpleGraph.binomialRandom_real_forall_not_isIsolated_and_not_connected_le`
* `SimpleGraph.tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected`
* `SimpleGraph.tendsto_binomialRandom_real_connected_nhds`

## References

* [A. Frieze, M. Karoński, *Introduction to Random Graphs*, Sections 3.1 and
  4.1][FriezeKaronski2016]
-/

public section

open MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Finset Topology

namespace SimpleGraph

variable {V : Type*}

/-! ### Exact probability of an isolated vertex subset -/

section IsolatedMoments

private theorem card_biUnion_incident [Fintype V] [DecidableEq V] (S : Finset V) :
    #(S.biUnion fun v => (Finset.univ.erase v).image (Sym2.mk v)) =
      #S * Fintype.card V - #S * (#S + 1) / 2 := by
  induction S using Finset.induction with
  | empty => simp
  | @insert v S hv ih =>
    have hcard : #((Finset.univ.erase v).image (Sym2.mk v)) = Fintype.card V - 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => Sym2.congr_right.1 h),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Finset.biUnion_insert, Finset.card_union, hcard, ih]
    have hinter : (Finset.univ.erase v).image (Sym2.mk v) ∩
        (S.biUnion fun v' => (Finset.univ.erase v').image (Sym2.mk v')) =
          S.image fun w => s(v, w) := by
      ext e
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_image]
      constructor
      · rintro ⟨⟨w, -, rfl⟩, u, hu, z, -, heq⟩
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim (hv hu)
        · exact ⟨_, hu, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        have hwv : w ≠ v := fun h => hv (h ▸ hw)
        exact ⟨⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ _⟩, rfl⟩, w, hw, v,
          Finset.mem_erase.mpr ⟨hwv.symm, Finset.mem_univ _⟩, Sym2.eq_swap⟩
    have hcard_inter : #((Finset.univ.erase v).image (Sym2.mk v) ∩
        S.biUnion (fun v' => (Finset.univ.erase v').image (Sym2.mk v'))) = #S := by
      rw [hinter, Finset.card_image_of_injective _ fun _ _ h => Sym2.congr_right.mp h]
    have hSn : #S + 1 ≤ Fintype.card V := by
      rw [← Finset.card_insert_of_notMem hv]
      exact Finset.card_le_univ _
    have hdiv_step : (#S + 1) * (#S + 2) / 2 = #S * (#S + 1) / 2 + (#S + 1) := by
      have hmul : (#S + 1) * (#S + 2) = #S * (#S + 1) + 2 * (#S + 1) := by ring
      rw [hmul, Nat.add_mul_div_left _ _ (by norm_num)]
    have htri_le : #S * (#S + 1) / 2 ≤ #S * Fintype.card V := by
      refine Nat.div_le_of_le_mul ?_
      nlinarith [hSn]
    have hadd_mul : (#S + 1) * Fintype.card V = #S * Fintype.card V + Fintype.card V := by ring
    rw [hcard_inter, Finset.card_insert_of_notMem hv, hdiv_step, hadd_mul]
    omega

/-- In `G(V, p)`, every vertex in a finite subset `S` is isolated with probability
`(1 - p) ^ (|S| |V| - |S| (|S| + 1) / 2)`. -/
theorem binomialRandom_real_forall_isIsolated [Fintype V] (p : I) (S : Finset V) :
    G(V, p).real {G | ∀ v ∈ S, G.IsIsolated v} =
      (1 - p : ℝ) ^ (#S * Fintype.card V - #S * (#S + 1) / 2) := by
  classical
  let t : Finset (Sym2 V) := S.biUnion fun v => (Finset.univ.erase v).image (Sym2.mk v)
  have hdiag : ∀ e ∈ t, ¬e.IsDiag := by
    intro e he
    obtain ⟨v, _, hev⟩ := Finset.mem_biUnion.mp he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hev
    simpa using (Finset.mem_erase.mp hw).1.symm
  have hset : {G : SimpleGraph V | ∀ v ∈ S, G.IsIsolated v} =
      {G | Disjoint (t : Set (Sym2 V)) G.edgeSet} := by
    ext G
    simp only [Set.mem_ofPred_eq, t, Finset.coe_biUnion, Finset.mem_coe,
      Set.disjoint_iUnion_left]
    exact forall₂_congr fun v _ => isIsolated_iff_disjoint_incident G v
  rw [hset, binomialRandom_real_disjoint_edgeSet p t hdiag, card_biUnion_incident]

end IsolatedMoments

/-! ### Threshold asymptotics and Poisson limit for isolated vertices -/

section ThresholdAsymptotics

private theorem tendsto_mul_pow_div_self_of_tendsto_mul_sub_log {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) (m : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) * (p n : ℝ)) ^ m / (n : ℝ)) atTop (𝓝 0) := by
  have hbd : ∀ᶠ n : ℕ in atTop, |(n : ℝ) * (p n : ℝ) - Real.log n - c| < 1 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hp) 1 zero_lt_one
    exact eventually_atTop.mpr ⟨N, fun n hn => by
      have := hN n hn
      rwa [Real.dist_eq] at this⟩
  have hlog_big : ∀ᶠ n : ℕ in atTop, |c| + 1 ≤ Real.log n :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually (eventually_ge_atTop _)
  have hlog_div : Tendsto (fun n : ℕ => Real.log n ^ m / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, one_mul, add_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hlog_div.const_mul (2 ^ m))
    (Eventually.of_forall fun n => by
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
      positivity) ?_
  filter_upwards [hbd, hlog_big, eventually_ge_atTop 1] with n hbn hln hn1
  have hn0 : (0 : ℝ) < n := by positivity
  have hnp0 : 0 ≤ (n : ℝ) * (p n : ℝ) := mul_nonneg hn0.le (unitInterval.nonneg _)
  have hle_log : (n : ℝ) * (p n : ℝ) ≤ 2 * Real.log n := by
    have := (abs_lt.mp hbn).2
    linarith [le_abs_self c]
  calc ((n : ℝ) * (p n : ℝ)) ^ m / (n : ℝ)
      ≤ (2 * Real.log n) ^ m / (n : ℝ) := by gcongr
    _ = 2 ^ m * (Real.log n ^ m / (n : ℝ)) := by rw [mul_pow, mul_div_assoc]

private theorem tendsto_coe_atTop_zero {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (p n : ℝ)) atTop (𝓝 0) := by
  refine (tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 1).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [hn0]

private theorem tendsto_one_sub_atTop_one {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (1 - (p n : ℝ))) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub (tendsto_coe_atTop_zero hp)

private theorem tendsto_mul_exp_neg_mul {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ))))
      atTop (𝓝 (Real.exp (-c))) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * (p n : ℝ) - Real.log n)))
      atTop (𝓝 (Real.exp (-c))) := (Real.continuous_exp.comp continuous_neg).tendsto c |>.comp hp
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by positivity
  rw [show -((n : ℝ) * (p n : ℝ) - Real.log n) = Real.log n + (-((n : ℝ) * (p n : ℝ))) by ring,
    Real.exp_add, Real.exp_log hn0]

/-- When `n p(n) - log n → c`, the expected number of isolated vertices satisfies
`n (1 - p(n)) ^ (n - 1) → exp (-c)`. -/
theorem tendsto_mul_one_sub_pow_sub_one {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1))
      atTop (𝓝 (Real.exp (-c))) := by
  have h1sub : Tendsto (fun n : ℕ => 1 - (p n : ℝ)) atTop (𝓝 1) := tendsto_one_sub_atTop_one hp
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine (tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 2).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn0]
  have hlog_err : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 - (p n : ℝ)) +
      (n : ℝ) * (p n : ℝ)) atTop (𝓝 0) := by
    have hlow : Tendsto (fun n : ℕ => -((n : ℝ) * (p n : ℝ) ^ 2 / (1 - (p n : ℝ))))
        atTop (𝓝 0) := by
      have h := (hsq.div h1sub one_ne_zero).neg
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with
        n hq
      have hq0 : 0 < 1 - (p n : ℝ) := by linarith
      have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)
      rw [Real.log_inv] at hinv
      have hlog_lb : -(p n : ℝ) / (1 - (p n : ℝ)) ≤ Real.log (1 - (p n : ℝ)) := by
        have hsub : (1 - (p n : ℝ))⁻¹ - 1 = (p n : ℝ) / (1 - (p n : ℝ)) := by
          field_simp [hq0.ne']
          ring
        rw [neg_div]
        linarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hmul : (n : ℝ) * (-(p n : ℝ) / (1 - (p n : ℝ)) + (p n : ℝ)) ≤
          (n : ℝ) * (Real.log (1 - (p n : ℝ)) + (p n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hn0
      have halg : (n : ℝ) * (-(p n : ℝ) / (1 - (p n : ℝ)) + (p n : ℝ)) =
          -((n : ℝ) * (p n : ℝ) ^ 2 / (1 - (p n : ℝ))) := by
        field_simp [hq0.ne']
        ring
      have halg2 : (n : ℝ) * (Real.log (1 - (p n : ℝ)) + (p n : ℝ)) =
          (n : ℝ) * Real.log (1 - (p n : ℝ)) + (n : ℝ) * (p n : ℝ) := by ring
      linarith
    · filter_upwards [h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with
        n hq
      have hlog_ub := Real.log_le_sub_one_of_pos (show 0 < 1 - (p n : ℝ) by linarith)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hmul : (n : ℝ) * (Real.log (1 - (p n : ℝ)) + (p n : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hn0 (by linarith)
      linarith
  have hpow_n : Tendsto (fun n : ℕ => (n : ℝ) * (1 - (p n : ℝ)) ^ n)
      atTop (𝓝 (Real.exp (-c))) := by
    have hexp_arg : Tendsto (fun n : ℕ =>
        ((n : ℝ) * Real.log (1 - (p n : ℝ)) + (n : ℝ) * (p n : ℝ)) -
          ((n : ℝ) * (p n : ℝ) - Real.log n)) atTop (𝓝 (-c)) := by
      simpa using hlog_err.sub hp
    have hexp := (Real.continuous_exp.tendsto (-c)).comp hexp_arg
    refine hexp.congr' ?_
    filter_upwards [eventually_ge_atTop 1,
      h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hq
    have hn0 : (0 : ℝ) < n := by positivity
    have hq0 : 0 < 1 - (p n : ℝ) := by linarith
    simp only [Function.comp_def]
    rw [show ((n : ℝ) * Real.log (1 - (p n : ℝ)) + (n : ℝ) * (p n : ℝ)) -
          ((n : ℝ) * (p n : ℝ) - Real.log n) =
        Real.log n + Real.log (1 - (p n : ℝ)) * (n : ℝ) by ring,
      Real.exp_add, Real.exp_log hn0, ← Real.rpow_def_of_pos hq0, Real.rpow_natCast]
  have hdiv := hpow_n.div h1sub one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1,
    h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hq
  have hq0 : 1 - (p n : ℝ) ≠ 0 := by linarith
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  dsimp only [Pi.div_apply]
  rw [Nat.succ_sub_one, pow_succ]
  field_simp [hq0]

private theorem tendsto_choose_div_pow (r : ℕ) :
    Tendsto (fun n : ℕ => (n.choose r : ℝ) / (n : ℝ) ^ r) atTop (𝓝 ((r.factorial : ℝ)⁻¹)) := by
  have hprod :
      Tendsto (fun n : ℕ => ∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
    have h1 : ∀ i : ℕ, Tendsto (fun n : ℕ => 1 - (i : ℝ) / (n : ℝ)) atTop (𝓝 1) := fun i => by
      simpa using tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa using tendsto_finsetProd (Finset.range r) fun i _ => h1 i
  have hdiv :
      Tendsto (fun n : ℕ => (∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))) / (r.factorial : ℝ))
        atTop (𝓝 ((r.factorial : ℝ)⁻¹)) := by
    simpa [one_div] using hprod.div_const (r.factorial : ℝ)
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (max r 1)] with n hn
  have hnr : r ≤ n := (le_max_left r 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right r 1).trans hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdesc : ((n.choose r : ℝ) * r.factorial) = ∏ i ∈ Finset.range r, ((n : ℝ) - i) := by
    have hnat : n.choose r * r.factorial = n.descFactorial r := by
      rw [mul_comm]
      exact (Nat.descFactorial_eq_factorial_mul_choose n r).symm
    have hcast : ((n.choose r : ℝ) * r.factorial) = (n.descFactorial r : ℝ) := by
      exact_mod_cast hnat
    rw [hcast, Nat.descFactorial_eq_prod_range]
    push_cast
    refine Finset.prod_congr rfl fun i hi => ?_
    have hir : i ≤ n := (Finset.mem_range.mp hi).le.trans hnr
    rw [Nat.cast_sub hir]
  have hfac_ne : (r.factorial : ℝ) ≠ 0 := by positivity
  calc (∏ i ∈ Finset.range r, (1 - (i : ℝ) / (n : ℝ))) / (r.factorial : ℝ)
      = (∏ i ∈ Finset.range r, (((n : ℝ) - i) / (n : ℝ))) / (r.factorial : ℝ) := by
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          field_simp [hn0]
    _ = ((∏ i ∈ Finset.range r, ((n : ℝ) - i)) / (n : ℝ) ^ r) / (r.factorial : ℝ) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    _ = (n.choose r : ℝ) / (n : ℝ) ^ r := by
          rw [← hdesc]
          field_simp [hfac_ne, hn0]

/-- At the connectivity threshold `n p(n) - log n → c`, the number of isolated vertices in
`G(Fin n, p n)` converges in distribution to `Poisson(exp (-c))`. -/
theorem tendsto_binomialRandom_real_natCard_isIsolated_eq {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | Nat.card {v // G.IsIsolated v} = k})
      atTop (𝓝 (Real.exp (-Real.exp (-c)) * (Real.exp (-c) ^ k / k.factorial))) := by
  have h1sub : Tendsto (fun n : ℕ => 1 - (p n : ℝ)) atTop (𝓝 1) := tendsto_one_sub_atTop_one hp
  have hmu : Tendsto (fun n : ℕ => (n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1))
      atTop (𝓝 (Real.exp (-c))) := tendsto_mul_one_sub_pow_sub_one hp
  refine ProbabilityTheory.tendsto_measureReal_natCard_eq_poisson_of_factorialMoments
    (fun n => G(Fin n, p n)) (fun n v => {G : SimpleGraph (Fin n) | G.IsIsolated v})
    (fun n _ => MeasurableSet.of_discrete) (fun r => ?_) k
  have hlim_eq :
      ((r.factorial : ℝ)⁻¹ * Real.exp (-c) ^ r) / (1 : ℝ) ^ (r * (r - 1) / 2) =
        Real.exp (-c) ^ r / r.factorial := by
    simp [div_eq_mul_inv, mul_comm]
  have hlim :
      Tendsto (fun n : ℕ => ((n.choose r : ℝ) / (n : ℝ) ^ r) *
          ((n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1)) ^ r /
          (1 - (p n : ℝ)) ^ (r * (r - 1) / 2))
        atTop (𝓝 (Real.exp (-c) ^ r / r.factorial)) := by
    rw [← hlim_eq]
    exact ((tendsto_choose_div_pow r).mul (hmu.pow r)).div (h1sub.pow (r * (r - 1) / 2)) (by simp)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max r 1),
    h1sub.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hq
  have hnr : r ≤ n := (le_max_left r 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right r 1).trans hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : 1 - (p n : ℝ) ≠ 0 := by linarith
  have hsum_eq :
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          G(Fin n, p n).real (⋂ v ∈ S, {G : SimpleGraph (Fin n) | G.IsIsolated v}) =
        (n.choose r : ℝ) * (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2) := by
    have hterm : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        G(Fin n, p n).real (⋂ v ∈ S, {G : SimpleGraph (Fin n) | G.IsIsolated v}) =
          (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2) := by
      intro S hS
      have hScard : #S = r := (Finset.mem_powersetCard.mp hS).2
      have hinter : (⋂ v ∈ S, {G : SimpleGraph (Fin n) | G.IsIsolated v}) =
          {G : SimpleGraph (Fin n) | ∀ v ∈ S, G.IsIsolated v} := by
        ext G
        simp
      rw [hinter, binomialRandom_real_forall_isIsolated, Fintype.card_fin, hScard]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum_eq]
  have hexp_eq : r * n - r * (r + 1) / 2 + r * (r - 1) / 2 = r * (n - 1) := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · have hr2 : r * (r + 1) = r * (r - 1) + 2 * r := by
        have h : r - 1 + 1 = r := Nat.sub_add_cancel hr
        nlinarith [h]
      have hdiv_diff : r * (r + 1) / 2 = r * (r - 1) / 2 + r := by
        rw [hr2, Nat.add_mul_div_left _ _ (by norm_num)]
      have hle1 : r * (r + 1) ≤ 2 * (r * n) := by nlinarith [hnr]
      have hle2 : r * (r + 1) / 2 ≤ r * n := Nat.div_le_of_le_mul hle1
      have hle3 : r * n - r * (r + 1) / 2 + r * (r - 1) / 2 = r * n - r := by omega
      rw [hle3, Nat.mul_sub_one]
  rw [div_eq_iff (pow_ne_zero _ hq0)]
  calc ((n.choose r : ℝ) / (n : ℝ) ^ r) * ((n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1)) ^ r
      = (n.choose r : ℝ) * (((1 - (p n : ℝ)) ^ (n - 1)) ^ r) := by
          rw [mul_pow]
          field_simp [hn0]
    _ = (n.choose r : ℝ) * (1 - (p n : ℝ)) ^ (r * (n - 1)) := by
          rw [← pow_mul, mul_comm (n - 1) r]
    _ = (n.choose r : ℝ) * (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2 + r * (r - 1) / 2) := by
          rw [hexp_eq]
    _ = (n.choose r : ℝ) * (1 - (p n : ℝ)) ^ (r * n - r * (r + 1) / 2) *
          (1 - (p n : ℝ)) ^ (r * (r - 1) / 2) := by
          rw [pow_add, mul_assoc]

/-- Specialization of `tendsto_binomialRandom_real_natCard_isIsolated_eq` to `k = 0`:
when `n p(n) - log n → c`, `G(Fin n, p n)` has no isolated vertex with probability tending to
`exp (-exp (-c))`. -/
theorem tendsto_binomialRandom_real_forall_not_isIsolated_nhds {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | ∀ v, ¬G.IsIsolated v})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
  have h := tendsto_binomialRandom_real_natCard_isIsolated_eq hp 0
  have hset : ∀ n : ℕ, {G : SimpleGraph (Fin n) | Nat.card {v // G.IsIsolated v} = 0} =
      {G | ∀ v, ¬G.IsIsolated v} := fun n => by
    ext G
    have hfin : Finite {v : Fin n // G.IsIsolated v} := Subtype.finite
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Nat.card_eq_zero, or_iff_left hfin.not_infinite,
      isEmpty_subtype]
  simpa only [hset, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using h

end ThresholdAsymptotics

/-! ### Component gap between no isolated vertices and connectivity -/

section ComponentGap

private theorem card_sym2_filter_not_isDiag [DecidableEq V] (S : Finset V) :
    #(S.sym2.filter (¬ ·.IsDiag)) = (#S).choose 2 := by
  have heq : S.sym2.filter (¬ ·.IsDiag) = S.sym2 \ S.image Sym2.diag := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image, Finset.mem_sym2_iff]
    constructor
    · rintro ⟨he, hnd⟩
      refine ⟨he, ?_⟩
      rintro ⟨u, -, rfl⟩
      exact hnd (Sym2.diag_isDiag u)
    · rintro ⟨he, hnd⟩
      refine ⟨he, fun hd => ?_⟩
      induction e using Sym2.ind with
      | h x y =>
        obtain rfl := Sym2.mk_isDiag_iff.mp hd
        exact hnd ⟨x, he x (by simp), rfl⟩
  have hsub : S.image Sym2.diag ⊆ S.sym2 := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    exact Finset.diag_mem_sym2_iff.mpr hu
  have hinj : Function.Injective (Sym2.diag : V → Sym2 V) := fun a b h => by
    simp only [Sym2.diag, Sym2.eq_iff, and_self, or_self] at h
    exact h
  rw [heq, Finset.card_sdiff_of_subset hsub, Finset.card_sym2,
    Finset.card_image_of_injective _ hinj, Nat.choose_succ_succ (#S) 1, Nat.choose_one_right]
  change #S + (#S).choose 2 - #S = (#S).choose 2
  omega

private theorem disjoint_sym2_filter_not_isDiag_cutPairs [Fintype V] [DecidableEq V]
    (S : Finset V) :
    Disjoint (S.sym2.filter (¬ ·.IsDiag)) ((S ×ˢ Sᶜ).image Sym2.mk.uncurry) := by
  rw [Finset.disjoint_left]
  intro e he_in he_cut
  obtain ⟨⟨u, v⟩, h_in, rfl⟩ := Finset.mem_image.mp he_cut
  have ⟨hu, hv⟩ := Finset.mem_product.mp h_in
  exact (Finset.mem_compl.mp hv) (Finset.mk_mem_sym2_iff.mp (Finset.mem_filter.mp he_in).1).2

private theorem binomialRandom_real_edgeSet_and_cut [Fintype V] [DecidableEq V] (p : I)
    (S : Finset V) {t : Finset (Sym2 V)} (ht : t ⊆ S.sym2.filter (¬ ·.IsDiag)) :
    G(V, p).real {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
      (p : ℝ) ^ #t * (1 - p : ℝ) ^ (#S * (Fintype.card V - #S)) := by
  let b : Sym2 V → Bool := fun e => decide (e ∈ t)
  let cP : Finset (Sym2 V) := (S ×ˢ Sᶜ).image Sym2.mk.uncurry
  have hdisj : Disjoint t (cP) := (disjoint_sym2_filter_not_isDiag_cutPairs S).mono_left ht
  have hdiag : ∀ e ∈ t ∪ cP, ¬e.IsDiag := by
    intro e he
    rcases Finset.mem_union.mp he with het | hec
    · exact (Finset.mem_filter.mp (ht het)).2
    · obtain ⟨⟨u, v⟩, h_in, rfl⟩ := Finset.mem_image.mp hec
      have ⟨hu, hv⟩ := Finset.mem_product.mp h_in
      rintro hd
      exact (Finset.mem_compl.mp hv) (Sym2.mk_isDiag_iff.1 hd ▸ hu)
  have hset : {G : SimpleGraph V | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
      {G | ∀ e ∈ t ∪ cP, e ∈ G.edgeSet ↔ b e = true} := by
    ext G
    simp only [Set.mem_ofPred_eq, Finset.mem_union, b, decide_eq_true_eq]
    constructor
    · rintro ⟨ht_edge, hcut⟩ e
      intro he
      constructor
      · rintro _
        rcases he with het | hec
        · exact het
        · obtain ⟨⟨u, v⟩, h_in, rfl⟩ := Finset.mem_image.mp hec
          have ⟨hu, hv⟩ := Finset.mem_product.mp h_in
          have hv' := Finset.mem_compl.mp hv
          exact absurd (hcut u hu v hv') (not_not.mpr ‹_›)
      · rintro ht_mem
        exact ht_edge e ht_mem
    · intro h
      constructor
      · intro e he
        exact (h e (Or.inl he)).mpr (by simp [he])
      · intro u hu v hv huv
        have hec : s(u, v) ∈ cP := Finset.mem_image.mpr ⟨(u, v),
          Finset.mem_product.mpr ⟨hu, Finset.mem_compl.mpr hv⟩, rfl⟩
        have hf := (h (s(u, v)) (Or.inr hec)).mp huv
        have hnot : ¬ (s(u, v) ∈ t) := by
          intro hbad
          exact Finset.disjoint_left.mp hdisj hbad hec
        revert hf
        simp [hnot]
  rw [hset, binomialRandom_real_edgePattern p (t ∪ cP) hdiag b,
    Finset.prod_union hdisj]
  have hp1 : ∏ e ∈ t, (if b e = true then (p : ℝ) else 1 - p) = (p : ℝ) ^ #t := by
    have h1 : ∀ e ∈ t, (if b e = true then (p : ℝ) else 1 - p) = (p : ℝ) := fun e he => by
      simp [b, he]
    rw [Finset.prod_congr rfl h1, Finset.prod_const]
  have hp2 : ∏ e ∈ cP, (if b e = true then (p : ℝ) else 1 - p) =
      (1 - p : ℝ) ^ (#S * (Fintype.card V - #S)) := by
    have h2 : ∀ e ∈ cP, (if b e = true then (p : ℝ) else 1 - p) = (1 - p : ℝ) := by
      intro e he
      have hnot : e ∉ t := Finset.disjoint_right.mp hdisj he
      simp [b, hnot]
    have hcard_cP : #cP = #S * (Fintype.card V - #S) := by
      have hinj : Set.InjOn Sym2.mk.uncurry (↑(S ×ˢ Sᶜ) : Set (V × V)) := by
        rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
        simp only [Finset.coe_product, Finset.coe_compl, Set.mem_prod, Finset.mem_coe,
          Set.mem_compl_iff] at huv huv'
        rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd huv.1 huv'.2
      change #((S ×ˢ Sᶜ).image Sym2.mk.uncurry) = _
      rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_compl]
    rw [Finset.prod_congr rfl h2, Finset.prod_const, hcard_cP]
  rw [hp1, hp2]

/-- Explicit union bound for the event that `G(V, p)` has no isolated vertex yet fails to be
connected. -/
theorem binomialRandom_real_forall_not_isIsolated_and_not_connected_le [Fintype V] [Nonempty V]
    (p : I) :
    G(V, p).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} ≤
      ∑ k ∈ Icc 2 (Fintype.card V / 2),
        ((Fintype.card V).choose k : ℝ) * ((k.choose 2).choose (k - 1) : ℝ) *
          (p : ℝ) ^ (k - 1) * (1 - p : ℝ) ^ (k * (Fintype.card V - k)) := by
  classical
  set n := Fintype.card V
  have hsub : {G : SimpleGraph V | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} ⊆
      ⋃ k ∈ Icc 2 (n / 2), ⋃ S ∈ powersetCard k (univ : Finset V),
        ⋃ t ∈ powersetCard (k - 1) (S.sym2.filter (¬ ·.IsDiag)),
          {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} := by
    intro G ⟨hni, hnc⟩
    obtain ⟨S, hS2, hShalf, hSconn, hScut⟩ :=
      exists_connected_induce_forall_not_adj_of_not_connected hnc hni
    obtain ⟨tS, htScard, htSedge⟩ := exists_card_sub_one_subset_edgeSet_of_connected hSconn
    let f : Sym2 (S : Set V) → Sym2 V := Sym2.map Subtype.val
    have hfinj : Function.Injective f := Sym2.map.injective Subtype.val_injective
    let t : Finset (Sym2 V) := tS.image f
    have ht_in : t ⊆ S.sym2.filter (¬ ·.IsDiag) := by
      intro e he
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [Finset.mem_filter, Finset.mem_sym2_iff]
      refine ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨x, _, rfl⟩ := Sym2.mem_map.mp hu
        exact x.2
      · induction e' using Sym2.ind with
        | _ a b =>
          change ¬Sym2.IsDiag s(a.1, b.1)
          simpa using Subtype.coe_ne_coe.mpr (htSedge _ he').2
    have ht_card : #t = #S - 1 := by
      rw [Finset.card_image_of_injective _ hfinj, htScard]
      simp
    have ht_edges : ∀ e ∈ t, e ∈ G.edgeSet := by
      intro e he
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      induction e' using Sym2.ind with
      | _ a b => exact (htSedge _ he').1
    simp only [Set.mem_iUnion, mem_Icc, mem_powersetCard, subset_univ, true_and,
      Set.mem_ofPred_eq, exists_prop]
    exact ⟨#S, ⟨hS2, by omega⟩, S, rfl, t, ⟨ht_in, ht_card⟩, ht_edges, hScut⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hS_bound : ∀ S ∈ (univ : Finset V).powersetCard k,
      G(V, p).real (⋃ t ∈ (S.sym2.filter (¬ ·.IsDiag)).powersetCard (k - 1),
          {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v}) ≤
        ((k.choose 2).choose (k - 1) : ℝ) * (p : ℝ) ^ (k - 1) * (1 - p : ℝ) ^ (k * (n - k)) := by
    intro S hS
    have hSk := (Finset.mem_powersetCard.mp hS).2
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ t ∈ (S.sym2.filter (¬ ·.IsDiag)).powersetCard (k - 1),
        G(V, p).real {G | (∀ e ∈ t, e ∈ G.edgeSet) ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v} =
          (p : ℝ) ^ (k - 1) * (1 - p : ℝ) ^ (k * (n - k)) := by
      intro t ht
      obtain ⟨ht_in, ht_card⟩ := Finset.mem_powersetCard.mp ht
      rw [binomialRandom_real_edgeSet_and_cut p S ht_in, ht_card, hSk]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      card_sym2_filter_not_isDiag, hSk, nsmul_eq_mul, mul_assoc]
  refine (Finset.sum_le_sum hS_bound).trans ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  exact le_of_eq (by ring)

private theorem tendsto_zero_of_nonneg_of_sq_tendsto_zero {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hsq : Tendsto (fun n => f n ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have h := Filter.Tendsto.sqrt hsq
  simpa [Real.sqrt_sq (hf _)] using h

/-- At the connectivity threshold `n p(n) - log n → c`, the probability that `G(Fin n, p n)` has
no isolated vertices yet is disconnected tends to `0`. -/
theorem tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ =>
        G(Fin n, p n).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected})
      atTop (𝓝 0) := by
  let term : ℕ → ℕ → ℝ := fun n k =>
    ((n.choose k : ℝ) * ((k.choose 2).choose (k - 1) : ℝ) *
      (p n : ℝ) ^ (k - 1) * (1 - (p n : ℝ)) ^ (k * (n - k)))
  have hp0 : Tendsto (fun n : ℕ => (p n : ℝ)) atTop (𝓝 0) := tendsto_coe_atTop_zero hp
  have hne : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ))))
      atTop (𝓝 (Real.exp (-c))) := tendsto_mul_exp_neg_mul hp
  have hk2 : Tendsto (fun n : ℕ => term n 2) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ =>
        (p n : ℝ) / 2 * ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 2 *
          Real.exp (4 * (p n : ℝ))) atTop (𝓝 0) := by
      have hexp4 : Tendsto (fun n : ℕ => Real.exp (4 * (p n : ℝ))) atTop (𝓝 1) := by
        simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
          (Real.continuous_exp.tendsto (4 * 0)).comp (hp0.const_mul 4)
      have h := ((hp0.div_const 2).mul (hne.pow 2)).mul hexp4
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun n => by
        dsimp only [term]
        have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
        have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
        positivity) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn2
    dsimp only [term]
    have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
    have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
    have hq_exp : (1 - (p n : ℝ)) ^ (2 * (n - 2)) ≤
        Real.exp (-(2 * ((n : ℝ) - 2) * (p n : ℝ))) := by
      refine Real.one_sub_pow_le_exp (unitInterval.le_one _) ?_
      have hsub : ((2 * (n - 2) : ℕ) : ℝ) = 2 * ((n : ℝ) - 2) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn2, Nat.cast_ofNat]
      rw [hsub]
    have hch2 : ((n.choose 2 : ℝ) * ((2 : ℕ).choose 2 |>.choose 1 : ℝ)) ≤ (n : ℝ) ^ 2 / 2 := by
      have h1 : (2 : ℕ).choose 2 = 1 := by decide
      have h2 : n.choose 2 * 2 = n * (n - 1) := Nat.choose_two_right n ▸ by
        have := Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
        exact this
      have h3 : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
        have h3' : (n.choose 2 : ℝ) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
          have : (n.choose 2 : ℝ) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast h2
          rw [this, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      rw [h1]
      norm_num
      exact h3
    have hexp_eq :
        ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 2 * Real.exp (4 * (p n : ℝ)) =
          (n : ℝ) ^ 2 * Real.exp (-(2 * ((n : ℝ) - 2) * (p n : ℝ))) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      rw [mul_assoc ((n : ℝ) ^ 2) _ _, ← Real.exp_add]
      congr 2
      ring
    calc (n.choose 2 : ℝ) * (((2 : ℕ).choose 2).choose 1 : ℝ) * (p n : ℝ) ^ 1 *
          (1 - (p n : ℝ)) ^ (2 * (n - 2))
        ≤ ((n : ℝ) ^ 2 / 2) * (p n : ℝ) * Real.exp (-(2 * ((n : ℝ) - 2) * (p n : ℝ))) := by
          rw [pow_one]
          gcongr
      _ = (p n : ℝ) / 2 * ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 2 *
            Real.exp (4 * (p n : ℝ)) := by
          rw [mul_assoc, mul_assoc _ (_ ^ 2) _, hexp_eq]
          ring
  let r : ℕ → ℝ := fun n =>
    ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))
  let A : ℕ → ℝ := fun n => (n : ℝ) * Real.exp 1 * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))
  have hr0 : Tendsto r atTop (𝓝 0) := by
    refine tendsto_zero_of_nonneg_of_sq_tendsto_zero (fun n => by
      dsimp [r]
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
      positivity) ?_
    have hsq_lim : Tendsto (fun n : ℕ =>
        (Real.exp 1 ^ 4 / 4) * (((n : ℝ) * (p n : ℝ)) ^ 2 / (n : ℝ)) *
          ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ))))) atTop (𝓝 0) := by
      have h := (((tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 2).const_mul
        (Real.exp 1 ^ 4 / 4)).mul hne)
      simpa using h
    refine hsq_lim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp [r]
    set E := Real.exp (-((n : ℝ) * (p n : ℝ) / 2))
    have hexp2 : E ^ 2 = Real.exp (-((n : ℝ) * (p n : ℝ))) := by
      dsimp [E]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hmerge :
        ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2 * E) ^ 2 =
          ((n : ℝ) ^ 2 * Real.exp 1 ^ 4 * (p n : ℝ) ^ 2 / 4) * E ^ 2 := by ring
    rw [hmerge, hexp2, mul_pow]
    field_simp [hn0]
  have htail : Tendsto (fun n : ℕ => 2 * A n * r n ^ 2) atTop (𝓝 0) := by
    refine tendsto_zero_of_nonneg_of_sq_tendsto_zero (fun n => by
      dsimp [A, r]
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
      positivity) ?_
    have hsq_lim : Tendsto (fun n : ℕ =>
        (Real.exp 1 ^ 10 / 4) * (((n : ℝ) * (p n : ℝ)) ^ 4 / (n : ℝ)) *
          ((n : ℝ) * Real.exp (-((n : ℝ) * (p n : ℝ)))) ^ 3) atTop (𝓝 0) := by
      have h := (((tendsto_mul_pow_div_self_of_tendsto_mul_sub_log hp 4).const_mul
        (Real.exp 1 ^ 10 / 4)).mul (hne.pow 3))
      simpa using h
    refine hsq_lim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp [A, r]
    set E := Real.exp (-((n : ℝ) * (p n : ℝ) / 2))
    have hexp6 : E ^ 6 = Real.exp (-((n : ℝ) * (p n : ℝ))) ^ 3 := by
      dsimp [E]
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hmerge :
        (2 * ((n : ℝ) * Real.exp 1 * E) *
            ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2 * E) ^ 2) ^ 2 =
          ((n : ℝ) ^ 6 * Real.exp 1 ^ 10 * (p n : ℝ) ^ 4 / 4) * E ^ 6 := by ring
    rw [hmerge, hexp6, mul_pow, mul_pow]
    field_simp [hn0]
  have hsum3 : Tendsto (fun n : ℕ => ∑ k ∈ Icc 3 (n / 2), term n k) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
      (Eventually.of_forall fun n => Finset.sum_nonneg fun k _ => by
        dsimp only [term]
        have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
        have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
        positivity) ?_
    filter_upwards [hr0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with
      n hr_half
    have hterm_le : ∀ k ∈ Icc 3 (n / 2), term n k ≤ A n * r n ^ (k - 1) := by
      intro k hk
      have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkn2 : k ≤ n / 2 := (Finset.mem_Icc.mp hk).2
      have hkn : k ≤ n := by omega
      have hk_half : (n : ℝ) / 2 ≤ (n : ℝ) - k := by
        have h2k : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
        linarith
      have hch1 : (n.choose k : ℝ) ≤ ((n : ℝ) * Real.exp 1 / k) ^ k :=
        choose_le_mul_exp_div_pow k n
      have hch2 : ((k.choose 2).choose (k - 1) : ℝ) ≤ ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) := by
        have h := choose_le_mul_exp_div_pow (k - 1) (k.choose 2)
        have hck : ((k.choose 2 : ℝ) * Real.exp 1 / ((k - 1 : ℕ) : ℝ)) =
            (k : ℝ) * Real.exp 1 / 2 := by
          have hk1 : 1 ≤ k := by omega
          have h2 : k.choose 2 * 2 = k * (k - 1) := Nat.choose_two_right k ▸
            Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd
          have h2r : (k.choose 2 : ℝ) * 2 = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h2
          have hk1r : ((k - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp [hk1r]
          linarith
        rwa [hck] at h
      have hq_exp : (1 - (p n : ℝ)) ^ (k * (n - k)) ≤
          Real.exp (-(k * ((n : ℝ) / 2) * (p n : ℝ))) := by
        refine Real.one_sub_pow_le_exp (unitInterval.le_one _) ?_
        have hcast : ((k * (n - k) : ℕ) : ℝ) = (k : ℝ) * ((n : ℝ) - k) := by
          rw [Nat.cast_mul, Nat.cast_sub hkn]
        rw [hcast]
        have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hk_half (Nat.cast_nonneg k)]
      have hexp_split : Real.exp (-(k * ((n : ℝ) / 2) * (p n : ℝ))) =
          Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) *
            Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) ^ (k - 1) := by
        have hk1 : 1 ≤ k := by omega
        rw [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sub hk1]
        ring_nf
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpow_comb :
          ((n : ℝ) * Real.exp 1 / k) ^ k * ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) *
              (p n : ℝ) ^ (k - 1) =
            ((n : ℝ) * Real.exp 1 / k) * ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) ^ (k - 1) := by
        let X : ℝ := (n : ℝ) * Real.exp 1 / k
        have hX : X ^ k = X * X ^ (k - 1) := by
          nth_rw 1 [show k = 1 + (k - 1) by omega]
          rw [pow_add, pow_one]
        have hinner : X * ((k : ℝ) * Real.exp 1 / 2) * (p n : ℝ) =
            (n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2 := by
          dsimp [X]
          field_simp [hk0]
        calc X ^ k * ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) * (p n : ℝ) ^ (k - 1)
            = X * (X * ((k : ℝ) * Real.exp 1 / 2) * (p n : ℝ)) ^ (k - 1) := by
              rw [hX, mul_pow, mul_pow]
              ring
          _ = X * ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) ^ (k - 1) := by
              rw [hinner]
      have hAn_div : (n : ℝ) * Real.exp 1 / k ≤ (n : ℝ) * Real.exp 1 := by
        have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        exact div_le_self (by positivity) hk_ge1
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
      have hq_nn : 0 ≤ 1 - (p n : ℝ) := by linarith [unitInterval.le_one (p n)]
      have hr_nn : 0 ≤ r n := by dsimp [r]; positivity
      dsimp only [term]
      calc (n.choose k : ℝ) * ((k.choose 2).choose (k - 1) : ℝ) * (p n : ℝ) ^ (k - 1) *
            (1 - (p n : ℝ)) ^ (k * (n - k))
          ≤ ((n : ℝ) * Real.exp 1 / k) ^ k * ((k : ℝ) * Real.exp 1 / 2) ^ (k - 1) *
              (p n : ℝ) ^ (k - 1) * Real.exp (-(k * ((n : ℝ) / 2) * (p n : ℝ))) := by
            gcongr
        _ = ((n : ℝ) * Real.exp 1 / k) * ((n : ℝ) * Real.exp 1 ^ 2 * (p n : ℝ) / 2) ^ (k - 1) *
              (Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) *
                Real.exp (-((n : ℝ) * (p n : ℝ) / 2)) ^ (k - 1)) := by
            rw [hpow_comb, hexp_split]
        _ = ((n : ℝ) * Real.exp 1 / k * Real.exp (-((n : ℝ) * (p n : ℝ) / 2))) *
              r n ^ (k - 1) := by
            dsimp [r]
            rw [mul_pow]
            ring
        _ ≤ A n * r n ^ (k - 1) := by
            dsimp [A]
            gcongr
    have hr_nn : 0 ≤ r n := by
      dsimp [r]
      have hp_nn : 0 ≤ (p n : ℝ) := unitInterval.nonneg _
      positivity
    have hA_nn : 0 ≤ A n := by
      dsimp [A]
      positivity
    have hgeom_sum : ∑ k ∈ Icc 3 (n / 2), A n * r n ^ (k - 1) ≤ 2 * A n * r n ^ 2 := by
      have hstep : ∀ k ∈ Icc 3 (n / 2),
          A n * r n ^ (k - 1) ≤ A n * r n ^ 2 * (1 / 2 : ℝ) ^ (k - 3) := by
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
        have hpow_split : r n ^ (k - 1) = r n ^ 2 * r n ^ (k - 3) := by
          rw [← pow_add, show 2 + (k - 3) = k - 1 by omega]
        rw [hpow_split, ← mul_assoc]
        gcongr
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum]
      have hsum_half : ∑ k ∈ Icc 3 (n / 2), (1 / 2 : ℝ) ^ (k - 3) ≤ 2 := by
        have hinj : ∀ a ∈ Icc 3 (n / 2), ∀ b ∈ Icc 3 (n / 2), a - 3 = b - 3 → a = b := by
          intro a ha b hb h
          have ha3 : 3 ≤ a := (Finset.mem_Icc.mp ha).1
          have hb3 : 3 ≤ b := (Finset.mem_Icc.mp hb).1
          omega
        have h1 : ∑ k ∈ Icc 3 (n / 2), (1 / 2 : ℝ) ^ (k - 3) ≤
            ∑ j ∈ Finset.range (n / 2 + 1), (1 / 2 : ℝ) ^ j := by
          rw [← Finset.sum_image (f := fun j => (1 / 2 : ℝ) ^ j) hinj]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro j hj
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
          have hkn2 := (Finset.mem_Icc.mp hk).2
          rw [Finset.mem_range]
          omega
        refine h1.trans ?_
        rw [geom_sum_eq (by norm_num)]
        have hp_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n / 2 + 1) := by positivity
        norm_num
        linarith
      nlinarith [mul_nonneg hA_nn (sq_nonneg (r n))]
    exact (Finset.sum_le_sum hterm_le).trans hgeom_sum
  have hsum_all : Tendsto (fun n : ℕ => ∑ k ∈ Icc 2 (n / 2), term n k) atTop (𝓝 0) := by
    have hadd : Tendsto (fun n : ℕ => term n 2 + ∑ k ∈ Icc 3 (n / 2), term n k) atTop (𝓝 0) := by
      simpa using hk2.add hsum3
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with n hn4
    have hsplit : Icc 2 (n / 2) = insert 2 (Icc 3 (n / 2)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (2 : ℕ) ∉ Icc 3 (n / 2) := by simp
    rw [hsplit, Finset.sum_insert hnot]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_all
    (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  simpa only [Fintype.card_fin] using
    @binomialRandom_real_forall_not_isIsolated_and_not_connected_le (Fin n) _
      (Fin.pos_iff_nonempty.mp hn1) (p n)

/-- **Erdős–Rényi connectivity threshold (constant case)**: if `n p(n) - log n → c`, then
`G(Fin n, p n)` is connected with probability tending to `exp (-exp (-c))`. -/
theorem tendsto_binomialRandom_real_connected_nhds {p : ℕ → I} {c : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ) - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => G(Fin n, p n).real {G | G.Connected})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
  have hiso := tendsto_binomialRandom_real_forall_not_isIsolated_nhds hp
  have hgap := tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected hp
  have hdiff : Tendsto (fun n : ℕ =>
      G(Fin n, p n).real {G | ∀ v, ¬G.IsIsolated v} -
        G(Fin n, p n).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
    simpa using hiso.sub hgap
  refine hdiff.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hsdiff :
      {G : SimpleGraph (Fin n) | ∀ v, ¬G.IsIsolated v} \ {G | G.Connected} =
        {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} := rfl
  rw [← hsdiff, measureReal_sdiff (@setOf_connected_subset (Fin n)
      (Fin.nontrivial_iff_two_le.mpr hn2)) MeasurableSet.of_discrete]
  ring

end ComponentGap

end SimpleGraph
