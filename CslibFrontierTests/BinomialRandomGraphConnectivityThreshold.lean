/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests for BinomialRandomGraph.ConnectivityThreshold)

public import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.ConnectivityThreshold
import Mathlib.Tactic

/-!
# Worked instances for the binomial random graph connectivity threshold

These kernel-checked examples verify `BinomialRandomGraph.ConnectivityThreshold` and the moved
disjoint-edge lemma in `BinomialRandomGraph.Basic`:
* boundary edge probabilities `p = 0` and `p = 1` for `binomialRandom_real_forall_isIsolated` and
  `binomialRandom_real_forall_not_isIsolated_and_not_connected_le`;
* exact finite values for `G(Fin 4, 1/2)` and `G(Fin 3, 1/2)`;
* the explicit nonvacuous component-gap bound `P(X = 0 ∧ ¬Connected) < 1 / 16` on `G(Fin 6, 1/2)`;
* a concrete threshold sequence `thresholdProb c n = clamp_0^1((log n + c) / n)` satisfying
  `n p(n) - log n → c`, yielding the Poisson limits of `Nat.card {v // G.IsIsolated v}` and
  the Erdős–Rényi connectivity limit `exp (-exp (-c))`.
-/

public section

namespace CslibFrontierTests.BinomialRandomGraphConnectivityThreshold

open SimpleGraph unitInterval Filter Finset
open scoped SimpleGraph Topology

/-- The midpoint probability `1 / 2` in `unitInterval`. -/
noncomputable def halfProb : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Threshold edge probability `min 1 (max 0 ((log n + c) / n))` at offset `c`. -/
noncomputable def thresholdProb (c : ℝ) (n : ℕ) : I :=
  ⟨max 0 (min 1 ((Real.log n + c) / n)), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

/-- `thresholdProb c n` satisfies `n p(n) - log n → c`. -/
theorem tendsto_mul_thresholdProb_sub_log (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (thresholdProb c n : ℝ) - Real.log n) atTop (𝓝 c) := by
  have hdiv : Tendsto (fun n : ℕ => (Real.log n + c) / (n : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def, pow_one, one_mul, add_zero] using h
    have h2 : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [add_div] using h1.add h2
  have hlog : ∀ᶠ n : ℕ in atTop, |c| + 1 ≤ Real.log n :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually (eventually_ge_atTop _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hlog,
    hdiv.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn1 hln hlt
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpos : 0 ≤ (Real.log n + c) / (n : ℝ) := by
    have hnum : 0 ≤ Real.log n + c := by linarith [neg_le_abs c]
    exact div_nonneg hnum (Nat.cast_nonneg n)
  have hle1 : (Real.log n + c) / (n : ℝ) ≤ 1 := by linarith
  have hval : (thresholdProb c n : ℝ) = (Real.log n + c) / (n : ℝ) := by
    change max 0 (min 1 ((Real.log n + c) / n)) = (Real.log n + c) / n
    rw [min_eq_right hle1, max_eq_right hpos]
  rw [hval]
  field_simp [hn0]
  ring

/-! ### Edge cases `p = 0` and `p = 1`, and moved `Basic` disjoint-edge API -/

example :
    G(Fin 4, (0 : I)).real {G | ∀ v ∈ ({0, 1} : Finset (Fin 4)), G.IsIsolated v} = 1 := by
  rw [binomialRandom_real_forall_isIsolated]
  simp

example :
    G(Fin 4, (1 : I)).real {G | ∀ v ∈ ({0, 1} : Finset (Fin 4)), G.IsIsolated v} = 0 := by
  rw [binomialRandom_real_forall_isIsolated]
  norm_num

example :
    G(Fin 4, (1 : I)).real {G | ∀ v ∈ (∅ : Finset (Fin 4)), G.IsIsolated v} = 1 := by
  rw [binomialRandom_real_forall_isIsolated]
  simp

example :
    G(Fin 6, (0 : I)).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} ≤ 0 := by
  have h := binomialRandom_real_forall_not_isIsolated_and_not_connected_le (V := Fin 6) (0 : I)
  refine h.trans_eq ?_
  rw [Fintype.card_fin, show Icc 2 (6 / 2) = {2, 3} from by decide,
    Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
  norm_num

example (p : I) (t : Finset (Sym2 (Fin 4))) (ht : ∀ e ∈ t, ¬e.IsDiag) :
    G(Fin 4, p).real {G | Disjoint (t : Set (Sym2 (Fin 4))) G.edgeSet} = (1 - p : ℝ) ^ #t :=
  binomialRandom_real_disjoint_edgeSet p t ht

/-! ### Exact values and nonvacuous explicit component-gap bound at `p = 1 / 2` -/

example :
    G(Fin 4, halfProb).real {G | ∀ v ∈ ({0, 1} : Finset (Fin 4)), G.IsIsolated v} = 1 / 32 := by
  rw [binomialRandom_real_forall_isIsolated]
  norm_num [halfProb]

example :
    G(Fin 3, halfProb).real {G | ∀ v : Fin 3, G.IsIsolated v} = 1 / 8 := by
  have h := binomialRandom_real_forall_isIsolated (V := Fin 3) halfProb Finset.univ
  have hp : (halfProb : ℝ) = 1 / 2 := rfl
  rw [hp] at h
  norm_num at h
  simpa only [Finset.mem_univ, forall_true_left] using h

example :
    G(Fin 6, halfProb).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected} < 1 / 16 := by
  have h := binomialRandom_real_forall_not_isIsolated_and_not_connected_le (V := Fin 6) halfProb
  have hp : (halfProb : ℝ) = 1 / 2 := rfl
  rw [hp, Fintype.card_fin, show Icc 2 (6 / 2) = {2, 3} from by decide,
    Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), show Nat.choose 6 2 = 15 from by decide,
    show Nat.choose 6 3 = 20 from by decide] at h
  norm_num at h
  linarith

/-! ### Threshold limits for `thresholdProb c n` -/

example (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - (thresholdProb c n : ℝ)) ^ (n - 1))
      atTop (𝓝 (Real.exp (-c))) :=
  tendsto_mul_one_sub_pow_sub_one (tendsto_mul_thresholdProb_sub_log c)

example :
    Tendsto (fun n : ℕ => G(Fin n, thresholdProb 0 n).real {G | Nat.card {v // G.IsIsolated v} = 1})
      atTop (𝓝 (Real.exp (-1))) := by
  simpa using tendsto_binomialRandom_real_natCard_isIsolated_eq
    (tendsto_mul_thresholdProb_sub_log 0) 1

example :
    Tendsto (fun n : ℕ => G(Fin n, thresholdProb 0 n).real {G | ∀ v, ¬G.IsIsolated v})
      atTop (𝓝 (Real.exp (-1))) := by
  simpa using tendsto_binomialRandom_real_forall_not_isIsolated_nhds
    (tendsto_mul_thresholdProb_sub_log 0)

example (c : ℝ) :
    Tendsto (fun n : ℕ =>
        G(Fin n, thresholdProb c n).real {G | (∀ v, ¬G.IsIsolated v) ∧ ¬G.Connected})
      atTop (𝓝 0) :=
  tendsto_binomialRandom_real_forall_not_isIsolated_and_not_connected
    (tendsto_mul_thresholdProb_sub_log c)

example (c : ℝ) :
    Tendsto (fun n : ℕ => G(Fin n, thresholdProb c n).real {G | G.Connected})
      atTop (𝓝 (Real.exp (-Real.exp (-c)))) :=
  tendsto_binomialRandom_real_connected_nhds (tendsto_mul_thresholdProb_sub_log c)

end CslibFrontierTests.BinomialRandomGraphConnectivityThreshold

end
