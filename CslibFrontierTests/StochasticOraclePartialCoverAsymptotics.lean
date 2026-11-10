/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverAsymptotics
import Mathlib.Tactic

/-!
# Source approximation-factor clients

These instantiate the actual greedy risk-comparison factor, including the
nonconstant failure budget `1/n`. Native time/space complexity is not asserted.
-/

open Cslib.Probability.StochasticOracle.PartialCover.Asymptotics Filter

example : (fun n : ℕ => factor (1 / 2) (1 / 3) n) =O[atTop]
    (fun n => (Real.log n) ^ 2) :=
  fixed_failure (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (fun n : ℕ => factor (1 / 2) (1 / (n : ℝ)) n) =O[atTop]
    (fun n => Real.log n) := by
  apply polynomial_failure (by norm_num) (by norm_num) _ (A := 1) (B := 1)
    (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  exact ⟨by positivity, (div_lt_one (by positivity)).mpr hnreal,
    by simp, by simp⟩

open Cslib Cslib.Probability.StochasticOracle
open PartialCover.Instance Cslib.Algorithms.Lean.Multicover

/-- The asymptotic function is exactly the bound for the executable greedy
batch, compared with every risk-feasible benchmark, without an optimum premise. -/
example {n m : ℕ} (I : PartialCover.Instance (Fin n) (Fin m))
    (hground : I.ground = Finset.univ) (hne : I.ground.Nonempty)
    (as bs : List (Oracle (Fin n)))
    (hcover : ∀ e, ∃ a ∈ as, e ∈ a.eligible)
    (hcost : ∀ a ∈ as, 0 ≤ a.cost) (hsub : ∀ a ∈ bs, a ∈ as)
    {q δ : ℝ} (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ) (hδone : δ < 1)
    (hrisk : (∑ e ∈ I.ground, q ^ chances e (bs.map Oracle.eligible)) ≤ δ) :
    (bill (batch as (repetitions q (δ / n))) : ℝ) ≤ factor q δ n * (bill bs : ℝ) := by
  simpa only [factor, Fintype.card_fin] using
    (greedy_risk_bill I hground hne as bs hcover hcost hsub hq hqone hδ hδone hrisk).2
