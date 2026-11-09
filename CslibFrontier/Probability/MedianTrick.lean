/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Finset.Median
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Combinatorics.MajorityVote
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The median trick

The **median trick** [Chakrabarti2025, Section 2.4] amplifies the success probability of any
estimator: if an estimate misses its target by more than `t` with probability at most `1 / 3`,
the median of `2 r` independent estimates misses by more than `t` with probability at most
`(8 / 9) ^ r`.

This holds for any estimate, whatever its distribution; algorithms such as Count-Sketch and KMV
distinct elements use it for estimators that are not averages.

## Main results

* `Cslib.Probability.dens_abs_median_sub_gt_le`: the median of `2 r` independent estimates that
  each miss `μ` by more than `t` with probability at most `1 / 3` misses `μ` by more than `t`
  with probability at most `(8 / 9) ^ r`.

## References

* [A. Chakrabarti, *Data Stream Algorithms*, Section 2.4][Chakrabarti2025]
-/

public section

namespace Cslib.Probability

open Finset Fintype

variable {Ω : Type*} [Fintype Ω]

/-- **The median trick** [Chakrabarti2025, Section 2.4]: if the estimate `g x` misses `μ` by more
than `t` for at most a third of the samples `x`, the median of `2 r` independent estimates misses
`μ` by more than `t` for at most an `(8 / 9) ^ r` fraction of the samples. -/
theorem dens_abs_median_sub_gt_le [Nonempty Ω] (g : Ω → ℝ) {μ t : ℝ}
    (hg : (dens {x | t < |g x - μ|} : ℝ) ≤ 1 / 3) (r : ℕ) :
    (dens {ω : Fin (2 * r) → Ω | t < |median (fun i => g (ω i)) - μ|} : ℝ) ≤ (8 / 9) ^ r := by
  classical
  let G : Finset Ω := {x | |g x - μ| ≤ t}
  have hGc : Gᶜ = ({x | t < |g x - μ|} : Finset Ω) := by
    ext x
    simp only [G, mem_compl, mem_filter, mem_univ, true_and, not_le]
  have hG : 2 * Fintype.card Ω ≤ 3 * G.card := by
    have h := card_compl_add_card G
    have hc : 3 * Gᶜ.card ≤ Fintype.card Ω := by
      rw [hGc]
      rw [nnratCast_dens, div_le_iff₀ (Nat.cast_pos.2 Fintype.card_pos)] at hg
      exact_mod_cast (by linarith : (3 * #({x | t < |g x - μ|} : Finset Ω) : ℝ) ≤
        Fintype.card Ω)
    omega
  have hmaj := card_filter_card_filter_le_le G hG r
  -- A sample with a majority of good estimates has a good median.
  have hsub : ({ω : Fin (2 * r) → Ω | t < |median (fun i => g (ω i)) - μ|} :
      Finset (Fin (2 * r) → Ω)) ⊆ ({ω | #{i | ω i ∈ G} ≤ r} : Finset (Fin (2 * r) → Ω)) :=
    fun ω hω => by
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      by_contra hlt
      rw [not_le] at hlt
      refine not_le.2 hω (abs_median_sub_le ?_)
      have : #{i | ω i ∈ G} = #{j | |g (ω j) - μ| ≤ t} := by
        congr 1
        ext i
        simp only [G, mem_filter, mem_univ, true_and]
      rw [Fintype.card_fin, ← this]
      omega
  calc (dens {ω : Fin (2 * r) → Ω | t < |median (fun i => g (ω i)) - μ|} : ℝ)
      ≤ dens ({ω | #{i | ω i ∈ G} ≤ r} : Finset (Fin (2 * r) → Ω)) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ (8 / 9) ^ r := by
      rw [nnratCast_dens, div_le_iff₀ (Nat.cast_pos.2 Fintype.card_pos), div_pow,
        div_mul_eq_mul_div, le_div_iff₀ (by positivity), Fintype.card_pi_const Ω, mul_comm]
      exact_mod_cast hmaj

end Cslib.Probability
