/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.MarkovChain.Coloring
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Expect
import Complexity.Foundations.Analysis.SpecialFunctions.ExpOneSubInvPow
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Freezing one vertex keeps a fraction of the colorings

Fix a proper coloring `b` of a graph `G` with maximum degree `Δ`, a set `U` of vertices and
`v ∈ U`, and let `X_U` be the proper `q`-colorings agreeing with `b` off `U`
(`SimpleGraph.frozenColorings`). Freezing `v` at its color `b v` keeps a fraction at least
`(1 - 1 / (q - Δ)) ^ Δ / q` of `X_U` when `Δ < q`
(`Cslib.Probability.MarkovChain.mul_card_frozenColorings_le_card_erase`), hence at least
`1 / (e q)` when `2Δ < q`
(`Cslib.Probability.MarkovChain.inv_exp_mul_le_card_frozenColorings_erase_div`). This is
[LevinPeres2017], Lemma 14.16, the lower bound on the ratios `|X_{k-1}| / |X_k|` estimated by the
approximate counting algorithm of [LevinPeres2017], Section 14.4.2.

The proof follows [LevinPeres2017]. Start from the uniform distribution `π` on `X_U` and recolor,
by heat-bath updates (`Cslib.Probability.MarkovChain.recolor`), the neighbors of `v` in `U` and
then `v`. Each update preserves `π` (`Cslib.Probability.MarkovChain.isStationary_recolor_frozen`).
An update at a neighbor avoids `b v` with probability at least `1 - 1 / (q - Δ)`, since at least
`q - Δ` colors are allowed. Once no neighbor has color `b v`, which already holds off `U` because
`b` is proper, the update at `v` picks `b v` with probability at least `1 / q`. The ending
distribution is `π`, and `x v = b v` is the event `x ∈ X_{U \ {v}}`.

## Main results

* `Cslib.Probability.MarkovChain.sum_uniformOfFinset_frozenColorings_ite`: under the uniform
  distribution on `X_U`, the probability that `x v = b v` is `|X_{U \ {v}}| / |X_U|`.
* `Cslib.Probability.MarkovChain.mul_card_frozenColorings_le_card_erase`: the bound
  `(1 - 1 / (q - Δ)) ^ Δ / q`.
* `Cslib.Probability.MarkovChain.inv_exp_mul_le_card_frozenColorings_erase_div`:
  [LevinPeres2017], Lemma 14.16.

## References

* [LevinPeres2017], Section 14.4.2.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF SimpleGraph

variable {V : Type*} {q : ℕ} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If every state of `E` in the support of `μ` moves into `E'` with probability at least `p`,
the probability of `E'` after one step is at least `p` times the probability of `E`. -/
private theorem le_sum_bind_ite {α : Type*} [Fintype α] (μ : PMF α) (K : α → PMF α)
    (E E' : α → Prop) [DecidablePred E] [DecidablePred E'] {p : ℝ}
    (hK : ∀ x, μ x ≠ 0 → E x → p ≤ ∑ y, (K x y).toReal * if E' y then 1 else 0) :
    p * ∑ x, (μ x).toReal * (if E x then 1 else 0) ≤
      ∑ y, ((μ.bind K) y).toReal * if E' y then 1 else 0 := by
  rw [sum_bind_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hμ : μ x = 0
  · rw [hμ, ENNReal.toReal_zero, zero_mul, zero_mul, mul_zero]
  by_cases hx : E x
  · rw [ite_eq_left hx, mul_one, mul_comm]
    exact mul_le_mul_of_nonneg_left (hK x hμ hx) ENNReal.toReal_nonneg
  · rw [ite_eq_right hx, mul_zero, mul_zero]
    exact mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun y _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))

/-- Under the uniform distribution on `X_U`, the probability that `x v = b v` is
`|X_{U \ {v}}| / |X_U|`. -/
theorem sum_uniformOfFinset_frozenColorings_ite {U : Finset V} {b : V → Fin q}
    (hne : (frozenColorings G q U b).Nonempty) (v : V) :
    ∑ x, ((uniformOfFinset (frozenColorings G q U b) hne) x).toReal *
        (if x v = b v then 1 else 0) =
      ((frozenColorings G q (U.erase v) b).card : ℝ) / (frozenColorings G q U b).card := by
  have hπ (x : V → Fin q) : ((uniformOfFinset (frozenColorings G q U b) hne) x).toReal *
      (if x v = b v then 1 else 0) =
        if x ∈ frozenColorings G q (U.erase v) b then
          ((frozenColorings G q U b).card : ℝ)⁻¹ else 0 := by
    rw [uniformOfFinset_apply, frozenColorings_erase]
    by_cases hx : x ∈ frozenColorings G q U b <;> by_cases hxv : x v = b v <;>
      simp [hx, hxv, Finset.mem_filter]
  simp only [hπ]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Freezing a vertex** ([LevinPeres2017], proof of Lemma 14.16): if `b` is a proper coloring,
`Δ < q` and `v ∈ U`, then freezing `v` at `b v` keeps a fraction at least
`(1 - 1 / (q - Δ)) ^ Δ / q` of the colorings agreeing with `b` off `U`. -/
theorem mul_card_frozenColorings_le_card_erase (hq : G.maxDegree < q) {b : V → Fin q}
    (hb : G.IsProperColoring b) {U : Finset V} {v : V} (hv : v ∈ U) :
    (1 - 1 / ((q - G.maxDegree : ℕ) : ℝ)) ^ G.maxDegree / q *
        (frozenColorings G q U b).card ≤ (frozenColorings G q (U.erase v) b).card := by
  have hne : (frozenColorings G q U b).Nonempty := ⟨b, mem_frozenColorings_self hb⟩
  set π := uniformOfFinset (frozenColorings G q U b) hne with hπ_def
  set r : ℝ := 1 - 1 / ((q - G.maxDegree : ℕ) : ℝ) with hr_def
  have hD : (1 : ℝ) ≤ ((q - G.maxDegree : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ q - G.maxDegree)
  have hr0 : 0 ≤ r := by
    rw [hr_def, sub_nonneg]
    exact div_le_one_of_le₀ hD (by linarith)
  have hr1 : r ≤ 1 := by
    rw [hr_def, sub_le_self_iff]
    positivity
  have hstat (w : V) (hw : w ∈ U) : π.bind (recolor G · w) = π :=
    isStationary_recolor_frozen G hne hw
  -- recoloring the vertices of `F ⊆ U` one at a time: no vertex of `F` has color `b v`
  have hF : ∀ F : Finset V, F ⊆ U →
      r ^ F.card ≤ ∑ x, (π x).toReal * if ∀ u ∈ F, x u ≠ b v then 1 else 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, ite_true, mul_one,
        Finset.card_empty, pow_zero]
      exact (sum_toReal π).ge
    | @insert w F hwF ih =>
      intro hsub
      have hwU : w ∈ U := hsub (Finset.mem_insert_self w F)
      have ih' := ih ((Finset.subset_insert w F).trans hsub)
      have key := le_sum_bind_ite π (recolor G · w) (fun x => ∀ u ∈ F, x u ≠ b v)
        (fun x => ∀ u ∈ insert w F, x u ≠ b v) (p := r) ?_
      · rw [hstat w hwU] at key
        calc r ^ (insert w F).card = r ^ F.card * r := by
              rw [Finset.card_insert_of_notMem hwF, pow_succ]
          _ ≤ (∑ x, (π x).toReal * if ∀ u ∈ F, x u ≠ b v then 1 else 0) * r :=
              mul_le_mul_of_nonneg_right ih' hr0
          _ = r * ∑ x, (π x).toReal * if ∀ u ∈ F, x u ≠ b v then 1 else 0 := mul_comm _ _
          _ ≤ _ := key
      intro x _ hx
      have hA := G.allowedColors_nonempty hq x w
      rw [recolor_of_nonempty G hA, sum_map_mul]
      have hupd (c' : Fin q) : (if ∀ u ∈ insert w F, Function.update x w c' u ≠ b v then
          (1 : ℝ) else 0) = 1 - if c' = b v then 1 else 0 := by
        by_cases hc' : c' = b v
        · rw [ite_eq_right fun h => h w (Finset.mem_insert_self w F)
            (by rw [Function.update_self, hc']), ite_eq_left hc', sub_self]
        · rw [ite_eq_right hc', sub_zero, ite_eq_left]
          intro u hu
          rcases Finset.mem_insert.1 hu with rfl | hu
          · rw [Function.update_self]
            exact hc'
          · rw [Function.update_of_ne (show u ≠ w from fun h => hwF (h ▸ hu))]
            exact hx u hu
      simp only [hupd, mul_sub, mul_one, Finset.sum_sub_distrib, sum_toReal]
      have hsum : ∑ c', ((uniformOfFinset (G.allowedColors x w) hA) c').toReal *
          (if c' = b v then (1 : ℝ) else 0) =
            ((uniformOfFinset (G.allowedColors x w) hA) (b v)).toReal := by
        rw [Finset.sum_eq_single (b v) (fun c' _ hc' => by rw [ite_eq_right hc', mul_zero])
          (fun h => absurd (Finset.mem_univ (b v)) h), ite_eq_left rfl, mul_one]
      rw [hsum, hr_def]
      have hcard : (((q - G.maxDegree : ℕ) : ℝ)) ≤ (G.allowedColors x w).card := by
        exact_mod_cast G.sub_maxDegree_le_card_allowedColors x w
      have hle : ((uniformOfFinset (G.allowedColors x w) hA) (b v)).toReal ≤
          1 / ((q - G.maxDegree : ℕ) : ℝ) := by
        rw [uniformOfFinset_apply]
        split_ifs
        · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, ← one_div]
          exact one_div_le_one_div_of_le (by linarith) hcard
        · rw [ENNReal.toReal_zero]
          positivity
      linarith
  -- the neighbors of `v` in `U`
  set F := U.filter fun u => G.Adj v u with hF_def
  have hFcard : F.card ≤ G.maxDegree := by
    refine (Finset.card_le_card fun u hu => ?_).trans
      ((G.card_neighborFinset_eq_degree v).trans_le (G.degree_le_maxDegree v))
    rw [hF_def, Finset.mem_filter] at hu
    exact (G.mem_neighborFinset v u).2 hu.2
  -- the final update at `v` picks `b v` with probability at least `1 / q`
  have hfinal : 1 / (q : ℝ) * ∑ x, (π x).toReal * (if ∀ u ∈ F, x u ≠ b v then 1 else 0) ≤
      ∑ x, (π x).toReal * if x v = b v then 1 else 0 := by
    have key := le_sum_bind_ite π (recolor G · v) (fun x => ∀ u ∈ F, x u ≠ b v)
      (fun x => x v = b v) (p := 1 / (q : ℝ)) ?_
    · rwa [hstat v hv] at key
    intro x hxπ hx
    obtain ⟨hxp, hxb⟩ := mem_frozenColorings.1
      ((mem_support_uniformOfFinset_iff hne x).1 ((PMF.mem_support_iff _ _).2 hxπ))
    have hbv : b v ∈ G.allowedColors x v := by
      refine (mem_allowedColors G).2 fun u hu => ?_
      by_cases huU : u ∈ U
      · exact hx u (Finset.mem_filter.2 ⟨huU, hu⟩)
      · rw [hxb u huU]
        exact (((isProperColoring_iff G).1 hb) v u hu).symm
    have hA : (G.allowedColors x v).Nonempty := ⟨b v, hbv⟩
    rw [recolor_of_nonempty G hA, sum_map_mul]
    simp only [Function.update_self]
    rw [Finset.sum_eq_single (b v) (fun c' _ hc' => by rw [ite_eq_right hc', mul_zero])
      (fun h => absurd (Finset.mem_univ (b v)) h), ite_eq_left rfl, mul_one,
      uniformOfFinset_apply, ite_eq_left hbv, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ← one_div]
    refine one_div_le_one_div_of_le (Nat.cast_pos.2 hA.card_pos) ?_
    have := Finset.card_le_univ (G.allowedColors x v)
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hX : (0 : ℝ) < (frozenColorings G q U b).card := Nat.cast_pos.2 hne.card_pos
  have hratio := sum_uniformOfFinset_frozenColorings_ite hne v
  rw [← hπ_def] at hratio
  have hmain : r ^ G.maxDegree / q ≤
      ((frozenColorings G q (U.erase v) b).card : ℝ) / (frozenColorings G q U b).card := by
    rw [← hratio]
    calc r ^ G.maxDegree / q = 1 / (q : ℝ) * r ^ G.maxDegree := by ring
      _ ≤ 1 / (q : ℝ) * ∑ x, (π x).toReal * (if ∀ u ∈ F, x u ≠ b v then 1 else 0) :=
          mul_le_mul_of_nonneg_left
            ((pow_le_pow_of_le_one hr0 hr1 hFcard).trans (hF F (Finset.filter_subset _ _)))
            (by positivity)
      _ ≤ _ := hfinal
  rwa [le_div_iff₀ hX] at hmain

/-- **The ratios are not too small** ([LevinPeres2017], Lemma 14.16): if `b` is a proper
coloring, `2Δ < q` and `v ∈ U`, then freezing `v` at `b v` keeps a fraction at least `1 / (e q)`
of the colorings agreeing with `b` off `U`. -/
theorem inv_exp_mul_le_card_frozenColorings_erase_div (hq : 2 * G.maxDegree < q) {b : V → Fin q}
    (hb : G.IsProperColoring b) {U : Finset V} {v : V} (hv : v ∈ U) :
    (Real.exp 1 * q)⁻¹ ≤
      ((frozenColorings G q (U.erase v) b).card : ℝ) / (frozenColorings G q U b).card := by
  have hne : (frozenColorings G q U b).Nonempty := ⟨b, mem_frozenColorings_self hb⟩
  have hX : (0 : ℝ) < (frozenColorings G q U b).card := Nat.cast_pos.2 hne.card_pos
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (by omega)
  have h := mul_card_frozenColorings_le_card_erase (by omega) hb hv
  have hexp : Real.exp (-1) ≤ (1 - 1 / ((q - G.maxDegree : ℕ) : ℝ)) ^ G.maxDegree := by
    rw [one_div]
    refine Real.exp_neg_one_le_one_sub_inv_pow ?_
    exact_mod_cast (by omega : G.maxDegree + 1 ≤ q - G.maxDegree)
  rw [le_div_iff₀ hX]
  calc (Real.exp 1 * q)⁻¹ * (frozenColorings G q U b).card
      = Real.exp (-1) / q * (frozenColorings G q U b).card := by
        rw [Real.exp_neg, mul_inv]
        ring
    _ ≤ (1 - 1 / ((q - G.maxDegree : ℕ) : ℝ)) ^ G.maxDegree / q *
          (frozenColorings G q U b).card := by
        gcongr
    _ ≤ _ := h

end Cslib.Probability.MarkovChain
