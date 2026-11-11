/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Copositive
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Motzkin–Straus theorem

For a finite simple graph `G` on a nonempty vertex type `V` with clique number `ω(G)`, the
maximum of the quadratic form `x ⬝ᵥ G.adjMatrix K *ᵥ x` over the standard simplex
`Convexity.StdSimplex K V` equals `1 - 1 / ω(G)` (note that [MotzkinStraus1965] sums over
unordered edges `∑_{ij ∈ E} x_i x_j = (1 / 2) * (x ⬝ᵥ G.adjMatrix K *ᵥ x)`, differing by a factor
of `2`). This generalizes the real Motzkin–Straus theorem (attributed to [MotzkinStraus1965], cited
from bibliographic metadata only without inspecting the published text) to any linearly ordered
field `K` (including `ℚ` and `ℝ`); the `K`-generalization and the
`SimpleGraph.copositiveCliqueMatrix` packaging below are original formulations of this library:

* **Upper bound** (`SimpleGraph.quadraticForm_adjMatrix_le_stdSimplex`): by strong induction on
  the support size of `x : Convexity.StdSimplex K V`. Whenever two distinct vertices `u, v` in the
  support of `x` are nonadjacent, shifting weight along `e_u - e_v` changes
  `x ⬝ᵥ G.adjMatrix K *ᵥ x` linearly; moving all weight of `v` onto `u` or vice versa strictly
  shrinks the support without decreasing the quadratic form. Once the support is a clique `S`,
  Cauchy–Schwarz gives
  `x ⬝ᵥ G.adjMatrix K *ᵥ x = 1 - ∑ v ∈ S, x v ^ 2 ≤ 1 - 1 / #S ≤ 1 - 1 / ω(G)`.
* **Attainment** (`SimpleGraph.exists_stdSimplex_quadraticForm_adjMatrix_eq_of_isNClique`): the
  uniform distribution on a maximum clique achieves `1 - 1 / ω(G)`.

We also record the integer matrix `SimpleGraph.copositiveCliqueMatrix G k` with entries `-1` on
edges and `k - 2` on non-edges and the diagonal, which is non-copositive iff `k ≤ G.cliqueNum`
(`SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff`) for `k ≥ 2` on a
nonempty finite graph.

## Main definitions

* `SimpleGraph.copositiveCliqueMatrix`: the integer symmetric matrix `(k - 2) J - (k - 1) A_G`.

## Main results

* `SimpleGraph.quadraticForm_adjMatrix_le_stdSimplex`: Motzkin–Straus upper bound over any
  linearly ordered field.
* `SimpleGraph.isGreatest_quadraticForm_adjMatrix`: Motzkin–Straus identity
  `max_{x : StdSimplex K V} xᵀ A_G x = 1 - 1 / ω(G)` over any linearly ordered field.
* `SimpleGraph.sSup_quadraticForm_adjMatrix`: the real `sSup` form.
* `SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff`: non-copositivity of
  `copositiveCliqueMatrix G k` characterizes `k ≤ G.cliqueNum` for `2 ≤ k`.

## References

* [T. S. Motzkin, E. G. Straus, *Maxima for graphs and a new proof of a theorem of Turán*,
  Canadian Journal of Mathematics 17 (1965), 533–540][MotzkinStraus1965] (bibliographic metadata
  only; the published article text is uninspected, and no internal theorem numbers are claimed).
-/

public section

open Finset Matrix

namespace SimpleGraph

section MotzkinStraus

variable {V K : Type*}

/-- Expanding `x ⬝ᵥ G.adjMatrix K *ᵥ x` as a double sum over adjacent pairs. -/
private theorem dotProduct_adjMatrix_eq_sum [Fintype V] [CommSemiring K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → K) :
    x ⬝ᵥ G.adjMatrix K *ᵥ x = ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
  simp only [dotProduct, mulVec, adjMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

/-- On a clique, the adjacency quadratic form of a vector supported inside it is
`(∑ x_v)^2 - ∑ x_v^2`. -/
private theorem dotProduct_adjMatrix_eq_of_isClique [Fintype V] [CommRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : G.IsClique (S : Set V)) {x : V → K} (hx : ∀ v, v ∉ S → x v = 0) :
    x ⬝ᵥ G.adjMatrix K *ᵥ x = (∑ v ∈ S, x v) ^ 2 - ∑ v ∈ S, x v ^ 2 := by
  classical
  rw [dotProduct_adjMatrix_eq_sum]
  have hzero : ∀ u, u ∉ S → ∑ v : V, (if G.Adj u v then x u * x v else 0) = 0 := fun u hu =>
    Finset.sum_eq_zero fun v _ => by split_ifs <;> simp only [hx u hu, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun u _ hu => hzero u hu]
  have hinner : ∀ u ∈ S, ∑ v : V, (if G.Adj u v then x u * x v else 0) =
      ∑ v ∈ S, if u = v then 0 else x u * x v := fun u hu => by
    have hsub : ∀ v, v ∉ S → (if G.Adj u v then x u * x v else 0) = 0 := fun v hv => by
      split_ifs <;> simp only [hx v hv, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hsub v hv]
    refine Finset.sum_congr rfl fun v hv => ?_
    by_cases huv : u = v
    · subst huv
      simp only [G.loopless.irrefl u, ↓reduceIte]
    · simp only [huv, ↓reduceIte, hS hu hv huv]
  rw [Finset.sum_congr rfl hinner]
  have hsq : (∑ v ∈ S, x v) ^ 2 =
      (∑ u ∈ S, ∑ v ∈ S, if u = v then 0 else x u * x v) + ∑ v ∈ S, x v ^ 2 := by
    rw [sq, Finset.sum_mul]
    have hsplit : ∀ u ∈ S, ∑ v ∈ S, x u * x v =
        (∑ v ∈ S, if u = v then 0 else x u * x v) + x u ^ 2 := fun u hu => by
      have heq : ∑ v ∈ S, x u * x v =
          ∑ v ∈ S, ((if u = v then 0 else x u * x v) + if u = v then x u * x u else 0) :=
        Finset.sum_congr rfl fun v _ => by
          split_ifs with h
          · rw [h, zero_add]
          · rw [add_zero]
      have heq' : (∑ v ∈ S, if u = v then x u * x u else 0) = x u ^ 2 := by
        rw [Finset.sum_ite_eq S u (fun _ => x u * x u)]
        split_ifs
        exact (sq (x u)).symm
      rw [heq, Finset.sum_add_distrib, heq']
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  exact eq_sub_of_add_eq hsq.symm

/-- Linear variation along `Pi.single u 1 - Pi.single v 1` when `u ≠ v` are nonadjacent. -/
private theorem dotProduct_adjMatrix_add_smul [Fintype V] [DecidableEq V] [CommRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (hadj : ¬G.Adj u v) (x : V → K) (t : K) :
    let d : V → K := Pi.single u 1 - Pi.single v 1
    (x + t • d) ⬝ᵥ G.adjMatrix K *ᵥ (x + t • d) =
      x ⬝ᵥ G.adjMatrix K *ᵥ x + 2 * t * ((G.adjMatrix K *ᵥ x) u - (G.adjMatrix K *ᵥ x) v) := by
  intro d
  set A := G.adjMatrix K
  have hdAx : d ⬝ᵥ (A *ᵥ x) = (A *ᵥ x) u - (A *ᵥ x) v := by
    simp only [d, Pi.sub_apply, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdAd : d ⬝ᵥ (A *ᵥ d) = 0 := by
    have hrow (w : V) : (A *ᵥ d) w = A w u - A w v := by
      simp only [d, mulVec, dotProduct, Pi.sub_apply, Pi.single_apply, mul_sub,
        Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    have hAd : d ⬝ᵥ (A *ᵥ d) = (A *ᵥ d) u - (A *ᵥ d) v := by
      simp only [d, Pi.sub_apply, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hAd, hrow u, hrow v]
    have hadj' : ¬G.Adj v u := fun h => hadj h.symm
    have huu : ¬G.Adj u u := G.loopless.irrefl u
    have hvv : ¬G.Adj v v := G.loopless.irrefl v
    simp only [A, adjMatrix_apply, huu, hvv, hadj, hadj', ↓reduceIte, sub_self]
  rw [Matrix.dotProduct_add_smul_symm G.transpose_adjMatrix x d t, hdAx, hdAd, mul_zero, add_zero]

private theorem quadraticForm_adjMatrix_le_aux [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V → K} (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∑ v, x v = 1) :
    x ⬝ᵥ G.adjMatrix K *ᵥ x ≤ 1 - 1 / (G.cliqueNum : K) := by
  classical
  suffices h : ∀ k (x : V → K), #{v | x v ≠ 0} = k → (∀ v, 0 ≤ x v) → ∑ v, x v = 1 →
      x ⬝ᵥ G.adjMatrix K *ᵥ x ≤ 1 - 1 / (G.cliqueNum : K) from h _ x rfl hx0 hx1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hk hx0 hx1
  set S : Finset V := {v | x v ≠ 0}
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hz : ∑ v, x v = 0 := Finset.sum_eq_zero fun v _ => by
      by_contra hne
      have : v ∈ S := by simp [S, hne]
      rw [hemp] at this
      exact Finset.notMem_empty v this
    linarith
  by_cases hclique : G.IsClique (S : Set V)
  · have hquad : x ⬝ᵥ G.adjMatrix K *ᵥ x = 1 - ∑ v ∈ S, x v ^ 2 := by
      have hxout : ∀ v, v ∉ S → x v = 0 := fun v hv => by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
      rw [dotProduct_adjMatrix_eq_of_isClique G hclique hxout]
      have hsum : ∑ v ∈ S, x v = 1 := by
        rw [← hx1]
        exact Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hxout v hv
      rw [hsum, one_pow]
    have hcs : (1 : K) ≤ (S.card : K) * ∑ v ∈ S, x v ^ 2 := by
      have hsum : ∑ v ∈ S, x v = 1 := by
        rw [← hx1]
        exact Finset.sum_subset (Finset.subset_univ S) fun v _ hv => by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
      simpa only [hsum, one_pow] using (sq_sum_le_card_mul_sum_sq (s := S) (f := x))
    have hScard_pos : 0 < S.card := Finset.card_pos.2 hSne
    have hScard_le : S.card ≤ G.cliqueNum := hclique.card_le_cliqueNum
    have hScardK : (0 : K) < S.card := by exact_mod_cast hScard_pos
    have homegaK : (S.card : K) ≤ G.cliqueNum := by exact_mod_cast hScard_le
    have hinv_le : 1 / (G.cliqueNum : K) ≤ 1 / (S.card : K) :=
      one_div_le_one_div_of_le hScardK homegaK
    have hinv_sum : 1 / (S.card : K) ≤ ∑ v ∈ S, x v ^ 2 := by
      rw [div_le_iff₀' hScardK]
      exact hcs
    rw [hquad]
    linarith
  · simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, not_forall] at hclique
    obtain ⟨u, huS, v, hvS, huv, hadj⟩ := hclique
    have hxu_pos : 0 < x u := lt_of_le_of_ne (hx0 u) (Ne.symm (by simpa [S] using huS))
    have hxv_pos : 0 < x v := lt_of_le_of_ne (hx0 v) (Ne.symm (by simpa [S] using hvS))
    let d : V → K := Pi.single u 1 - Pi.single v 1
    have hdsum : ∑ w : V, d w = 0 := by
      simp [d, Finset.sum_sub_distrib]
    have hstep (t : K) (ht1 : 0 ≤ x u + t) (ht2 : 0 ≤ x v - t) :
        (∀ w, 0 ≤ (x + t • d) w) ∧ ∑ w, (x + t • d) w = 1 := by
      refine ⟨fun w => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply, Pi.single_apply]
        by_cases hwu : w = u
        · subst hwu
          simpa [huv] using ht1
        · by_cases hwv : w = v
          · subst hwv
            simpa [Ne.symm huv] using ht2
          · simpa [hwu, hwv] using hx0 w
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hdsum, mul_zero, add_zero, hx1]
    have hlt_supp (t : K) (hzero : (x + t • d) u = 0 ∨ (x + t • d) v = 0) :
        #{w | (x + t • d) w ≠ 0} < k := by
      rw [← hk]
      apply Finset.card_lt_card
      refine ⟨fun w hw => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        by_contra hxw
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hxw
        have hwu : w ≠ u := fun h => by subst h; exact hxu_pos.ne' hxw
        have hwv : w ≠ v := fun h => by subst h; exact hxv_pos.ne' hxw
        apply hw
        simp [d, hxw, hwu, hwv]
      · rcases hzero with hzu | hzv
        · have := hsub huS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this hzu
        · have := hsub hvS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this hzv
    rcases le_total ((G.adjMatrix K *ᵥ x) v) ((G.adjMatrix K *ᵥ x) u) with hle | hle
    · have ht := hstep (x v) (by linarith) (by linarith)
      have hlt := hlt_supp (x v) (Or.inr (by simp [d, Ne.symm huv]))
      have hih := ih _ hlt (x + x v • d) rfl ht.1 ht.2
      have hlin := dotProduct_adjMatrix_add_smul G hadj x (x v)
      dsimp only at hlin
      have hnonneg : 0 ≤ 2 * x v * ((G.adjMatrix K *ᵥ x) u - (G.adjMatrix K *ᵥ x) v) :=
        mul_nonneg (mul_nonneg (by norm_num) hxv_pos.le) (sub_nonneg.2 hle)
      linarith
    · have ht := hstep (-x u) (by linarith) (by linarith)
      have hlt := hlt_supp (-x u) (Or.inl (by simp [d, huv]))
      have hih := ih _ hlt (x + (-x u) • d) rfl ht.1 ht.2
      have hlin := dotProduct_adjMatrix_add_smul G hadj x (-x u)
      dsimp only at hlin
      have hnonneg : 0 ≤ 2 * (-x u) * ((G.adjMatrix K *ᵥ x) u - (G.adjMatrix K *ᵥ x) v) := by
        have : 2 * (-x u) * ((G.adjMatrix K *ᵥ x) u - (G.adjMatrix K *ᵥ x) v) =
            2 * x u * ((G.adjMatrix K *ᵥ x) v - (G.adjMatrix K *ᵥ x) u) := by ring
        rw [this]
        exact mul_nonneg (mul_nonneg (by norm_num) hxu_pos.le) (sub_nonneg.2 hle)
      linarith

/-- **Motzkin–Straus upper bound**: on `Convexity.StdSimplex K V`, `x ⬝ᵥ G.adjMatrix K *ᵥ x`
is at most `1 - 1 / G.cliqueNum` (library generalization over arbitrary linearly ordered fields `K`;
[MotzkinStraus1965] was not inspected directly). -/
theorem quadraticForm_adjMatrix_le_stdSimplex [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : Convexity.StdSimplex K V) :
    (x.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (x.weights : V → K) ≤ 1 - 1 / (G.cliqueNum : K) :=
  quadraticForm_adjMatrix_le_aux G x.weights_nonneg x.total_of_fintype

/-- The uniform weight vector on a `k`-clique (`1 ≤ k`) gives a point of
`Convexity.StdSimplex K V` achieving `1 - 1 / k`. -/
theorem exists_stdSimplex_quadraticForm_adjMatrix_eq_of_isNClique [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {k : ℕ} (hk : 1 ≤ k)
    (hS : G.IsNClique k S) :
    ∃ x : Convexity.StdSimplex K V,
      (x.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (x.weights : V → K) = 1 - 1 / (k : K) := by
  classical
  let xVec : V → K := fun v => if v ∈ S then 1 / (k : K) else 0
  have hkpos : (0 : K) < k := by exact_mod_cast hk
  have hk_ne : (k : K) ≠ 0 := hkpos.ne'
  have hx0 : ∀ v, 0 ≤ xVec v := fun v => by dsimp only [xVec]; split_ifs <;> positivity
  have hx1 : ∑ v : V, xVec v = 1 := by
    have hite : ∑ v : V, xVec v = ∑ _v ∈ S, (1 / (k : K)) := by
      dsimp only [xVec]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hite, Finset.sum_const, hS.card_eq, nsmul_eq_mul, mul_one_div_cancel hk_ne]
  let x : Convexity.StdSimplex K V :=
    { weights := Finsupp.equivFunOnFinite.symm xVec
      nonneg := fun v => by
        simpa only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_equivFunOnFinite_symm] using hx0 v
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        simpa only [Finsupp.coe_equivFunOnFinite_symm] using hx1 }
  refine ⟨x, ?_⟩
  rw [show (x.weights : V → K) = xVec from Finsupp.coe_equivFunOnFinite_symm xVec]
  have hxout : ∀ v, v ∉ S → xVec v = 0 := fun v hv => by
    dsimp only [xVec]
    split_ifs
    rfl
  rw [dotProduct_adjMatrix_eq_of_isClique G hS.isClique hxout]
  have hs1 : ∑ v ∈ S, xVec v = 1 := by
    have heq : ∑ v ∈ S, xVec v = ∑ _v ∈ S, (1 / (k : K)) :=
      Finset.sum_congr rfl fun v hv => by
        dsimp only [xVec]
        split_ifs
        rfl
    rw [heq, Finset.sum_const, hS.card_eq, nsmul_eq_mul, mul_one_div_cancel hk_ne]
  have hs2 : ∑ v ∈ S, xVec v ^ 2 = 1 / (k : K) := by
    have heq : ∑ v ∈ S, xVec v ^ 2 = ∑ _v ∈ S, (1 / (k : K)) ^ 2 :=
      Finset.sum_congr rfl fun v hv => by
        dsimp only [xVec]
        split_ifs
        rfl
    rw [heq, Finset.sum_const, hS.card_eq, nsmul_eq_mul, sq, ← mul_assoc,
      mul_one_div_cancel hk_ne, one_mul]
  rw [hs1, hs2, one_pow]

/-- **The Motzkin–Straus theorem** (library generalization to arbitrary linearly ordered fields `K`;
[MotzkinStraus1965] is cited at paper level without inspecting the published text): on a nonempty
finite graph, the maximum of `x ⬝ᵥ G.adjMatrix K *ᵥ x` over `Convexity.StdSimplex K V` equals
`1 - 1 / G.cliqueNum`. Note that [MotzkinStraus1965] maximizes
`∑_{ij ∈ E} x_i x_j = (1 / 2) * (x ⬝ᵥ G.adjMatrix K *ᵥ x)`, giving `(1 / 2) * (1 - 1 / ω(G))`
(differing by a factor of `2`). -/
theorem isGreatest_quadraticForm_adjMatrix [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj] :
    IsGreatest
      (Set.range fun x : Convexity.StdSimplex K V =>
        (x.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (x.weights : V → K))
      (1 - 1 / (G.cliqueNum : K)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS⟩ := G.exists_isNClique_cliqueNum
    have hpos : 1 ≤ G.cliqueNum := Nat.one_le_iff_ne_zero.2 G.cliqueNum_ne_zero_of_finite
    obtain ⟨x, hxeq⟩ :=
      exists_stdSimplex_quadraticForm_adjMatrix_eq_of_isNClique (K := K) G hpos hS
    exact ⟨x, hxeq⟩
  · rintro _ ⟨x, rfl⟩
    exact quadraticForm_adjMatrix_le_stdSimplex G x

/-- **The Motzkin–Straus theorem** over `ℝ` in `sSup` form (attributed to [MotzkinStraus1965];
the published text is uninspected, and [MotzkinStraus1965] includes a factor of `1 / 2` from
summing over unordered edges). -/
theorem sSup_quadraticForm_adjMatrix [Fintype V]
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj] :
    sSup
        (Set.range fun x : Convexity.StdSimplex ℝ V =>
          (x.weights : V → ℝ) ⬝ᵥ G.adjMatrix ℝ *ᵥ (x.weights : V → ℝ)) =
      1 - 1 / (G.cliqueNum : ℝ) :=
  (isGreatest_quadraticForm_adjMatrix G).csSup_eq

/-! ### Copositive matrix characterization of the clique number -/

/-- The symmetric integer matrix `(k - 2) J - (k - 1) A_G` (library packaging for the clique
reduction): entries are `-1` on edges of `G` and `k - 2` on non-edges and the diagonal. For
`k ≥ 2` on a nonempty finite graph, this matrix fails to be copositive iff `G` has a `k`-clique. -/
@[expose] def copositiveCliqueMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Matrix V V ℤ :=
  of fun u v => if G.Adj u v then (-1 : ℤ) else (k : ℤ) - 2

@[simp]
theorem copositiveCliqueMatrix_apply (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (u v : V) :
    G.copositiveCliqueMatrix k u v = if G.Adj u v then (-1 : ℤ) else (k : ℤ) - 2 :=
  rfl

theorem isSymm_copositiveCliqueMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (G.copositiveCliqueMatrix k).IsSymm := by
  ext u v
  simp only [transpose_apply, copositiveCliqueMatrix_apply, adj_comm]

/-- On any vector, `x ⬝ᵥ M *ᵥ x = (k - 2) * (∑ x_v)^2 - (k - 1) * (x ⬝ᵥ A_G *ᵥ x)`. -/
theorem dotProduct_copositiveCliqueMatrix [Fintype V] [CommRing K]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (x : V → K) :
    x ⬝ᵥ ((G.copositiveCliqueMatrix k).map (Int.cast : ℤ → K) *ᵥ x) =
      ((k : K) - 2) * (∑ v, x v) ^ 2 - ((k : K) - 1) * (x ⬝ᵥ G.adjMatrix K *ᵥ x) := by
  rw [dotProduct_adjMatrix_eq_sum]
  simp only [dotProduct, mulVec, map_apply, copositiveCliqueMatrix_apply, Finset.mul_sum]
  have lhs_eq :
      (∑ u : V, ∑ v : V,
          x u * ((Int.cast (if G.Adj u v then (-1 : ℤ) else (k : ℤ) - 2) : K) * x v)) =
        ((k : K) - 2) * (∑ u : V, ∑ v : V, x u * x v) -
          ((k : K) - 1) * (∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0) := by
    trans ∑ u : V, ∑ v : V, (((k : K) - 2) * (x u * x v) -
        ((k : K) - 1) * (if G.Adj u v then x u * x v else 0))
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> push_cast <;> ring
    · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hprod : (∑ u : V, ∑ v : V, x u * x v) = ∑ v : V, x v * ∑ v' : V, x v' :=
    Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
  rw [lhs_eq, sq, Finset.sum_mul, hprod]
  congr 1
  simp only [Finset.mul_sum]

/-- For `k ≥ 2` on a nonempty finite graph, `copositiveCliqueMatrix G k` is non-copositive iff
`G` has a clique of size `k`. -/
theorem exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff [Fintype V]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k) :
    (∃ x : V → K, (∀ v, 0 ≤ x v) ∧
        x ⬝ᵥ ((G.copositiveCliqueMatrix k).map (Int.cast : ℤ → K) *ᵥ x) < 0) ↔
      k ≤ G.cliqueNum := by
  constructor
  · intro h
    obtain ⟨y, hylt⟩ := (Matrix.exists_nonneg_dotProduct_lt_zero_iff_stdSimplex _).1 h
    rw [dotProduct_copositiveCliqueMatrix, y.total_of_fintype, one_pow, mul_one] at hylt
    have hms := quadraticForm_adjMatrix_le_stdSimplex G y
    have hk1 : (0 : K) < (k : K) - 1 := by
      have : (2 : K) ≤ k := by exact_mod_cast hk
      linarith
    have homega_pos : 0 < G.cliqueNum := Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
    have homegaK : (0 : K) < G.cliqueNum := by exact_mod_cast homega_pos
    have hstep : ((k : K) - 2) / ((k : K) - 1) <
        (y.weights : V → K) ⬝ᵥ G.adjMatrix K *ᵥ (y.weights : V → K) := by
      rw [div_lt_iff₀ hk1]
      linarith
    have hcmp : ((k : K) - 2) / ((k : K) - 1) < 1 - 1 / (G.cliqueNum : K) := hstep.trans_le hms
    have hid : 1 - 1 / ((k : K) - 1) = ((k : K) - 2) / ((k : K) - 1) := by
      field_simp [hk1.ne']
      ring
    rw [← hid] at hcmp
    have hinv : 1 / (G.cliqueNum : K) < 1 / ((k : K) - 1) := by linarith
    have hltK : (k : K) - 1 < (G.cliqueNum : K) := by
      rwa [one_div_lt_one_div homegaK hk1] at hinv
    have hlt_nat : k - 1 < G.cliqueNum := by
      have : ((k - 1 : ℕ) : K) < G.cliqueNum := by
        rwa [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      exact_mod_cast this
    omega
  · intro hle
    classical
    obtain ⟨S, hS⟩ := G.exists_isNClique_cliqueNum
    let x : V → K := fun v => if v ∈ S then 1 else 0
    refine ⟨x, fun v => by dsimp [x]; split_ifs <;> positivity, ?_⟩
    rw [dotProduct_copositiveCliqueMatrix]
    have hxout : ∀ v, v ∉ S → x v = 0 := fun v hv => by
      dsimp only [x]
      split_ifs
      rfl
    have hsum : ∑ v, x v = (G.cliqueNum : K) := by
      have heq : ∑ v, x v = ∑ _v ∈ S, (1 : K) := by
        dsimp [x]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [heq, Finset.sum_const, hS.card_eq, nsmul_eq_mul, mul_one]
    have hquad : x ⬝ᵥ G.adjMatrix K *ᵥ x = (G.cliqueNum : K) ^ 2 - G.cliqueNum := by
      rw [dotProduct_adjMatrix_eq_of_isClique G hS.isClique hxout]
      have hs1 : ∑ v ∈ S, x v = G.cliqueNum := by
        have heq : ∑ v ∈ S, x v = ∑ _v ∈ S, (1 : K) :=
          Finset.sum_congr rfl fun v hv => by
            dsimp only [x]
            split_ifs
            rfl
        rw [heq, Finset.sum_const, hS.card_eq, nsmul_eq_mul, mul_one]
      have hs2 : ∑ v ∈ S, x v ^ 2 = G.cliqueNum := by
        have heq : ∑ v ∈ S, x v ^ 2 = ∑ _v ∈ S, (1 : K) ^ 2 :=
          Finset.sum_congr rfl fun v hv => by
            dsimp only [x]
            split_ifs
            rfl
        rw [heq, Finset.sum_const, hS.card_eq, nsmul_eq_mul, one_pow, mul_one]
      rw [hs1, hs2]
    rw [hsum, hquad]
    have homegaK : (0 : K) < G.cliqueNum := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hk.trans hle))
    have hleK : (k : K) ≤ G.cliqueNum := by exact_mod_cast hle
    have hcalc : ((k : K) - 2) * (G.cliqueNum : K) ^ 2 -
        ((k : K) - 1) * ((G.cliqueNum : K) ^ 2 - G.cliqueNum) =
        (G.cliqueNum : K) * ((k : K) - 1 - G.cliqueNum) := by ring
    rw [hcalc]
    exact mul_neg_of_pos_of_neg homegaK (by linarith)

end MotzkinStraus

end SimpleGraph
