/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.SimpleGraph
public import CslibFrontier.Foundations.Combinatorics.Expander.Walk
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.Combinatorics.Expander.Harmonic
import CslibFrontier.Foundations.Combinatorics.Expander.Spectrum
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# Visit counts of random walks on connected regular multigraphs

On a connected `d`-regular multigraph on `n` vertices, the number of visits of a `t`-step random
walk to a fixed vertex `v` is close to `t / n` with high probability, for all large `t`
(`eventually_visits_mem_Icc`). This is
[Arora and Barak, Chapter 7, Exercise 9(b)(ii)][AroraBarak07].
No aperiodicity is needed: on a bipartite graph the walk alternates sides, but the fraction of
time spent at `v` still converges.

The proof has two steps.

* **Mean ergodic theorem.** The walk operator is a contraction of `EuclideanSpace ℝ V` whose
  fixed vectors are the constants on a connected graph (the maximum principle
  `Cslib.RotationMap.eq_of_walk_eq_self` of `Expander.Harmonic`). By von Neumann's mean ergodic
  theorem (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`), the Cesàro averages
  `(1 / N) ∑_{j < N} Pʲ f` of a function `f` of total `0` tend to `0`, uniformly in the start
  vertex (`exists_abs_sum_walk_pow_le`).
* **Second moment.** For `f = 1_v - 1 / n`, the sum `S_t = ∑_{i=1}^{t} f(X_i)` is the number of
  visits minus `t / n`. Conditioning on the first step gives recursions for its first and second
  moments over the `d ^ t` label sequences (`expect_visitSum_sq_succ`), from which
  `𝔼 S_t² = o(t²)`. Chebyshev's inequality finishes the proof.

## Main definitions

* `Cslib.RotationMap.visits`: the number of visits to `v` at times `1, …, t` of the walk along a
  label sequence.

## Main results

* `Cslib.RotationMap.visits_eq`: the defining count of `visits`.
* `Cslib.RotationMap.exists_abs_sum_walk_pow_le`: uniform Cesàro convergence.
* `Cslib.RotationMap.eventually_visits_mem_Icc`: Arora and Barak, Exercise 7.9(b)(ii), for all
  large `t`; `Cslib.RotationMap.exists_visits_mem_Icc` is the existential form of the source.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
-/

public section

namespace Cslib.RotationMap

open Finset Filter Topology
open scoped BigOperators

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [Nonempty D] {G : RotationMap V D}

/-! ### The mean ergodic step -/

omit [Fintype V] [DecidableEq V] in
/-- A function of absolute value at most `c` stays so under the walk operator. -/
theorem abs_walk_le {f : V → ℝ} {c : ℝ} (hf : ∀ x, |f x| ≤ c) (x : V) : |G.walk f x| ≤ c := by
  rw [walk_apply]
  refine (abs_expect_le _ _).trans (expect_le univ_nonempty fun i _ => hf _)

omit [Fintype V] [DecidableEq V] in
theorem abs_walk_pow_le {f : V → ℝ} {c : ℝ} (hf : ∀ x, |f x| ≤ c) (j : ℕ) (x : V) :
    |(G.walk ^ j) f x| ≤ c := by
  induction j generalizing x with
  | zero => exact hf x
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact abs_walk_le ih x

omit [DecidableEq V] in
/-- **Uniform Cesàro convergence.** On a connected regular multigraph, for a function `f` of total
`0` the sums `∑_{j < N} Pʲ f` are eventually at most `ε N` in absolute value at every vertex. -/
theorem exists_abs_sum_walk_pow_le (hG : G.toSimpleGraph.Preconnected) {f : V → ℝ}
    (hf : ∑ v, f v = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀, ∀ N ≥ N₀, ∀ v, |∑ j ∈ range N, (G.walk ^ j) f v| ≤ ε * N := by
  set W := LinearMap.toContinuousLinearMap G.walkEuclidean
  have hW : ‖W‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact G.norm_walkEuclidean_le x
  have hlim := W.tendsto_birkhoffAverage_orthogonalProjection hW (WithLp.toLp 2 f)
  have hproj : (W.eqLocus (1 : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
      ).orthogonalProjectionOnto (WithLp.toLp 2 f) = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    intro c hc
    have hfix : G.walk c.ofLp = c.ofLp := by
      have : W c = c := hc
      have := congrArg WithLp.ofLp this
      rwa [← WithLp.toLp_ofLp 2 c] at this
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rcases isEmpty_or_nonempty V with hV | ⟨⟨u⟩⟩
    · simp [dotProduct]
    have hconst : ∀ x, c.ofLp x = c.ofLp u := fun x => eq_of_walk_eq_self hG hfix x u
    simp only [dotProduct, hconst, star_trivial]
    rw [← sum_mul, hf, zero_mul]
  rw [hproj, ZeroMemClass.coe_zero] at hlim
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨max N₀ 1, fun N hN v => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have h := hN₀ N (le_of_max_le_left hN)
  rw [dist_zero_right] at h
  have hiter : ∀ j (x : EuclideanSpace ℝ V), (W^[j] x).ofLp = (G.walk ^ j) x.ofLp := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have hcoord := (PiLp.norm_apply_le (birkhoffAverage ℝ W _root_.id N (WithLp.toLp 2 f)) v).trans
    h.le
  rw [birkhoffAverage, birkhoffSum] at hcoord
  simp only [id, WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply, hiter,
    smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast] at hcoord
  rw [inv_mul_le_iff₀ (by linarith)] at hcoord
  linarith

/-! ### Visit counts and their moments -/

/-- The number of visits to `v` at times `1, …, t` of the walk from `u` along the labels `k`. -/
@[expose] def visits (G : RotationMap V D) (u v : V) {t : ℕ} (k : Fin t → D) : ℕ :=
  #{i ∈ range t | G.walkAt (u, k) (i + 1) = v}

omit [Fintype V] [Fintype D] [Nonempty D] in
/-- The defining equation of `visits`: the count of times `1, …, t` at which the walk is at `v`. -/
theorem visits_eq (u v : V) {t : ℕ} (k : Fin t → D) :
    G.visits u v k = #{i ∈ range t | G.walkAt (u, k) (i + 1) = v} :=
  rfl

/-- The sum of `f` over the vertices at times `1, …, t` of a walk. -/
private def visitSum (G : RotationMap V D) (f : V → ℝ) (u : V) {t : ℕ} (k : Fin t → D) : ℝ :=
  ∑ i ∈ range t, f (G.walkAt (u, k) (i + 1))

omit [Fintype V] [DecidableEq V] [Fintype D] [Nonempty D] in
private theorem visitSum_cons (f : V → ℝ) (u : V) {t : ℕ} (a : D) (k : Fin t → D) :
    visitSum G f u (Fin.cons a k : Fin (t + 1) → D) =
      f (G.neighbor u a) + visitSum G f (G.neighbor u a) k := by
  simp only [visitSum]
  rw [sum_range_succ']
  simp only [walkAt_cons_succ, walkAt_zero]
  ring

omit [Fintype V] [DecidableEq V] in
private theorem expect_visitSum (f : V → ℝ) :
    ∀ (t : ℕ) (u : V), 𝔼 k : Fin t → D, visitSum G f u k =
      ∑ j ∈ range t, (G.walk ^ (j + 1)) f u
  | 0, u => by simp [visitSum]
  | t + 1, u => by
    rw [Fin.expect_univ_cons]
    have h : ∀ a, 𝔼 k : Fin t → D, visitSum G f u (Fin.cons a k : Fin (t + 1) → D) =
        (f + ∑ j ∈ range t, (G.walk ^ (j + 1)) f) (G.neighbor u a) := by
      intro a
      simp only [visitSum_cons, expect_add_distrib, expect_visitSum f t,
        Pi.add_apply, Finset.sum_apply]
      simp
    simp_rw [h]
    rw [← walk_apply, map_add, map_sum, sum_range_succ', Pi.add_apply, Finset.sum_apply,
      pow_one, add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [pow_succ' G.walk (j + 1), Module.End.mul_apply]

omit [Fintype V] [DecidableEq V] in
private theorem expect_visitSum_sq_succ (f : V → ℝ) (t : ℕ) (u : V) :
    𝔼 k : Fin (t + 1) → D, visitSum G f u k ^ 2 =
      G.walk (fun w => f w ^ 2 + 2 * f w * (𝔼 k : Fin t → D, visitSum G f w k) +
        𝔼 k : Fin t → D, visitSum G f w k ^ 2) u := by
  rw [Fin.expect_univ_cons, walk_apply]
  refine expect_congr rfl fun a _ => ?_
  simp only [visitSum_cons, add_sq, expect_add_distrib, ← mul_expect]
  simp

omit [Fintype V] [DecidableEq V] in
/-- The second moment of `S_t` is at most `t (1 + 2 M)` if `|f| ≤ 1` and the first moments of
`S_s` for `s < t` are at most `M` in absolute value. -/
private theorem expect_visitSum_sq_le (f : V → ℝ) (hf : ∀ x, |f x| ≤ 1) (M : ℕ → ℝ)
    (hM : ∀ s w, |𝔼 k : Fin s → D, visitSum G f w k| ≤ M s) :
    ∀ (t : ℕ) (u : V), 𝔼 k : Fin t → D, visitSum G f u k ^ 2 ≤ ∑ s ∈ range t, (1 + 2 * M s)
  | 0, u => by simp [visitSum]
  | t + 1, u => by
    rw [expect_visitSum_sq_succ, sum_range_succ]
    have hb : ∀ w, |f w ^ 2 + 2 * f w * (𝔼 k : Fin t → D, visitSum G f w k) +
        𝔼 k : Fin t → D, visitSum G f w k ^ 2| ≤ ∑ s ∈ range t, (1 + 2 * M s) + (1 + 2 * M t) := by
      intro w
      have h1 : f w ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hf w)
      have h2 : |2 * f w * (𝔼 k : Fin t → D, visitSum G f w k)| ≤ 2 * M t := by
        rw [abs_mul, abs_mul, abs_two]
        have := hf w
        have := hM t w
        have := abs_nonneg (f w)
        have := abs_nonneg (𝔼 k : Fin t → D, visitSum G f w k)
        nlinarith
      have h3 := expect_visitSum_sq_le f hf M hM t w
      have h4 : 0 ≤ 𝔼 k : Fin t → D, visitSum G f w k ^ 2 :=
        expect_nonneg fun _ _ => sq_nonneg _
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (f w), abs_le.1 h2, (abs_nonneg _).trans (hM t w),
          sum_nonneg (s := range t) (f := fun s => (1 + 2 * M s)) fun s _ =>
            by nlinarith [(abs_nonneg _).trans (hM s w)]]
      · nlinarith [abs_le.1 h2]
    exact (le_abs_self _).trans (abs_walk_le hb u)

/-! ### Concentration -/

/-- **Arora–Barak, Exercise 7.9(b)(ii).** On a connected `d`-regular multigraph on `n` vertices,
for every `u`, `v` and `ε > 0`, for all large `t`, at least a `1 - ε` fraction of the `d ^ t`
label sequences give a walk from `u` whose number of visits to `v` at times `1, …, t` lies in
`[(1 - ε) t / n, (1 + ε) t / n]`. -/
theorem eventually_visits_mem_Icc (hG : G.toSimpleGraph.Connected) (u v : V) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ t in atTop, (1 - ε) * (Fintype.card D : ℝ) ^ t ≤
      #{k : Fin t → D | (G.visits u v k : ℝ) ∈
        Set.Icc ((1 - ε) * t / Fintype.card V) ((1 + ε) * t / Fintype.card V)} := by
  have : Nonempty V := hG.nonempty
  set n := Fintype.card V with hn_def
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set f : V → ℝ := fun x => (if x = v then 1 else 0) - 1 / n with hf_def
  have hf0 : ∑ x, f x = 0 := by
    simp only [f, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
      nsmul_eq_mul]
    field_simp
    simp [n]
  have hf1 : ∀ x, |f x| ≤ 1 := by
    intro x
    have h1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn]; exact_mod_cast Fintype.card_pos
    have h0 : 0 < 1 / (n : ℝ) := by positivity
    simp only [f]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  set η := ε ^ 3 / (4 * n ^ 2) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_abs_sum_walk_pow_le hG.preconnected hf0 hη0
  have hM : ∀ s w, |𝔼 k : Fin s → D, visitSum G f w k| ≤ η * (s + 1) + (N₀ + 1) := by
    intro s w
    rw [expect_visitSum]
    have hshift : ∑ j ∈ range s, (G.walk ^ (j + 1)) f w =
        ∑ j ∈ range (s + 1), (G.walk ^ j) f w - f w := by
      rw [sum_range_succ']; simp
    rw [hshift]
    have hsum : |∑ j ∈ range (s + 1), (G.walk ^ j) f w| ≤ η * (s + 1) + N₀ := by
      by_cases h : N₀ ≤ s + 1
      · have := hN₀ (s + 1) h w
        push_cast at this
        have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
        linarith
      · calc |∑ j ∈ range (s + 1), (G.walk ^ j) f w|
            ≤ ∑ j ∈ range (s + 1), |(G.walk ^ j) f w| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ range (s + 1), (1 : ℝ) :=
              sum_le_sum fun j _ => abs_walk_pow_le hf1 j w
          _ = s + 1 := by simp
          _ ≤ N₀ := by exact_mod_cast (Nat.lt_of_not_le h).le
          _ ≤ η * (s + 1) + N₀ := by have : 0 ≤ η * (s + 1) := by positivity
                                     linarith
    have := abs_sub (∑ j ∈ range (s + 1), (G.walk ^ j) f w) (f w)
    linarith [hf1 w]
  have hq := expect_visitSum_sq_le f hf1 _ hM
  have hgauss : ∀ m : ℕ, ∑ s ∈ range m, ((s : ℝ) + 1) = m * (m + 1) / 2 := by
    intro m
    have h := congrArg (Nat.cast (R := ℝ)) (sum_range_id_mul_two (m + 1))
    rw [sum_range_succ'] at h
    push_cast at h
    linarith
  -- the bound on the second moment is eventually small
  set T₀ := ⌈2 * n ^ 2 * (3 + 2 * N₀) / ε ^ 3⌉₊ + 1
  filter_upwards [eventually_ge_atTop T₀] with t ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast le_trans (Nat.le_add_left 1 _) ht
  have htT : 2 * n ^ 2 * (3 + 2 * N₀) / ε ^ 3 ≤ t := by
    have := Nat.le_ceil (2 * n ^ 2 * (3 + 2 * (N₀ : ℝ)) / ε ^ 3)
    have h2 : ((⌈2 * n ^ 2 * (3 + 2 * (N₀ : ℝ)) / ε ^ 3⌉₊ : ℕ) : ℝ) ≤ t := by
      exact_mod_cast le_trans (Nat.le_succ _) ht
    linarith
  set a : ℝ := ε * t / n with ha
  have ha0 : 0 < a := by positivity
  have hsum_eq : ∑ s ∈ range t, (1 + 2 * (η * (s + 1) + (N₀ + 1))) =
      t * (3 + 2 * N₀) + η * t * (t + 1) := by
    have h := hgauss t
    have : ∑ s ∈ range t, (1 + 2 * (η * (s + 1) + (N₀ + 1))) =
        ∑ s ∈ range t, ((3 + 2 * N₀ : ℝ) + 2 * η * ((s : ℝ) + 1)) :=
      sum_congr rfl fun s _ => by ring
    rw [this, sum_add_distrib, ← mul_sum, h]
    simp; ring
  have hq' : 𝔼 k : Fin t → D, visitSum G f u k ^ 2 ≤ ε * a ^ 2 := by
    refine (hq t u).trans (hsum_eq.le.trans ?_)
    have h1 : t * (3 + 2 * (N₀ : ℝ)) ≤ ε ^ 3 * t ^ 2 / (2 * n ^ 2) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 3)] at htT
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : η * t * (t + 1) ≤ ε ^ 3 * t ^ 2 / (2 * n ^ 2) := by
      rw [hη]
      have : (t : ℝ) + 1 ≤ 2 * t := by linarith
      calc ε ^ 3 / (4 * n ^ 2) * t * (t + 1) ≤ ε ^ 3 / (4 * n ^ 2) * t * (2 * t) := by gcongr
        _ = ε ^ 3 * t ^ 2 / (2 * n ^ 2) := by field_simp; ring
    calc t * (3 + 2 * (N₀ : ℝ)) + η * t * (t + 1)
        ≤ ε ^ 3 * t ^ 2 / (2 * n ^ 2) + ε ^ 3 * t ^ 2 / (2 * n ^ 2) := add_le_add h1 h2
      _ = ε * a ^ 2 := by rw [ha]; field_simp; ring
  -- Chebyshev
  have hS : ∀ k : Fin t → D, visitSum G f u k = (G.visits u v k : ℝ) - t / n := by
    intro k
    simp only [visitSum, f, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, visits]
    rw [sum_boole]
    simp [div_eq_mul_inv]
  have hgood : ∀ k : Fin t → D, |visitSum G f u k| ≤ a →
      (G.visits u v k : ℝ) ∈ Set.Icc ((1 - ε) * t / n) ((1 + ε) * t / n) := by
    intro k hk
    rw [hS, abs_le] at hk
    constructor
    · have : (1 - ε) * t / n = t / n - a := by rw [ha]; ring
      linarith
    · have : (1 + ε) * t / n = t / n + a := by rw [ha]; ring
      linarith
  -- Chebyshev: Markov's inequality for `S²` at level `a²`
  have hcard : (Fintype.card (Fin t → D) : ℝ) = (Fintype.card D : ℝ) ^ t := by simp
  have hd : (0 : ℝ) < (Fintype.card D : ℝ) ^ t := by positivity
  have hmk := Fintype.mul_dens_filter_le_expect
    (fun k : Fin t → D => sq_nonneg (visitSum G f u k)) (a ^ 2)
  have hbad : (#{k : Fin t → D | a ^ 2 ≤ visitSum G f u k ^ 2} : ℝ) ≤
      ε * (Fintype.card D : ℝ) ^ t := by
    rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
      hcard] at hmk
    have ha2 : 0 < a ^ 2 := by positivity
    have h := hmk.trans hq'
    rw [mul_div_assoc', div_le_iff₀ hd,
      show ε * a ^ 2 * (Fintype.card D : ℝ) ^ t = a ^ 2 * (ε * (Fintype.card D : ℝ) ^ t) by
        ring] at h
    exact le_of_mul_le_mul_left h ha2
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin t → D)))
    (fun k => a ^ 2 ≤ visitSum G f u k ^ 2)
  have hsplit' : (#{k : Fin t → D | ¬ a ^ 2 ≤ visitSum G f u k ^ 2} : ℝ) +
      #{k : Fin t → D | a ^ 2 ≤ visitSum G f u k ^ 2} = (Fintype.card D : ℝ) ^ t := by
    rw [← hcard, ← card_univ, add_comm]
    exact_mod_cast hsplit
  have hmono : (#{k : Fin t → D | ¬ a ^ 2 ≤ visitSum G f u k ^ 2} : ℝ) ≤
      #{k : Fin t → D | (G.visits u v k : ℝ) ∈
        Set.Icc ((1 - ε) * t / n) ((1 + ε) * t / n)} := by
    exact_mod_cast card_le_card fun k hk => by
      simp only [mem_filter, mem_univ, true_and, not_le] at hk ⊢
      exact hgood k (abs_le_of_sq_le_sq' hk.le ha0.le |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩))
  linarith

/-- **Arora–Barak, Exercise 7.9(b)(ii)**, in the source's form: for every `u`, `v` and `ε > 0`
there is `t` such that, with probability at least `1 - ε` over the `d ^ t` label sequences, the
number of visits to `v` of the `t`-step walk from `u` lies in `[(1 - ε) t / n, (1 + ε) t / n]`. -/
theorem exists_visits_mem_Icc (hG : G.toSimpleGraph.Connected) (u v : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, (1 - ε) * (Fintype.card D : ℝ) ^ t ≤
      #{k : Fin t → D | (G.visits u v k : ℝ) ∈
        Set.Icc ((1 - ε) * t / Fintype.card V) ((1 + ε) * t / Fintype.card V)} :=
  (eventually_visits_mem_Icc hG u v hε).exists

end Cslib.RotationMap
