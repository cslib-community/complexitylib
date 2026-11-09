/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Hamming
import CslibFrontier.Probability.PMF.Union

/-!
# Packing lower bounds for differential privacy

A private mechanism cannot place most of its mass in many pairwise disjoint regions, one for
each of many datasets, when those datasets are all close to a common centre. This is the
packing argument behind lower bounds on the error of `(ε, 0)`-private mechanisms, due to Hardt
and Talwar [DworkRoth2014, Lemma 8.4 and §8.3].

`DifferentiallyPrivate.card_mul_le` is the general form, for any adjacency relation. Take a
mechanism that is `(ε, δ)`-private for the relation relating a centre `x₀` to the datasets `x j`
(`j ∈ J`), and pairwise disjoint events `B j` with `Pr[M (x j) ∈ B j] ≥ p`. Then
`|J| · p ≤ exp ε + |J| · δ`. The proof compares each `x j` with `x₀` and sums the bounds
`Pr[M x₀ ∈ B j]`, which are at most `1` in total by disjointness.

With group privacy for Hamming adjacency (`DifferentiallyPrivate.hammingDist_le`), datasets within
Hamming distance `m` of the centre give `|J| · p ≤ exp (m ε) + |J| · ∑ i < m, exp (i ε) δ`
(`DifferentiallyPrivate.card_mul_le_of_hammingDist_le`), and `|J| · p ≤ exp (m ε)` for pure
privacy (`DifferentiallyPrivate.card_mul_le_of_hammingDist_le_of_pure`).
`DifferentiallyPrivate.log_two_mul_le_of_hammingDist_le` is the form of [DworkRoth2014,
Lemma 8.4]: `2 ^ s` datasets at pairwise Hamming distance at most `Δ` with success probability
at least `1 / 2` force `ε ≥ ln 2 · (s - 1) / Δ`. Dwork and Roth measure distance by the `ℓ₁`
distance between histograms; here datasets are tuples of rows compared by Hamming distance.

The application is the lower bound for one-way marginals [DworkRoth2014, Theorem 8.7]. A dataset
of `n` rows in `{0, 1} ^ k` has `k` one-way marginals (`oneWayMarginals`), the number of rows
whose `j`-th bit is set. Suppose an `(ε, 0)`-private mechanism answers, on every dataset, all of
them with error less than `n / 2` with probability at least `p`. Then `2 ^ k · p ≤ exp (n ε)`
(`DifferentiallyPrivate.two_pow_mul_le_of_oneWayMarginals`), so `(k - 1) ln 2 ≤ n ε` for
`p = 1 / 2` (`DifferentiallyPrivate.log_two_mul_le_of_oneWayMarginals`) and `n = Ω(k / ε)`. The
packed datasets are the `2 ^ k` datasets with `n` equal rows.

## Main definitions

* `Cslib.Privacy.oneWayMarginals`: the one-way marginals of a dataset of bit-vector rows.
* `Cslib.Privacy.accurateMarginals`: the answers giving every one-way marginal with error less
  than half the number of rows.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.card_mul_le`: the packing bound for a general adjacency.
* `Cslib.Privacy.DifferentiallyPrivate.card_mul_le_of_hammingDist_le`,
  `Cslib.Privacy.DifferentiallyPrivate.card_mul_le_of_hammingDist_le_of_pure`: the packing bound
  for datasets near a centre in Hamming distance.
* `Cslib.Privacy.DifferentiallyPrivate.log_two_mul_le_of_hammingDist_le`: the Hamming form of
  [DworkRoth2014, Lemma 8.4].
* `Cslib.Privacy.DifferentiallyPrivate.two_pow_mul_le_of_oneWayMarginals`,
  `Cslib.Privacy.DifferentiallyPrivate.log_two_mul_le_of_oneWayMarginals`: one-way marginals need
  `Ω(k / ε)` rows [DworkRoth2014, Theorem 8.7].

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u v

variable {D : Type u} {R : Type v}

namespace DifferentiallyPrivate

variable {Adj : D → D → Prop} {M : D → PMF R} {ε : ℝ} {δ : ℝ≥0∞}

/-- **Packing bound.** Let `M` be `(ε, δ)`-private for an adjacency relating `x₀` to each `x j`,
`j ∈ J`. If the events `B j` are pairwise disjoint and `M (x j)` lands in `B j` with probability
at least `p`, then `|J| · p ≤ exp ε + |J| · δ`. This is the counting step of [DworkRoth2014,
Lemma 8.4]. -/
theorem card_mul_le {ι : Type*} (h : DifferentiallyPrivate Adj M ε δ) (J : Finset ι) (x₀ : D)
    (x : ι → D) (hx : ∀ j ∈ J, Adj (x j) x₀) {B : ι → Set R}
    (hB : (J : Set ι).PairwiseDisjoint B) {p : ℝ≥0∞}
    (hp : ∀ j ∈ J, p ≤ (M (x j)).toOuterMeasure (B j)) :
    J.card * p ≤ ENNReal.ofReal (Real.exp ε) + J.card * δ := by
  calc (J.card : ℝ≥0∞) * p = ∑ j ∈ J, p := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ J, (ENNReal.ofReal (Real.exp ε) * (M x₀).toOuterMeasure (B j) + δ) :=
        Finset.sum_le_sum fun j hj => (hp j hj).trans (h (hx j hj) (B j))
    _ = ENNReal.ofReal (Real.exp ε) * ∑ j ∈ J, (M x₀).toOuterMeasure (B j) + J.card * δ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (Real.exp ε) * 1 + J.card * δ := by
        gcongr
        exact Probability.PMF.sum_toOuterMeasure_le_one (M x₀) J hB
    _ = ENNReal.ofReal (Real.exp ε) + J.card * δ := by rw [mul_one]

variable {ι X : Type*} [Fintype ι] [DecidableEq X] {M : (ι → X) → PMF R}

/-- **Packing bound in Hamming distance.** If `M` is `(ε, δ)`-private for Hamming adjacency, the
datasets `x j` (`j ∈ J`) are within Hamming distance `m` of a centre `x₀`, the events `B j` are
pairwise disjoint and `Pr[M (x j) ∈ B j] ≥ p`, then
`|J| · p ≤ exp (m ε) + |J| · ∑ i < m, exp (i ε) δ`. This is the Hamming-distance analogue of
[DworkRoth2014, Lemma 8.4], with a centre in place of pairwise distances and with `δ`. -/
theorem card_mul_le_of_hammingDist_le {κ : Type*} (h : DifferentiallyPrivate HammingAdjacent M ε δ)
    (J : Finset κ) (x₀ : ι → X) (x : κ → ι → X) {m : ℕ}
    (hx : ∀ j ∈ J, hammingDist (x j) x₀ ≤ m) {B : κ → Set R}
    (hB : (J : Set κ).PairwiseDisjoint B) {p : ℝ≥0∞}
    (hp : ∀ j ∈ J, p ≤ (M (x j)).toOuterMeasure (B j)) :
    J.card * p ≤ ENNReal.ofReal (Real.exp (m * ε)) +
      J.card * ∑ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (i * ε)) * δ :=
  (h.hammingDist_le m).card_mul_le J x₀ x hx hB hp

/-- **Packing bound for pure privacy.** If `M` is `(ε, 0)`-private for Hamming adjacency, the
datasets `x j` (`j ∈ J`) are within Hamming distance `m` of `x₀`, the events `B j` are pairwise
disjoint and `Pr[M (x j) ∈ B j] ≥ p`, then `|J| · p ≤ exp (m ε)`. -/
theorem card_mul_le_of_hammingDist_le_of_pure {κ : Type*}
    (h : DifferentiallyPrivate HammingAdjacent M ε 0) (J : Finset κ) (x₀ : ι → X) (x : κ → ι → X)
    {m : ℕ} (hx : ∀ j ∈ J, hammingDist (x j) x₀ ≤ m) {B : κ → Set R}
    (hB : (J : Set κ).PairwiseDisjoint B) {p : ℝ≥0∞}
    (hp : ∀ j ∈ J, p ≤ (M (x j)).toOuterMeasure (B j)) :
    J.card * p ≤ ENNReal.ofReal (Real.exp (m * ε)) := by
  simpa using (h.hammingDist_le_of_pure m).card_mul_le J x₀ x hx hB hp

/-- **[DworkRoth2014, Lemma 8.4], Hamming form.** If `M` is `(ε, 0)`-private for Hamming
adjacency and `2 ^ s` datasets at pairwise Hamming distance at most `Δ` have pairwise disjoint
events `B j` with `Pr[M (x j) ∈ B j] ≥ 1 / 2`, then `ln 2 · (s - 1) ≤ Δ ε`. Dwork and Roth state
this for histograms at `ℓ₁` distance at most `Δ`. -/
theorem log_two_mul_le_of_hammingDist_le (h : DifferentiallyPrivate HammingAdjacent M ε 0) (s : ℕ)
    (x : Fin (2 ^ s) → ι → X) {Δ : ℕ} (hx : ∀ i j, hammingDist (x i) (x j) ≤ Δ)
    {B : Fin (2 ^ s) → Set R} (hB : Pairwise (Function.onFun Disjoint B))
    (hp : ∀ j, 2⁻¹ ≤ (M (x j)).toOuterMeasure (B j)) :
    Real.log 2 * (s - 1) ≤ Δ * ε := by
  have hle := h.card_mul_le_of_hammingDist_le_of_pure Finset.univ (x 0) x
    (fun j _ => hx j 0) (fun i _ j _ hij => hB hij) (fun j _ => hp j)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  have hlhs : ((2 ^ s : ℕ) : ℝ≥0∞) * 2⁻¹ = ENNReal.ofReal (2 ^ s / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
      div_eq_mul_inv]
    push_cast
    rfl
  rw [hlhs, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at hle
  have hpos : (0 : ℝ) < 2 ^ s / 2 := by positivity
  have := Real.log_le_log hpos hle
  rw [Real.log_exp, Real.log_div (by positivity) two_ne_zero, Real.log_pow] at this
  linarith

end DifferentiallyPrivate

section Marginals

variable {ι κ : Type*} [Fintype ι]

/-- The one-way marginals of a dataset whose rows are bit vectors indexed by `κ`: the `j`-th
marginal is the number of rows whose `j`-th bit is set [DworkRoth2014, Theorem 8.7]. -/
def oneWayMarginals (x : ι → κ → Bool) (j : κ) : ℝ :=
  (Finset.univ.filter fun i => x i j = true).card

/-- The `j`-th marginal of the dataset with every row equal to `w` is `n` if `w j` is set and `0`
otherwise. -/
theorem oneWayMarginals_const (w : κ → Bool) (j : κ) :
    oneWayMarginals (fun _ : ι => w) j = if w j = true then (Fintype.card ι : ℝ) else 0 := by
  unfold oneWayMarginals
  by_cases hw : w j = true <;> simp [hw]

/-- Unfolding `oneWayMarginals`. -/
theorem oneWayMarginals_apply (x : ι → κ → Bool) (j : κ) :
    oneWayMarginals x j = (Finset.univ.filter fun i => x i j = true).card := by
  rw [oneWayMarginals]

/-- The answers `a` that give every one-way marginal of `x` with error less than `n / 2`, `n` being
the number of rows: the open `ℓ∞` ball `B_x` of [DworkRoth2014, Theorem 8.7]. -/
def accurateMarginals (x : ι → κ → Bool) : Set (κ → ℝ) :=
  {a | ∀ j, |a j - oneWayMarginals x j| < Fintype.card ι / 2}

/-- Unfolding `accurateMarginals`. -/
theorem mem_accurateMarginals {x : ι → κ → Bool} {a : κ → ℝ} :
    a ∈ accurateMarginals x ↔ ∀ j, |a j - oneWayMarginals x j| < Fintype.card ι / 2 :=
  Iff.rfl

/-- With at least one row, the accurate answers form the open ball of radius `n / 2` around the
marginals in the sup metric. -/
theorem accurateMarginals_eq_ball [Fintype κ] [Nonempty ι] (x : ι → κ → Bool) :
    accurateMarginals x = Metric.ball (oneWayMarginals x) (Fintype.card ι / 2) := by
  have hr : (0 : ℝ) < Fintype.card ι / 2 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    positivity
  ext a
  rw [Metric.mem_ball, dist_pi_lt_iff hr, mem_accurateMarginals]
  simp only [Real.dist_eq]

/-- The accuracy events of two different constant datasets are disjoint. -/
theorem disjoint_accurateMarginals_const {w w' : κ → Bool} (hw : w ≠ w') :
    Disjoint (accurateMarginals fun _ : ι => w) (accurateMarginals fun _ : ι => w') := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  refine Set.disjoint_left.mpr fun a ha ha' => ?_
  have h1 := ha j
  have h2 := ha' j
  rw [oneWayMarginals_const] at h1 h2
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  cases hwj : w j <;> cases hwj' : w' j <;>
    simp only [hwj, hwj', ne_eq, not_true_eq_false, Bool.false_eq_true, ↓reduceIte, sub_zero,
      abs_lt] at h1 h2 hj ⊢ <;> linarith

end Marginals

namespace DifferentiallyPrivate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {M : (ι → κ → Bool) → PMF (κ → ℝ)} {ε : ℝ}

/-- **One-way marginals, [DworkRoth2014, Theorem 8.7].** Let `M` be `(ε, 0)`-private for
Hamming adjacency on datasets of `n` rows in `{0, 1} ^ κ`. If on every dataset `M` answers all
one-way marginals with error less than `n / 2` with probability at least `p`, then
`2 ^ |κ| · p ≤ exp (n ε)`. -/
theorem two_pow_mul_le_of_oneWayMarginals (h : DifferentiallyPrivate HammingAdjacent M ε 0)
    {p : ℝ≥0∞} (hp : ∀ x, p ≤ (M x).toOuterMeasure (accurateMarginals x)) :
    2 ^ Fintype.card κ * p ≤ ENNReal.ofReal (Real.exp (Fintype.card ι * ε)) := by
  classical
  have hle := h.card_mul_le_of_hammingDist_le_of_pure (Finset.univ : Finset (κ → Bool))
    (fun _ => fun _ => false) (fun w => fun _ => w) (m := Fintype.card ι)
    (fun _ _ => hammingDist_le_card_fintype)
    (fun w _ w' _ hww' => disjoint_accurateMarginals_const hww') (fun w _ => hp _)
  simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] using hle

/-- **One-way marginals need `Ω(k / ε)` rows, [DworkRoth2014, Theorem 8.7].** If an
`(ε, 0)`-private mechanism on datasets of `n` rows in `{0, 1} ^ k` answers, on every dataset, all
`k` one-way marginals with error less than `n / 2` with probability at least `1 / 2`, then
`(k - 1) ln 2 ≤ n ε`. -/
theorem log_two_mul_le_of_oneWayMarginals (h : DifferentiallyPrivate HammingAdjacent M ε 0)
    (hp : ∀ x, 2⁻¹ ≤ (M x).toOuterMeasure (accurateMarginals x)) :
    (Fintype.card κ - 1) * Real.log 2 ≤ Fintype.card ι * ε := by
  have hle := h.two_pow_mul_le_of_oneWayMarginals hp
  have hlhs : (2 : ℝ≥0∞) ^ Fintype.card κ * 2⁻¹ = ENNReal.ofReal (2 ^ Fintype.card κ / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
      div_eq_mul_inv]
  rw [hlhs, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at hle
  have hpos : (0 : ℝ) < 2 ^ Fintype.card κ / 2 := by positivity
  have := Real.log_le_log hpos hle
  rw [Real.log_exp, Real.log_div (by positivity) two_ne_zero, Real.log_pow] at this
  linarith

end DifferentiallyPrivate

end Cslib.Privacy
