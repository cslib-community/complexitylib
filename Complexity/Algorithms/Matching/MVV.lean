/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Matching.Edmonds
public import Complexity.Probability.Isolation
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Isolating weights and the Mulmuley–Vazirani–Vazirani matching algorithm

The algebraic and probabilistic core of the parallel matching algorithm of Mulmuley, Vazirani and
Vazirani [MulmuleyVaziraniVazirani1987] [Motwani and Raghavan, Section 12.4][MotwaniRaghavan95],
for a bipartite graph `G : V × V → Bool`. Give each edge `(i, j)` a weight `w (i, j)` and let `B`
be the Edmonds matrix at the values `2 ^ w (i, j)`
(`Cslib.Algorithms.Matching.weightedEdmonds G w`, a matrix over `ℤ`). Each perfect matching `σ`
contributes `± 2 ^ (weight of σ)` to `det B`. When the minimum-weight perfect matching `σ₀` is
unique, of weight `W`, every other term is divisible by `2 ^ (W + 1)`, so

* `2 ^ W` divides `det B` and `2 ^ (W + 1)` does not
  (`Cslib.Algorithms.Matching.two_pow_dvd_det_weightedEdmonds`,
  `Cslib.Algorithms.Matching.not_two_pow_succ_dvd_det_weightedEdmonds`), so `W` is the `2`-adic
  valuation of `det B` (`Cslib.Algorithms.Matching.matchingWeight_eq_padicValInt_det`);
* `σ₀` matches `i` to `j` exactly when `2 ^ (W + 1)` does not divide `B i j * adj(B) j i`
  (`Cslib.Algorithms.Matching.apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate`), since that product
  is the signed sum over the perfect matchings that match `i` to `j`.

MVV state these lemmas for the Tutte matrix of a general graph, where the power is `2 ^ (2 W)`;
the statements here are their bipartite (Edmonds-matrix) form. The procedure
`Cslib.Algorithms.Matching.mvvOutput G w` computes `W` from `det B` and outputs the pairs `(i, j)`
passing the divisibility test; on isolating weights it outputs exactly `σ₀`
(`Cslib.Algorithms.Matching.mvvOutput_iff_apply_eq`).

The isolation lemma makes the minimum unique with probability at least `1 / 2` when the edge
weights are independent and uniform on `{1, …, N}` with `N ≥ 2 |E|`
(`Cslib.Algorithms.Matching.half_le_dens_exists_isUniqueMinMatching`, from
`Cslib.Probability.half_le_dens_minWeightSets_card_eq_one`). Together, the procedure returns a
perfect matching of `G` with probability at least `1 / 2`
(`Cslib.Algorithms.Matching.half_le_dens_mvv`). Probabilities are proportions of the weight
functions, as in the isolation lemma. The parallel (NC) computation of the determinant and the
adjugate is not formalized.

## Main definitions

* `Cslib.Algorithms.Matching.weightedEdmonds`: the Edmonds matrix at powers of two.
* `Cslib.Algorithms.Matching.IsUniqueMinMatching`: a unique minimum-weight perfect matching.
* `Cslib.Algorithms.Matching.mvvOutput`: the pairs output by the procedure.
* `Cslib.Algorithms.Matching.MVVSucceeds`: the output is a perfect matching.

## Main results

* `Cslib.Algorithms.Matching.matchingWeight_eq_padicValInt_det`: the weight of the isolated
  matching is the `2`-adic valuation of the determinant.
* `Cslib.Algorithms.Matching.apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate`: reading off the
  matching.
* `Cslib.Algorithms.Matching.mvvOutput_iff_apply_eq`: the procedure is correct on isolating
  weights.
* `Cslib.Algorithms.Matching.half_le_dens_exists_isUniqueMinMatching`: the isolation lemma for
  perfect matchings.
* `Cslib.Algorithms.Matching.half_le_dens_mvv`: the procedure succeeds with probability at least
  `1 / 2`.

## References

* [K. Mulmuley, U. V. Vazirani and V. V. Vazirani, *Matching is as easy as matrix
  inversion*][MulmuleyVaziraniVazirani1987]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*, Section 12.4][MotwaniRaghavan95]
-/

public section

namespace Cslib.Algorithms.Matching

open Finset Matrix Equiv Cslib.Circuits.BipartiteMatching Cslib.Probability

/-! ### Signed sums of powers of two with a unique smallest exponent -/

/-- A sum of `ε s * 2 ^ w s` over a finite set whose exponents all exceed `W` is divisible by
`2 ^ (W + 1)`. -/
private theorem two_pow_succ_dvd_sum {ι : Type*} {T : Finset ι} {ε : ι → ℤ} {w : ι → ℕ} {W : ℕ}
    (hw : ∀ s ∈ T, W < w s) : (2 : ℤ) ^ (W + 1) ∣ ∑ s ∈ T, ε s * 2 ^ w s :=
  dvd_sum fun s hs => (pow_dvd_pow 2 (hw s hs)).mul_left _

/-- **A unique smallest exponent**: if `s₀ ∈ T` has a unit coefficient `ε s₀` and every other
element of `T` has a larger exponent than `s₀`, then `2 ^ w s₀` divides
`∑ s ∈ T, ε s * 2 ^ w s` and `2 ^ (w s₀ + 1)` does not. -/
private theorem two_pow_dvd_sum_and_not_dvd {ι : Type*} {T : Finset ι} {ε : ι → ℤ}
    {w : ι → ℕ} {s₀ : ι} (hs₀ : s₀ ∈ T) (hε : IsUnit (ε s₀))
    (hw : ∀ s ∈ T, s ≠ s₀ → w s₀ < w s) :
    (2 : ℤ) ^ w s₀ ∣ ∑ s ∈ T, ε s * 2 ^ w s ∧
      ¬ (2 : ℤ) ^ (w s₀ + 1) ∣ ∑ s ∈ T, ε s * 2 ^ w s := by
  classical
  rw [← add_sum_erase T _ hs₀]
  have hrest := two_pow_succ_dvd_sum (T := T.erase s₀) (ε := ε) (w := w) (W := w s₀)
    fun s hs => hw s (mem_of_mem_erase hs) (ne_of_mem_erase hs)
  refine ⟨dvd_add (dvd_mul_left _ _) ((pow_dvd_pow 2 (Nat.le_succ _)).trans hrest), fun h => ?_⟩
  have h1 := (dvd_add_left hrest).1 h
  rw [pow_succ'] at h1
  have h2 : (2 : ℤ) ∣ ε s₀ := (mul_dvd_mul_iff_right (pow_ne_zero _ two_ne_zero)).1 h1
  rcases Int.isUnit_iff.1 hε with h | h <;> rw [h] at h2 <;> norm_num at h2

/-! ### The weighted Edmonds matrix -/

variable {V : Type*}

/-- The Edmonds matrix at the powers of two `2 ^ w (i, j)`. -/
def weightedEdmonds (G : V × V → Bool) (w : V × V → ℕ) : Matrix V V ℤ :=
  edmondsEval G fun e => 2 ^ w e

/-- An entry of the weighted Edmonds matrix. -/
theorem weightedEdmonds_apply (G : V × V → Bool) (w : V × V → ℕ) (i j : V) :
    weightedEdmonds G w i j = if G (i, j) then 2 ^ w (i, j) else 0 := by
  rw [weightedEdmonds, edmondsEval_apply]

variable [Fintype V] [DecidableEq V]

/-- The weight `∑ v, w (v, σ v)` of the perfect matching `σ`. -/
def matchingWeight (w : V × V → ℕ) (σ : Perm V) : ℕ := ∑ v, w (v, σ v)

omit [DecidableEq V] in
/-- The weight of a perfect matching is the sum of the weights of its pairs. -/
theorem matchingWeight_def (w : V × V → ℕ) (σ : Perm V) :
    matchingWeight w σ = ∑ v, w (v, σ v) := by
  rw [matchingWeight]

/-- The perfect matchings of `G`, as permutations. -/
def perfectMatchings (G : V × V → Bool) : Finset (Perm V) :=
  univ.filter fun σ => ∀ v, G (v, σ v) = true

/-- Membership in `perfectMatchings`. -/
theorem mem_perfectMatchings {G : V × V → Bool} {σ : Perm V} :
    σ ∈ perfectMatchings G ↔ ∀ v, G (v, σ v) = true := by
  simp [perfectMatchings]

/-- The term of `σ` in the Leibniz expansion of the weighted Edmonds matrix: `2` to the weight of
`σ` for a perfect matching, `0` otherwise. -/
theorem prod_weightedEdmonds (G : V × V → Bool) (w : V × V → ℕ) (σ : Perm V) :
    ∏ v, weightedEdmonds G w v (σ v) =
      if σ ∈ perfectMatchings G then 2 ^ matchingWeight w σ else 0 := by
  split_ifs with hσ
  · rw [matchingWeight, ← prod_pow_eq_pow_sum]
    refine prod_congr rfl fun v _ => ?_
    rw [weightedEdmonds, edmondsEval_apply, ite_eq_left (mem_perfectMatchings.1 hσ v)]
  · obtain ⟨v, hv⟩ : ∃ v, G (v, σ v) = false := by
      by_contra! h
      exact hσ (mem_perfectMatchings.2 fun v => by simpa using h v)
    exact prod_eq_zero (mem_univ v) (by rw [weightedEdmonds, edmondsEval_apply,
      ite_eq_right (by simp [hv])])

/-- The determinant of the weighted Edmonds matrix as a signed sum over the perfect matchings. -/
theorem det_weightedEdmonds (G : V × V → Bool) (w : V × V → ℕ) :
    (weightedEdmonds G w).det =
      ∑ σ ∈ perfectMatchings G, (Perm.sign σ : ℤ) * 2 ^ matchingWeight w σ := by
  rw [← det_transpose, det_apply, perfectMatchings, sum_filter]
  refine sum_congr rfl fun σ _ => ?_
  simp only [transpose_apply, prod_weightedEdmonds, perfectMatchings, mem_filter, mem_univ,
    true_and, Units.smul_def, zsmul_eq_mul]
  split_ifs <;> simp

/-- The entry `B i j` of the weighted Edmonds matrix times the cofactor `adj(B) j i` is the signed
sum over the perfect matchings that match `i` to `j`. -/
theorem mul_adjugate_weightedEdmonds (G : V × V → Bool) (w : V × V → ℕ) (i j : V) :
    weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i =
      ∑ σ ∈ (perfectMatchings G).filter (fun σ => σ i = j),
        (Perm.sign σ : ℤ) * 2 ^ matchingWeight w σ := by
  rw [adjugate_apply, ← det_updateRow_smul, ← det_transpose, det_apply,
    sum_filter, perfectMatchings, sum_filter]
  refine sum_congr rfl fun σ _ => ?_
  have hprod : ∏ v, ((weightedEdmonds G w).updateRow i
      (weightedEdmonds G w i j • Pi.single j 1))ᵀ (σ v) v =
      if σ i = j then ∏ v, weightedEdmonds G w v (σ v) else 0 := by
    split_ifs with hij
    · refine prod_congr rfl fun v _ => ?_
      rw [transpose_apply]
      by_cases hv : v = i
      · subst hv
        rw [updateRow_self, Pi.smul_apply, hij, Pi.single_eq_same, smul_eq_mul, mul_one]
      · rw [updateRow_ne hv]
    · refine prod_eq_zero (mem_univ i) ?_
      rw [transpose_apply, updateRow_self, Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero]
  rw [Units.smul_def, zsmul_eq_mul, hprod, prod_weightedEdmonds]
  simp only [perfectMatchings, mem_filter, mem_univ, true_and]
  split_ifs <;> simp

/-! ### Reading off a unique minimum-weight perfect matching -/

/-- `σ₀` is the **unique minimum-weight perfect matching** of the bipartite graph `G` under `w`. -/
def IsUniqueMinMatching (G : V × V → Bool) (w : V × V → ℕ) (σ₀ : Perm V) : Prop :=
  σ₀ ∈ perfectMatchings G ∧
    ∀ σ ∈ perfectMatchings G, σ ≠ σ₀ → matchingWeight w σ₀ < matchingWeight w σ

/-- `σ₀` is the unique minimum-weight perfect matching when it is a perfect matching and every
other perfect matching is strictly heavier. -/
theorem isUniqueMinMatching_iff {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V} :
    IsUniqueMinMatching G w σ₀ ↔ σ₀ ∈ perfectMatchings G ∧
      ∀ σ ∈ perfectMatchings G, σ ≠ σ₀ → matchingWeight w σ₀ < matchingWeight w σ := by
  rw [IsUniqueMinMatching]

/-- Being the unique minimum-weight perfect matching is decidable. -/
instance (G : V × V → Bool) (w : V × V → ℕ) (σ₀ : Perm V) :
    Decidable (IsUniqueMinMatching G w σ₀) :=
  inferInstanceAs (Decidable (σ₀ ∈ perfectMatchings G ∧
    ∀ σ ∈ perfectMatchings G, σ ≠ σ₀ → matchingWeight w σ₀ < matchingWeight w σ))

/-- Both halves of the divisibility of the determinant by powers of two. -/
private theorem two_pow_dvd_det_and_not_dvd {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V}
    (h : IsUniqueMinMatching G w σ₀) :
    (2 : ℤ) ^ matchingWeight w σ₀ ∣ (weightedEdmonds G w).det ∧
      ¬ (2 : ℤ) ^ (matchingWeight w σ₀ + 1) ∣ (weightedEdmonds G w).det := by
  rw [det_weightedEdmonds]
  exact two_pow_dvd_sum_and_not_dvd (ε := fun σ => ((Perm.sign σ : ℤˣ) : ℤ))
    (w := fun σ => matchingWeight w σ) h.1 (Units.isUnit _) h.2

/-- **The weight of the isolated matching divides the determinant**: if `σ₀` is the unique
minimum-weight perfect matching of the bipartite graph `G`, of weight `W`, then `2 ^ W` divides
the determinant of the weighted Edmonds matrix. With `not_two_pow_succ_dvd_det_weightedEdmonds`,
this is the bipartite (Edmonds-matrix) form of the determinant lemma of
[MulmuleyVaziraniVazirani1987], which is stated for the Tutte matrix of a general graph, where the
power is `2 ^ (2 W)`; see [Motwani and Raghavan, Section 12.4][MotwaniRaghavan95]. -/
theorem two_pow_dvd_det_weightedEdmonds {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V}
    (h : IsUniqueMinMatching G w σ₀) :
    (2 : ℤ) ^ matchingWeight w σ₀ ∣ (weightedEdmonds G w).det :=
  (two_pow_dvd_det_and_not_dvd h).1

/-- If `σ₀` is the unique minimum-weight perfect matching of the bipartite graph `G`, of weight
`W`, then `2 ^ (W + 1)` does not divide the determinant of the weighted Edmonds matrix. So `W` is
the exponent of the largest power of two dividing it (`matchingWeight_eq_padicValInt_det`). -/
theorem not_two_pow_succ_dvd_det_weightedEdmonds {G : V × V → Bool} {w : V × V → ℕ}
    {σ₀ : Perm V} (h : IsUniqueMinMatching G w σ₀) :
    ¬ (2 : ℤ) ^ (matchingWeight w σ₀ + 1) ∣ (weightedEdmonds G w).det :=
  (two_pow_dvd_det_and_not_dvd h).2

/-- The determinant of the weighted Edmonds matrix is nonzero when the minimum-weight perfect
matching is unique. -/
theorem det_weightedEdmonds_ne_zero {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V}
    (h : IsUniqueMinMatching G w σ₀) : (weightedEdmonds G w).det ≠ 0 := fun h0 =>
  not_two_pow_succ_dvd_det_weightedEdmonds h (h0 ▸ dvd_zero _)

/-- Both halves of the divisibility of `B i j * adj(B) j i` by powers of two. -/
private theorem two_pow_dvd_mul_adjugate_and_iff {G : V × V → Bool} {w : V × V → ℕ}
    {σ₀ : Perm V} (h : IsUniqueMinMatching G w σ₀) (i j : V) :
    (2 : ℤ) ^ matchingWeight w σ₀ ∣
        weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i ∧
      (σ₀ i = j ↔ ¬ (2 : ℤ) ^ (matchingWeight w σ₀ + 1) ∣
        weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i) := by
  rw [mul_adjugate_weightedEdmonds]
  have hunit : IsUnit ((Perm.sign σ₀ : ℤˣ) : ℤ) := Units.isUnit _
  by_cases hij : σ₀ i = j
  · have hmem : σ₀ ∈ (perfectMatchings G).filter (fun σ => σ i = j) := mem_filter.2 ⟨h.1, hij⟩
    have := two_pow_dvd_sum_and_not_dvd (ε := fun σ => ((Perm.sign σ : ℤˣ) : ℤ))
      (w := fun σ => matchingWeight w σ) hmem hunit
      fun σ hσ hne => h.2 σ (mem_filter.1 hσ).1 hne
    exact ⟨this.1, iff_of_true hij this.2⟩
  · have hdvd := two_pow_succ_dvd_sum (T := (perfectMatchings G).filter (fun σ => σ i = j))
      (ε := fun σ => (Perm.sign σ : ℤ)) (w := fun σ => matchingWeight w σ)
      (W := matchingWeight w σ₀) fun σ hσ => h.2 σ (mem_filter.1 hσ).1
        fun he => hij (he ▸ (mem_filter.1 hσ).2)
    exact ⟨(pow_dvd_pow 2 (Nat.le_succ _)).trans hdvd, iff_of_false hij (not_not.2 hdvd)⟩

/-- If `σ₀` is the unique minimum-weight perfect matching of the bipartite graph `G`, of weight
`W`, then `2 ^ W` divides `B i j * adj(B) j i` for all `i, j`, where `B` is the weighted Edmonds
matrix. -/
theorem two_pow_dvd_mul_adjugate_weightedEdmonds {G : V × V → Bool} {w : V × V → ℕ}
    {σ₀ : Perm V} (h : IsUniqueMinMatching G w σ₀) (i j : V) :
    (2 : ℤ) ^ matchingWeight w σ₀ ∣
      weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i :=
  (two_pow_dvd_mul_adjugate_and_iff h i j).1

/-- **Reading off the isolated matching**: if `σ₀` is the unique minimum-weight perfect matching of
the bipartite graph `G`, of weight `W`, then `σ₀` matches `i` to `j` exactly when `2 ^ (W + 1)`
does not divide `B i j * adj(B) j i`, where `B` is the weighted Edmonds matrix. This is the
bipartite (Edmonds-matrix) form of the edge test of [MulmuleyVaziraniVazirani1987], which is
stated for the Tutte matrix of a general graph; see
[Motwani and Raghavan, Section 12.4][MotwaniRaghavan95]. -/
theorem apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate {G : V × V → Bool} {w : V × V → ℕ}
    {σ₀ : Perm V} (h : IsUniqueMinMatching G w σ₀) (i j : V) :
    σ₀ i = j ↔ ¬ (2 : ℤ) ^ (matchingWeight w σ₀ + 1) ∣
      weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i :=
  (two_pow_dvd_mul_adjugate_and_iff h i j).2

/-- The weight of the unique minimum-weight perfect matching is the exponent of the largest power
of two dividing the determinant of the weighted Edmonds matrix. -/
theorem matchingWeight_eq_padicValInt_det {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V}
    (h : IsUniqueMinMatching G w σ₀) :
    matchingWeight w σ₀ = padicValInt 2 (weightedEdmonds G w).det := by
  have hle := ((padicValInt_dvd_iff (p := 2) _ _).1
    (by exact_mod_cast two_pow_dvd_det_weightedEdmonds h)).resolve_left
    (det_weightedEdmonds_ne_zero h)
  have hlt : ¬ matchingWeight w σ₀ + 1 ≤ padicValInt 2 (weightedEdmonds G w).det :=
    fun hle' => not_two_pow_succ_dvd_det_weightedEdmonds h
      (by exact_mod_cast (padicValInt_dvd_iff (p := 2) _ _).2 (Or.inr hle'))
  omega

/-! ### The output of the procedure -/

/-- **The output of the Mulmuley–Vazirani–Vazirani procedure** on the bipartite graph `G` with
weights `w`: with `B` the weighted Edmonds matrix and `W` the exponent of the largest power of two
dividing `det B`, the pair `(i, j)` is output when `2 ^ (W + 1)` does not divide
`B i j * adj(B) j i`. -/
def mvvOutput (G : V × V → Bool) (w : V × V → ℕ) (i j : V) : Prop :=
  ¬ (2 : ℤ) ^ (padicValInt 2 (weightedEdmonds G w).det + 1) ∣
    weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i

/-- The defining divisibility test of `mvvOutput`. -/
theorem mvvOutput_iff {G : V × V → Bool} {w : V × V → ℕ} {i j : V} :
    mvvOutput G w i j ↔ ¬ (2 : ℤ) ^ (padicValInt 2 (weightedEdmonds G w).det + 1) ∣
      weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i := by
  rw [mvvOutput]

/-- The output of the procedure is decidable. -/
instance (G : V × V → Bool) (w : V × V → ℕ) (i j : V) : Decidable (mvvOutput G w i j) :=
  inferInstanceAs (Decidable (¬ (2 : ℤ) ^ (padicValInt 2 (weightedEdmonds G w).det + 1) ∣
    weightedEdmonds G w i j * adjugate (weightedEdmonds G w) j i))

/-- **The procedure is correct on isolating weights**: if `σ₀` is the unique minimum-weight perfect
matching of the bipartite graph `G` under `w`, the procedure outputs exactly the pairs of `σ₀`. -/
theorem mvvOutput_iff_apply_eq {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V}
    (h : IsUniqueMinMatching G w σ₀) (i j : V) : mvvOutput G w i j ↔ σ₀ i = j := by
  rw [mvvOutput_iff, ← matchingWeight_eq_padicValInt_det h,
    apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate h]

/-- **The procedure succeeds** on the bipartite graph `G` with weights `w`: its output is a perfect
matching of `G`. -/
def MVVSucceeds (G : V × V → Bool) (w : V × V → ℕ) : Prop :=
  ∃ σ ∈ perfectMatchings G, ∀ i j, σ i = j ↔ mvvOutput G w i j

/-- The procedure succeeds when its output is the graph of a perfect matching. -/
theorem mvvSucceeds_iff {G : V × V → Bool} {w : V × V → ℕ} :
    MVVSucceeds G w ↔ ∃ σ ∈ perfectMatchings G, ∀ i j, σ i = j ↔ mvvOutput G w i j := by
  rw [MVVSucceeds]

/-- Success of the procedure is decidable. -/
instance (G : V × V → Bool) (w : V × V → ℕ) : Decidable (MVVSucceeds G w) :=
  inferInstanceAs (Decidable (∃ σ ∈ perfectMatchings G, ∀ i j, σ i = j ↔ mvvOutput G w i j))

/-- The procedure succeeds whenever the minimum-weight perfect matching is unique. -/
theorem mvvSucceeds_of_isUniqueMinMatching {G : V × V → Bool} {w : V × V → ℕ} {σ₀ : Perm V}
    (h : IsUniqueMinMatching G w σ₀) : MVVSucceeds G w :=
  mvvSucceeds_iff.2 ⟨σ₀, h.1, fun i j => (mvvOutput_iff_apply_eq h i j).symm⟩

/-! ### Isolating weights -/

/-- The edges of the bipartite graph `G`. -/
abbrev Edges (G : V × V → Bool) := {e : V × V // G e = true}

/-- The edges of the perfect matching `σ`. -/
def matchingEdges (G : V × V → Bool) (σ : Perm V) : Finset (Edges G) :=
  univ.filter fun e => σ e.1.1 = e.1.2

/-- An edge `(i, j)` belongs to the matching `σ` when `σ i = j`. -/
theorem mem_matchingEdges {G : V × V → Bool} {σ : Perm V} {e : Edges G} :
    e ∈ matchingEdges G σ ↔ σ e.1.1 = e.1.2 := by
  simp [matchingEdges]

/-- The weight `x + 1 ∈ {1, …, N}` on the edges of `G`, extended by `0` to all pairs. -/
def extendWeight {G : V × V → Bool} {N : ℕ} (w : Edges G → Fin N) (e : V × V) : ℕ :=
  if h : G e = true then (w ⟨e, h⟩).val + 1 else 0

omit [Fintype V] [DecidableEq V] in
/-- On an edge, the extended weight is the label plus one. -/
theorem extendWeight_of_edge {G : V × V → Bool} {N : ℕ} (w : Edges G → Fin N) {e : V × V}
    (h : G e = true) : extendWeight w e = (w ⟨e, h⟩).val + 1 := by
  unfold extendWeight
  simp [h]

omit [Fintype V] [DecidableEq V] in
/-- Off the edges, the extended weight is `0`. -/
theorem extendWeight_of_not_edge {G : V × V → Bool} {N : ℕ} (w : Edges G → Fin N) {e : V × V}
    (h : G e = false) : extendWeight w e = 0 := by
  unfold extendWeight
  simp [h]

/-- Distinct perfect matchings have distinct edge sets. -/
theorem matchingEdges_injOn (G : V × V → Bool) :
    Set.InjOn (matchingEdges G) (perfectMatchings G : Set (Perm V)) := by
  intro σ hσ τ _ h
  refine Equiv.ext fun v => ?_
  have hmem : (⟨(v, σ v), mem_perfectMatchings.1 hσ v⟩ : Edges G) ∈ matchingEdges G σ := by
    simp [matchingEdges]
  rw [h] at hmem
  simp only [matchingEdges, mem_filter, mem_univ, true_and] at hmem
  exact hmem.symm

/-- The isolation-lemma weight of the edges of a perfect matching is its matching weight under
the extended weights. -/
theorem setWeight_matchingEdges {G : V × V → Bool} {σ : Perm V} (hσ : σ ∈ perfectMatchings G)
    {N : ℕ} (w : Edges G → Fin N) :
    setWeight (fun x : Fin N => x.val + 1) w (matchingEdges G σ) =
      matchingWeight (extendWeight w) σ := by
  rw [setWeight, matchingWeight]
  symm
  refine sum_nbij' (fun v => ⟨(v, σ v), mem_perfectMatchings.1 hσ v⟩) (fun e => e.1.1)
    (fun v _ => by simp [matchingEdges]) (fun _ _ => mem_univ _) (fun v _ => rfl) ?_ ?_
  · intro e he
    simp only [matchingEdges, mem_filter, mem_univ, true_and] at he
    ext <;> simp [he]
  · intro v _
    simp [extendWeight, mem_perfectMatchings.1 hσ v]

/-- **The isolation lemma for bipartite perfect matchings** [MulmuleyVaziraniVazirani1987]: if the
bipartite graph `G` has a perfect matching and its edges get independent uniform weights from
`{1, …, N}` with `N ≥ 2 |E|`, then with probability at least `1 / 2` the minimum-weight perfect
matching is unique. -/
theorem half_le_dens_exists_isUniqueMinMatching {G : V × V → Bool} (hG : HasPerfectMatching G)
    {N : ℕ} [NeZero N] (hN : 2 * Fintype.card (Edges G) ≤ N) :
    1 / 2 ≤ dens (univ.filter fun w : Edges G → Fin N =>
      ∃ σ₀, IsUniqueMinMatching G (extendWeight w) σ₀) := by
  classical
  obtain ⟨σ, hσ⟩ := hG
  have hF : ((perfectMatchings G).image (matchingEdges G)).Nonempty :=
    ⟨_, mem_image_of_mem _ (mem_perfectMatchings.2 hσ)⟩
  refine (half_le_dens_minWeightSets_card_eq_one hN hF).trans (dens_le_dens fun w hw => ?_)
  simp only [mem_filter, mem_univ, true_and, card_eq_one] at hw ⊢
  obtain ⟨S, hS⟩ := hw
  have hSmem : S ∈ minWeightSets (fun x : Fin N => x.val + 1) w
      ((perfectMatchings G).image (matchingEdges G)) := hS ▸ mem_singleton_self S
  obtain ⟨hSF, hSmin⟩ := mem_minWeightSets.1 hSmem
  obtain ⟨σ₀, hσ₀, rfl⟩ := mem_image.1 hSF
  refine ⟨σ₀, hσ₀, fun τ hτ hne => ?_⟩
  rw [← setWeight_matchingEdges hσ₀, ← setWeight_matchingEdges hτ]
  refine lt_of_le_of_ne (hSmin _ (mem_image_of_mem _ hτ)) fun heq => hne ?_
  refine matchingEdges_injOn G hτ hσ₀ ?_
  have : matchingEdges G τ ∈ minWeightSets (fun x : Fin N => x.val + 1) w
      ((perfectMatchings G).image (matchingEdges G)) :=
    mem_minWeightSets.2 ⟨mem_image_of_mem _ hτ, fun T hT => heq ▸ hSmin T hT⟩
  rw [hS] at this
  exact mem_singleton.1 this

/-- **The Mulmuley–Vazirani–Vazirani algorithm for bipartite graphs, algebraic core**
[MulmuleyVaziraniVazirani1987] [Motwani and Raghavan, Section 12.4][MotwaniRaghavan95]: if the
bipartite graph `G` has a perfect matching and its edges get independent uniform weights `w` from
`{1, …, N}` with `N ≥ 2 |E|`, then with probability at least `1 / 2` the procedure `mvvOutput`
outputs a perfect matching of `G`. -/
theorem half_le_dens_mvv {G : V × V → Bool} (hG : HasPerfectMatching G) {N : ℕ} [NeZero N]
    (hN : 2 * Fintype.card (Edges G) ≤ N) :
    1 / 2 ≤ dens (univ.filter fun w : Edges G → Fin N => MVVSucceeds G (extendWeight w)) := by
  refine (half_le_dens_exists_isUniqueMinMatching hG hN).trans (dens_le_dens fun w hw => ?_)
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  obtain ⟨σ₀, h⟩ := hw
  exact mvvSucceeds_of_isUniqueMinMatching h

end Cslib.Algorithms.Matching
