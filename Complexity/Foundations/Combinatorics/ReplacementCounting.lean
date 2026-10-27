/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SharedSummaries
public import Complexity.Foundations.Combinatorics.SubsetPairCount
public import Complexity.Foundations.Data.BitString.Sign
public import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Replacement designs and algebraic assembly for the shared-summary counting routine

Section 3 of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] evaluates a finite
sum of products of polynomial factors on the Boolean cube,
$$Z = \sum_{x \in \{0, 1\}^n} \prod_{f \in F} \Phi_f((x_v)_{v \in I_f}),$$
over any commutative `ℚ`-algebra `A` by embedding `Z` as `H(0)` for a low-degree univariate
polynomial `H(T) ∈ A[T]` built from polynomial replacement rows `P⃗_{f,v}(T)`.

This module provides the algebraic design interface, domain cardinality bounds, and assembly
identities from §§3.1–3.3 and §3.5 (Definition 3.1, Lemma 3.2, Proposition 3.4, and equations
(3.1)–(3.6), (3.11)–(3.15), pp. 21–26), leaving the §3.4 affine/Taylor expansion (equations
(3.7)–(3.10)) to `AffineTaylor`, the fixed-denominator coefficient bit-length condition
(Definition 3.1(5)) to staged jet arithmetic, and Turing-machine time/space bounds to the runtime
layer.

## Main definitions

* `Cslib.ReplacementCounting.intMeasurementBox`: integer summary box `[-D, D]^c` of size `(2D+1)^c`.
* `Cslib.ReplacementCounting.piGroupEquiv`: decomposition `(∀ g, {i // group i = g} → α) ≃ (ι → α)`.
* `Cslib.ReplacementCounting.Design`: algebraic `(r, τ, D)`-replacement design (Def. 3.1(1)–(4)).
* `Cslib.ReplacementCounting.targetSum`, `Cslib.ReplacementCounting.liftedFactorProduct`,
  `Cslib.ReplacementCounting.targetPolynomial`: `Z` (eq. (3.1)), disjoint-incidence product
  (eq. (3.2)), and `H(T)` (eq. (3.3)).
* `Cslib.ReplacementCounting.jetOrder`: confluent Taylor jet order `J = ⌊d_H / Q⌋ + 1` (eq. (3.5)).

## Main results

* `Cslib.ReplacementCounting.pow_mul_subsetPairCount_le`,
  `Cslib.ReplacementCounting.subsetPairCount_le_one_div_pow_mul`,
  `Cslib.ReplacementCounting.subsetPairCount_le_ratio_pow`: weighted `Cslib.subsetPairCount` bounds
  (eq. (3.15)).
* `Cslib.ReplacementCounting.boolean_mulVec_mem_intMeasurementBox`,
  `Cslib.ReplacementCounting.card_intMeasurementBox`: Boolean measurement inclusion and box size.
* `Cslib.ReplacementCounting.Design.evalRow_eq_of_same_measurements`: kernel shifts imply fiber
  locality via `Cslib.SharedSummaries.fiber_locality_of_kernel_shifts`.
* `Cslib.ReplacementCounting.eval_zero_targetPolynomial`,
  `Cslib.ReplacementCounting.natDegree_targetPolynomial_le_of_liftedTotalDegree_le`: `H(0) = Z` and
  degree bound `≤ d * d₀`.
* `Cslib.ReplacementCounting.Design.sum_restricted_prod_eq_sum_measurement_fibers`: restricted-slice
  factorization via `Cslib.SharedSummaries.sum_prod_eq_sum_measurement_fibers` (Lemma 3.2 and
  equations (3.11), (3.13)).
* `Cslib.ReplacementCounting.targetSum_eq_of_taylorJet`,
  `Cslib.ReplacementCounting.Design.targetSum_eq_of_taylorJet`: exact recovery of `Z` from confluent
  Taylor jets via `Polynomial.eval_zero_eq_of_taylorJet`.
* `Cslib.ReplacementCounting.Design.domainExaminationBound_real`: `2 Q r C_q (2D+1)^{2τn} 2^{2n/r}`
  bound across nodes, subset pairs, and measurement boxes (eq. (3.12) and Proposition 3.4).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§3.1–3.3 and §3.5,
  Definition 3.1, Lemma 3.2, Proposition 3.4, pp. 21–26.
-/

public section

namespace Cslib.ReplacementCounting

open Finset
open scoped BigOperators

/-! ### 1. Subset-pair count and weighted binomial bound (equations (3.14)–(3.15)) -/

export Cslib (subsetPairCount subsetPairCount_zero_right subsetPairCount_zero_left
  subsetPairCount_mono_right subsetPairCount_pos subsetPairCount_eq_three_pow
  subsetPairCount_le_three_pow sum_powerset_filter_card_le_two_pow
  subsetPairCount_eq_sum_powerset_fin card_subsetPairs_eq_subsetPairCount
  card_subsetPairs_eq_subsetPairCount_of_card)

/-- **Weighted binomial bound for subset pairs** ([OpenAI2026ETH], equation (3.15), p. 25):
for `0 ≤ η ≤ 1`, `η ^ q * C_q ≤ (1 + 2 * η) ^ n`. -/
theorem pow_mul_subsetPairCount_le {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (n q : ℕ) :
    η ^ q * (subsetPairCount n q : ℝ) ≤ (1 + 2 * η) ^ n := by
  rw [Cslib.subsetPairCount]
  push_cast
  rw [mul_sum]
  have hle : ∑ s ∈ range (min q n + 1), η ^ q * ((2 : ℝ) ^ s * (n.choose s : ℝ)) ≤
      ∑ s ∈ range (min q n + 1), (2 * η) ^ s * 1 ^ (n - s) * (n.choose s : ℝ) := by
    refine sum_le_sum fun s hs => ?_
    have hs_min : s ≤ min q n := Nat.le_of_lt_succ (mem_range.mp hs)
    have hpow : η ^ q ≤ η ^ s := pow_le_pow_of_le_one hη₀ hη₁ (hs_min.trans (min_le_left q n))
    calc
      η ^ q * ((2 : ℝ) ^ s * (n.choose s : ℝ)) ≤ η ^ s * ((2 : ℝ) ^ s * (n.choose s : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (2 * η) ^ s * 1 ^ (n - s) * (n.choose s : ℝ) := by rw [mul_pow, one_pow, mul_one]; ring
  have hfull : ∑ s ∈ range (min q n + 1), (2 * η) ^ s * 1 ^ (n - s) * (n.choose s : ℝ) ≤
      ∑ s ∈ range (n + 1), (2 * η) ^ s * 1 ^ (n - s) * (n.choose s : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ (min_le_right q n)))
      fun _ _ _ => by positivity
  have hbin : ∑ s ∈ range (n + 1), (2 * η) ^ s * 1 ^ (n - s) * (n.choose s : ℝ) =
      (1 + 2 * η) ^ n := by
    simpa only [add_comm (2 * η) 1] using (add_pow (2 * η) (1 : ℝ) n).symm
  exact (hle.trans hfull).trans_eq hbin

/-- **Divided form of the weighted binomial bound** ([OpenAI2026ETH], equation (3.15), p. 25):
for `0 < η ≤ 1`, `C_q ≤ (1 / η) ^ q * (1 + 2 * η) ^ n`. -/
theorem subsetPairCount_le_one_div_pow_mul {η : ℝ} (hη₀ : 0 < η) (hη₁ : η ≤ 1) (n q : ℕ) :
    (subsetPairCount n q : ℝ) ≤ (1 / η) ^ q * (1 + 2 * η) ^ n := by
  have hpos : 0 < η ^ q := pow_pos hη₀ q
  have hmul := mul_le_mul_of_nonneg_left
    (pow_mul_subsetPairCount_le hη₀.le hη₁ n q) (by positivity : 0 ≤ (1 / η) ^ q)
  have hcancel : (1 / η) ^ q * (η ^ q * (subsetPairCount n q : ℝ)) =
      (subsetPairCount n q : ℝ) := by rw [one_div_pow, one_div, inv_mul_cancel_left₀ hpos.ne']
  exact hcancel ▸ hmul

/-- Specialization of `subsetPairCount_le_one_div_pow_mul` to `η = R / Q` for `1 ≤ R ≤ Q`
([OpenAI2026ETH], p. 26): `C_q ≤ (Q / R) ^ q * (1 + 2 * (R / Q)) ^ n`. -/
theorem subsetPairCount_le_ratio_pow {R Q : ℕ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (n q : ℕ) :
    (subsetPairCount n q : ℝ) ≤ ((Q : ℝ) / R) ^ q * (1 + 2 * ((R : ℝ) / Q)) ^ n := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hR
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hR.trans hRQ)
  have hη₀ : 0 < (R : ℝ) / Q := div_pos hRpos hQpos
  have hη₁ : (R : ℝ) / Q ≤ 1 := (div_le_one hQpos).mpr (by exact_mod_cast hRQ)
  simpa only [one_div_div] using subsetPairCount_le_one_div_pow_mul hη₀ hη₁ n q

/-! ### 2. Integer measurement boxes and group decompositions -/

/-- The integer interval box `[-D, D]^c` bounding `c` integer linear measurements of `{0, 1}`
assignments when each row has `ℓ₁`-norm at most `D` ([OpenAI2026ETH], pp. 22–23). -/
@[expose] def intMeasurementBox (D c : ℕ) : Finset (Fin c → ℤ) :=
  Fintype.piFinset fun _ : Fin c => Icc (-(D : ℤ)) (D : ℤ)

/-- `[-D, D] ∩ ℤ` has cardinality `2 * D + 1`. -/
theorem card_Icc_neg_natCast (D : ℕ) : #(Icc (-(D : ℤ)) (D : ℤ)) = 2 * D + 1 := by
  rw [Int.card_Icc]; omega

/-- `intMeasurementBox D c` has cardinality `(2 * D + 1) ^ c`. -/
@[simp] theorem card_intMeasurementBox (D c : ℕ) :
    #(intMeasurementBox D c) = (2 * D + 1) ^ c := by
  simp only [intMeasurementBox, Fintype.card_piFinset, card_Icc_neg_natCast, prod_const, card_univ,
    Fintype.card_fin]

private theorem natAbs_mul_bitVal_le (a : ℤ) (b : Bool) :
    (a * BitString.bitVal ℤ b).natAbs ≤ a.natAbs := by
  cases b
  · simp only [BitString.bitVal_false, mul_zero, Int.natAbs_zero, Nat.zero_le]
  · simp only [BitString.bitVal_true, mul_one, le_refl]

/-- Any `{0, 1}` inner product against an integer row of `ℓ₁`-norm at most `D` lies in
`[-D, D] ∩ ℤ`. -/
theorem boolean_dot_mem_Icc {α : Type*} [Fintype α] {w : α → ℤ} {D : ℕ}
    (hw : (∑ i : α, (w i).natAbs) ≤ D) (x : α → Bool) :
    (∑ i : α, w i * BitString.bitVal ℤ (x i)) ∈ Icc (-(D : ℤ)) (D : ℤ) := by
  set z := ∑ i : α, w i * BitString.bitVal ℤ (x i)
  have habs : z.natAbs ≤ D :=
    (Int.natAbs_sum_le univ _).trans
      ((sum_le_sum fun i _ => natAbs_mul_bitVal_le (w i) (x i)).trans hw)
  have hcast : (z.natAbs : ℤ) ≤ D := by exact_mod_cast habs
  have hle : z ≤ z.natAbs := Int.le_natAbs
  have hneg : -z ≤ z.natAbs := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -z))
  rw [mem_Icc]; omega

/-- Applying a `c`-row integer matrix whose rows have `ℓ₁`-norm at most `D` to a Boolean vector
lands inside `intMeasurementBox D c`. -/
theorem boolean_mulVec_mem_intMeasurementBox {α : Type*} [Fintype α] {c D : ℕ}
    {C : Fin c → α → ℤ} (hC : ∀ k, (∑ i : α, (C k i).natAbs) ≤ D) (x : α → Bool) :
    (fun k => ∑ i : α, C k i * BitString.bitVal ℤ (x i)) ∈ intMeasurementBox D c :=
  Fintype.mem_piFinset.mpr fun k => boolean_dot_mem_Icc (hC k) x

/-- The image of the Boolean cube `α → Bool` under a `c`-row integer matrix of row `ℓ₁`-norm at
most `D` is contained in `intMeasurementBox D c` and has cardinality at most `(2 * D + 1) ^ c`. -/
theorem card_image_boolean_mulVec_le {α : Type*} [Fintype α] [DecidableEq α] {c D : ℕ}
    {C : Fin c → α → ℤ} (hC : ∀ k, (∑ i : α, (C k i).natAbs) ≤ D) :
    #(univ.image fun x : α → Bool => fun k => ∑ i : α, C k i * BitString.bitVal ℤ (x i)) ≤
      (2 * D + 1) ^ c := by
  have hsub : (univ.image fun x : α → Bool =>
      fun k => ∑ i : α, C k i * BitString.bitVal ℤ (x i)) ⊆ intMeasurementBox D c := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := mem_image.mp hy
    exact boolean_mulVec_mem_intMeasurementBox hC x
  exact (card_le_card hsub).trans_eq (card_intMeasurementBox D c)

/-- Canonical decomposition of functions on `ι` into functions on the fibers of `group : ι → G`,
specializing `(Equiv.piCongrFiberwise fun _ => Equiv.refl _).symm`. -/
@[expose] def piGroupEquiv {ι G α : Type*} (group : ι → G) :
    (∀ g : G, {i : ι // group i = g} → α) ≃ (ι → α) :=
  (Equiv.piCongrFiberwise (γ₁ := fun _ => α) (f := group) fun _ => Equiv.refl _).symm

/-- Evaluating `piGroupEquiv` at `i` when `group i = g` selects `u g ⟨i, hi⟩`. -/
@[simp] theorem piGroupEquiv_apply_of_eq {ι G α : Type*} (group : ι → G)
    (u : ∀ g : G, {i : ι // group i = g} → α) {i : ι} {g : G} (hi : group i = g) :
    piGroupEquiv group u i = u g ⟨i, hi⟩ := by
  subst hi
  rw [piGroupEquiv, Equiv.piCongrFiberwise_symm_apply, Equiv.refl_symm, Equiv.refl_apply]

private def extendFromGroup {ι G R : Type*} [DecidableEq G] [Zero R] (group : ι → G) (g : G)
    (ξ : {i : ι // group i = g} → R) (i : ι) : R :=
  if h : group i = g then ξ ⟨i, h⟩ else 0

private theorem piGroupEquiv_add_single {ι G R : Type*} [DecidableEq G] [AddMonoid R]
    (group : ι → G) (x : ∀ h : G, {i : ι // group i = h} → R) (h : G)
    (delta : {i : ι // group i = h} → R) :
    piGroupEquiv group (x + Pi.single h delta) =
      piGroupEquiv group x + extendFromGroup group h delta := by
  funext i
  simp only [Pi.add_apply, piGroupEquiv_apply_of_eq _ _ rfl, extendFromGroup]
  by_cases hi : group i = h
  · subst hi; simp only [Pi.single_eq_same, ↓reduceDIte]
  · simp only [Pi.single_eq_of_ne hi, Pi.zero_apply, hi, ↓reduceDIte, add_zero]

/-! ### 3. Definition 3.1 `(r, τ, D)`-replacement design interface -/

/-- Algebraic `(r, τ, D)`-replacement design at `Q` distinct nonzero integer evaluation nodes for a
finite family of factors `s : Finset F` with variable scopes `scope : ∀ f, κ f → ι`
([OpenAI2026ETH], Definition 3.1(1)–(4), pp. 21–22).

Condition (5) of Definition 3.1 (the integer bit-length bound after clearing `(R - 1)! Q!`) is a
staging property for exact fixed-denominator arithmetic in Appendix B and is kept separate from this
algebraic interface. -/
structure Design (ι : Type*) [Fintype ι] [DecidableEq ι] {F : Type*} (s : Finset F)
    (κ : F → Type*) (scope : ∀ f, κ f → ι) (r Q R D : ℕ) (τ : ℝ) where
  /-- Number of variable groups satisfies `2 ≤ r`. -/
  two_le_r : 2 ≤ r
  /-- Row `ℓ₁`-bound satisfies `1 ≤ D`. -/
  one_le_D : 1 ≤ D
  /-- Replacement degree bound satisfies `1 ≤ R`. -/
  one_le_R : 1 ≤ R
  /-- Number of evaluation nodes satisfies `R < Q`. -/
  R_lt_Q : R < Q
  /-- Total measurement-row density parameter satisfies `0 < τ`. -/
  τ_pos : 0 < τ
  /-- Total measurement-row density parameter satisfies `τ ≤ 1 / 2`. -/
  τ_le_half : τ ≤ 1 / 2
  /-- Evaluation nodes in `ℤ` (in the paper `1, …, Q`), pairwise distinct and nonzero. -/
  nodes : Fin Q → ℤ
  nodes_injective : Function.Injective nodes
  nodes_ne_zero : ∀ t, nodes t ≠ 0
  /-- Partition `[n] = S_{t,1} ⊔ ⋯ ⊔ S_{t,r}` at node `t`, encoded by `i ↦ g`. -/
  varGroup : Fin Q → ι → Fin r
  /-- Group size bound `|S_{t,g}| ≤ 2n / r`, stated multiplicatively as `|S_{t,g}| * r ≤ 2 * n`. -/
  card_varGroup_le : ∀ t g, #{i : ι | varGroup t i = g} * r ≤ 2 * Fintype.card ι
  /-- Assigned group `σ_f(t) ∈ [r]` of factor `f` at node `t`. -/
  factorGroup : F → Fin Q → Fin r
  /-- Number of integer measurement rows `c_{t,g}` on group `g` at node `t`. -/
  numRows : Fin Q → Fin r → ℕ
  /-- Total measurement row bound `∑_g c_{t,g} ≤ 2 τ n`. -/
  sum_numRows_le : ∀ t, ((∑ g : Fin r, numRows t g : ℕ) : ℝ) ≤ 2 * τ * Fintype.card ι
  /-- Integer measurement matrices `C_{t,g}`, indexed on `ι` and supported on `S_{t,g}`. -/
  matrix : ∀ t : Fin Q, ∀ g : Fin r, Fin (numRows t g) → ι → ℤ
  matrix_support : ∀ t g k i, varGroup t i ≠ g → matrix t g k i = 0
  /-- Every row of `C_{t,g}` has sum of absolute values at most `D`. -/
  row_l1_le : ∀ t g k, (∑ i : ι, (matrix t g k i).natAbs) ≤ D
  /-- Polynomial replacement rows `P⃗_{f,v}(T) ∈ ℚ[T]^{1 × n}`. -/
  row : ∀ f, κ f → ι → Polynomial ℚ
  /-- At `T = 0`, `P⃗_{f,v}(0) = δ_{scope f v}`. -/
  row_eval_zero : ∀ f ∈ s, ∀ v i, (row f v i).eval 0 = if i = scope f v then 1 else 0
  /-- Each replacement entry has univariate degree at most `R`. -/
  row_natDegree_le : ∀ f ∈ s, ∀ v i, (row f v i).natDegree ≤ R
  /-- Kernel condition (Definition 3.1(4)): for `g ≠ σ_f(t)` and `ξ` supported on `S_{t,g}`,
  `C_{t,g} ξ = 0` implies `⟨P⃗_{f,v}(nodes t), ξ⟩ = 0`. -/
  kernel_zero : ∀ t, ∀ f ∈ s, ∀ v, ∀ g ≠ factorGroup f t, ∀ ξ : ι → ℚ,
    (∀ i, varGroup t i ≠ g → ξ i = 0) →
    (∀ k, ∑ i : ι, (matrix t g k i : ℚ) * ξ i = 0) →
    ∑ i : ι, (row f v i).eval (nodes t : ℚ) * ξ i = 0

namespace Design

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] {s : Finset F} {κ : F → Type*}
  {scope : ∀ f, κ f → ι} {r Q R D : ℕ} {τ : ℝ}
  (M : Design ι s κ scope r Q R D τ)

/-- `Q` is strictly positive because `1 ≤ R < Q`. -/
theorem Q_pos (M : Design ι s κ scope r Q R D τ) : 0 < Q :=
  lt_of_lt_of_le Nat.zero_lt_one (M.one_le_R.trans M.R_lt_Q.le)

/-- `r` is strictly positive because `2 ≤ r`. -/
theorem r_pos (M : Design ι s κ scope r Q R D τ) : 0 < r :=
  lt_of_lt_of_le (by decide : 0 < 2) M.two_le_r

/-- Variables belonging to group `g` at node `t` (`S_{t,g}`). -/
@[expose] def groupSet (t : Fin Q) (g : Fin r) : Finset ι :=
  univ.filter fun i => M.varGroup t i = g

private theorem sum_groupSubtype {β : Type*} [AddCommMonoid β] (t : Fin Q) (g : Fin r)
    (f : {i : ι // M.varGroup t i = g} → β) (g' : ι → β)
    (hfg : ∀ i : {i : ι // M.varGroup t i = g}, f i = g' i.1) :
    (∑ i : {i : ι // M.varGroup t i = g}, f i) = ∑ i ∈ M.groupSet t g, g' i := by
  have hcongr : (∑ i : {i : ι // M.varGroup t i = g}, f i) =
      ∑ i : {i : ι // M.varGroup t i = g}, g' i.1 := sum_congr rfl fun i _ => hfg i
  rw [hcongr, ← sum_subtype (M.groupSet t g)
    (fun i => by simp only [groupSet, mem_filter, mem_univ, true_and]) g']

/-- The group sets `S_{t,g}` partition `Finset.univ`. -/
theorem biUnion_groupSet (t : Fin Q) :
    (univ : Finset (Fin r)).biUnion (M.groupSet t) = univ := by
  ext i; simp only [groupSet, mem_biUnion, mem_univ, mem_filter, true_and, exists_eq']

/-- Distinct groups at node `t` are disjoint. -/
theorem disjoint_groupSet (t : Fin Q) {g₁ g₂ : Fin r} (hne : g₁ ≠ g₂) :
    Disjoint (M.groupSet t g₁) (M.groupSet t g₂) :=
  Finset.disjoint_left.mpr fun _ hi₁ hi₂ =>
    hne ((mem_filter.mp hi₁).2.symm.trans (mem_filter.mp hi₂).2)

/-- Natural-division form of the group size bound: `#S_{t,g} ≤ (2 * n) / r`. -/
theorem card_groupSet_le_div (t : Fin Q) (g : Fin r) :
    #(M.groupSet t g) ≤ (2 * Fintype.card ι) / r :=
  (Nat.le_div_iff_mul_le M.r_pos).mpr (M.card_varGroup_le t g)

/-- Real-division form of the group size bound: `(#S_{t,g} : ℝ) ≤ 2 * n / r`. -/
theorem card_groupSet_le_real (t : Fin Q) (g : Fin r) :
    (#(M.groupSet t g) : ℝ) ≤ 2 * (Fintype.card ι : ℝ) / r := by
  rw [le_div_iff₀ (by exact_mod_cast M.r_pos : (0 : ℝ) < r)]
  exact_mod_cast M.card_varGroup_le t g

/-- Type of local Boolean assignments on group `g` at node `t` (`{0, 1}^{S_{t,g}}`). -/
abbrev LocalCube (t : Fin Q) (g : Fin r) : Type _ :=
  {i : ι // M.varGroup t i = g} → Bool

/-- Cardinality of the local Boolean cube on group `g` at node `t` is `2 ^ #S_{t,g}`. -/
theorem card_localCube (t : Fin Q) (g : Fin r) :
    Fintype.card (M.LocalCube t g) = 2 ^ #(M.groupSet t g) := by
  have hcard : Fintype.card {i : ι // M.varGroup t i = g} = #(M.groupSet t g) :=
    Fintype.card_subtype fun i => M.varGroup t i = g
  simp only [LocalCube, Fintype.card_fun, Fintype.card_bool, hcard]

/-- Local integer measurement of `u ∈ {0, 1}^{S_{t,g}}` under `C_{t,g}`. -/
@[expose] def localMeasure (t : Fin Q) (g : Fin r) (u : M.LocalCube t g) :
    Fin (M.numRows t g) → ℤ :=
  fun k => ∑ i : {i : ι // M.varGroup t i = g}, M.matrix t g k i.1 * BitString.bitVal ℤ (u i)

/-- Global integer measurement of `x : ι → Bool` on group `g` at node `t`. -/
@[expose] def globalMeasure (t : Fin Q) (g : Fin r) (x : ι → Bool) :
    Fin (M.numRows t g) → ℤ :=
  fun k => ∑ i : ι, M.matrix t g k i * BitString.bitVal ℤ (x i)

/-- Because `C_{t,g}` is supported on `S_{t,g}`, the global measurement of a glued assignment
agrees with the local measurement on group `g`. -/
theorem globalMeasure_piGroupEquiv (t : Fin Q) (g : Fin r)
    (u : ∀ h : Fin r, M.LocalCube t h) :
    M.globalMeasure t g (piGroupEquiv (M.varGroup t) u) = M.localMeasure t g (u g) := by
  funext k
  simp only [globalMeasure, localMeasure]
  have hsub : (∑ i : {i : ι // M.varGroup t i = g},
      M.matrix t g k i.1 * BitString.bitVal ℤ (u g i)) =
      ∑ i ∈ M.groupSet t g, M.matrix t g k i *
        BitString.bitVal ℤ (piGroupEquiv (M.varGroup t) u i) :=
    M.sum_groupSubtype t g _ _ fun i => by rw [piGroupEquiv_apply_of_eq (M.varGroup t) u i.2]
  rw [hsub]
  refine (sum_subset (subset_univ _) fun i _ hi => ?_).symm
  rw [M.matrix_support t g k i (fun h => hi (mem_filter.mpr ⟨mem_univ i, h⟩)), zero_mul]

/-- Per-group measurement box `[-D, D]^{c_{t,g}}` at node `t`. -/
@[expose] def groupBox (t : Fin Q) (g : Fin r) : Finset (Fin (M.numRows t g) → ℤ) :=
  intMeasurementBox D (M.numRows t g)

/-- Full measurement tuple box `∏_g [-D, D]^{c_{t,g}}` at node `t`. -/
@[expose] def measurementBox (t : Fin Q) :
    Finset (∀ g : Fin r, Fin (M.numRows t g) → ℤ) :=
  Fintype.piFinset (M.groupBox t)

/-- Every local Boolean assignment on group `g` has its measurement in `M.groupBox t g`. -/
theorem localMeasure_mem_groupBox (t : Fin Q) (g : Fin r) (u : M.LocalCube t g) :
    M.localMeasure t g u ∈ M.groupBox t g := by
  refine boolean_mulVec_mem_intMeasurementBox (fun k => ?_) u
  have hle : (∑ i : {i : ι // M.varGroup t i = g}, (M.matrix t g k i.1).natAbs) ≤
      ∑ i : ι, (M.matrix t g k i).natAbs := by
    rw [M.sum_groupSubtype t g _ (fun i => (M.matrix t g k i).natAbs) (fun _ => rfl)]
    exact sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  exact hle.trans (M.row_l1_le t g k)

/-- Exact cardinality `(2 * D + 1) ^ (∑_g c_{t,g})` of `M.measurementBox t`
([OpenAI2026ETH], p. 23). -/
theorem card_measurementBox (t : Fin Q) :
    #(M.measurementBox t) = (2 * D + 1) ^ (∑ g : Fin r, M.numRows t g) := by
  simp only [measurementBox, groupBox, Fintype.card_piFinset, card_intMeasurementBox,
    Finset.prod_pow_eq_pow_sum]

/-- Real-exponent bound `(#(M.measurementBox t) : ℝ) ≤ (2D + 1) ^ (2 τ n)` from
`∑_g c_{t,g} ≤ 2 τ n` ([OpenAI2026ETH], equation (3.12), p. 25). -/
theorem card_measurementBox_le_rpow (t : Fin Q) :
    (#(M.measurementBox t) : ℝ) ≤ (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) := by
  rw [M.card_measurementBox t]
  have hcast : (((2 * D + 1) ^ (∑ g : Fin r, M.numRows t g) : ℕ) : ℝ) =
      (2 * (D : ℝ) + 1) ^ ((∑ g : Fin r, M.numRows t g : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  rw [hcast]
  have hbase : (1 : ℝ) ≤ 2 * (D : ℝ) + 1 := by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    linarith
  exact Real.rpow_le_rpow_of_exponent_le hbase (M.sum_numRows_le t)

/-- Evaluation of the rational replacement linear form `⟨P⃗_{f,v}(nodes t), x⟩` on `x : ι → ℚ`. -/
@[expose] noncomputable def evalRowRat (t : Fin Q) (f : F) (v : κ f) (x : ι → ℚ) : ℚ :=
  ∑ i : ι, (M.row f v i).eval (M.nodes t : ℚ) * x i

/-- Evaluation of the rational replacement linear form `⟨P⃗_{f,v}(nodes t), x⟩` on a Boolean
assignment `x : ι → Bool`. -/
@[expose] noncomputable def evalRow (t : Fin Q) (f : F) (v : κ f) (x : ι → Bool) : ℚ :=
  M.evalRowRat t f v fun i => BitString.bitVal ℚ (x i)

/-- Single-group invariance ([OpenAI2026ETH], p. 22): if `x, x' : ι → ℚ` agree outside `S_{t,h}` for
some `h ≠ σ_f(t)` and have equal `C_{t,h}` measurements, then `⟨P⃗_{f,v}(nodes t), x⟩ =
⟨P⃗_{f,v}(nodes t), x'⟩`. -/
theorem evalRowRat_eq_of_eq_outside_group {t : Fin Q} {f : F} (hf : f ∈ s) (v : κ f)
    {h : Fin r} (hh : h ≠ M.factorGroup f t) {x x' : ι → ℚ}
    (hout : ∀ i, M.varGroup t i ≠ h → x i = x' i)
    (hmeas : ∀ k, ∑ i : ι, (M.matrix t h k i : ℚ) * x i =
      ∑ i : ι, (M.matrix t h k i : ℚ) * x' i) :
    M.evalRowRat t f v x = M.evalRowRat t f v x' := by
  have hker := M.kernel_zero t f hf v h hh (fun i => x i - x' i)
    (fun i hi => sub_eq_zero.mpr (hout i hi))
    (fun k => by simp only [mul_sub, sum_sub_distrib]; exact sub_eq_zero.mpr (hmeas k))
  unfold evalRowRat
  have hsub : (∑ i : ι, (M.row f v i).eval (M.nodes t : ℚ) * x i) -
      ∑ i : ι, (M.row f v i).eval (M.nodes t : ℚ) * x' i =
      ∑ i : ι, (M.row f v i).eval (M.nodes t : ℚ) * (x i - x' i) := by
    simp only [mul_sub, sum_sub_distrib]
  exact sub_eq_zero.mp (hsub.trans hker)

private def ratLocalMeasureLinearMap (t : Fin Q) (g : Fin r) :
    ({i : ι // M.varGroup t i = g} → ℚ) →ₗ[ℚ] (Fin (M.numRows t g) → ℚ) where
  toFun ξ k := ∑ i : {i : ι // M.varGroup t i = g}, (M.matrix t g k i.1 : ℚ) * ξ i
  map_add' ξ₁ ξ₂ := funext fun k => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c ξ := funext fun k => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun _ _ => by ring

private theorem matrix_sum_extendFromGroup (t : Fin Q) (h : Fin r) (k : Fin (M.numRows t h))
    (delta : {i : ι // M.varGroup t i = h} → ℚ) :
    (∑ i : ι, (M.matrix t h k i : ℚ) * extendFromGroup (M.varGroup t) h delta i) =
      M.ratLocalMeasureLinearMap t h delta k := by
  simp only [ratLocalMeasureLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [M.sum_groupSubtype t h _
    (fun i => (M.matrix t h k i : ℚ) * extendFromGroup (M.varGroup t) h delta i)
    (fun i => by simp only [extendFromGroup, i.2, ↓reduceDIte])]
  refine (sum_subset (subset_univ _) fun i _ hi => ?_).symm
  have hne : M.varGroup t i ≠ h := fun hh => hi (mem_filter.mpr ⟨mem_univ i, hh⟩)
  simp only [extendFromGroup, hne, ↓reduceDIte, mul_zero]

/-- All-groups rational invariance ([OpenAI2026ETH], p. 22), derived via
`Cslib.SharedSummaries.fiber_locality_of_kernel_shifts`: if `x, x' : ι → ℚ` agree on the assigned
group `S_{t,σ_f(t)}` and have equal `C_{t,h}` measurements on all other groups `h ≠ σ_f(t)`, then
`⟨P⃗_{f,v}(nodes t), x⟩ = ⟨P⃗_{f,v}(nodes t), x'⟩`. -/
theorem evalRowRat_eq_of_eq_on_assigned_group {t : Fin Q} {f : F} (hf : f ∈ s) (v : κ f)
    {x x' : ι → ℚ}
    (hassigned : ∀ i, M.varGroup t i = M.factorGroup f t → x i = x' i)
    (hmeas : ∀ h, h ≠ M.factorGroup f t → ∀ k,
      ∑ i : ι, (M.matrix t h k i : ℚ) * x i = ∑ i : ι, (M.matrix t h k i : ℚ) * x' i) :
    M.evalRowRat t f v x = M.evalRowRat t f v x' := by
  let g₀ := M.factorGroup f t
  let xLoc := (piGroupEquiv (M.varGroup t)).symm x
  let xLoc' := (piGroupEquiv (M.varGroup t)).symm x'
  have hg₀ : xLoc g₀ = xLoc' g₀ := funext fun i => by
    simp only [xLoc, xLoc', piGroupEquiv, Equiv.symm_symm, Equiv.piCongrFiberwise_apply,
      Equiv.refl_apply]
    exact hassigned i.1 i.2
  have hsame : ∀ h, M.ratLocalMeasureLinearMap t h (xLoc h) =
      M.ratLocalMeasureLinearMap t h (xLoc' h) := by
    intro h
    by_cases hh : h = g₀
    · subst hh; rw [hg₀]
    · funext k
      have hsupp : ∀ z : ι → ℚ,
          M.ratLocalMeasureLinearMap t h ((piGroupEquiv (M.varGroup t)).symm z h) k =
            ∑ i : ι, (M.matrix t h k i : ℚ) * z i := by
        intro z
        simp only [ratLocalMeasureLinearMap, LinearMap.coe_mk, AddHom.coe_mk, piGroupEquiv,
          Equiv.symm_symm, Equiv.piCongrFiberwise_apply, Equiv.refl_apply]
        rw [M.sum_groupSubtype t h _ (fun i => (M.matrix t h k i : ℚ) * z i) (fun _ => rfl)]
        refine sum_subset (subset_univ _) fun i _ hi => ?_
        rw [M.matrix_support t h k i (fun hh' => hi (mem_filter.mpr ⟨mem_univ i, hh'⟩)),
          Int.cast_zero, zero_mul]
      rw [hsupp x, hsupp x', hmeas h hh k]
  have hshift : ∀ g h, h ≠ g → ∀ (base : ∀ j : Fin r, {i : ι // M.varGroup t i = j} → ℚ)
      (delta : {i : ι // M.varGroup t i = h} → ℚ),
      M.ratLocalMeasureLinearMap t h delta = 0 →
      (if g = g₀ then M.evalRowRat t f v (piGroupEquiv (M.varGroup t) (base + Pi.single h delta))
        else 0) =
      (if g = g₀ then M.evalRowRat t f v (piGroupEquiv (M.varGroup t) base) else 0) := by
    intro g h hne base delta hdelta
    by_cases hgg : g = g₀
    · subst hgg
      simp only [↓reduceIte]
      rw [piGroupEquiv_add_single]
      have hker := M.kernel_zero t f hf v h hne (extendFromGroup (M.varGroup t) h delta)
        (fun i hi => by simp only [extendFromGroup, hi, ↓reduceDIte])
        (fun k => by rw [M.matrix_sum_extendFromGroup t h k delta]; exact congrFun hdelta k)
      unfold evalRowRat
      simp only [Pi.add_apply, mul_add, sum_add_distrib, hker, add_zero]
    · simp only [hgg, ↓reduceIte]
  have hloc := SharedSummaries.fiber_locality_of_kernel_shifts (A := ℚ)
    (M.ratLocalMeasureLinearMap t)
    (fun g u => if g = g₀ then M.evalRowRat t f v (piGroupEquiv (M.varGroup t) u) else 0)
    hshift g₀ xLoc xLoc' hsame hg₀
  simpa only [↓reduceIte, xLoc, xLoc', Equiv.apply_symm_apply] using hloc

/-- Boolean fiber-locality of `evalRow`: if two grouped Boolean assignments `u, u'` have the same
integer measurements on every group and agree on `σ_f(t)`, then `evalRow` agrees on their glued
Boolean assignments. -/
theorem evalRow_eq_of_same_measurements {t : Fin Q} {f : F} (hf : f ∈ s) (v : κ f)
    {u u' : ∀ h : Fin r, M.LocalCube t h}
    (hmeas : ∀ h, M.localMeasure t h (u h) = M.localMeasure t h (u' h))
    (hsame : u (M.factorGroup f t) = u' (M.factorGroup f t)) :
    M.evalRow t f v (piGroupEquiv (M.varGroup t) u) =
      M.evalRow t f v (piGroupEquiv (M.varGroup t) u') := by
  have hbit : ∀ b : Bool, (BitString.bitVal ℤ b : ℚ) = BitString.bitVal ℚ b := by
    rintro (_ | _) <;> simp only [BitString.bitVal_false, BitString.bitVal_true,
      Int.cast_zero, Int.cast_one]
  refine M.evalRowRat_eq_of_eq_on_assigned_group hf v (fun i hi => ?_) (fun h _ k => ?_)
  · rw [piGroupEquiv_apply_of_eq (M.varGroup t) u hi,
      piGroupEquiv_apply_of_eq (M.varGroup t) u' hi, hsame]
  · have hm := congrFun (M.globalMeasure_piGroupEquiv t h u ▸
      M.globalMeasure_piGroupEquiv t h u' ▸ hmeas h) k
    have hcast := congrArg (Int.cast : ℤ → ℚ) hm
    simpa only [globalMeasure, Int.cast_sum, Int.cast_mul, hbit] using hcast

/-- Replacement rows mapped into any commutative `ℚ`-algebra `A`. -/
@[expose] noncomputable def rowIn (A : Type*) [CommRing A] [Algebra ℚ A]
    (f : F) (v : κ f) (i : ι) : Polynomial A :=
  (M.row f v i).map (algebraMap ℚ A)

end Design

/-! ### 4. Target sum `Z`, univariate polynomial `H(T)`, and degree bounds (§3.1, eqs. 3.1–3.3) -/

/-- The target Boolean-cube sum `Z = ∑_{x ∈ {0, 1}^n} ∏_{f ∈ s} Φ_f((x_v)_{v ∈ I_f})`
([OpenAI2026ETH], equation (3.1), p. 21). -/
@[expose] noncomputable def targetSum {ι F A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {κ : F → Type*} (s : Finset F) (scope : ∀ f, κ f → ι) (Φ : ∀ f, MvPolynomial (κ f) A) : A :=
  ∑ x : ι → Bool, ∏ f ∈ s, MvPolynomial.eval (BitString.bitVal A ∘ x ∘ scope f) (Φ f)

/-- Disjoint-incidence product polynomial `∏_{f ∈ s} Φ_f((Y_{f,v})_{v ∈ κ f})` in
`MvPolynomial (Σ f, κ f) A`, whose `totalDegree` is bounded by `d` in equation (3.2) of
[OpenAI2026ETH] (p. 21). -/
@[expose] noncomputable def liftedFactorProduct {F A : Type*} [CommSemiring A] {κ : F → Type*}
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) : MvPolynomial (Σ f, κ f) A :=
  ∏ f ∈ s, MvPolynomial.rename (Sigma.mk f) (Φ f)

/-- The disjoint-incidence product has total degree at most `∑_{f ∈ s} (Φ f).totalDegree`. -/
theorem totalDegree_liftedFactorProduct_le {F A : Type*} [CommSemiring A] {κ : F → Type*}
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) :
    (liftedFactorProduct s Φ).totalDegree ≤ ∑ f ∈ s, (Φ f).totalDegree :=
  (MvPolynomial.totalDegree_finsetProd s _).trans
    (sum_le_sum fun f _ => MvPolynomial.totalDegree_rename_le (Sigma.mk f) (Φ f))

/-- Linear replacement form `⟨P⃗_{f,v}(T), x⟩ = ∑_i P_{f,v,i}(T) x_i` in `Polynomial A`. -/
@[expose] noncomputable def replacementEval {ι A : Type*} [Fintype ι] [CommRing A]
    (row : ι → Polynomial A) (x : ι → Bool) : Polynomial A :=
  ∑ i : ι, row i * Polynomial.C (BitString.bitVal A (x i))

/-- Target univariate polynomial `H(T) = ∑_{x ∈ {0,1}^n} ∏_{f ∈ s} Φ_f(⟨P⃗_{f,v}(T), x⟩)` in
`Polynomial A` ([OpenAI2026ETH], equation (3.3), p. 21). -/
@[expose] noncomputable def targetPolynomial {ι F A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) : Polynomial A :=
  ∑ x : ι → Bool, ∏ f ∈ s,
    MvPolynomial.eval₂ Polynomial.C (fun v => replacementEval (P f v) x) (Φ f)

/-- Evaluating `targetPolynomial` at a scalar `t : A` evaluates every replacement row at `t`. -/
theorem eval_targetPolynomial {ι F A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) (t : A) :
    (targetPolynomial s Φ P).eval t =
      ∑ x : ι → Bool, ∏ f ∈ s,
        MvPolynomial.eval
          (fun v => ∑ i : ι, (P f v i).eval t * BitString.bitVal A (x i)) (Φ f) := by
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id A := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, RingHom.id_apply]
  rw [← Polynomial.coe_evalRingHom, targetPolynomial, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_prod]
  refine prod_congr rfl fun f _ => ?_
  rw [Polynomial.coe_evalRingHom, MvPolynomial.polynomial_eval_eval₂, hC]
  have hfun : (fun v => (replacementEval (P f v) x).eval t) =
      fun v => ∑ i : ι, (P f v i).eval t * BitString.bitVal A (x i) := by
    funext v
    rw [← Polynomial.coe_evalRingHom, replacementEval, map_sum]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hfun]; rfl

/-- **At `T = 0`, `H(0) = Z`** ([OpenAI2026ETH], equations (3.1) and (3.3), p. 21): when every
replacement row restores `δ_{scope f v}` at `T = 0`, `(targetPolynomial s Φ P).eval 0` equals
`targetSum s scope Φ`. -/
theorem eval_zero_targetPolynomial {ι F A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {κ : F → Type*} (s : Finset F) (scope : ∀ f, κ f → ι) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A)
    (hzero : ∀ f ∈ s, ∀ v i, (P f v i).eval 0 = if i = scope f v then 1 else 0) :
    (targetPolynomial s Φ P).eval 0 = targetSum s scope Φ := by
  rw [eval_targetPolynomial]
  unfold targetSum
  refine sum_congr rfl fun x _ => prod_congr rfl fun f hf => ?_
  have hfun : (fun v => ∑ i : ι, (P f v i).eval 0 * BitString.bitVal A (x i)) =
      BitString.bitVal A ∘ x ∘ scope f := by
    funext v
    have hsum : (∑ i : ι, (P f v i).eval 0 * BitString.bitVal A (x i)) =
        ∑ i : ι, if i = scope f v then BitString.bitVal A (x i) else 0 :=
      sum_congr rfl fun i _ => by
        rw [hzero f hf v i]; split_ifs <;> simp only [one_mul, zero_mul]
    simp only [hsum, sum_ite_eq', mem_univ, ↓reduceIte]; rfl
  rw [hfun]

/-- Substituting univariate polynomials of degree at most `d₀` into a multivariate polynomial `p`
gives a univariate polynomial of `natDegree` at most `p.totalDegree * d₀`. -/
theorem natDegree_eval₂_polynomial_le {σ A : Type*} [CommSemiring A] (p : MvPolynomial σ A)
    (q : σ → Polynomial A) {d₀ : ℕ} (hq : ∀ v, (q v).natDegree ≤ d₀) :
    (MvPolynomial.eval₂ Polynomial.C q p).natDegree ≤ p.totalDegree * d₀ := by
  classical
  rw [MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  calc
    (∑ v ∈ m.support, (q v ^ m v).natDegree) ≤ ∑ v ∈ m.support, m v * d₀ :=
      sum_le_sum fun v _ => Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (m v) (hq v))
    _ = (∑ v ∈ m.support, m v) * d₀ := (sum_mul _ _ d₀).symm
    _ ≤ p.totalDegree * d₀ :=
      Nat.mul_le_mul_right d₀ (by simpa only [Finsupp.sum] using MvPolynomial.le_totalDegree hm)

private theorem natDegree_replacementEval_le {ι A : Type*} [Fintype ι] [CommRing A]
    {row : ι → Polynomial A} {d₀ : ℕ} (hrow : ∀ i, (row i).natDegree ≤ d₀) (x : ι → Bool) :
    (replacementEval row x).natDegree ≤ d₀ :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (Polynomial.natDegree_mul_C_le _ _).trans (hrow i)

/-- **Degree bound for `H(T)` from the lifted product degree** ([OpenAI2026ETH], equations
(3.2)–(3.3), p. 21): if `liftedFactorProduct s Φ` has total degree at most `d` and active
replacement rows have `natDegree` at most `d₀`, then `(targetPolynomial s Φ P).natDegree ≤ d * d₀`.
-/
theorem natDegree_targetPolynomial_le_of_liftedTotalDegree_le {ι F A : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing A] {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) {d d₀ : ℕ}
    (hd : (liftedFactorProduct s Φ).totalDegree ≤ d)
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ d₀) :
    (targetPolynomial s Φ P).natDegree ≤ d * d₀ := by
  classical
  unfold targetPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  let q : (Σ f, κ f) → Polynomial A := fun fv =>
    if fv.1 ∈ s then replacementEval (P fv.1 fv.2) x else 0
  have hq : ∀ fv, (q fv).natDegree ≤ d₀ := fun fv => by
    dsimp only [q]
    split_ifs with hfs
    · exact natDegree_replacementEval_le (hP fv.1 hfs fv.2) x
    · simp only [Polynomial.natDegree_zero, Nat.zero_le]
  have hprod : (∏ f ∈ s, MvPolynomial.eval₂ Polynomial.C (fun v => replacementEval (P f v) x)
        (Φ f)) = MvPolynomial.eval₂ Polynomial.C q (liftedFactorProduct s Φ) := by
    unfold liftedFactorProduct
    rw [← MvPolynomial.coe_eval₂Hom, map_prod]
    refine prod_congr rfl fun f hf => ?_
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
    have hcomp : q ∘ Sigma.mk f = fun v => replacementEval (P f v) x :=
      funext fun v => by simp only [q, Function.comp_apply, hf, ↓reduceIte]
    rw [hcomp]
  rw [hprod]
  exact (natDegree_eval₂_polynomial_le _ q hq).trans (Nat.mul_le_mul_right d₀ hd)

/-- **Sum-of-degrees bound for `H(T)`**: if active replacement rows have `natDegree` at most `d₀`,
then `(targetPolynomial s Φ P).natDegree ≤ (∑_{f ∈ s} (Φ f).totalDegree) * d₀`. -/
theorem natDegree_targetPolynomial_le {ι F A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) {d₀ : ℕ}
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ d₀) :
    (targetPolynomial s Φ P).natDegree ≤ (∑ f ∈ s, (Φ f).totalDegree) * d₀ :=
  natDegree_targetPolynomial_le_of_liftedTotalDegree_le s Φ P
    (totalDegree_liftedFactorProduct_le s Φ) hP

/-- Specialization to degree-`≤ R - 1` replacement rows (as constructed in Section 4 of
[OpenAI2026ETH]): `(targetPolynomial s Φ P).natDegree ≤ d * (R - 1)` and `≤ d * R`. -/
theorem natDegree_targetPolynomial_le_mul_pred {ι F A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) {d R : ℕ}
    (hd : (∑ f ∈ s, (Φ f).totalDegree) ≤ d)
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ R - 1) :
    (targetPolynomial s Φ P).natDegree ≤ d * (R - 1) ∧
      (targetPolynomial s Φ P).natDegree ≤ d * R := by
  have h1 := (natDegree_targetPolynomial_le s Φ P hP).trans (Nat.mul_le_mul_right (R - 1) hd)
  exact ⟨h1, h1.trans (Nat.mul_le_mul_left d (Nat.sub_le R 1))⟩

/-! ### 5. Jet order and generic Hermite recovery of `Z = H(0)` (equations (3.5)–(3.6)) -/

/-- Confluent Taylor jet order `J = ⌊d_H / Q⌋ + 1` ([OpenAI2026ETH], equation (3.5), p. 24). -/
@[expose] def jetOrder (dH Q : ℕ) : ℕ :=
  dH / Q + 1

/-- `jetOrder` is always positive. -/
theorem jetOrder_pos (dH Q : ℕ) : 0 < jetOrder dH Q :=
  Nat.succ_pos _

/-- Ceiling form `⌈(d_H + 1) / Q⌉ = (d_H + Q) / Q` coincides with `jetOrder d_H Q` for `0 < Q`. -/
theorem add_div_eq_jetOrder (dH : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    (dH + Q) / Q = jetOrder dH Q :=
  Nat.add_div_right dH hQ

/-- When `0 < Q`, `Q * jetOrder d_H Q` strictly exceeds `d_H` ([OpenAI2026ETH], eq. (3.5), p. 24).
-/
theorem lt_mul_jetOrder (dH : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    dH < Q * jetOrder dH Q := by
  calc
    dH < dH / Q * Q + Q := Nat.lt_div_mul_add hQ
    _ = Q * jetOrder dH Q := by unfold jetOrder; ring

/-- **Exact `Z = H(0)` recovery from confluent Taylor jets** ([OpenAI2026ETH], §3.4, p. 24):
given `N` injective integer nodes (`0 < N`), jet order `0 < J`, and replacement rows over a
commutative `ℚ`-algebra `A` restoring `scope` at `T = 0` such that
`(targetPolynomial s Φ P).natDegree < N * J`, `targetSum s scope Φ` is recovered directly from
`Polynomial.taylorJet` via `Polynomial.eval_zero_eq_of_taylorJet`. -/
theorem targetSum_eq_of_taylorJet {ι F : Type*} [Fintype ι] [DecidableEq ι] (A : Type*)
    [CommRing A] [Algebra ℚ A] {κ : F → Type*} (s : Finset F) (scope : ∀ f, κ f → ι)
    (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (hzero : ∀ f ∈ s, ∀ v i, (P f v i).eval 0 = if i = scope f v then 1 else 0)
    {N J : ℕ} {nodes : Fin N → ℤ} (hnodes : Function.Injective nodes) (hN : 0 < N) (hJ : 0 < J)
    (hdeg : (targetPolynomial s Φ P).natDegree < N * J) :
    targetSum s scope Φ = ((Polynomial.hermiteMatrix nodes J).det : ℚ)⁻¹ •
      (((Polynomial.hermiteMatrix nodes J).map (Int.cast : ℤ → A)).updateCol (⟨0, hN⟩, ⟨0, hJ⟩)
        (Polynomial.taylorJet (fun i => (nodes i : A)) J (targetPolynomial s Φ P))).det := by
  rw [← eval_zero_targetPolynomial s scope Φ P hzero]
  refine Polynomial.eval_zero_eq_of_taylorJet A hnodes hN hJ ?_
  exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hdeg)

/-! ### 6. Restricted-slice fiber sums and Proposition 3.4 bounds on a `Design` -/

namespace Design

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] {s : Finset F} {κ : F → Type*}
  {scope : ∀ f, κ f → ι} {r Q R D : ℕ} {τ : ℝ}
  (M : Design ι s κ scope r Q R D τ)

/-- Restricted local Boolean cube `X_{g, E}` on group `g` at node `t`, fixing `u_i = true` for
`i ∈ E ∩ S_{t,g}` ([OpenAI2026ETH], Lemma 3.2 proof, p. 23). -/
@[expose] def restrictedLocalCube (t : Fin Q) (E : Finset ι) (g : Fin r) :
    Finset (M.LocalCube t g) :=
  univ.filter fun u => ∀ i : {i : ι // M.varGroup t i = g}, i.1 ∈ E → u i = true

/-- Product of factors assigned to group `g` at node `t` when each factor `f` is evaluated on its
baseline vector `v ↦ M.evalRow t f v x` ([OpenAI2026ETH], equation (3.11), p. 25). -/
@[expose] noncomputable def groupedFactor {B : Type*} [CommRing B]
    (evalFactor : ∀ f, (κ f → ℚ) → B) (t : Fin Q) (g : Fin r)
    (u : ∀ h : Fin r, M.LocalCube t h) : B :=
  ∏ f ∈ s.filter (fun f => M.factorGroup f t = g),
    evalFactor f fun v => M.evalRow t f v (piGroupEquiv (M.varGroup t) u)

/-- Grouping factors by `σ_f(t)` preserves the full product over `s` ([OpenAI2026ETH],
equation (3.11), p. 25). -/
theorem prod_groupedFactor_eq {B : Type*} [CommRing B] (evalFactor : ∀ f, (κ f → ℚ) → B)
    (t : Fin Q) (u : ∀ h : Fin r, M.LocalCube t h) :
    (∏ g : Fin r, M.groupedFactor evalFactor t g u) =
      ∏ f ∈ s, evalFactor f fun v => M.evalRow t f v (piGroupEquiv (M.varGroup t) u) :=
  Finset.prod_fiberwise_of_maps_to (fun f _ => mem_univ (M.factorGroup f t)) _

/-- `groupedFactor` depends on `u` only through `u g` and the integer measurements of all groups. -/
theorem groupedFactor_locality {B : Type*} [CommRing B] (evalFactor : ∀ f, (κ f → ℚ) → B)
    (t : Fin Q) (g : Fin r) (u u' : ∀ h : Fin r, M.LocalCube t h)
    (hmeas : ∀ h, M.localMeasure t h (u h) = M.localMeasure t h (u' h))
    (hsame : u g = u' g) :
    M.groupedFactor evalFactor t g u = M.groupedFactor evalFactor t g u' := by
  unfold groupedFactor
  refine prod_congr rfl fun f hf => ?_
  have hfun : (fun v => M.evalRow t f v (piGroupEquiv (M.varGroup t) u)) =
      fun v => M.evalRow t f v (piGroupEquiv (M.varGroup t) u') :=
    funext fun v => M.evalRow_eq_of_same_measurements (mem_filter.mp hf).1 v hmeas
      ((mem_filter.mp hf).2 ▸ hsame)
  rw [hfun]

/-- **Restricted-slice measurement-fiber factorization** ([OpenAI2026ETH], Lemma 3.2 and equations
(3.11), (3.13), pp. 22–25): for any subset `E ⊆ ι`, ring `B`, evaluator `evalFactor`, and valid
unrestricted fiber representative selector, the sum over `{x : ι → Bool | ∀ i ∈ E, x i = true}`
factors into per-group sums over `M.measurementBox t` via
`Cslib.SharedSummaries.sum_prod_eq_sum_measurement_fibers`. -/
theorem sum_restricted_prod_eq_sum_measurement_fibers {B : Type*} [CommRing B]
    (evalFactor : ∀ f, (κ f → ℚ) → B) (t : Fin Q) (E : Finset ι)
    (representative : ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ y hy g, M.localMeasure t g (representative y hy g) = y g) :
    (∑ x ∈ univ.filter (fun x : ι → Bool => ∀ i ∈ E, x i = true),
        ∏ f ∈ s, evalFactor f fun v => M.evalRow t f v x) =
      ∑ y ∈ M.measurementBox t,
        SharedSummaries.fiberContribution (M.localMeasure t) (M.restrictedLocalCube t E)
          (M.groupedFactor evalFactor t) representative y := by
  have hbij : (∑ x ∈ univ.filter (fun x : ι → Bool => ∀ i ∈ E, x i = true),
        ∏ f ∈ s, evalFactor f fun v => M.evalRow t f v x) =
      ∑ u ∈ Fintype.piFinset (M.restrictedLocalCube t E),
        ∏ g : Fin r, M.groupedFactor evalFactor t g u := by
    refine (Finset.sum_nbij (piGroupEquiv (M.varGroup t)) ?_ ?_ ?_ ?_).symm
    · intro u hu
      refine mem_filter.mpr ⟨mem_univ _, fun i hiE => ?_⟩
      rw [piGroupEquiv_apply_of_eq _ _ rfl]
      exact (mem_filter.mp (Fintype.mem_piFinset.mp hu (M.varGroup t i))).2 ⟨i, rfl⟩ hiE
    · intro u₁ _ u₂ _ heq
      exact (piGroupEquiv (M.varGroup t)).injective heq
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      refine ⟨(piGroupEquiv (M.varGroup t)).symm x, mem_coe.mpr ?_,
        (piGroupEquiv (M.varGroup t)).apply_symm_apply x⟩
      refine Fintype.mem_piFinset.mpr fun g => mem_filter.mpr ⟨mem_univ _, fun i hiE => ?_⟩
      simpa only [piGroupEquiv, Equiv.symm_symm, Equiv.piCongrFiberwise_apply,
        Equiv.refl_apply] using hx.2 i.1 hiE
    · intro u _
      exact M.prod_groupedFactor_eq evalFactor t u
  rw [hbij]
  exact SharedSummaries.sum_prod_eq_sum_measurement_fibers (M.localMeasure t) (M.groupBox t)
    (M.localMeasure_mem_groupBox t) (M.restrictedLocalCube t E) (M.groupedFactor evalFactor t)
    (M.groupedFactor_locality evalFactor t) representative valid

/-- Target polynomial `H(T) ∈ A[T]` instantiated with `M.rowIn A`. -/
@[expose] noncomputable def targetPoly {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) : Polynomial A :=
  targetPolynomial s Φ (M.rowIn A)

/-- At `T = 0`, `(M.targetPoly Φ).eval 0 = targetSum s scope Φ`. -/
theorem eval_zero_targetPoly {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) :
    (M.targetPoly Φ).eval 0 = targetSum s scope Φ := by
  refine eval_zero_targetPolynomial s scope Φ (M.rowIn A) fun f hf v i => ?_
  rw [rowIn, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
    Polynomial.coeff_zero_eq_eval_zero, M.row_eval_zero f hf v i]
  split_ifs <;> simp only [map_one, map_zero]

/-- Degree bound `(M.targetPoly Φ).natDegree ≤ d * R` when `(liftedFactorProduct s Φ).totalDegree
≤ d` ([OpenAI2026ETH], equations (3.2)–(3.3), p. 21). -/
theorem natDegree_targetPoly_le {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) {d : ℕ} (hd : (liftedFactorProduct s Φ).totalDegree ≤ d) :
    (M.targetPoly Φ).natDegree ≤ d * R :=
  natDegree_targetPolynomial_le_of_liftedTotalDegree_le s Φ (M.rowIn A) hd fun f hf v i =>
    Polynomial.natDegree_map_le.trans (M.row_natDegree_le f hf v i)

/-- **Unrestricted node evaluation `H(nodes t)` via measurement fibers** ([OpenAI2026ETH], §3.3,
p. 23): evaluating `M.targetPoly Φ` at `M.nodes t` equals the `E = ∅` measurement-fiber sum over
`M.measurementBox t`. -/
theorem eval_nodes_targetPoly_eq_sum_measurement_fibers {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q)
    (representative : ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ y hy g, M.localMeasure t g (representative y hy g) = y g) :
    (M.targetPoly Φ).eval (M.nodes t : A) =
      ∑ y ∈ M.measurementBox t,
        SharedSummaries.fiberContribution (M.localMeasure t) (M.restrictedLocalCube t ∅)
          (M.groupedFactor (fun f q => MvPolynomial.eval (algebraMap ℚ A ∘ q) (Φ f)) t)
          representative y := by
  have hbit : ∀ b : Bool, BitString.bitVal A b = algebraMap ℚ A (BitString.bitVal ℚ b) := by
    rintro (_ | _) <;> simp only [BitString.bitVal_false, BitString.bitVal_true, map_zero, map_one]
  have hlhs : (M.targetPoly Φ).eval (M.nodes t : A) =
      ∑ x ∈ univ.filter (fun x : ι → Bool => ∀ i ∈ (∅ : Finset ι), x i = true),
        ∏ f ∈ s, MvPolynomial.eval (algebraMap ℚ A ∘ fun v => M.evalRow t f v x) (Φ f) := by
    rw [targetPoly, eval_targetPolynomial]
    have hfilt : (univ.filter fun x : ι → Bool => ∀ i ∈ (∅ : Finset ι), x i = true) = univ := by
      ext x; simp only [mem_filter, mem_univ, notMem_empty, IsEmpty.forall_iff, implies_true,
        and_self]
    rw [hfilt]
    refine sum_congr rfl fun x _ => prod_congr rfl fun f _ => ?_
    have hfun : (fun v => ∑ i : ι, (M.rowIn A f v i).eval (M.nodes t : A) *
        BitString.bitVal A (x i)) = algebraMap ℚ A ∘ fun v => M.evalRow t f v x := by
      funext v
      simp only [Function.comp_apply, evalRow, evalRowRat, map_sum, map_mul, ← hbit, rowIn]
      refine sum_congr rfl fun i _ => ?_
      have hnode : (M.nodes t : A) = algebraMap ℚ A (M.nodes t : ℚ) := by simp only [map_intCast]
      rw [hnode, Polynomial.eval_map_apply]
    rw [hfun]
  rw [hlhs]
  exact M.sum_restricted_prod_eq_sum_measurement_fibers
    (fun f q => MvPolynomial.eval (algebraMap ℚ A ∘ q) (Φ f)) t ∅ representative valid

/-- Factor `Φ_{f, U}(x; z) ∈ Polynomial A` at node `t` after fixing `X⃗ = 1_U` in the Taylor
correction ([OpenAI2026ETH], equations (3.8) and (3.11), pp. 24–25). -/
@[expose] noncomputable def shiftedFactorEval {A : Type*} [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q) (U : Finset ι) (f : F) (qBaseline : κ f → ℚ) :
    Polynomial A :=
  MvPolynomial.eval₂ Polynomial.C
    (fun v => Polynomial.C (algebraMap ℚ A (qBaseline v)) +
      ∑ i ∈ U, (Polynomial.taylor (M.nodes t : A) (M.rowIn A f v i) -
        Polynomial.C ((M.rowIn A f v i).eval (M.nodes t : A))))
    (Φ f)

/-- Specialization of `sum_restricted_prod_eq_sum_measurement_fibers` to the Taylor-shifted factors
`Φ_{f, U}(x; z)` in `Polynomial A` ([OpenAI2026ETH], equations (3.11) and (3.13), p. 25). -/
theorem sum_restricted_shiftedFactor_eq_sum_measurement_fibers {A : Type*} [CommRing A]
    [Algebra ℚ A] (Φ : ∀ f, MvPolynomial (κ f) A) (t : Fin Q) (E U : Finset ι)
    (representative : ∀ y : ∀ g : Fin r, Fin (M.numRows t g) → ℤ,
      (∀ g, ∃ u : M.LocalCube t g, M.localMeasure t g u = y g) → ∀ g, M.LocalCube t g)
    (valid : ∀ y hy g, M.localMeasure t g (representative y hy g) = y g) :
    (∑ x ∈ univ.filter (fun x : ι → Bool => ∀ i ∈ E, x i = true),
        ∏ f ∈ s, M.shiftedFactorEval Φ t U f (fun v => M.evalRow t f v x)) =
      ∑ y ∈ M.measurementBox t,
        SharedSummaries.fiberContribution (M.localMeasure t) (M.restrictedLocalCube t E)
          (M.groupedFactor (M.shiftedFactorEval Φ t U) t) representative y :=
  M.sum_restricted_prod_eq_sum_measurement_fibers (M.shiftedFactorEval Φ t U) t E
    representative valid

/-- **Hermite jet recovery of `Z` for a `Design`** ([OpenAI2026ETH], equations (3.5)–(3.6) and
Proposition 3.4, pp. 24–25): whenever `(liftedFactorProduct s Φ).totalDegree ≤ d` and `d * R <
Q * J` (in particular for `J = jetOrder (d * R) Q`), `targetSum s scope Φ` equals the Hermite
determinant expression in the order-`J` Taylor jets of `M.targetPoly Φ` at `M.nodes`. -/
theorem targetSum_eq_of_taylorJet (A : Type*) [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) {d J : ℕ} (hd : (liftedFactorProduct s Φ).totalDegree ≤ d)
    (hJ : 0 < J) (hQJ : d * R < Q * J) :
    targetSum s scope Φ = ((Polynomial.hermiteMatrix M.nodes J).det : ℚ)⁻¹ •
      (((Polynomial.hermiteMatrix M.nodes J).map (Int.cast : ℤ → A)).updateCol
        (⟨0, M.Q_pos⟩, ⟨0, hJ⟩)
        (Polynomial.taylorJet (fun i => (M.nodes i : A)) J (M.targetPoly Φ))).det := by
  rw [← M.eval_zero_targetPoly Φ]
  refine Polynomial.eval_zero_eq_of_taylorJet A M.nodes_injective M.Q_pos hJ ?_
  exact Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr ((M.natDegree_targetPoly_le Φ hd).trans_lt hQJ))

/-- Specialization of `Design.targetSum_eq_of_taylorJet` at the canonical jet order
`J = jetOrder (d * R) Q = ⌊d * R / Q⌋ + 1` ([OpenAI2026ETH], equation (3.5), p. 24). -/
theorem targetSum_eq_of_taylorJet_jetOrder (A : Type*) [CommRing A] [Algebra ℚ A]
    (Φ : ∀ f, MvPolynomial (κ f) A) {d : ℕ} (hd : (liftedFactorProduct s Φ).totalDegree ≤ d) :
    targetSum s scope Φ =
      ((Polynomial.hermiteMatrix M.nodes (jetOrder (d * R) Q)).det : ℚ)⁻¹ •
        (((Polynomial.hermiteMatrix M.nodes (jetOrder (d * R) Q)).map (Int.cast : ℤ → A)).updateCol
          (⟨0, M.Q_pos⟩, ⟨0, jetOrder_pos _ _⟩)
          (Polynomial.taylorJet (fun i => (M.nodes i : A)) (jetOrder (d * R) Q)
            (M.targetPoly Φ))).det :=
  M.targetSum_eq_of_taylorJet A Φ hd (jetOrder_pos _ _) (lt_mul_jetOrder (d * R) M.Q_pos)

/-- Exact natural-number two-pass local-cube scan count
`2 (2D + 1) ^ (∑_g c_{t,g}) ∑_g 2 ^ |S_{t,g}|` at node `t` ([OpenAI2026ETH], Lemma 3.2, p. 22). -/
theorem two_mul_card_measurementBox_mul_sum_card_localCube (t : Fin Q) :
    2 * #(M.measurementBox t) * (∑ g : Fin r, Fintype.card (M.LocalCube t g)) =
      2 * (2 * D + 1) ^ (∑ g : Fin r, M.numRows t g) *
        ∑ g : Fin r, 2 ^ #(M.groupSet t g) := by
  rw [M.card_measurementBox t, sum_congr rfl fun g _ => M.card_localCube t g]

/-- Sum of local Boolean cube cardinalities across all `r` groups at node `t` is at most
`r * 2 ^ ((2 * n) / r)`. -/
theorem sum_card_localCube_le (t : Fin Q) :
    (∑ g : Fin r, Fintype.card (M.LocalCube t g)) ≤
      r * 2 ^ ((2 * Fintype.card ι) / r) := by
  calc
    (∑ g : Fin r, Fintype.card (M.LocalCube t g)) = ∑ g : Fin r, 2 ^ #(M.groupSet t g) :=
      sum_congr rfl fun g _ => M.card_localCube t g
    _ ≤ ∑ _g : Fin r, 2 ^ ((2 * Fintype.card ι) / r) :=
      sum_le_sum fun g _ => Nat.pow_le_pow_right (by decide : 0 < 2) (M.card_groupSet_le_div t g)
    _ = r * 2 ^ ((2 * Fintype.card ι) / r) := by
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- Per-pair Boolean-vector scan bound at node `t` ([OpenAI2026ETH], equation (3.12), p. 25):
two scans of all `r` local cubes across every tuple in `M.measurementBox t` inspect at most
`2 * r * (2D + 1) ^ (2 τ n) * 2 ^ (2 n / r)` local assignments. -/
theorem singlePairScanBound_real (t : Fin Q) :
    (2 * (#(M.measurementBox t) : ℝ) * ∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ)) ≤
      2 * (r : ℝ) * (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) *
        (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) := by
  have hmeas := M.card_measurementBox_le_rpow t
  have hgroup : (∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ)) ≤
      (r : ℝ) * (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) := by
    calc
      (∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ)) =
          ∑ g : Fin r, (2 : ℝ) ^ (#(M.groupSet t g) : ℝ) :=
        sum_congr rfl fun g _ => by rw [M.card_localCube t g, Real.rpow_natCast]; norm_cast
      _ ≤ ∑ _g : Fin r, (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) :=
        sum_le_sum fun g _ =>
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (M.card_groupSet_le_real t g)
      _ = (r : ℝ) * (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    2 * (#(M.measurementBox t) : ℝ) * ∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ) ≤
        2 * (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) *
          ((r : ℝ) * (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r)) := by
      have hmul := mul_le_mul hmeas hgroup (by positivity) (by positivity)
      linarith
    _ = 2 * (r : ℝ) * (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) *
          (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) := by ring

/-- **Total finite-domain examination bound across all `Q` nodes and `C_q` subset pairs**
([OpenAI2026ETH], Proposition 3.4, p. 25): summing the two-pass local-cube scan count over all
`t : Fin Q` and all subset pairs `(E, U)` with `#E ≤ q` and `U ⊆ E` yields at most
`2 Q r C_q (2D + 1) ^ (2 τ n) 2 ^ (2 n / r)`. -/
theorem domainExaminationBound_real (q : ℕ) :
    (∑ t : Fin Q, (#{p : Finset ι × Finset ι | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
        (2 * (#(M.measurementBox t) : ℝ) *
          ∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ))) ≤
      2 * (Q : ℝ) * (r : ℝ) * (subsetPairCount (Fintype.card ι) q : ℝ) *
        (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) *
        (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) := by
  rw [card_subsetPairs_eq_subsetPairCount]
  calc
    (∑ t : Fin Q, (subsetPairCount (Fintype.card ι) q : ℝ) *
        (2 * (#(M.measurementBox t) : ℝ) *
          ∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ))) ≤
        ∑ _t : Fin Q, (subsetPairCount (Fintype.card ι) q : ℝ) *
          (2 * (r : ℝ) * (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) *
            (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r)) :=
      sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (M.singlePairScanBound_real t) (Nat.cast_nonneg _)
    _ = 2 * (Q : ℝ) * (r : ℝ) * (subsetPairCount (Fintype.card ι) q : ℝ) *
          (2 * (D : ℝ) + 1) ^ (2 * τ * Fintype.card ι) *
          (2 : ℝ) ^ (2 * (Fintype.card ι : ℝ) / r) := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Design

end Cslib.ReplacementCounting
