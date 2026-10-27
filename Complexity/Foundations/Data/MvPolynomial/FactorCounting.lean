/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SharedSummaries
public import Complexity.Foundations.Data.MvPolynomial.AffineTaylor
public import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Factor counting via shared linear summaries and Hermite–Taylor reconstruction

This module formalizes the mathematical identities of **Section 3 (Sections 3.1–3.5, printed
pp. 21–26)** of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] connecting
the affine-Taylor restricted-subset jet identity
(`Complexity.Foundations.Data.MvPolynomial.AffineTaylor`), finite shared-summary factorization
(`Complexity.Foundations.Combinatorics.SharedSummaries`), and confluent Hermite interpolation
(`Complexity.Foundations.Data.Polynomial.HermiteInterpolation`):

1. **Target sum restoration at `T = 0` and univariate degree bounds (§3.1 eqs. 3.1–3.3 & §3.4
   eq. 3.5, pp. 21, 24):**
   - `targetSum s Φ varOf`: the target Boolean-cube sum
     $Z = \sum_{x \in \{0, 1\}^\iota} \prod_{f \in s} \Phi_f((x_{\mathrm{varOf}(f, v)})_v)$
     (equation 3.1).
   - `eval_zero_replacedSum_eq_targetSum`: when every replacement entry $P_{f, v, i}(0)$ equals
     $\delta_{\mathrm{varOf}(f, v), i}$, evaluating `replacedSum s Φ P` at $T = 0$ recovers
     `targetSum s Φ varOf` ($H(0) = Z$, equation 3.3).
   - `natDegree_aeval_polynomial_le`, `natDegree_replacedSum_le`, and
     `degree_replacedSum_lt_of_sum_totalDegree_le`: when every replacement entry has degree at
     most $R$ and $\sum_{f \in s} \mathrm{totalDegree}(\Phi_f) \le d$, `replacedSum s Φ P` has
     `natDegree ≤ d * R` (equations 3.2–3.3) and `degree < Q * J` whenever $d R < Q J$ (in
     particular for $q = \lfloor d R / Q \rfloor$ and $J = q + 1$, equation 3.5).

2. **Factor grouping by assigned group, integer measurement boxes, and `SharedSummaries`
   factorization (§3.2–3.4 eqs. 3.4, 3.11–3.13, pp. 22–25):**
   - `GroupCoord`, `groupReassemble`, `groupRestrict`, `groupSplitEquiv`, `extendGroupVec`:
     splitting global assignments $x : \iota \to \alpha$ across variable groups
     $S_g = \{i : \iota \mid \mathrm{varGroupOf}(i) = g\}$ and extending local vectors by zero.
   - `evalAffineFactor` ($\Phi_{f, U}(x; z)$) and `groupFactorProduct` ($A_{g, U}(x; z)$,
     equation 3.11), satisfying
     $\prod_{g : G} A_{g, U}(x; z) = G_x(\mathbf{1}_U, z)$
     (`prod_groupFactorProduct_eq_map_eval_factorProduct`) and baseline congruence
     (`groupFactorProduct_congr_baseline`).
   - `localAllowed`, `sum_restricted_factorProduct_eq_sum_measurement_fibers`, and
     `coeff_taylor_replacedSum_eq_sum_measurement_fibers`: under measurement-fiber baseline
     locality, the restricted cube sum $Z_{t, E, U}(z) = \sum_{x|_E = 1} G_x(\mathbf{1}_U, z)$
     and the Taylor jet coefficients $[z^j] H(t + z)$ ($j \le q$, equation 3.13) factor through
     `Cslib.SharedSummaries.fiberContribution`.
   - `groupFactorProduct_locality_of_kernel_shifts`: rational kernel-shift invariance of the
     scalar baselines at node $t$ (Definition 3.1 (4)) implies measurement-fiber locality of
     `groupFactorProduct` via `Cslib.SharedSummaries.fiber_locality_of_kernel_shifts`.
   - `intMeasurementBox`, `card_intMeasurementBox`, `mulVec_bitVal_mem_intMeasurementBox`:
     when every row of an integer matrix $C \in \mathbb{Z}^{\rho \times \sigma}$ has $\ell_1$-norm
     at most $D$, every Boolean vector's measurement lies in $[-D, D]^\rho$ of size
     $(2D + 1)^{|\rho|}$.

3. **Hermite–Taylor–SharedSummaries target-sum synthesis (§3.4 & Proposition 3.4 correctness,
   pp. 24–25):**
   - `targetSum_eq_of_taylorJet`: over any commutative $\mathbb{Q}$-algebra $A$, when the
     replacement rows restore variables at $T = 0$ and have degree $\le R$ with $d R < Q J$,
     `targetSum s Φ varOf` is recovered by `Polynomial.eval_zero_eq_of_taylorJet` at any $Q$
     distinct integer nodes from the order-$J$ Taylor jet of `replacedSum s Φ P`.

4. **The three exponential costs: subset-pair count $C_q$ and weighted binomial bound (§3.5
   eqs. 3.14–3.15, p. 25):**
   - `subsetPairCount q n`: $C_q = \sum_{s = 0}^{\min(q, n)} \binom{n}{s} 2^s$ (equation 3.14).
   - `sum_card_powerset_filter_card_le_eq_subsetPairCount`: exact count of pairs $(E, U)$ with
     $|E| \le q$ and $U \subseteq E$, together with `subsetPairCount_zero_left` ($C_0 = 1$) and
     `subsetPairCount_of_le` ($C_q = 3^n$ for $n \le q$).
   - `pow_mul_subsetPairCount_le`: for $0 \le \eta \le 1$,
     $\eta^q C_q \le \sum_{s = 0}^n \binom{n}{s} (2\eta)^s = (1 + 2\eta)^n$ (equation 3.15).

## Main definitions

* `Cslib.AffineTaylor.targetSum`: the target Boolean-cube sum $Z$ (equation 3.1).
* `Cslib.AffineTaylor.GroupCoord`, `Cslib.AffineTaylor.groupReassemble`,
  `Cslib.AffineTaylor.groupRestrict`, `Cslib.AffineTaylor.groupSplitEquiv`,
  `Cslib.AffineTaylor.extendGroupVec`: variable-group partition and zero-extension operations.
* `Cslib.AffineTaylor.evalAffineFactor`, `Cslib.AffineTaylor.groupFactorProduct`:
  evaluated affine factor $\Phi_{f, U}(x; z)$ and grouped product $A_{g, U}(x; z)$ (equation 3.11).
* `Cslib.AffineTaylor.localAllowed`, `Cslib.AffineTaylor.intMeasurementBox`: per-group fixed-bit
  Boolean subsets and the integer measurement box $[-D, D]^\rho$.
* `Cslib.AffineTaylor.subsetPairCount`: the subset-pair count $C_q(n)$ (equation 3.14).

## Main results

* `Cslib.AffineTaylor.eval_zero_replacedSum_eq_targetSum`: restoration $H(0) = Z$ (equation 3.3).
* `Cslib.AffineTaylor.natDegree_replacedSum_le`,
  `Cslib.AffineTaylor.degree_replacedSum_lt_of_sum_totalDegree_le`: univariate degree bounds
  $\deg_T H \le d R < Q J$ (equations 3.2–3.3, 3.5).
* `Cslib.AffineTaylor.prod_groupFactorProduct_eq_map_eval_factorProduct`:
  $\prod_g A_{g, U}(x; z) = G_x(\mathbf{1}_U, z)$ (equation 3.11).
* `Cslib.AffineTaylor.sum_restricted_factorProduct_eq_sum_measurement_fibers`,
  `Cslib.AffineTaylor.coeff_taylor_replacedSum_eq_sum_measurement_fibers`:
  factorization of $Z_{t, E, U}(z)$ and $[z^j] H(t + z)$ through
  `Cslib.SharedSummaries.fiberContribution` (Lemma 3.2 and equation 3.13).
* `Cslib.AffineTaylor.groupFactorProduct_locality_of_kernel_shifts`: kernel-shift invariance
  implies measurement-fiber locality of `groupFactorProduct`.
* `Cslib.AffineTaylor.card_intMeasurementBox`,
  `Cslib.AffineTaylor.mulVec_bitVal_mem_intMeasurementBox`: integer measurement box bounds.
* `Cslib.AffineTaylor.targetSum_eq_of_taylorJet`: Hermite recovery of `targetSum` from the
  order-$J$ Taylor jet of `replacedSum` (Proposition 3.4 correctness).
* `Cslib.AffineTaylor.sum_card_powerset_filter_card_le_eq_subsetPairCount`,
  `Cslib.AffineTaylor.subsetPairCount_zero_left`, `Cslib.AffineTaylor.subsetPairCount_of_le`,
  `Cslib.AffineTaylor.pow_mul_subsetPairCount_le`: equations (3.14)–(3.15).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Sections 3.1–3.5
  (printed pp. 21–26).
-/

@[expose] public noncomputable section

open scoped BigOperators
open Finset Matrix Polynomial Cslib.BitString Cslib.SharedSummaries

namespace Cslib.AffineTaylor

variable {A : Type*} [CommRing A] {ι F G : Type*} {κ : F → Type*}

/-! ### Part 1: Target sum restoration at `T = 0` and degree bounds (§3.1 & §3.4, pp. 21, 24) -/

open Classical in
/-- The target Boolean-cube sum
`Z = ∑ x : ι → Bool, ∏ f ∈ s, Φ_f((x (varOf f v))_v)` (equation (3.1) of `[OpenAI2026ETH]`). -/
def targetSum [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (varOf : ∀ f, κ f → ι) : A :=
  ∑ x : ι → Bool, ∏ f ∈ s,
    MvPolynomial.eval (fun v => bitVal A (x (varOf f v))) (Φ f)

@[simp]
theorem targetSum_empty [Fintype ι]
    (Φ : ∀ f, MvPolynomial (κ f) A) (varOf : ∀ f, κ f → ι) :
    targetSum (∅ : Finset F) Φ varOf = (2 : A) ^ Fintype.card ι := by
  classical
  simp only [targetSum, prod_empty, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]

/-- When a replacement row `row : ι → Polynomial A` evaluates at `t` to the Kronecker delta at
`v₀ : ι`, the scalar baseline `∑ i, (row i).eval t * bitVal A (x i)` equals `bitVal A (x v₀)`. -/
theorem sum_eval_mul_bitVal_eq_of_eq_ite [Fintype ι] [DecidableEq ι]
    {row : ι → Polynomial A} {t : A} {v₀ : ι}
    (hrow : ∀ i : ι, (row i).eval t = if i = v₀ then 1 else 0) (x : ι → Bool) :
    (∑ i : ι, (row i).eval t * bitVal A (x i)) = bitVal A (x v₀) := by
  simp only [hrow, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]

/-- **Restoration at `T = 0` (equation (3.3), p. 21):**
If every replacement entry `P f v i` evaluates at `0` to `if i = varOf f v then 1 else 0`, then
evaluating `replacedSum s Φ P` at `0` recovers `targetSum s Φ varOf` (`H(0) = Z`). -/
theorem eval_zero_replacedSum_eq_targetSum [Fintype ι] [DecidableEq ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) (varOf : ∀ f, κ f → ι)
    (hP0 : ∀ f ∈ s, ∀ (v : κ f) (i : ι),
      (P f v i).eval 0 = if i = varOf f v then 1 else 0) :
    (replacedSum s Φ P).eval 0 = targetSum s Φ varOf := by
  rw [eval_replacedSum, targetSum]
  refine sum_congr rfl fun x _ => prod_congr rfl fun f hf => ?_
  have hfun : (fun v => ∑ i : ι, (P f v i).eval 0 * bitVal A (x i)) =
      fun v => bitVal A (x (varOf f v)) := by
    funext v
    exact sum_eval_mul_bitVal_eq_of_eq_ite (hP0 f hf v) x
  rw [hfun]

/-- If every entry of a replacement row `row : ι → Polynomial A` has `natDegree ≤ R`, then its
Boolean linear combination `∑ i, row i * C (bitVal A (x i))` has `natDegree ≤ R`. -/
theorem natDegree_sum_mul_C_bitVal_le [Fintype ι]
    {row : ι → Polynomial A} {R : ℕ} (hdeg : ∀ i : ι, (row i).natDegree ≤ R) (x : ι → Bool) :
    (∑ i : ι, row i * Polynomial.C (bitVal A (x i))).natDegree ≤ R := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (Polynomial.natDegree_mul_C_le (row i) (bitVal A (x i))).trans (hdeg i)

/-- Substituting univariate polynomials `q : σ → Polynomial A` of `natDegree ≤ R` into a
multivariate polynomial `Φ : MvPolynomial σ A` yields a univariate polynomial of `natDegree` at
most `Φ.totalDegree * R`. -/
theorem natDegree_aeval_polynomial_le {σ : Type*}
    (Φ : MvPolynomial σ A) {q : σ → Polynomial A} {R : ℕ}
    (hq : ∀ v : σ, (q v).natDegree ≤ R) :
    (MvPolynomial.aeval q Φ).natDegree ≤ Φ.totalDegree * R := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  have hC :
      (Polynomial.C (Φ.coeff m) * ∏ v ∈ m.support, q v ^ m v).natDegree ≤
        (∏ v ∈ m.support, q v ^ m v).natDegree :=
    Polynomial.natDegree_C_mul_le (Φ.coeff m) (∏ v ∈ m.support, q v ^ m v)
  refine hC.trans ?_
  have hprod :
      (∏ v ∈ m.support, q v ^ m v).natDegree ≤ ∑ v ∈ m.support, (q v ^ m v).natDegree :=
    Polynomial.natDegree_prod_le m.support (fun v => q v ^ m v)
  refine hprod.trans ?_
  have hpow : ∑ v ∈ m.support, (q v ^ m v).natDegree ≤ ∑ v ∈ m.support, m v * R := by
    refine sum_le_sum fun v _ => ?_
    exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (m v) (hq v))
  refine hpow.trans ?_
  rw [← sum_mul]
  exact Nat.mul_le_mul_right R (MvPolynomial.le_totalDegree hm)

/-- **Univariate degree bound on `replacedSum` (equations (3.2)–(3.3), p. 21):**
If every replacement entry `P f v i` has `natDegree ≤ R`, then `replacedSum s Φ P` has `natDegree`
at most `(∑ f ∈ s, (Φ f).totalDegree) * R`. -/
theorem natDegree_replacedSum_le [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    {R : ℕ} (hP : ∀ f ∈ s, ∀ (v : κ f) (i : ι), (P f v i).natDegree ≤ R) :
    (replacedSum s Φ P).natDegree ≤ (∑ f ∈ s, (Φ f).totalDegree) * R := by
  classical
  rw [replacedSum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  refine (Polynomial.natDegree_prod_le s _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun f hf => ?_
  exact natDegree_aeval_polynomial_le (Φ f) fun v =>
    natDegree_sum_mul_C_bitVal_le (hP f hf v) x

/-- When `∑ f ∈ s, (Φ f).totalDegree ≤ d` and every replacement entry has `natDegree ≤ R`,
`replacedSum s Φ P` has `natDegree ≤ d * R`. -/
theorem natDegree_replacedSum_le_of_sum_totalDegree_le [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    {d R : ℕ} (hd : ∑ f ∈ s, (Φ f).totalDegree ≤ d)
    (hP : ∀ f ∈ s, ∀ (v : κ f) (i : ι), (P f v i).natDegree ≤ R) :
    (replacedSum s Φ P).natDegree ≤ d * R :=
  (natDegree_replacedSum_le s Φ P hP).trans (Nat.mul_le_mul_right R hd)

/-- **Hermite degree condition for `replacedSum` (equation (3.5), p. 24):**
When `∑ f ∈ s, (Φ f).totalDegree ≤ d`, every replacement entry has `natDegree ≤ R`, and
`d * R < Q * J`, the polynomial `replacedSum s Φ P` has `degree < ↑(Q * J)`. -/
theorem degree_replacedSum_lt_of_sum_totalDegree_le [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    {d R Q J : ℕ} (hd : ∑ f ∈ s, (Φ f).totalDegree ≤ d)
    (hP : ∀ f ∈ s, ∀ (v : κ f) (i : ι), (P f v i).natDegree ≤ R)
    (hQJ : d * R < Q * J) :
    (replacedSum s Φ P).degree < ↑(Q * J) := by
  refine Polynomial.degree_le_natDegree.trans_lt ?_
  exact WithBot.coe_lt_coe.mpr
    ((natDegree_replacedSum_le_of_sum_totalDegree_le s Φ P hd hP).trans_lt hQJ)

/-! ### Part 2: Variable group partition, grouped factors, and `SharedSummaries` (§3.2–3.4) -/

/-- The subtype of variable coordinates assigned to group `g : G` under `varGroupOf : ι → G`. -/
abbrev GroupCoord (varGroupOf : ι → G) (g : G) : Type _ :=
  {i : ι // varGroupOf i = g}

/-- Reassembling a family of per-group assignments `x : ∀ g : G, GroupCoord varGroupOf g → α` into
a global assignment `ι → α`. -/
def groupReassemble (varGroupOf : ι → G) {α : Type*}
    (x : ∀ g : G, GroupCoord varGroupOf g → α) : ι → α :=
  fun i => x (varGroupOf i) ⟨i, rfl⟩

/-- Restricting a global assignment `x : ι → α` to the coordinates of group `g : G`. -/
def groupRestrict (varGroupOf : ι → G) {α : Type*}
    (x : ι → α) (g : G) : GroupCoord varGroupOf g → α :=
  fun i => x i.1

@[simp]
theorem groupReassemble_groupRestrict (varGroupOf : ι → G) {α : Type*} (x : ι → α) :
    groupReassemble varGroupOf (groupRestrict varGroupOf x) = x :=
  rfl

@[simp]
theorem groupRestrict_groupReassemble (varGroupOf : ι → G) {α : Type*}
    (x : ∀ g : G, GroupCoord varGroupOf g → α) :
    groupRestrict varGroupOf (groupReassemble varGroupOf x) = x := by
  ext g ⟨i, hi⟩
  subst hi
  rfl

/-- Equivalence between per-group assignments `∀ g : G, GroupCoord varGroupOf g → α` and global
assignments `ι → α`. -/
def groupSplitEquiv (varGroupOf : ι → G) (α : Type*) :
    (∀ g : G, GroupCoord varGroupOf g → α) ≃ (ι → α) where
  toFun := groupReassemble varGroupOf
  invFun := groupRestrict varGroupOf
  left_inv := groupRestrict_groupReassemble varGroupOf
  right_inv := groupReassemble_groupRestrict varGroupOf

/-- Extending a local vector `δ : GroupCoord varGroupOf h → A` on group `h` by zero outside
group `h` ($\tilde{\xi}$ in Definition 3.1 (4), p. 22). -/
def extendGroupVec [DecidableEq G] (varGroupOf : ι → G) (h : G)
    (δ : GroupCoord varGroupOf h → A) : ι → A :=
  fun i => if hi : varGroupOf i = h then δ ⟨i, hi⟩ else 0

@[simp]
theorem extendGroupVec_of_eq [DecidableEq G] (varGroupOf : ι → G) {h : G}
    (δ : GroupCoord varGroupOf h → A) {i : ι} (hi : varGroupOf i = h) :
    extendGroupVec varGroupOf h δ i = δ ⟨i, hi⟩ := by
  simp only [extendGroupVec, hi, ↓reduceDIte]

@[simp]
theorem extendGroupVec_of_ne [DecidableEq G] (varGroupOf : ι → G) {h : G}
    (δ : GroupCoord varGroupOf h → A) {i : ι} (hi : varGroupOf i ≠ h) :
    extendGroupVec varGroupOf h δ i = 0 := by
  simp only [extendGroupVec, hi, ↓reduceDIte]

/-- Reassembling `x + Pi.single h δ` adds the zero-extended vector
`extendGroupVec varGroupOf h δ`. -/
theorem groupReassemble_add_single_eq [DecidableEq G] (varGroupOf : ι → G)
    (x : ∀ g : G, GroupCoord varGroupOf g → A) (h : G) (δ : GroupCoord varGroupOf h → A) :
    groupReassemble varGroupOf (x + Pi.single h δ) =
      groupReassemble varGroupOf x + extendGroupVec varGroupOf h δ := by
  funext i
  simp only [groupReassemble, Pi.add_apply, extendGroupVec]
  by_cases hi : varGroupOf i = h
  · subst hi
    simp only [Pi.single_eq_same, ↓reduceDIte]
  · simp only [Pi.single_eq_of_ne hi, Pi.zero_apply, hi, ↓reduceDIte]

/-- Factor `Φ` evaluated at the affine-Taylor input with formal variables fixed to the indicator
of `U ⊆ ι` ($\Phi_{f, U}(x; z)$ in Section 3.4, p. 25). -/
def evalAffineFactor [Fintype ι] [DecidableEq ι] {σ : Type*}
    (Φ : MvPolynomial σ A) (rows : σ → ι → Polynomial A)
    (t : A) (U : Finset ι) (x : ι → Bool) : Polynomial A :=
  (affineFactor Φ rows t x).map (MvPolynomial.eval fun i => bitVal A (decide (i ∈ U)))

/-- The product of evaluated affine factors assigned to group `g : G` at node `t`
($A_{g, U}(x; z) = \prod_{f \in s : \sigma_f(t) = g} \Phi_{f, U}(x; z)$, equation (3.11) of
`[OpenAI2026ETH]`, p. 25). -/
def groupFactorProduct [Fintype ι] [DecidableEq ι] [DecidableEq G]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (factorGroupOf : F → G) (t : A) (U : Finset ι) (g : G) (x : ι → Bool) : Polynomial A :=
  ∏ f ∈ s.filter (fun f => factorGroupOf f = g), evalAffineFactor (Φ f) (P f) t U x

/-- **Equation (3.11) group product factorization (p. 25):**
Multiplying `groupFactorProduct` across all groups `g : G` recovers the evaluated full factor
product `G_x(1_U, z)`. -/
theorem prod_groupFactorProduct_eq_map_eval_factorProduct
    [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (factorGroupOf : F → G) (t : A) (U : Finset ι) (x : ι → Bool) :
    ∏ g : G, groupFactorProduct s Φ P factorGroupOf t U g x =
      (factorProduct s Φ P t x).map (MvPolynomial.eval fun i => bitVal A (decide (i ∈ U))) := by
  unfold groupFactorProduct evalAffineFactor factorProduct
  rw [Polynomial.map_prod]
  exact prod_fiberwise_of_maps_to (fun f _ => mem_univ (factorGroupOf f)) _

/-- `evalAffineFactor` depends on the Boolean assignment `x` only through the scalar baselines of
its rows at node `t`. -/
theorem evalAffineFactor_congr_baseline [Fintype ι] [DecidableEq ι] {σ : Type*}
    (Φ : MvPolynomial σ A) {rows : σ → ι → Polynomial A} {t : A} (U : Finset ι)
    {x x' : ι → Bool}
    (h : ∀ v : σ, ∑ i : ι, (rows v i).eval t * bitVal A (x i) =
      ∑ i : ι, (rows v i).eval t * bitVal A (x' i)) :
    evalAffineFactor Φ rows t U x = evalAffineFactor Φ rows t U x' := by
  unfold evalAffineFactor
  rw [affineFactor_congr_baseline Φ h]

/-- `groupFactorProduct` depends on `x` only through the scalar baselines at node `t` of the
factors assigned to group `g`. -/
theorem groupFactorProduct_congr_baseline [Fintype ι] [DecidableEq ι] [DecidableEq G]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) {P : ∀ f, κ f → ι → Polynomial A}
    (factorGroupOf : F → G) {t : A} (U : Finset ι) (g : G) {x x' : ι → Bool}
    (h : ∀ f ∈ s, factorGroupOf f = g → ∀ v : κ f,
      ∑ i : ι, (P f v i).eval t * bitVal A (x i) =
        ∑ i : ι, (P f v i).eval t * bitVal A (x' i)) :
    groupFactorProduct s Φ P factorGroupOf t U g x =
      groupFactorProduct s Φ P factorGroupOf t U g x' := by
  unfold groupFactorProduct
  refine prod_congr rfl fun f hf => ?_
  rw [mem_filter] at hf
  exact evalAffineFactor_congr_baseline (Φ f) U (h f hf.1 hf.2)

/-- The set of local Boolean assignments on group `g` whose coordinates in `E` are fixed to `true`
(Lemma 3.2, p. 23). -/
def localAllowed [Fintype ι] [DecidableEq ι] [DecidableEq G]
    (varGroupOf : ι → G) (E : Finset ι) (g : G) :
    Finset (GroupCoord varGroupOf g → Bool) :=
  univ.filter fun u => ∀ i : GroupCoord varGroupOf g, i.1 ∈ E → u i = true

/-- A tuple of local assignments belongs to `Fintype.piFinset (localAllowed varGroupOf E)` iff its
reassembled global assignment is `true` on every coordinate of `E`. -/
theorem mem_piFinset_localAllowed_iff [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    (varGroupOf : ι → G) (E : Finset ι) (x : ∀ g : G, GroupCoord varGroupOf g → Bool) :
    x ∈ Fintype.piFinset (localAllowed varGroupOf E) ↔
      ∀ i ∈ E, groupReassemble varGroupOf x i = true := by
  rw [Fintype.mem_piFinset]
  simp only [localAllowed, mem_filter, mem_univ, true_and, groupReassemble]
  constructor
  · intro h i hiE
    exact h (varGroupOf i) ⟨i, rfl⟩ hiE
  · intro h g ⟨i, hi⟩ hiE
    subst hi
    exact h i hiE

/-- Summing over the restricted global Boolean cube `{x : ι → Bool | ∀ i ∈ E, x i = true}` equals
summing over the product of per-group restricted cubes
`Fintype.piFinset (localAllowed varGroupOf E)`. -/
theorem sum_filter_cube_eq_sum_piFinset_localAllowed {B : Type*} [AddCommMonoid B]
    [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    (varGroupOf : ι → G) (E : Finset ι) (f : (ι → Bool) → B) :
    (∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true), f x) =
      ∑ x ∈ Fintype.piFinset (localAllowed varGroupOf E), f (groupReassemble varGroupOf x) := by
  refine sum_nbij' (groupRestrict varGroupOf) (groupReassemble varGroupOf) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter] at hx
    rw [mem_piFinset_localAllowed_iff, groupReassemble_groupRestrict]
    exact hx.2
  · intro x hx
    rw [mem_filter]
    exact ⟨mem_univ _, (mem_piFinset_localAllowed_iff varGroupOf E x).mp hx⟩
  · intro x _
    exact groupReassemble_groupRestrict varGroupOf x
  · intro x _
    exact groupRestrict_groupReassemble varGroupOf x
  · intro _ _
    rfl

/-- **Restricted sum factorization through `SharedSummaries` (Lemma 3.2 & eqs. 3.4, 3.11–3.13,
pp. 23–25):**
When the grouped factor products `groupFactorProduct` are measurement-fiber local on the variable
groups, the restricted sum $Z_{t, E, U}(z) = \sum_{x|_E = 1} G_x(\mathbf{1}_U, z)$ equals the sum
of `SharedSummaries.fiberContribution` over the measurement box. -/
theorem sum_restricted_factorProduct_eq_sum_measurement_fibers
    [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {Y : G → Type*} [∀ g, DecidableEq (Y g)]
    (varGroupOf : ι → G) (factorGroupOf : F → G)
    (measure : ∀ g, (GroupCoord varGroupOf g → Bool) → Y g)
    (box : ∀ g, Finset (Y g)) (covers : ∀ g u, measure g u ∈ box g)
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (E U : Finset ι)
    (locality : ∀ g x x', (∀ h, measure h (x h) = measure h (x' h)) → x g = x' g →
      groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x) =
        groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x'))
    (representative :
      ∀ y : (∀ g, Y g), (∀ g, ∃ u, measure g u = y g) → ∀ g, GroupCoord varGroupOf g → Bool)
    (valid : ∀ y hy g, measure g (representative y hy g) = y g) :
    (∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
        (factorProduct s Φ P t x).map (MvPolynomial.eval fun i => bitVal A (decide (i ∈ U)))) =
      ∑ y ∈ Fintype.piFinset box,
        fiberContribution measure (localAllowed varGroupOf E)
          (fun g x => groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x))
          representative y := by
  rw [sum_filter_cube_eq_sum_piFinset_localAllowed varGroupOf E]
  simp_rw [← prod_groupFactorProduct_eq_map_eval_factorProduct s Φ P factorGroupOf t U]
  exact sum_prod_eq_sum_measurement_fibers measure box covers (localAllowed varGroupOf E)
    (fun g x => groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x))
    locality representative valid

/-- **Equation (3.13) Taylor jet coefficient via `SharedSummaries` (p. 25):**
For every order `j ≤ q`, `[z^j] H(t + z)` equals the signed Möbius sum over pairs `(E, U)` with
`#E ≤ q` and `U ⊆ E` of the `[z^j]`-coefficients of the `SharedSummaries.fiberContribution` sums. -/
theorem coeff_taylor_replacedSum_eq_sum_measurement_fibers
    [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {Y : G → Type*} [∀ g, DecidableEq (Y g)]
    (varGroupOf : ι → G) (factorGroupOf : F → G)
    (measure : ∀ g, (GroupCoord varGroupOf g → Bool) → Y g)
    (box : ∀ g, Finset (Y g)) (covers : ∀ g u, measure g u ∈ box g)
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) {j q : ℕ} (hj : j ≤ q)
    (locality : ∀ U ∈ (univ : Finset ι).powerset, ∀ g x x',
      (∀ h, measure h (x h) = measure h (x' h)) → x g = x' g →
      groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x) =
        groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x'))
    (representative :
      ∀ y : (∀ g, Y g), (∀ g, ∃ u, measure g u = y g) → ∀ g, GroupCoord varGroupOf g → Bool)
    (valid : ∀ y hy g, measure g (representative y hy g) = y g) :
    (Polynomial.taylor t (replacedSum s Φ P)).coeff j =
      ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) *
          (∑ y ∈ Fintype.piFinset box,
            fiberContribution measure (localAllowed varGroupOf E)
              (fun g x =>
                groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x))
              representative y).coeff j := by
  rw [coeff_taylor_replacedSum_eq_restricted_subsets s Φ P t hj]
  refine sum_congr rfl fun E _ => sum_congr rfl fun U _ => ?_
  congr 1
  have hsum := sum_restricted_factorProduct_eq_sum_measurement_fibers varGroupOf factorGroupOf
    measure box covers s Φ P t E U (locality U (mem_powerset.mpr (subset_univ U)))
    representative valid
  have hcoeff := congrArg (fun p : Polynomial A => p.coeff j) hsum
  rw [Polynomial.finsetSum_coeff] at hcoeff
  refine Eq.trans ?_ hcoeff
  refine sum_congr (by ext x; simp only [mem_filter, mem_univ, true_and]) fun x _ => ?_
  rw [Polynomial.coeff_map]
  congr 2
  funext i
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

/-- **Kernel-shift invariance implies `groupFactorProduct` fiber locality (Definition 3.1 (4) &
Lemma 3.2, pp. 22–23):**
When the linear measurements `measure h : (GroupCoord varGroupOf h → ℚ) →ₗ[ℚ] W h` annihilate
off-group shifts in the scalar baselines of every factor assigned to `g` at node `t`,
`groupFactorProduct` is measurement-fiber local on the Boolean groups. -/
theorem groupFactorProduct_locality_of_kernel_shifts
    [Algebra ℚ A] [Fintype ι] [DecidableEq ι] [Finite G] [DecidableEq G]
    {W : G → Type*} [∀ g, AddCommGroup (W g)] [∀ g, Module ℚ (W g)]
    (varGroupOf : ι → G) (factorGroupOf : F → G)
    (measure : ∀ g, (GroupCoord varGroupOf g → ℚ) →ₗ[ℚ] W g)
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (U : Finset ι)
    (rowQ : ∀ f, κ f → ι → ℚ)
    (hrow : ∀ f ∈ s, ∀ v i, (P f v i).eval t = algebraMap ℚ A (rowQ f v i))
    (hker : ∀ f ∈ s, ∀ (v : κ f) (h : G), h ≠ factorGroupOf f →
      ∀ δ : GroupCoord varGroupOf h → ℚ, measure h δ = 0 →
        ∑ i : ι, rowQ f v i * extendGroupVec varGroupOf h δ i = 0)
    (g : G) (x x' : ∀ h : G, GroupCoord varGroupOf h → Bool)
    (sameMeasurements : ∀ h,
      measure h (fun i => bitVal ℚ (x h i)) = measure h (fun i => bitVal ℚ (x' h i)))
    (sameCoordinate : x g = x' g) :
    groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x) =
      groupFactorProduct s Φ P factorGroupOf t U g (groupReassemble varGroupOf x') := by
  cases nonempty_fintype G
  refine groupFactorProduct_congr_baseline s Φ factorGroupOf U g fun f hfs hfg v => ?_
  have hshift : ∀ g' h : G, h ≠ g' →
      ∀ (y : ∀ k, GroupCoord varGroupOf k → ℚ) (δ : GroupCoord varGroupOf h → ℚ),
        measure h δ = 0 →
        (if g' = factorGroupOf f then
          ∑ i : ι, rowQ f v i * groupReassemble varGroupOf (y + Pi.single h δ) i
        else 0) =
        (if g' = factorGroupOf f then
          ∑ i : ι, rowQ f v i * groupReassemble varGroupOf y i
        else 0) := by
    intro g' h hne y δ hδ
    split_ifs with hg'
    · subst hg'
      rw [groupReassemble_add_single_eq]
      simp only [Pi.add_apply, mul_add, sum_add_distrib]
      rw [hker f hfs v h hne δ hδ, add_zero]
    · rfl
  have hloc := fiber_locality_of_kernel_shifts (A := ℚ) measure
    (fun g' (y : ∀ k, GroupCoord varGroupOf k → ℚ) =>
      if g' = factorGroupOf f then ∑ i : ι, rowQ f v i * groupReassemble varGroupOf y i else 0)
    hshift g (fun h i => bitVal ℚ (x h i)) (fun h i => bitVal ℚ (x' h i))
    sameMeasurements (by rw [sameCoordinate])
  simp only [hfg, ↓reduceIte] at hloc
  have hcast := congrArg (algebraMap ℚ A) hloc
  simp only [map_sum, map_mul] at hcast
  have hbit (y : ∀ k, GroupCoord varGroupOf k → Bool) (i : ι) :
      algebraMap ℚ A (groupReassemble varGroupOf (fun h j => bitVal ℚ (y h j)) i) =
        bitVal A (groupReassemble varGroupOf y i) := by
    dsimp only [groupReassemble, bitVal]
    cases y (varGroupOf i) ⟨i, rfl⟩ <;> simp
  simp_rw [hbit, ← hrow f hfs v] at hcast
  exact hcast

open Classical in
/-- The finite box of integer measurement vectors `y : ρ → ℤ` with every coordinate in
`[-D, D]` (Section 3.3, p. 23). -/
def intMeasurementBox (ρ : Type*) [Fintype ρ] (D : ℕ) : Finset (ρ → ℤ) :=
  Fintype.piFinset fun _ : ρ => Icc (-(D : ℤ)) (D : ℤ)

/-- The integer measurement box `[-D, D]^ρ` has cardinality `(2 * D + 1) ^ |ρ|` (Section 3.3,
p. 23). -/
theorem card_intMeasurementBox (ρ : Type*) [Fintype ρ] (D : ℕ) :
    #(intMeasurementBox ρ D) = (2 * D + 1) ^ Fintype.card ρ := by
  classical
  rw [intMeasurementBox, Fintype.card_piFinset, prod_const, card_univ, Int.card_Icc]
  congr 1
  omega

/-- Every Boolean vector `u : σ → Bool` multiplied by an integer matrix `C : Matrix ρ σ ℤ` whose
rows have `ℓ₁`-norm at most `D` lands in `intMeasurementBox ρ D` (Section 3.2–3.3, pp. 22–23). -/
theorem mulVec_bitVal_mem_intMeasurementBox {ρ σ : Type*} [Fintype ρ] [Fintype σ]
    (C : Matrix ρ σ ℤ) {D : ℕ} (hC : ∀ r : ρ, (∑ j : σ, |C r j|) ≤ (D : ℤ))
    (u : σ → Bool) :
    C.mulVec (fun j => bitVal ℤ (u j)) ∈ intMeasurementBox ρ D := by
  classical
  rw [intMeasurementBox, Fintype.mem_piFinset]
  intro r
  rw [mem_Icc, ← abs_le]
  calc
    |C.mulVec (fun j => bitVal ℤ (u j)) r|
      = |∑ j : σ, C r j * bitVal ℤ (u j)| := rfl
    _ ≤ ∑ j : σ, |C r j * bitVal ℤ (u j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : σ, |C r j| := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        cases u j <;> simp [bitVal]
    _ ≤ (D : ℤ) := hC r

/-! ### Part 3: Hermite–Taylor target-sum synthesis (§3.4 & Proposition 3.4, pp. 24–25) -/

/-- **Proposition 3.4 target-sum recovery via Hermite interpolation (pp. 24–25):**
Over a commutative `ℚ`-algebra `A`, when the replacement rows restore variables at `T = 0`, have
`natDegree ≤ R`, and `d * R < Q * J` (`∑ f ∈ s, (Φ f).totalDegree ≤ d`), the target sum
`targetSum s Φ varOf` is recovered at `0` by confluent Hermite interpolation from the order-`J`
Taylor jet of `replacedSum s Φ P` at any `Q` distinct integer nodes `t : Fin Q → ℤ`. -/
theorem targetSum_eq_of_taylorJet [Algebra ℚ A] [Fintype ι] [DecidableEq ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) (varOf : ∀ f, κ f → ι)
    {d R Q J : ℕ} {t : Fin Q → ℤ} (ht : Function.Injective t) (hQ : 0 < Q) (hJ : 0 < J)
    (hP0 : ∀ f ∈ s, ∀ (v : κ f) (i : ι),
      (P f v i).eval 0 = if i = varOf f v then 1 else 0)
    (hd : ∑ f ∈ s, (Φ f).totalDegree ≤ d)
    (hP : ∀ f ∈ s, ∀ (v : κ f) (i : ι), (P f v i).natDegree ≤ R)
    (hQJ : d * R < Q * J) :
    targetSum s Φ varOf = ((hermiteMatrix t J).det : ℚ)⁻¹ •
      (((hermiteMatrix t J).map (Int.cast : ℤ → A)).updateCol (⟨0, hQ⟩, ⟨0, hJ⟩)
        (taylorJet (fun i => (t i : A)) J (replacedSum s Φ P))).det := by
  rw [← eval_zero_replacedSum_eq_targetSum s Φ P varOf hP0]
  exact eval_zero_eq_of_taylorJet A ht hQ hJ
    (degree_replacedSum_lt_of_sum_totalDegree_le s Φ P hd hP hQJ)

/-! ### Part 4: Subset-pair count `C_q` and weighted binomial bound (§3.5 eqs. 3.14–3.15, p. 25) -/

/-- The number of subset pairs `(E, U)` with `U ⊆ E ⊆ [n]` and `|E| ≤ q`:
$$C_q(n) = \sum_{s = 0}^{\min(q, n)} \binom{n}{s} 2^s$$
(equation (3.14) of `[OpenAI2026ETH]`, p. 25). -/
def subsetPairCount (q n : ℕ) : ℕ :=
  ∑ s ∈ range (min q n + 1), n.choose s * 2 ^ s

open Classical in
/-- **Equation (3.14) subset-pair cardinality identity (p. 25):**
On a `Fintype ι`, the total number of pairs `(E, U)` with `E ⊆ univ`, `#E ≤ q`, and `U ⊆ E`
equals `subsetPairCount q (Fintype.card ι)`. -/
theorem sum_card_powerset_filter_card_le_eq_subsetPairCount [Fintype ι] (q : ℕ) :
    (∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q), #(E.powerset)) =
      subsetPairCount q (Fintype.card ι) := by
  unfold subsetPairCount
  have hmaps : ∀ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
      #E ∈ range (min q (Fintype.card ι) + 1) := by
    intro E hE
    rw [mem_filter] at hE
    rw [mem_range, Nat.lt_succ_iff, le_min_iff]
    exact ⟨hE.2, card_le_univ E⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_range, Nat.lt_succ_iff, le_min_iff] at hs
  have hfib :
      ((univ : Finset ι).powerset.filter (fun E => #E ≤ q)).filter (fun E => #E = s) =
        powersetCard s (univ : Finset ι) := by
    ext E
    simp only [mem_filter, mem_powerset, mem_powersetCard, subset_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hs.1, h⟩⟩
  rw [hfib]
  have hconst : ∀ E ∈ powersetCard s (univ : Finset ι), #(E.powerset) = 2 ^ s := by
    intro E hE
    rw [card_powerset, (mem_powersetCard.mp hE).2]
  rw [sum_congr rfl hconst, sum_const, card_powersetCard, card_univ, smul_eq_mul]

/-- At `q = 0`, `C_0(n) = 1` (Section 3.5, p. 25). -/
@[simp]
theorem subsetPairCount_zero_left (n : ℕ) : subsetPairCount 0 n = 1 := by
  simp [subsetPairCount]

/-- When `n ≤ q`, `C_q(n) = 3 ^ n` (Section 3.5, p. 25). -/
theorem subsetPairCount_of_le {q n : ℕ} (hq : n ≤ q) : subsetPairCount q n = 3 ^ n := by
  calc
    subsetPairCount q n = ∑ s ∈ range (n + 1), 2 ^ s * 1 ^ (n - s) * n.choose s := by
      rw [subsetPairCount, Nat.min_eq_right hq]
      refine sum_congr rfl fun s _ => by ring
    _ = (2 + 1) ^ n := (add_pow 2 1 n).symm
    _ = 3 ^ n := by norm_num

/-- **Equation (3.15) weighted binomial bound (p. 25):**
For any `0 ≤ η ≤ 1` in a linearly ordered commutative ring `R`,
$$\eta^q C_q(n) \le \sum_{s = 0}^n \binom{n}{s} (2\eta)^s = (1 + 2\eta)^n.$$ -/
theorem pow_mul_subsetPairCount_le {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (q n : ℕ) {η : R} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    η ^ q * (subsetPairCount q n : R) ≤ (1 + 2 * η) ^ n := by
  rw [subsetPairCount, Nat.cast_sum, mul_sum]
  have hle₁ :
      (∑ s ∈ range (min q n + 1), η ^ q * ((n.choose s * 2 ^ s : ℕ) : R)) ≤
        ∑ s ∈ range (min q n + 1), (n.choose s : R) * (2 * η) ^ s := by
    refine sum_le_sum fun s hs => ?_
    rw [mem_range, Nat.lt_succ_iff, le_min_iff] at hs
    have hpow : η ^ q ≤ η ^ s := pow_le_pow_of_le_one hη0 hη1 hs.1
    have hnonneg : (0 : R) ≤ ((n.choose s * 2 ^ s : ℕ) : R) := Nat.cast_nonneg _
    calc
      η ^ q * ((n.choose s * 2 ^ s : ℕ) : R)
        ≤ η ^ s * ((n.choose s * 2 ^ s : ℕ) : R) := mul_le_mul_of_nonneg_right hpow hnonneg
      _ = (n.choose s : R) * (2 * η) ^ s := by
        push_cast
        rw [mul_pow]
        ring
  have hsub : range (min q n + 1) ⊆ range (n + 1) :=
    range_mono (Nat.succ_le_succ (min_le_right q n))
  have hle₂ :
      (∑ s ∈ range (min q n + 1), (n.choose s : R) * (2 * η) ^ s) ≤
        ∑ s ∈ range (n + 1), (n.choose s : R) * (2 * η) ^ s := by
    refine sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) s)
  have hbinom :
      (∑ s ∈ range (n + 1), (n.choose s : R) * (2 * η) ^ s) = (1 + 2 * η) ^ n := by
    rw [add_comm (1 : R) (2 * η), add_pow]
    refine sum_congr rfl fun s _ => ?_
    ring
  exact (hle₁.trans hle₂).trans_eq hbinom

end Cslib.AffineTaylor
