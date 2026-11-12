/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import CslibFrontier.Crypto.Protocols.PIR.Collusion
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Product
import CslibFrontier.Foundations.Data.Nat.Clog
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform

/-!
# Polynomial Shamir `t`-private information retrieval

[Chor, Goldreich, Kushilevitz and Sudan, Section 1.1, pp. 1–2, and Section 2.2,
pp. 4–5][ChorGoldreichKushilevitzSudan1998] note that polynomial-interpolation PIR extends to
coalitions of up to `t` colluding servers (`t < k`): in the headline summary of Section 1.1 (whose
construction was omitted from the April 21, 1998 journal version and referred back to the FOCS 1995
preliminary version), for an integer function `t(n)` and integer constant `c > 1`, they state a
`t(n)`-private scheme for `c · t(n)` servers with communication `O(t(n) · n ^ (1 / c))`.

This module formalizes an explicit finite-field polynomial construction built on Shamir secret
sharing ([Shamir][Shamir1979]; `Cslib.Crypto.Protocols.SecretSharing.Shamir`):

* **Linear Shamir PIR (`PIR.shamir`).** Over any finite field `F` with `Shamir.Params F S`
  (`params.threshold = t < |S|` distinct nonzero evaluation points, so `|F| > |S|`), the user
  shares the standard basis indicator `eᵢ : ι → F` entrywise with independent degree-`t` Shamir
  sharings, each server returns the linear inner product `∑ j, x j * q s j` in `F`, and the user
  interpolates the constant term via `Shamir.Polynomial.reconstruct`. Applying the generic matrix
  balancing transformation `Scheme.rows`
  ([CGKS, Section 3.4, p. 11][ChorGoldreichKushilevitzSudan1998]) gives `(t + 1)`-server
  `t`-private PIR on `n ≤ m ^ 2` bits using `|S| * (2 m * ⌈log₂ |F|⌉)` bits
  (`hasTPrivateScheme_of_le_mul_self`).
* **Degree-`d` hypercube polynomial PIR (`PIR.shamirCube`).** Indexing the database by a cube
  `D → ι` (`d = |D|`), the user shares the `d` coordinate indicators independently with degree `t`,
  and each server evaluates `∑ j, x j * ∏ l, q s l (j l)`, a polynomial of degree at most `d * t`
  whose constant term is `1` if `x i = true` and `0` otherwise (`isCorrect_shamirCube` when
  `d * t < |S|`). Unauthorized coalitions of size `≤ t` see uniform coordinate tables
  (`eval_coalitionQuery_shamirCube`, proved from `Shamir.uniformOfFintype_map_restrict_share_pi`),
  yielding unbalanced `(d t + 1)`-server PIR (`hasTPrivateScheme_of_le_pow`) and, after applying
  `Scheme.rows (Fin ℓ)`, balanced `|S|`-server PIR communicating at most
  `|S| * ((d + 1) * ℓ * ⌈log₂ |F|⌉)` bits for `n ≤ ℓ ^ (d + 1)` when `d * t < |S|`
  (`hasTPrivateScheme_rows_of_le_pow`, instantiated over `ZMod p` for primes `p > k` via
  `zmodShamirParams` in `hasTPrivateScheme_prime_of_le_pow` and
  `hasTPrivateScheme_prime_rows_of_le_pow`).
* **Sharpness of the collusion threshold (`not_isTPrivate_succ_shamir`,
  `not_isTPrivate_succ_shamirCube`).** Any `t + 1` colluding servers are authorized in Shamir
  secret sharing and reconstruct coordinate indicators, breaking `(t + 1)`-privacy when `|ι| ≥ 2`
  (and `[Nonempty D]`, i.e. `d ≥ 1`, on the cube `D → ι`; when `D` is empty, `D → ι` is a singleton
  so privacy holds trivially).

## Source adaptation and model boundaries

* **Weaker finite-field communication variant:** at `d = c - 1` (`c ≥ 2`, `t ≥ 1`),
  `hasTPrivateScheme_rows_of_le_pow` and `hasTPrivateScheme_prime_rows_of_le_pow` match CGKS
  Section 1.1's exact server count `k = c · t` and fixed-`t` database exponent `n ^ (1 / c)`, but
  retain the field bit-width factor `⌈log₂ |F|⌉` with `|F| > c · t`. This is a weaker finite-field
  communication bound than CGKS Section 1.1's varying-`t(n)` `O(t(n) · n ^ (1 / c))` headline
  bound. The checked endpoints impose no upper bound on `|F|` in terms of `c · t`, so they do not
  replace the field factor by `log(c t)`.
* **Computation and randomness model:** CGKS Section 2.4 (p. 6) requires polynomial-time user and
  server computations over uniform bit strings `r ∈ {0, 1}^{ℓ_rnd}`. As in `PIR.Basic`, this module
  certifies exact `ProbComp` correctness, coalition privacy, and fixed-length communication bit
  counts without machine runtime bounds or fair-coin implementations of uniform sampling over `F`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.shamir`: linear Shamir `t`-private PIR over a finite field `F`.
* `Cslib.Crypto.Protocols.PIR.shamirCube`: degree-`d` polynomial `t`-private PIR on `D → ι`.
* `Cslib.Crypto.Protocols.PIR.zmodShamirParams`: canonical `Shamir.Params (ZMod p) (Fin k)` for
  `t < k < p` with `p` prime.

## Main results

* `Cslib.Crypto.Protocols.PIR.isCorrect_shamir`, `Cslib.Crypto.Protocols.PIR.isTPrivate_shamir`,
  `Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamir`: correctness, `t`-privacy, and `(t + 1)`
  threshold sharpness of `PIR.shamir`.
* `Cslib.Crypto.Protocols.PIR.isCorrect_shamirCube`,
  `Cslib.Crypto.Protocols.PIR.isTPrivate_shamirCube`,
  `Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamirCube`: correctness for `|D| * t < |S|`,
  `t`-privacy, and `(t + 1)` threshold sharpness (under `[Nonempty D]` and `[Nontrivial ι]`) of
  `PIR.shamirCube`.
* `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_mul_self`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_pow`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_rows_of_le_pow`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_of_le_pow`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_rows_of_le_pow`: communication bounds for
  matrix-balanced linear and unbalanced/`rows`-balanced degree-`d` polynomial `t`-private PIR.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 1.1, 2.2, 2.4 and 3.4 (pp. 1–2, 4–6 and
  11); numbering of the authors' journal version of April 21, 1998
* [A. Shamir, *How to Share a Secret*][Shamir1979]
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability
open Cslib.Crypto.Protocols.SecretSharing

section ShamirPIR

variable {F S : Type} [Field F] [Fintype F] [Fintype S]

/-- Linear Shamir `t`-private PIR over a finite field `F` ([Shamir1979]; adapting
[CGKS, Sections 1.1 and 2.2, pp. 1–2 and 4–5][ChorGoldreichKushilevitzSudan1998]): to read `x i`,
the user shares the indicator vector `j ↦ (if j = i then 1 else 0)` entrywise with independent
degree-`t` Shamir sharings, each server returns the field inner product with `x`, and the user
reconstructs at `0`. -/
noncomputable def shamir (ι : Type) [Fintype ι] [DecidableEq ι] (params : Shamir.Params F S) :
    Scheme ι S Unit (ι → F) F where
  query i := do
    let r ← ProbComp.uniform (ι → Shamir.Randomness params)
    pure ((), fun s j => Shamir.share params (r j) (if j = i then 1 else 0) s)
  answer _ x a := ∑ j : ι, if x j then a j else 0
  reconstruct _ _ ans :=
    open scoped Classical in decide (Shamir.Polynomial.reconstruct params.point ans = 1)

/-- Degree-`d` polynomial `t`-private PIR on the cube `D → ι` ([Shamir1979]; adapting
[CGKS, Sections 1.1 and 2.2, pp. 1–2 and 4–5][ChorGoldreichKushilevitzSudan1998]): the user shares
each coordinate indicator `u ↦ (if u = i l then 1 else 0)` with degree `t = params.threshold`, each
server returns `∑ j, x j * ∏ l, a l (j l)` in `F` (evaluating a polynomial of degree at most
`|D| * t` whose constant term is `x i`), and the user interpolates the constant term from the
`|S| > |D| * t` server answers. -/
noncomputable def shamirCube (D ι : Type) [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (params : Shamir.Params F S) : Scheme (D → ι) S Unit (D → ι → F) F where
  query i := do
    let r ← ProbComp.uniform (D → ι → Shamir.Randomness params)
    pure ((), fun s l u => Shamir.share params (r l u) (if u = i l then 1 else 0) s)
  answer _ x a := ∑ j : D → ι, if x j then ∏ l : D, a l (j l) else 0
  reconstruct _ _ ans :=
    open scoped Classical in decide (Shamir.Polynomial.reconstruct params.point ans = 1)

/-- Any coalition `T` of at most `params.threshold` servers in `PIR.shamir` sees a uniform family
of query vectors, independent of the queried index. -/
theorem eval_coalitionQuery_shamir {ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq S]
    (params : Shamir.Params F S) (T : Finset S) (hT : T.card ≤ params.threshold) (i : ι) :
    ProbComp.eval ((shamir ι params).coalitionQuery T i) = PMF.uniformOfFintype (T → ι → F) := by
  rw [Scheme.eval_coalitionQuery, shamir]
  simp only [pmf_norm, ProbComp.eval_uniform]
  exact Shamir.uniformOfFintype_map_restrict_share_pi params T hT
    (fun j => if j = i then 1 else 0)

/-- **Linear Shamir PIR is `t`-private** for `t = params.threshold`. -/
theorem isTPrivate_shamir {ι : Type} [Fintype ι] [DecidableEq ι] (params : Shamir.Params F S) :
    (shamir ι params).IsTPrivate params.threshold := by
  classical
  rw [Scheme.isTPrivate_iff]
  intro T hT i i'
  rw [eval_coalitionQuery_shamir params T hT i, eval_coalitionQuery_shamir params T hT i']

/-- **Linear Shamir PIR is perfectly correct**: Lagrange reconstruction at `0` recovers `1` when
`x i = true` and `0` when `x i = false`. -/
theorem isCorrect_shamir {ι : Type} [Fintype ι] [DecidableEq ι] (params : Shamir.Params F S) :
    (shamir ι params).IsCorrect := by
  classical
  rw [Scheme.isCorrect_iff]
  intro x i _ q hrq
  simp only [shamir, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨r, -, -, rfl⟩ := hrq
  let sec : ι → F := fun j => if x j then (if j = i then 1 else 0) else 0
  let coeff : ι → Shamir.Randomness params := fun j => if x j then r j else 0
  have hans :
      (fun s : S =>
        ∑ j : ι, if x j then Shamir.share params (r j) (if j = i then 1 else 0) s else 0) =
        fun s : S => Shamir.share params (∑ j : ι, coeff j) (∑ j : ι, sec j) s := by
    funext s
    rw [Shamir.share_sum Finset.univ params coeff sec s]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hxj : x j <;> simp [coeff, sec, hxj]
  dsimp only [shamir]
  rw [hans, Shamir.Polynomial.reconstruct_share_eq_secret params]
  have hsum : ∑ j : ι, sec j = if x i then 1 else 0 := by
    simp only [sec]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsum]
  cases x i <;> simp

omit [Fintype F] [Fintype S] in
private theorem ne_of_map_eq_pure_one_zero {α : Type} {p q : PMF α} (f : α → F)
    (hp : p.map f = PMF.pure 1) (hq : q.map f = PMF.pure 0) : p ≠ q := by
  intro heq
  rw [heq, hq] at hp
  have hsupp := congrArg PMF.support hp
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hsupp
  exact zero_ne_one hsupp

/-- **Sharpness of the collusion threshold**: `(params.threshold + 1)` servers are authorized in
Shamir secret sharing and can reconstruct the target index, so `PIR.shamir` is not
`(params.threshold + 1)`-private on any nontrivial database index type (`|ι| ≥ 2`). -/
theorem not_isTPrivate_succ_shamir {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (params : Shamir.Params F S) :
    ¬ (shamir ι params).IsTPrivate (params.threshold + 1) := by
  intro hpriv
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne ι
  obtain ⟨T, -, hcard⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt params.threshold_lt_card)
  have hT : Shamir.authorized params T := by rw [Shamir.authorized, hcard]
  have hrec (idx : ι) :
      (ProbComp.eval ((shamir ι params).coalitionQuery T idx)).map
          (fun (qT : T → ι → F) => Shamir.reconstruct params T (fun s => qT s i₀)) =
        PMF.pure (if i₀ = idx then (1 : F) else 0) := by
    rw [Scheme.eval_coalitionQuery, shamir, ProbComp.eval_bind]
    simp only [ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind, PMF.pure_map,
      Shamir.reconstruct_share_eq_secret params _ _ hT, PMF.bind_const]
  refine ne_of_map_eq_pure_one_zero
    (fun (qT : T → ι → F) => Shamir.reconstruct params T (fun s => qT s i₀))
    (by rw [hrec i₀, ite_eq_left rfl]) (by rw [hrec i₁, ite_eq_right hne])
    (hpriv.eval_coalitionQuery_eq T hcard.le i₀ i₁)

/-- Any coalition `T` of at most `params.threshold` servers in `PIR.shamirCube` sees uniform
coordinate query tables, independent of the target cube point. -/
theorem eval_coalitionQuery_shamirCube {D ι : Type} [Fintype D] [DecidableEq D]
    [Fintype ι] [DecidableEq ι] [DecidableEq S] (params : Shamir.Params F S)
    (T : Finset S) (hT : T.card ≤ params.threshold) (i : D → ι) :
    ProbComp.eval ((shamirCube D ι params).coalitionQuery T i) =
      PMF.uniformOfFintype (T → D → ι → F) := by
  rw [Scheme.eval_coalitionQuery, shamirCube]
  simp only [pmf_norm, ProbComp.eval_uniform]
  change (PMF.uniformOfFintype (D → ι → Shamir.Randomness params)).map
    (fun r (s : T) l u => Shamir.share params (r l u) (if u = i l then 1 else 0) s) = _
  let cur : ((D × ι) → Shamir.Randomness params) ≃ (D → ι → Shamir.Randomness params) :=
    Equiv.curry D ι (Shamir.Randomness params)
  let outCur : (T → (D × ι) → F) ≃ (T → D → ι → F) :=
    Equiv.arrowCongr (Equiv.refl T) (Equiv.curry D ι F)
  rw [← PMF.uniformOfFintype_map_equiv cur, PMF.map_comp]
  have hcomp :
      ((fun (r : D → ι → Shamir.Randomness params) (s : T) l u =>
          Shamir.share params (r l u) (if u = i l then 1 else 0) s) ∘ cur) =
        outCur ∘ (fun (r : (D × ι) → Shamir.Randomness params) (s : T) lu =>
          Shamir.share params (r lu) (if lu.2 = i lu.1 then 1 else 0) s) := rfl
  rw [hcomp, ← PMF.map_comp,
    Shamir.uniformOfFintype_map_restrict_share_pi params T hT
      (fun lu : D × ι => if lu.2 = i lu.1 then 1 else 0)]
  exact PMF.uniformOfFintype_map_equiv outCur

/-- **Degree-`d` polynomial PIR is `t`-private** for `t = params.threshold`. -/
theorem isTPrivate_shamirCube {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (params : Shamir.Params F S) :
    (shamirCube D ι params).IsTPrivate params.threshold := by
  classical
  rw [Scheme.isTPrivate_iff]
  intro T hT i i'
  rw [eval_coalitionQuery_shamirCube params T hT i, eval_coalitionQuery_shamirCube params T hT i']

/-- **Sharpness of the collusion threshold for `PIR.shamirCube`**: even when `|S| > |D| * t`
servers are used for degree-`d t` reconstruction, any `params.threshold + 1` colluding servers can
reconstruct coordinate indicators and learn `i`, so `PIR.shamirCube` is not
`(params.threshold + 1)`-private whenever `D` is nonempty (`d ≥ 1`) and `ι` is nontrivial
(`|ι| ≥ 2`). -/
theorem not_isTPrivate_succ_shamirCube {D ι : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι] (params : Shamir.Params F S) :
    ¬ (shamirCube D ι params).IsTPrivate (params.threshold + 1) := by
  intro hpriv
  obtain ⟨l₀⟩ := ‹Nonempty D›
  obtain ⟨u₀, u₁, hne⟩ := exists_pair_ne ι
  obtain ⟨T, -, hcard⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt params.threshold_lt_card)
  have hT : Shamir.authorized params T := by rw [Shamir.authorized, hcard]
  have hrec (idx : D → ι) :
      (ProbComp.eval ((shamirCube D ι params).coalitionQuery T idx)).map
          (fun (qT : T → D → ι → F) => Shamir.reconstruct params T (fun s => qT s l₀ u₀)) =
        PMF.pure (if u₀ = idx l₀ then (1 : F) else 0) := by
    rw [Scheme.eval_coalitionQuery, shamirCube, ProbComp.eval_bind]
    simp only [ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind, PMF.pure_map,
      Shamir.reconstruct_share_eq_secret params _ _ hT, PMF.bind_const]
  refine ne_of_map_eq_pure_one_zero
    (fun (qT : T → D → ι → F) => Shamir.reconstruct params T (fun s => qT s l₀ u₀))
    (by rw [hrec (fun _ => u₀), ite_eq_left rfl]) (by rw [hrec (fun _ => u₁), ite_eq_right hne])
    (hpriv.eval_coalitionQuery_eq T hcard.le (fun _ => u₀) (fun _ => u₁))

/-- **Degree-`d` polynomial PIR is perfectly correct** whenever `|D| * params.threshold < |S|`:
each server evaluates a polynomial of degree at most `|D| * t` whose constant term is `1` if `x i`
and `0` otherwise. -/
theorem isCorrect_shamirCube {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (params : Shamir.Params F S) (hdeg : Fintype.card D * params.threshold < Fintype.card S) :
    (shamirCube D ι params).IsCorrect := by
  classical
  rw [Scheme.isCorrect_iff]
  intro x i _ q hrq
  simp only [shamirCube, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨r, -, -, rfl⟩ := hrq
  let factor (l : D) (u : ι) : _root_.Polynomial F :=
    Shamir.Polynomial.sharingPolynomial (if u = i l then 1 else 0)
      (Shamir.Polynomial.tailPolynomial params.threshold (r l u))
  let term (j : D → ι) : _root_.Polynomial F :=
    if x j then ∏ l : D, factor l (j l) else 0
  let poly : _root_.Polynomial F := ∑ j : D → ι, term j
  have heval (s : S) :
      poly.eval (params.point s) =
        ∑ j : D → ι,
          if x j then
            ∏ l : D, Shamir.share params (r l (j l)) (if j l = i l then 1 else 0) s
          else 0 := by
    simp only [poly, term, _root_.Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hxj : x j
    · simp only [hxj, ↓reduceIte, _root_.Polynomial.eval_prod, factor, Shamir.share]
    · simp [hxj]
  have hfactor_deg (l : D) (u : ι) : (factor l u).natDegree ≤ params.threshold :=
    Shamir.Polynomial.natDegree_sharingPolynomial_le _ _
      (Shamir.Polynomial.tailPolynomial_degree_lt _ _)
  have hterm_deg (j : D → ι) : (term j).natDegree ≤ Fintype.card D * params.threshold := by
    by_cases hxj : x j
    · simp only [term, hxj, ↓reduceIte]
      refine (_root_.Polynomial.natDegree_prod_le _ _).trans ?_
      simpa using Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hfactor_deg l (j l)
    · simp [term, hxj]
  have hpoly_deg : poly.degree < Fintype.card S := by
    have hnat : poly.natDegree ≤ Fintype.card D * params.threshold :=
      _root_.Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => hterm_deg j
    refine _root_.Polynomial.degree_le_natDegree.trans_lt ?_
    exact_mod_cast hnat.trans_lt hdeg
  have hconst : poly.constantCoeff = if x i then 1 else 0 := by
    simp only [poly, term, map_sum _root_.Polynomial.constantCoeff]
    rw [Finset.sum_eq_single i]
    · by_cases hxi : x i
      · simp only [hxi, ↓reduceIte, map_prod _root_.Polynomial.constantCoeff, factor,
          Shamir.Polynomial.constantCoeff_sharingPolynomial, Finset.prod_const_one]
      · simp [hxi]
    · intro j _ hji
      obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp hji
      by_cases hxj : x j
      · simp only [hxj, ↓reduceIte, map_prod _root_.Polynomial.constantCoeff]
        refine Finset.prod_eq_zero (Finset.mem_univ l₀) ?_
        dsimp only [factor]
        rw [ite_eq_right hl₀, Shamir.Polynomial.constantCoeff_sharingPolynomial]
      · simp [hxj]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hans :
      (fun s : S =>
        ∑ j : D → ι,
          if x j then
            ∏ l : D, Shamir.share params (r l (j l)) (if j l = i l then 1 else 0) s
          else 0) =
        fun s : S => poly.eval (params.point s) :=
    funext fun s => (heval s).symm
  dsimp only [shamirCube]
  rw [hans,
    Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq params.point_injective hpoly_deg,
    hconst]
  cases x i <;> simp

end ShamirPIR

section ShamirCommunication

/-- Communication upper bound for `shamirCube`: each server receives `|D| * |ι|` field elements and
sends `1` field element. -/
theorem communication_shamirCube_le {F S D ι : Type} [Fintype F] [Fintype S]
    [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι] :
    communication S (D → ι → F) F ≤
      Fintype.card S * ((Fintype.card D * Fintype.card ι + 1) * Nat.clog 2 (Fintype.card F)) := by
  rw [communication_eq]
  simp only [Fintype.card_fun]
  rw [← pow_mul, Nat.mul_comm (Fintype.card ι)]
  have hclog := Nat.clog_pow_le_mul 2 (Fintype.card F) (Fintype.card D * Fintype.card ι)
  nlinarith

/-- Communication upper bound for `rows`-balanced `shamirCube`
([CGKS, Section 3.4, p. 11][ChorGoldreichKushilevitzSudan1998]): each server receives `|D| * |ι|`
field elements and sends `|ρ|` field elements. -/
theorem communication_shamirCube_rows_le {F S ρ D ι : Type} [Fintype F] [Fintype S]
    [Fintype ρ] [DecidableEq ρ] [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι] :
    communication S (D → ι → F) (ρ → F) ≤
      Fintype.card S *
        ((Fintype.card D * Fintype.card ι + Fintype.card ρ) * Nat.clog 2 (Fintype.card F)) := by
  rw [communication_eq]
  simp only [Fintype.card_fun]
  rw [← pow_mul, Nat.mul_comm (Fintype.card ι)]
  have hQ := Nat.clog_pow_le_mul 2 (Fintype.card F) (Fintype.card D * Fintype.card ι)
  have hA := Nat.clog_pow_le_mul 2 (Fintype.card F) (Fintype.card ρ)
  nlinarith

/-- Communication upper bound for matrix-balanced linear Shamir PIR (`(shamir ι params).rows ρ`). -/
theorem communication_shamir_rows_le {F S ρ ι : Type} [Fintype F] [Fintype S]
    [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι] :
    communication S (ι → F) (ρ → F) ≤
      Fintype.card S * ((Fintype.card ι + Fintype.card ρ) * Nat.clog 2 (Fintype.card F)) := by
  rw [communication_eq]
  simp only [Fintype.card_fun]
  have hQ := Nat.clog_pow_le_mul 2 (Fintype.card F) (Fintype.card ι)
  have hA := Nat.clog_pow_le_mul 2 (Fintype.card F) (Fintype.card ρ)
  nlinarith

end ShamirCommunication

section ShamirBounds

variable {F S : Type} [Field F] [Fintype F] [Fintype S]

/-- **`(t + 1)`-server `O(√n)` `t`-private PIR**: applying `Scheme.rows` to `PIR.shamir` solves any
`n ≤ m ^ 2` with `|S|` servers (`params.threshold < |S|`) and `|S| * 2 m * ⌈log₂ |F|⌉` bits. -/
theorem hasTPrivateScheme_of_le_mul_self (params : Shamir.Params F S) {n m : ℕ}
    (h : n ≤ m * m) :
    HasTPrivateScheme (Fin n) params.threshold (Fintype.card S)
      (Fintype.card S * (2 * m * Nat.clog 2 (Fintype.card F))) := by
  classical
  let e : Fin n ↪ Fin m × Fin m := (Fin.castLEEmb h).trans finProdFinEquiv.symm.toEmbedding
  have hP := ((isCorrect_shamir (ι := Fin m) params).rows (Fin m)).comap e false
    |>.hasTPrivateScheme (((isTPrivate_shamir (ι := Fin m) params).rows (Fin m)).comap e false)
  refine hP.mono ?_
  have hcomm := communication_shamir_rows_le (F := F) (S := S) (ρ := Fin m) (ι := Fin m)
  simp only [Fintype.card_fin] at hcomm
  linarith

/-- **Unbalanced `(d t + 1)`-server `O(n ^ (1 / d))` `t`-private PIR**: whenever
`d * params.threshold < |S|` and `n ≤ ℓ ^ d`, `PIR.shamirCube` gives a perfectly correct `t`-private
scheme communicating at most `|S| * ((d * ℓ + 1) * ⌈log₂ |F|⌉)` bits. -/
theorem hasTPrivateScheme_of_le_pow (params : Shamir.Params F S) {n d ℓ : ℕ}
    (hdeg : d * params.threshold < Fintype.card S) (h : n ≤ ℓ ^ d) :
    HasTPrivateScheme (Fin n) params.threshold (Fintype.card S)
      (Fintype.card S * ((d * ℓ + 1) * Nat.clog 2 (Fintype.card F))) := by
  classical
  let e : Fin n ↪ (Fin d → Fin ℓ) :=
    (Fin.castLEEmb h).trans finFunctionFinEquiv.symm.toEmbedding
  have hdeg' : Fintype.card (Fin d) * params.threshold < Fintype.card S := by
    simpa using hdeg
  have hP := (isCorrect_shamirCube (D := Fin d) (ι := Fin ℓ) params hdeg').comap e false
    |>.hasTPrivateScheme ((isTPrivate_shamirCube (D := Fin d) (ι := Fin ℓ) params).comap e false)
  refine hP.mono ?_
  have hcomm := communication_shamirCube_le (F := F) (S := S) (D := Fin d) (ι := Fin ℓ)
  simpa only [Fintype.card_fin] using hcomm

/-- **Balanced `c t`-server finite-field `t`-private PIR** (weaker finite-field communication
variant of [CGKS, Section 1.1, pp. 1–2, via Section 3.4, p. 11][ChorGoldreichKushilevitzSudan1998]):
applying `Scheme.rows` (`Fin ℓ`) to `PIR.shamirCube (Fin d) (Fin ℓ)` solves any `n ≤ ℓ ^ (d + 1)`
whenever `d * params.threshold < |S|`, using `|S| * ((d + 1) * ℓ * ⌈log₂ |F|⌉)` bits. For
`c = d + 1 ≥ 2` and `t = params.threshold ≥ 1`, `(c - 1) * t < c * t` holds with **exact
`|S| = c * t` servers**, retaining the field bit-width factor `⌈log₂ |F|⌉` (`|F| > c * t`). -/
theorem hasTPrivateScheme_rows_of_le_pow (params : Shamir.Params F S) {n d ℓ : ℕ}
    (hdeg : d * params.threshold < Fintype.card S) (h : n ≤ ℓ ^ (d + 1)) :
    HasTPrivateScheme (Fin n) params.threshold (Fintype.card S)
      (Fintype.card S * ((d + 1) * ℓ * Nat.clog 2 (Fintype.card F))) := by
  classical
  have hsplit : n ≤ ℓ * ℓ ^ d := by simpa [pow_succ'] using h
  let eProd : Fin n ↪ Fin ℓ × Fin (ℓ ^ d) :=
    (Fin.castLEEmb hsplit).trans finProdFinEquiv.symm.toEmbedding
  let e : Fin n ↪ Fin ℓ × (Fin d → Fin ℓ) :=
    eProd.trans (Equiv.prodCongr (Equiv.refl (Fin ℓ)) finFunctionFinEquiv.symm).toEmbedding
  have hdeg' : Fintype.card (Fin d) * params.threshold < Fintype.card S := by
    simpa using hdeg
  have hP := ((isCorrect_shamirCube (D := Fin d) (ι := Fin ℓ) params hdeg').rows (Fin ℓ)).comap
      e false
    |>.hasTPrivateScheme
      (((isTPrivate_shamirCube (D := Fin d) (ι := Fin ℓ) params).rows (Fin ℓ)).comap e false)
  refine hP.mono ?_
  have hcomm :=
    communication_shamirCube_rows_le (F := F) (S := S) (ρ := Fin ℓ) (D := Fin d) (ι := Fin ℓ)
  simp only [Fintype.card_fin] at hcomm
  nlinarith

end ShamirBounds

/-- Canonical Shamir parameters for `k` servers over `ZMod p` using evaluation points `1, …, k`
when `t < k < p` for a prime `p`. -/
def zmodShamirParams {t k p : ℕ} [Fact p.Prime] (htk : t < k) (hkp : k < p) :
    Shamir.Params (ZMod p) (Fin k) where
  threshold := t
  threshold_lt_card := by simpa using htk
  point s := ((s.val + 1 : ℕ) : ZMod p)
  point_injective := by
    intro s₁ s₂ h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext (by omega)
  point_nonzero s := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega

@[simp] theorem threshold_zmodShamirParams {t k p : ℕ} [Fact p.Prime] (htk : t < k) (hkp : k < p) :
    (zmodShamirParams htk hkp).threshold = t := by
  rw [zmodShamirParams]

@[simp] theorem point_zmodShamirParams {t k p : ℕ} [Fact p.Prime] (htk : t < k) (hkp : k < p)
    (s : Fin k) : (zmodShamirParams htk hkp).point s = ((s.val + 1 : ℕ) : ZMod p) := by
  rw [zmodShamirParams]

/-- Concrete prime-field `t`-private `k`-server polynomial PIR for `d * t < k < p` and
`n ≤ ℓ ^ d`. -/
theorem hasTPrivateScheme_prime_of_le_pow {n d ℓ t k p : ℕ} [Fact p.Prime]
    (hdeg : d * t < k) (hd : 0 < d) (hkp : k < p) (hn : n ≤ ℓ ^ d) :
    HasTPrivateScheme (Fin n) t k (k * ((d * ℓ + 1) * Nat.clog 2 p)) := by
  have htk : t < k := (Nat.le_mul_of_pos_left t hd).trans_lt hdeg
  have h := hasTPrivateScheme_of_le_pow (zmodShamirParams htk hkp) (by simpa using hdeg) hn
  simpa [ZMod.card] using h

/-- Concrete prime-field `rows`-balanced `t`-private `k`-server polynomial PIR for `d * t < k < p`
and `n ≤ ℓ ^ (d + 1)` (weaker finite-field communication variant of
[CGKS, Section 1.1, pp. 1–2, via Section 3.4, p. 11][ChorGoldreichKushilevitzSudan1998], achieving
exact `k = c * t` servers at `d = c - 1` when `1 < c` and `0 < t` with factor `⌈log₂ p⌉`). -/
theorem hasTPrivateScheme_prime_rows_of_le_pow {n d ℓ t k p : ℕ} [Fact p.Prime]
    (htk : t < k) (hdeg : d * t < k) (hkp : k < p) (hn : n ≤ ℓ ^ (d + 1)) :
    HasTPrivateScheme (Fin n) t k (k * ((d + 1) * ℓ * Nat.clog 2 p)) := by
  have h := hasTPrivateScheme_rows_of_le_pow (zmodShamirParams htk hkp) (by simpa using hdeg) hn
  simpa [ZMod.card] using h

end Cslib.Crypto.Protocols.PIR
