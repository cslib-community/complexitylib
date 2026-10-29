/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.PolyTime.Int.Table
public import Complexity.Computability.PolyTime.JetArray
public import Complexity.Foundations.BooleanAnalysis.SparseEquations
public import Complexity.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Algebra.Field.Rat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Int.Order
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Beigel–Tarui parity-amplifier coefficients and staged factor jet evaluation

Lemma 5.1 and Appendix B.1–B.2 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] expand
$p_\ell(Y) = (1 - Y)^\ell \sum_{j < \ell} \binom{\ell + j - 1}{j} Y^j$ in powers of
$h(Y) = Y (Y - 1)$ with linear remainders $a_{\ell, s} + b_{\ell, s} Y$, and evaluate a single
parity-amplifier factor on a fixed-denominator $z$-jet cleared by $\Gamma = \Delta^{2 \ell - 1}$.

* `Cslib.polyAdd`, `Cslib.mulZJet`, `Cslib.polyMul`, `Cslib.divModByH`: executable univariate
  polynomial and 1D $z$-jet arithmetic bridged to `Polynomial.ofCoeffList`, `Polynomial.coeffNorm1`,
  and monic division by `Polynomial.hPoly`.
* `Cslib.parityLinearCoeffs`, `Cslib.evalParityAmplifier`: $(a_{\ell, s}, b_{\ell, s})$ expansion
  bridged to `Polynomial.parityAmplifier` and `Polynomial.parityBaseDigit`, parity congruence mod
  $2^\ell$, $2^{7 \ell^2}$ magnitude bound, and `ComputableInPolyTime`.
* `Cslib.evalParityFactorJet`: $\Gamma$-cleared $J \times \ell$ factor table built with
  `Cslib.tabulateTable` and `Cslib.rowEntry`, bridged to `Cslib.IsTableShape`, `Cslib.jetL1Norm`,
  and `Cslib.BitString.parityFactorCleared`, with $\mathbb{Z}[X]$ / $\mathbb{Q}[X]$ ($\Delta \ne 0$)
  / $j = 0$ identities, Appendix B.2 norm/bit bounds, and `ComputableInPolyTime`.
-/

@[expose] public section

namespace Cslib

open Polynomial Turing.MultiTapeTM

/-! ### Coefficient $\ell_1$-norms and list/polynomial helpers -/

/-- The $\ell_1$-norm $\sum_i |c_i|$ of an integer coefficient list. -/
def polyNorm1 (p : List ℤ) : ℕ := (p.map Int.natAbs).sum

/-- `Cslib.jetL1Norm` equals the sum of `Cslib.polyNorm1` across rows. -/
theorem jetL1Norm_eq_sum_map_polyNorm1 (rows : List (List ℤ)) :
    jetL1Norm rows = (rows.map polyNorm1).sum := rfl

/-- `polyNorm1` of the empty coefficient list is `0`. -/
theorem polyNorm1_nil : polyNorm1 [] = 0 := rfl

/-- `polyNorm1` of `c :: p` adds `c.natAbs` to `polyNorm1 p`. -/
theorem polyNorm1_cons (c : ℤ) (p : List ℤ) :
    polyNorm1 (c :: p) = c.natAbs + polyNorm1 p := rfl

/-- `polyNorm1` is additive across list concatenation. -/
theorem polyNorm1_append (p q : List ℤ) :
    polyNorm1 (p ++ q) = polyNorm1 p + polyNorm1 q := by
  simp only [polyNorm1, List.map_append, List.sum_append]

/-- Reversing a coefficient list preserves `polyNorm1`. -/
theorem polyNorm1_reverse (p : List ℤ) : polyNorm1 p.reverse = polyNorm1 p := by
  simp only [polyNorm1, List.map_reverse, List.sum_reverse]

/-- Taking a prefix does not increase `polyNorm1`. -/
theorem polyNorm1_take_le (p : List ℤ) (n : ℕ) : polyNorm1 (p.take n) ≤ polyNorm1 p := by
  rw [polyNorm1, polyNorm1, List.map_take]
  have h := List.monotone_sum_take (p.map Int.natAbs) (le_max_left n (p.map Int.natAbs).length)
  dsimp only at h; rwa [List.take_of_length_le (le_max_right n _)] at h

/-- Every coefficient `z ∈ p` has `z.natAbs ≤ polyNorm1 p`. -/
theorem natAbs_mem_le_polyNorm1 {p : List ℤ} {z : ℤ} (hz : z ∈ p) : z.natAbs ≤ polyNorm1 p :=
  List.le_sum_of_mem (List.mem_map_of_mem hz)

private lemma natAbs_sum_le_polyNorm1 (p : List ℤ) : p.sum.natAbs ≤ polyNorm1 p :=
  List.le_sum_of_subadditive Int.natAbs Int.natAbs_zero.le Int.natAbs_add_le p

/-- Uniform entrywise magnitude bound `B` implies `polyNorm1 p ≤ p.length * B`. -/
theorem polyNorm1_le_length_mul {p : List ℤ} {B : ℕ} (h : ∀ z ∈ p, z.natAbs ≤ B) :
    polyNorm1 p ≤ p.length * B := by
  have hmem : ∀ x ∈ p.map Int.natAbs, x ≤ B := fun _ hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx; exact h z hz
  simpa only [polyNorm1, List.length_map, smul_eq_mul] using
    List.sum_le_length_nsmul (p.map Int.natAbs) B hmem

private lemma sum_map_range_eq_finset {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  (List.sum_map_range n f).trans (Fin.sum_univ_eq_sum_range f n)

private lemma eq_map_range_getD {l : List ℤ} {n : ℕ} (h : l.length = n) :
    l = (List.range n).map fun i => l.getD i 0 :=
  List.ext_getElem (by simp only [h, List.length_map, List.length_range]) fun i hi _ => by
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ 0 hi]

/-- Bounding `z.natAbs ≤ 2 ^ e` bounds `(encIntBin z).length ≤ e + 2`. -/
theorem length_encIntBin_le_of_natAbs_le {z : ℤ} {e : ℕ} (hz : z.natAbs ≤ 2 ^ e) :
    (encIntBin z).length ≤ e + 2 := by
  rw [length_encIntBin]
  have := Nat.size_le.mpr (hz.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self e)))
  omega

/-! ### Univariate polynomial and 1D $z$-jet primitives -/

/-- Addition of univariate integer polynomials represented by low-first coefficient lists. -/
def polyAdd (p q : List ℤ) : List ℤ :=
  (List.range (max p.length q.length)).map fun i => p.getD i 0 + q.getD i 0

/-- The $k$-th Cauchy-product coefficient $\sum_{i \le k} p_i q_{k - i}$. -/
def cauchyCoeff (p q : List ℤ) (k : ℕ) : ℤ :=
  ((List.range (k + 1)).map fun i => p.getD i 0 * q.getD (k - i) 0).sum

/-- 1D truncated $z$-jet Cauchy product $(u \cdot v) \bmod z^J$ of length $J$. -/
def mulZJet (J : ℕ) (u v : List ℤ) : List ℤ := (List.range J).map (cauchyCoeff u v)

/-- Multiplication of univariate integer polynomials represented by low-first coefficient lists. -/
def polyMul (p q : List ℤ) : List ℤ := mulZJet (p.length + q.length) p q

/-- Single Horner-division step for monic division by $Y^2 - Y$. -/
def ParityFactorEval.divModByHStep (state : List ℤ × (ℤ × ℤ)) (c : ℤ) : List ℤ × (ℤ × ℤ) :=
  (state.2.2 :: state.1, (c, state.2.1 + state.2.2))

/-- Monic division of `p` by $h(Y) = Y^2 - Y$ with linear remainder `(a, b)`. -/
def divModByH (p : List ℤ) : List ℤ × (ℤ × ℤ) :=
  p.reverse.foldl ParityFactorEval.divModByHStep ([], (0, 0))

private lemma getD_take_of_lt (u : List ℤ) {i J : ℕ} (hi : i < J) :
    (u.take J).getD i 0 = u.getD i 0 := by
  by_cases hlen : i < u.length
  · rw [List.getD_eq_getElem _ 0 (by simp only [List.length_take]; omega),
      List.getD_eq_getElem _ 0 hlen, List.getElem_take]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_take]; omega),
      List.getD_eq_default _ _ (by omega)]

private lemma coeff_ofCoeffList_mul_eq {R : Type*} [Semiring R] (p q : List R) (k : ℕ) :
    (ofCoeffList p * ofCoeffList q).coeff k =
      ((List.range (k + 1)).map fun i => p.getD i 0 * q.getD (k - i) 0).sum := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (ofCoeffList p).coeff i * (ofCoeffList q).coeff j), ← sum_map_range_eq_finset]
  exact congrArg List.sum (List.map_congr_left fun i _ => by simp only [coeff_ofCoeffList])

/-- Entrywise `getD` specification of `polyAdd`. -/
theorem getD_polyAdd (p q : List ℤ) (i : ℕ) :
    (polyAdd p q).getD i 0 = p.getD i 0 + q.getD i 0 := by
  by_cases hi : i < max p.length q.length
  · exact List.getD_map_range _ 0 hi
  · have hlen : (polyAdd p q).length ≤ i := by
      simp only [polyAdd, List.length_map, List.length_range]; omega
    rw [List.getD_eq_default _ _ hlen, List.getD_eq_default p _ (by omega),
      List.getD_eq_default q _ (by omega), add_zero]

/-- `polyAdd` represents polynomial addition under `Polynomial.ofCoeffList`. -/
theorem ofCoeffList_polyAdd (p q : List ℤ) :
    ofCoeffList (polyAdd p q) = ofCoeffList p + ofCoeffList q := by
  ext i; simp only [coeff_ofCoeffList, coeff_add, getD_polyAdd]

/-- Triangle inequality for `polyNorm1` of `polyAdd`. -/
theorem polyNorm1_polyAdd_le (p q : List ℤ) :
    polyNorm1 (polyAdd p q) ≤ polyNorm1 p + polyNorm1 q := by
  simp only [polyNorm1, ← Polynomial.coeffNorm1_ofCoeffList, ofCoeffList_polyAdd]
  exact coeffNorm1_add_le _ _

/-- `mulZJet J u v` has length `J`. -/
@[simp] theorem length_mulZJet (J : ℕ) (u v : List ℤ) : (mulZJet J u v).length = J := by
  simp only [mulZJet, List.length_map, List.length_range]

/-- Below `J`, `ofCoeffList (mulZJet J u v)` has the same coefficients as
`ofCoeffList u * ofCoeffList v`. -/
theorem coeff_ofCoeffList_mulZJet {J j : ℕ} (hj : j < J) (u v : List ℤ) :
    (ofCoeffList (mulZJet J u v)).coeff j = (ofCoeffList u * ofCoeffList v).coeff j := by
  rw [coeff_ofCoeffList, mulZJet, List.getD_map_range _ 0 hj, coeff_ofCoeffList_mul_eq, cauchyCoeff]

/-- Coefficient specification of `mulZJet` on degree-$< J$ prefixes. -/
theorem getD_mulZJet_of_lt {J j : ℕ} (hj : j < J) (u v : List ℤ) :
    (mulZJet J u v).getD j 0 = (ofCoeffList (u.take J) * ofCoeffList (v.take J)).coeff j := by
  rw [← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet hj, Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have := Finset.mem_antidiagonal.mp hkl; simp only [coeff_ofCoeffList]
  rw [getD_take_of_lt u (by omega), getD_take_of_lt v (by omega)]

/-- `polyMul` represents polynomial multiplication under `Polynomial.ofCoeffList`. -/
theorem ofCoeffList_polyMul (p q : List ℤ) :
    ofCoeffList (polyMul p q) = ofCoeffList p * ofCoeffList q := by
  ext k; by_cases hk : k < p.length + q.length
  · exact coeff_ofCoeffList_mulZJet hk p q
  · rw [coeff_ofCoeffList, List.getD_eq_default _ _ (by rw [polyMul, length_mulZJet]; omega),
      coeff_ofCoeffList_mul_eq]
    symm; apply List.sum_eq_zero; intro _ hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi; by_cases hip : i < p.length
    · rw [List.getD_eq_default q _ (by omega), mul_zero]
    · rw [List.getD_eq_default p _ (by omega), zero_mul]

/-- Submultiplicativity of `polyNorm1` under truncated $z$-jet multiplication `mulZJet`. -/
theorem polyNorm1_mulZJet_le (J : ℕ) (u v : List ℤ) :
    polyNorm1 (mulZJet J u v) ≤ polyNorm1 (u.take J) * polyNorm1 (v.take J) := by
  rw [polyNorm1, mulZJet, List.map_map, Function.comp_def, sum_map_range_eq_finset]
  have hterms :
      ∑ j ∈ Finset.range J, (cauchyCoeff u v j).natAbs =
        ∑ j ∈ Finset.range J,
          ((ofCoeffList (u.take J) * ofCoeffList (v.take J)).coeff j).natAbs :=
    Finset.sum_congr rfl fun j hj => by
      have hlt := Finset.mem_range.mp hj
      rw [← getD_mulZJet_of_lt hlt, mulZJet, List.getD_map_range _ 0 hlt]
  rw [hterms, polyNorm1, polyNorm1, ← Polynomial.coeffNorm1_ofCoeffList (u.take J),
    ← Polynomial.coeffNorm1_ofCoeffList (v.take J)]
  exact (sum_natAbs_coeff_le_coeffNorm1 _ _).trans (coeffNorm1_mul_le _ _)

/-- Submultiplicativity of `polyNorm1` under `polyMul`. -/
theorem polyNorm1_polyMul_le (p q : List ℤ) :
    polyNorm1 (polyMul p q) ≤ polyNorm1 p * polyNorm1 q :=
  (polyNorm1_mulZJet_le _ p q).trans
    (Nat.mul_le_mul (polyNorm1_take_le p _) (polyNorm1_take_le q _))

/-- Polynomial division identity for `divModByH` dividing by $X^2 - X$. -/
theorem ofCoeffList_divModByH (p : List ℤ) :
    ofCoeffList p =
      ofCoeffList (divModByH p).1 * (X ^ 2 - X) +
        (C (divModByH p).2.1 + C (divModByH p).2.2 * X) := by
  induction p with
  | nil => simp only [divModByH, List.reverse_nil, List.foldl_nil, ofCoeffList_nil, zero_mul,
      map_zero, add_zero]
  | cons c rest ih =>
    have hcons : divModByH (c :: rest) = ParityFactorEval.divModByHStep (divModByH rest) c := by
      simp only [divModByH, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ofCoeffList_cons, hcons, ParityFactorEval.divModByHStep, ofCoeffList_cons, ih]
    simp only [map_add]; ring

private lemma foldl_divModByHStep_bounds (w : List ℤ) :
    let s := w.foldl ParityFactorEval.divModByHStep ([], (0, 0))
    s.1.length = w.length ∧ s.2.1.natAbs + s.2.2.natAbs ≤ polyNorm1 w ∧
      ∀ z ∈ s.1, z.natAbs ≤ polyNorm1 w := by
  induction w using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Int.natAbs_zero, add_zero, polyNorm1_nil, le_rfl,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self]
  | append_singleton u c ih =>
    rcases ih with ⟨hlen, hrem, hq⟩
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, ParityFactorEval.divModByHStep,
      List.length_cons, List.length_append, List.length_nil, polyNorm1_append, polyNorm1_cons,
      polyNorm1_nil, add_zero]
    have hadd := Int.natAbs_add_le (u.foldl ParityFactorEval.divModByHStep ([], (0, 0))).2.1
      (u.foldl ParityFactorEval.divModByHStep ([], (0, 0))).2.2
    refine ⟨by omega, by omega, fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hmem
    · omega
    · have := hq z hmem; omega

/-- Quotient length invariant of `divModByH`. -/
@[simp] theorem length_divModByH_fst (p : List ℤ) : (divModByH p).1.length = p.length := by
  simpa only [divModByH, List.length_reverse] using (foldl_divModByHStep_bounds p.reverse).1

/-- Linear remainder magnitude bound for `divModByH` ([OpenAI2026ETH], Lemma B.1). -/
theorem natAbs_divModByH_snd_le (p : List ℤ) :
    (divModByH p).2.1.natAbs ≤ polyNorm1 p ∧ (divModByH p).2.2.natAbs ≤ polyNorm1 p := by
  have h := (foldl_divModByHStep_bounds p.reverse).2.1; rw [polyNorm1_reverse] at h
  change (divModByH p).2.1.natAbs + (divModByH p).2.2.natAbs ≤ polyNorm1 p at h; omega

/-- Quotient $\ell_1$-norm bound for `divModByH` ([OpenAI2026ETH], Lemma B.1). -/
theorem polyNorm1_divModByH_fst_le (p : List ℤ) :
    polyNorm1 (divModByH p).1 ≤ p.length * polyNorm1 p := by
  have hmem : ∀ z ∈ (divModByH p).1, z.natAbs ≤ polyNorm1 p := fun z hz => by
    have h := (foldl_divModByHStep_bounds p.reverse).2.2 z hz; rwa [polyNorm1_reverse] at h
  simpa only [length_divModByH_fst] using polyNorm1_le_length_mul hmem

/-- `divModByH` computes the exact monic quotient and remainder on division by
`Polynomial.hPoly = X ^ 2 - X`. -/
theorem divByMonic_and_modByMonic_hPoly_ofCoeffList (p : List ℤ) :
    ofCoeffList p /ₘ hPoly = ofCoeffList (divModByH p).1 ∧
      ofCoeffList p %ₘ hPoly = C (divModByH p).2.1 + C (divModByH p).2.2 * X := by
  refine div_modByMonic_unique _ _ monic_hPoly ⟨?_, ?_⟩
  · rw [hPoly, ofCoeffList_divModByH p]; ring
  · have hr : C (divModByH p).2.1 + C (divModByH p).2.2 * X =
        ofCoeffList [(divModByH p).2.1, (divModByH p).2.2] := by
      simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero]; ring
    rw [hr]
    refine degree_le_natDegree.trans_lt ?_
    rw [degree_eq_natDegree monic_hPoly.ne_zero, Nat.cast_lt, natDegree_hPoly]
    exact (natDegree_ofCoeffList_le _).trans_lt
      (by simp only [List.length_cons, List.length_nil]; omega)

/-! ### Beigel–Tarui parity-amplifier coefficients (`parityLinearCoeffs`) -/

/-- Prefix-sum step mapping $v$ to $(\sum_{i \le j} v_i)_{j < |v|}$. -/
def ParityFactorEval.prefixSumPoly (v : List ℤ) : List ℤ :=
  (List.range v.length).map fun j => (v.take (j + 1)).sum

/-- Degree-$< \ell$ Taylor inverse of $(1 - Y)^\ell$ modulo $Y^\ell$. -/
def ParityFactorEval.taylorInvOneSubPow (ℓ : ℕ) : List ℤ :=
  ParityFactorEval.prefixSumPoly^[ℓ - 1] (List.replicate ℓ 1)

/-- Coefficient list of $(1 - Y)^\ell$. -/
def ParityFactorEval.oneSubPow (ℓ : ℕ) : List ℤ := (polyMul [1, -1])^[ℓ] [1]

/-- Coefficient list of $p_\ell(Y) = (1 - Y)^\ell \sum_{j < \ell} \binom{\ell + j - 1}{j} Y^j$. -/
def parityPolyCoeffs (ℓ : ℕ) : List ℤ :=
  if ℓ = 0 then []
  else polyMul (ParityFactorEval.oneSubPow ℓ) (ParityFactorEval.taylorInvOneSubPow ℓ)

/-- Single outer division step appending the linear remainder of `divModByH`. -/
def ParityFactorEval.parityDivStep (state : List ℤ × List (ℤ × ℤ)) : List ℤ × List (ℤ × ℤ) :=
  let dm := divModByH state.1; (dm.1, state.2 ++ [dm.2])

/-- Executable Beigel–Tarui linear remainder table `[(a_0, b_0), ..., (a_{ℓ-1}, b_{ℓ-1})]`
expanding $p_\ell(Y) = \sum_{s < \ell} (a_s + b_s Y) (Y (Y - 1))^s$. -/
def parityLinearCoeffs (ℓ : ℕ) : List (ℤ × ℤ) :=
  (ParityFactorEval.parityDivStep^[ℓ] (parityPolyCoeffs ℓ, [])).2

/-- Integer evaluation of the Beigel–Tarui $(a_s, b_s)$ expansion in powers of $y (y - 1)$. -/
def evalParityAmplifier (ℓ : ℕ) (y : ℤ) : ℤ :=
  ((List.range ℓ).map fun s =>
    let ab := (parityLinearCoeffs ℓ).getD s (0, 0)
    (ab.1 + ab.2 * y) * (y * (y - 1)) ^ s).sum

private lemma prefixSumPoly_iterate_eq (ℓ m : ℕ) :
    ParityFactorEval.prefixSumPoly^[m] (List.replicate ℓ (1 : ℤ)) =
      (List.range ℓ).map fun j => ((m + j).choose j : ℤ) := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero, id_eq, zero_add, Nat.choose_self, Nat.cast_one]
    exact List.ext_getElem
      (by simp only [List.length_replicate, List.length_map, List.length_range])
      fun j _ _ => by simp only [List.getElem_replicate, List.getElem_map]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]; unfold ParityFactorEval.prefixSumPoly
    apply List.ext_getElem (by simp only [List.length_map, List.length_range])
    intro j hj _; simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega : j + 1 ≤ ℓ),
      sum_map_range_eq_finset]
    have h1 : ∑ i ∈ Finset.range (j + 1), (m + i).choose i =
        ∑ i ∈ Finset.range (j + 1), (i + m).choose m :=
      Finset.sum_congr rfl fun i _ => by rw [← Nat.choose_symm_add, add_comm]
    have hsum : ∑ i ∈ Finset.range (j + 1), (m + i).choose i = (m + 1 + j).choose j := by
      rw [h1, Nat.sum_range_add_choose, show j + m + 1 = m + 1 + j by omega, Nat.choose_symm_add]
    exact mod_cast hsum

private lemma ofCoeffList_map_range {R : Type*} [Semiring R] (n : ℕ) (f : ℕ → R) :
    ofCoeffList ((List.range n).map f) = ∑ j ∈ Finset.range n, C (f j) * X ^ j := by
  ext k; rw [coeff_ofCoeffList, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_boole, Finset.sum_ite_eq (Finset.range n) k f,
    Finset.mem_range]
  by_cases hk : k < n
  · rw [List.getD_map_range _ 0 hk, ite_eq_left hk]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega),
      ite_eq_right hk]

private lemma ofCoeffList_oneSubPow (i : ℕ) :
    ofCoeffList (ParityFactorEval.oneSubPow i) = (1 - X : ℤ[X]) ^ i := by
  induction i with
  | zero => simp only [ParityFactorEval.oneSubPow, Function.iterate_zero, id_eq, ofCoeffList_cons,
      ofCoeffList_nil, mul_zero, add_zero, map_one, pow_zero]
  | succ i ih =>
    have hbase : ofCoeffList ([1, -1] : List ℤ) = 1 - X := by
      simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, map_one, map_neg]; ring
    simp only [ParityFactorEval.oneSubPow, Function.iterate_succ_apply',
      ofCoeffList_polyMul] at ih ⊢
    rw [hbase, ih, pow_succ']

private lemma length_oneSubPow (i : ℕ) : (ParityFactorEval.oneSubPow i).length = 2 * i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [ParityFactorEval.oneSubPow, Function.iterate_succ_apply'] at ih ⊢
    rw [polyMul, length_mulZJet, ih]; simp only [List.length_cons, List.length_nil]; omega

private lemma polyNorm1_oneSubPow_le (i : ℕ) :
    polyNorm1 (ParityFactorEval.oneSubPow i) ≤ 2 ^ i := by
  induction i with
  | zero => simp only [ParityFactorEval.oneSubPow, Function.iterate_zero, id_eq, polyNorm1_cons,
      polyNorm1_nil, Int.natAbs_one, add_zero, pow_zero, le_rfl]
  | succ i ih =>
    simp only [ParityFactorEval.oneSubPow, Function.iterate_succ_apply'] at ih ⊢
    have hnorm : polyNorm1 ([1, -1] : List ℤ) = 2 := by decide
    refine (polyNorm1_polyMul_le _ _).trans ?_
    rw [hnorm, pow_succ']; exact Nat.mul_le_mul_left 2 ih

/-- `parityPolyCoeffs ℓ` represents `Polynomial.parityAmplifier ℓ` under
`Polynomial.ofCoeffList`. -/
theorem ofCoeffList_parityPolyCoeffs_eq_parityAmplifier (ℓ : ℕ) :
    ofCoeffList (parityPolyCoeffs ℓ) = parityAmplifier ℓ := by
  by_cases h0 : ℓ = 0
  · subst h0; simp only [parityPolyCoeffs, ↓reduceIte, ofCoeffList_nil, parityAmplifier_zero]
  · rw [parityPolyCoeffs, ite_eq_right h0, ofCoeffList_polyMul, ofCoeffList_oneSubPow,
      ParityFactorEval.taylorInvOneSubPow, prefixSumPoly_iterate_eq, ofCoeffList_map_range,
      parityAmplifier, parityKernel, paritySeriesAux]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    simp only [eq_intCast, Int.cast_natCast]

/-- Polynomial specification of `parityPolyCoeffs` for $1 \le \ell$. -/
theorem ofCoeffList_parityPolyCoeffs {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ofCoeffList (parityPolyCoeffs ℓ) =
      (1 - X) ^ ℓ * ∑ j ∈ Finset.range ℓ, C (((ℓ + j - 1).choose j : ℕ) : ℤ) * X ^ j := by
  rw [ofCoeffList_parityPolyCoeffs_eq_parityAmplifier, parityAmplifier, parityKernel,
    paritySeriesAux]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [show ℓ - 1 + j = ℓ + j - 1 by omega]; simp only [eq_intCast, Int.cast_natCast]

private lemma parityDivStep_iterate_spec (p : List ℤ) (s : ℕ) :
    let st := ParityFactorEval.parityDivStep^[s] (p, [])
    st.1.length = p.length ∧ st.2.length = s ∧
      ofCoeffList st.1 = iterDivByH (ofCoeffList p) s ∧
      ∀ j < s, st.2.getD j (0, 0) =
        ((baseDigitByH (ofCoeffList p) j).coeff 0, (baseDigitByH (ofCoeffList p) j).coeff 1) := by
  induction s with
  | zero =>
    simp only [Function.iterate_zero, id_eq, List.length_nil, iterDivByH, Nat.not_lt_zero,
      IsEmpty.forall_iff, implies_true, and_self]
  | succ s ih =>
    set st := ParityFactorEval.parityDivStep^[s] (p, []); set dm := divModByH st.1
    rcases ih with ⟨hlen1, hlen2, hiter, hdigits⟩
    obtain ⟨hdiv, hmod⟩ := divByMonic_and_modByMonic_hPoly_ofCoeffList st.1
    rw [show ParityFactorEval.parityDivStep^[s + 1] (p, []) = (dm.1, st.2 ++ [dm.2]) from
      Function.iterate_succ_apply' ParityFactorEval.parityDivStep s (p, [])]
    refine ⟨(length_divModByH_fst st.1).trans hlen1,
      by simp only [List.length_append, List.length_singleton, hlen2], ?_, fun j hj => ?_⟩
    · rw [iterDivByH, ← hiter, hdiv]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjeq
      · rw [List.getD_append _ _ _ _ (by omega)]; exact hdigits j hlt
      · rw [hjeq, List.getD_append_right _ _ _ _ (by omega), hlen2, Nat.sub_self,
          List.getD_cons_zero]
        have hrem : baseDigitByH (ofCoeffList p) s = C dm.2.1 + C dm.2.2 * X := by
          rw [baseDigitByH, ← hiter, hmod]
        rw [hrem]
        exact Prod.ext
          (by simp only [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero])
          (by simp only [coeff_add, coeff_C_succ, coeff_C_mul, coeff_X_one, mul_one, zero_add])

/-- `parityLinearCoeffs ℓ` has length `ℓ`. -/
@[simp] theorem length_parityLinearCoeffs (ℓ : ℕ) : (parityLinearCoeffs ℓ).length = ℓ :=
  (parityDivStep_iterate_spec (parityPolyCoeffs ℓ) ℓ).2.1

/-- Entry `s` of `parityLinearCoeffs ℓ` equals the `(coeff 0, coeff 1)` pair of
`Polynomial.parityBaseDigit ℓ s`. -/
theorem getD_parityLinearCoeffs_eq_parityBaseDigit (ℓ s : ℕ) :
    (parityLinearCoeffs ℓ).getD s (0, 0) =
      ((parityBaseDigit ℓ s).coeff 0, (parityBaseDigit ℓ s).coeff 1) := by
  by_cases hs : s < ℓ
  · simpa only [parityLinearCoeffs, parityBaseDigit,
      ofCoeffList_parityPolyCoeffs_eq_parityAmplifier] using
      (parityDivStep_iterate_spec (parityPolyCoeffs ℓ) ℓ).2.2.2 s hs
  · rw [List.getD_eq_default _ _ (by rw [length_parityLinearCoeffs]; omega)]
    have hzero : iterDivByH (parityAmplifier ℓ) s = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hs)
      clear hs
      induction d with
      | zero => simpa only [add_zero] using iterDivByH_parityAmplifier_self ℓ
      | succ d ih => rw [← add_assoc, iterDivByH, ih, zero_divByMonic]
    simp only [parityBaseDigit, baseDigitByH, hzero, zero_modByMonic, coeff_zero]

/-- Exact $\mathbb{Z}[X]$ identity expanding $p_\ell(X)$ in powers of $X^2 - X$. -/
theorem ofCoeffList_parityPolyCoeffs_eq_sum (ℓ : ℕ) :
    ofCoeffList (parityPolyCoeffs ℓ) =
      ∑ s ∈ Finset.range ℓ,
        (C ((parityLinearCoeffs ℓ).getD s (0, 0)).1 +
          C ((parityLinearCoeffs ℓ).getD s (0, 0)).2 * X) * (X ^ 2 - X) ^ s := by
  rw [ofCoeffList_parityPolyCoeffs_eq_parityAmplifier, parityAmplifier_eq_sum_baseDigit]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [getD_parityLinearCoeffs_eq_parityBaseDigit, ← parityBaseDigit_eq_C_add_C_mul_X, hPoly]

/-- `evalParityAmplifier ℓ y` agrees with `(Polynomial.parityAmplifier ℓ).eval y`. -/
theorem evalParityAmplifier_eq_eval_parityAmplifier (ℓ : ℕ) (y : ℤ) :
    evalParityAmplifier ℓ y = (parityAmplifier ℓ).eval y := by
  rw [← ofCoeffList_parityPolyCoeffs_eq_parityAmplifier, ofCoeffList_parityPolyCoeffs_eq_sum,
    eval_finsetSum, evalParityAmplifier, sum_map_range_eq_finset]
  exact Finset.sum_congr rfl fun s _ => by
    simp only [eval_mul, eval_add, eval_C, eval_X, eval_pow, eval_sub]; ring

/-- For $1 \le \ell$ and every integer $y$, the $(a_{\ell, s}, b_{\ell, s})$ expansion evaluates to
$p_\ell(y) = (1 - y)^\ell \sum_{j < \ell} \binom{\ell + j - 1}{j} y^j$. -/
theorem evalParityAmplifier_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : ℤ) :
    evalParityAmplifier ℓ y =
      (1 - y) ^ ℓ * ∑ j ∈ Finset.range ℓ, (((ℓ + j - 1).choose j : ℕ) : ℤ) * y ^ j := by
  rw [evalParityAmplifier_eq_eval_parityAmplifier,
    ← ofCoeffList_parityPolyCoeffs_eq_parityAmplifier, ofCoeffList_parityPolyCoeffs hℓ, eval_mul,
    eval_pow, eval_sub, eval_one, eval_X, eval_finsetSum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  simp only [eval_mul, eval_C, eval_pow, eval_X]

/-- **Beigel–Tarui parity amplification** ([OpenAI2026ETH], Lemma 5.1): for $1 \le \ell$ and every
$y \in \mathbb{Z}$, $p_\ell(y) \equiv [2 \mid y] \pmod{2^\ell}$. -/
theorem evalParityAmplifier_modEq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : ℤ) :
    evalParityAmplifier ℓ y ≡ (if 2 ∣ y then 1 else 0) [ZMOD 2 ^ ℓ] := by
  rw [evalParityAmplifier_eq_eval_parityAmplifier]
  split_ifs with heven
  · exact parityAmplifier_eval_modEq_one_of_even hℓ (even_iff_two_dvd.mpr heven)
  · exact parityAmplifier_eval_modEq_zero_of_odd ℓ
      (Int.not_even_iff_odd.mp (mt even_iff_two_dvd.mp heven))

/-! ### Magnitude and bit-length bounds for `parityLinearCoeffs` (Lemma B.1) -/

private lemma length_and_norm_taylorIterate (ℓ i : ℕ) (hi : i ≤ ℓ - 1) :
    (ParityFactorEval.prefixSumPoly^[i] (List.replicate ℓ (1 : ℤ))).length = ℓ ∧
      (∀ z ∈ ParityFactorEval.prefixSumPoly^[i] (List.replicate ℓ (1 : ℤ)),
        z.natAbs ≤ 2 ^ (2 * ℓ)) ∧
      polyNorm1 (ParityFactorEval.prefixSumPoly^[i] (List.replicate ℓ (1 : ℤ))) ≤
        2 ^ (3 * ℓ) := by
  rw [prefixSumPoly_iterate_eq]
  have hmem : ∀ z ∈ (List.range ℓ).map (fun j => (((i + j).choose j : ℕ) : ℤ)),
      z.natAbs ≤ 2 ^ (2 * ℓ) := fun _ hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hj; rw [Int.natAbs_natCast]
    have hch : (i + j).choose j ≤ 2 ^ (i + j) := by
      rw [← Nat.sum_range_choose (i + j)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    exact hch.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨by simp only [List.length_map, List.length_range], hmem, ?_⟩
  calc polyNorm1 ((List.range ℓ).map fun j => (((i + j).choose j : ℕ) : ℤ))
      ≤ ℓ * 2 ^ (2 * ℓ) := by
        simpa only [List.length_map, List.length_range] using polyNorm1_le_length_mul hmem
    _ ≤ 2 ^ ℓ * 2 ^ (2 * ℓ) := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (3 * ℓ) := by rw [← pow_add]; congr 1; omega

private lemma length_parityPolyCoeffs_le (ℓ : ℕ) : (parityPolyCoeffs ℓ).length ≤ 4 * ℓ := by
  by_cases h0 : ℓ = 0
  · subst h0; simp only [parityPolyCoeffs, ↓reduceIte, List.length_nil, Nat.mul_zero, le_rfl]
  · rw [parityPolyCoeffs, ite_eq_right h0, polyMul, length_mulZJet, length_oneSubPow,
      ParityFactorEval.taylorInvOneSubPow, (length_and_norm_taylorIterate ℓ (ℓ - 1) le_rfl).1]
    omega

private lemma polyNorm1_parityPolyCoeffs_le (ℓ : ℕ) :
    polyNorm1 (parityPolyCoeffs ℓ) ≤ 2 ^ (4 * ℓ) := by
  by_cases h0 : ℓ = 0
  · subst h0
    simp only [parityPolyCoeffs, ↓reduceIte, polyNorm1_nil, Nat.mul_zero, pow_zero, zero_le]
  · rw [parityPolyCoeffs, ite_eq_right h0]
    exact (polyNorm1_polyMul_le _ _).trans
      ((Nat.mul_le_mul (polyNorm1_oneSubPow_le ℓ)
        (length_and_norm_taylorIterate ℓ (ℓ - 1) le_rfl).2.2).trans_eq
        (by rw [← pow_add]; congr 1; omega))

private lemma pow_four_mul_le_seven_sq {ℓ r : ℕ} (hr : r ≤ ℓ) :
    (4 * ℓ) ^ r * 2 ^ (4 * ℓ) ≤ 2 ^ (7 * ℓ ^ 2) := by
  rcases eq_or_ne ℓ 0 with rfl | h0
  · obtain rfl : r = 0 := by omega
    norm_num
  · have h4 : 4 * ℓ ≤ 2 ^ (3 * ℓ) :=
      (Nat.mul_le_mul_left 4 Nat.lt_two_pow_self.le).trans
        ((pow_add 2 2 ℓ).symm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hexp : 3 * ℓ * ℓ + 4 * ℓ ≤ 7 * ℓ ^ 2 :=
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_left ℓ (by omega : 0 < ℓ))) _).trans_eq (by ring)
    calc (4 * ℓ) ^ r * 2 ^ (4 * ℓ)
        ≤ (2 ^ (3 * ℓ)) ^ ℓ * 2 ^ (4 * ℓ) := Nat.mul_le_mul_right _
            ((Nat.pow_le_pow_left h4 r).trans (Nat.pow_le_pow_right Nat.one_le_two_pow hr))
      _ = 2 ^ (3 * ℓ * ℓ + 4 * ℓ) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (7 * ℓ ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp

private lemma parityDivStep_iterate_bounds (ℓ s : ℕ) (hs : s ≤ ℓ) :
    let st := ParityFactorEval.parityDivStep^[s] (parityPolyCoeffs ℓ, [])
    st.1.length ≤ 4 * ℓ ∧ st.2.length = s ∧ polyNorm1 st.1 ≤ (4 * ℓ) ^ s * 2 ^ (4 * ℓ) ∧
      ∀ ab ∈ st.2, ab.1.natAbs ≤ 2 ^ (7 * ℓ ^ 2) ∧ ab.2.natAbs ≤ 2 ^ (7 * ℓ ^ 2) := by
  induction s with
  | zero =>
    refine ⟨length_parityPolyCoeffs_le ℓ, rfl, ?_, fun _ h => False.elim (List.not_mem_nil h)⟩
    simpa only [Function.iterate_zero, id_eq, pow_zero, one_mul] using
      polyNorm1_parityPolyCoeffs_le ℓ
  | succ s ih =>
    set st := ParityFactorEval.parityDivStep^[s] (parityPolyCoeffs ℓ, [])
    rcases ih (by omega) with ⟨hlen1, hlen2, hnorm, hmem⟩
    rw [show ParityFactorEval.parityDivStep^[s + 1] (parityPolyCoeffs ℓ, []) =
      ((divModByH st.1).1, st.2 ++ [(divModByH st.1).2]) from
      Function.iterate_succ_apply' ParityFactorEval.parityDivStep s _]
    refine ⟨(length_divModByH_fst st.1).trans_le hlen1,
      by simp only [List.length_append, List.length_singleton, hlen2],
      (polyNorm1_divModByH_fst_le st.1).trans
        ((Nat.mul_le_mul hlen1 hnorm).trans_eq (by rw [pow_succ']; ring)), fun ab hab => ?_⟩
    rcases List.mem_append.mp hab with hprev | hnew
    · exact hmem ab hprev
    · rw [List.mem_singleton] at hnew; subst hnew
      have hdm := natAbs_divModByH_snd_le st.1
      have hcap := hnorm.trans (pow_four_mul_le_seven_sq (by omega : s ≤ ℓ))
      exact ⟨hdm.1.trans hcap, hdm.2.trans hcap⟩

/-- **Coefficient magnitude bound** ([OpenAI2026ETH], Lemma B.1): every pair $(a_s, b_s)$ in
`parityLinearCoeffs ℓ` has $|a_s|, |b_s| \le 2^{7 \ell^2}$. -/
theorem natAbs_mem_parityLinearCoeffs_le {ℓ : ℕ} {ab : ℤ × ℤ}
    (hab : ab ∈ parityLinearCoeffs ℓ) :
    ab.1.natAbs ≤ 2 ^ (7 * ℓ ^ 2) ∧ ab.2.natAbs ≤ 2 ^ (7 * ℓ ^ 2) :=
  (parityDivStep_iterate_bounds ℓ ℓ le_rfl).2.2.2 ab hab

private lemma natAbs_getD_parityLinearCoeffs_le (ℓ s : ℕ) :
    ((parityLinearCoeffs ℓ).getD s (0, 0)).1.natAbs ≤ 2 ^ (7 * ℓ ^ 2) ∧
      ((parityLinearCoeffs ℓ).getD s (0, 0)).2.natAbs ≤ 2 ^ (7 * ℓ ^ 2) := by
  by_cases hs : s < (parityLinearCoeffs ℓ).length
  · rw [List.getD_eq_getElem _ (0, 0) hs]
    exact natAbs_mem_parityLinearCoeffs_le (List.getElem_mem hs)
  · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- **Coefficient bit-length bound** ([OpenAI2026ETH], Lemma B.1): every coefficient in
`parityLinearCoeffs ℓ` uses at most $7 \ell^2 + 2$ bits under `encIntBin`. -/
theorem length_encIntBin_mem_parityLinearCoeffs_le {ℓ : ℕ} {ab : ℤ × ℤ}
    (hab : ab ∈ parityLinearCoeffs ℓ) :
    (encIntBin ab.1).length ≤ 7 * ℓ ^ 2 + 2 ∧ (encIntBin ab.2).length ≤ 7 * ℓ ^ 2 + 2 := by
  obtain ⟨h1, h2⟩ := natAbs_mem_parityLinearCoeffs_le hab
  exact ⟨length_encIntBin_le_of_natAbs_le h1, length_encIntBin_le_of_natAbs_le h2⟩

/-! ### Staged fixed-denominator factor jet evaluation (`evalParityFactorJet`) -/

/-- Truncate or zero-pad a 1D integer $z$-jet to length $J$. -/
def truncZJet (J : ℕ) (u : List ℤ) : List ℤ := (List.range J).map fun j => u.getD j 0

/-- 1D truncated $z$-jet power $u^s \bmod z^J$ of length $J$. -/
def powZJet (J : ℕ) (u : List ℤ) (s : ℕ) : List ℤ := (mulZJet J u)^[s] (truncZJet J [1])

/-- Column-$s$ cleared $z$-jet $\Delta^{2 (\ell - 1 - s)} (\Delta a_s + b_s Y) (Y (Y - \Delta))^s$
of length $J$. -/
def ParityFactorEval.colJet (J ℓ : ℕ) (Δ : ℤ) (yJet : List ℤ) (coeffs : List (ℤ × ℤ))
    (hJet : List ℤ) (s : ℕ) : List ℤ :=
  let ab := coeffs.getD s (0, 0)
  let linJet := polyAdd [Δ * ab.1] (polyMul [ab.2] (truncZJet J yJet))
  mulZJet J [Δ ^ (2 * (ℓ - 1 - s))] (mulZJet J linJet (powZJet J hJet s))

/-- Column list `(colJet ... s)_{s < ℓ}` for `evalParityFactorJet`. -/
def ParityFactorEval.cols (J ℓ : ℕ) (Δ : ℤ) (yJet : List ℤ) : List (List ℤ) :=
  let coeffs := parityLinearCoeffs ℓ
  let yTrunc := truncZJet J yJet
  let hJet := mulZJet J yTrunc (polyAdd yTrunc [-Δ])
  (List.range ℓ).map fun s => ParityFactorEval.colJet J ℓ Δ yJet coeffs hJet s

/-- Staged fixed-denominator parity-factor jet evaluation ([OpenAI2026ETH], Appendix B.2): returns
a $J \times \ell$ integer table (`J` rows of length `ℓ`) whose entry `(j, s)` (`j < J`, `s < ℓ`) is
unconditionally (including when $\Delta = 0$) the $z^j$ coefficient of the homogenized integer
polynomial $\Delta^{2 (\ell - 1 - s)} (\Delta a_s + b_s \widetilde{Y}(z))
(\widetilde{Y}(z) (\widetilde{Y}(z) - \Delta))^s \bmod z^J$ for
$\widetilde{Y}(z) = \sum_{r < J} \text{yJet}[r] z^r$. When $\Delta \ne 0$, this equals the $z^j$
coefficient of $\Gamma \cdot (a_s + b_s Y(z)) (Y(z) (Y(z) - 1))^s \bmod z^J$ for
$Y(z) = \Delta^{-1} \widetilde{Y}(z)$ and $\Gamma = \Delta^{2 \ell - 1}$ (see
`evalParityFactorJet_entry_cast_rat`; for $\Delta = 0$, e.g.
`evalParityFactorJet 1 1 0 [1] = [[-1]]`, whereas the rational expression has $\Gamma = 0$). -/
def evalParityFactorJet (J ℓ : ℕ) (Δ : ℤ) (yJet : List ℤ) : List (List ℤ) :=
  let cols := ParityFactorEval.cols J ℓ Δ yJet
  tabulateTable J ℓ fun j s => rowEntry cols s j

/-- `truncZJet J u` has length `J`. -/
@[simp] theorem length_truncZJet (J : ℕ) (u : List ℤ) : (truncZJet J u).length = J := by
  simp only [truncZJet, List.length_map, List.length_range]

/-- `powZJet J u s` has length `J`. -/
@[simp] theorem length_powZJet (J : ℕ) (u : List ℤ) (s : ℕ) : (powZJet J u s).length = J := by
  induction s with
  | zero => simp only [powZJet, Function.iterate_zero, id_eq, length_truncZJet]
  | succ s _ => simp only [powZJet, Function.iterate_succ_apply', length_mulZJet]

/-- `evalParityFactorJet J ℓ Δ yJet` has rectangular shape `J × ℓ`. -/
theorem isTableShape_evalParityFactorJet (J ℓ : ℕ) (Δ : ℤ) (yJet : List ℤ) :
    IsTableShape J ℓ (evalParityFactorJet J ℓ Δ yJet) :=
  isTableShape_tabulateTable J ℓ _

/-- `truncZJet J u` represents `u.take J` under `Polynomial.ofCoeffList`. -/
theorem ofCoeffList_truncZJet (J : ℕ) (u : List ℤ) :
    ofCoeffList (truncZJet J u) = ofCoeffList (u.take J) := by
  ext k; rw [coeff_ofCoeffList, coeff_ofCoeffList]; by_cases hk : k < J
  · rw [truncZJet, List.getD_map_range _ 0 hk, getD_take_of_lt u hk]
  · rw [List.getD_eq_default (truncZJet J u) _ (by rw [length_truncZJet]; omega),
      List.getD_eq_default (u.take J) _ (by simp only [List.length_take]; omega)]

/-- Polynomial multiplication preserves coefficient equality below degree `J`. -/
theorem coeff_eq_below_mul {P₁ P₂ Q₁ Q₂ : ℤ[X]} {J : ℕ}
    (h1 : ∀ i < J, P₁.coeff i = Q₁.coeff i) (h2 : ∀ i < J, P₂.coeff i = Q₂.coeff i) :
    ∀ j < J, (P₁ * P₂).coeff j = (Q₁ * Q₂).coeff j := by
  intro j hj; rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have := Finset.mem_antidiagonal.mp hkl; rw [h1 kl.1 (by omega), h2 kl.2 (by omega)]

/-- Coefficient specification of `powZJet` on degree-$< J$ prefixes. -/
theorem getD_powZJet_of_lt {J j : ℕ} (hj : j < J) (u : List ℤ) (s : ℕ) :
    (powZJet J u s).getD j 0 = (ofCoeffList (u.take J) ^ s).coeff j := by
  revert j; induction s with
  | zero =>
    intro j hj
    have h1 : ofCoeffList ([1] : List ℤ) = 1 := by
      simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, map_one]
    have htake : ([1] : List ℤ).take J = [1] :=
      List.take_of_length_le (by simp only [List.length_singleton]; omega)
    simpa only [powZJet, Function.iterate_zero, id_eq, pow_zero, ← coeff_ofCoeffList,
      ofCoeffList_truncZJet, htake] using congrArg (fun P => P.coeff j) h1
  | succ s ih =>
    intro j hj
    rw [show powZJet J u (s + 1) = mulZJet J u (powZJet J u s) from
      Function.iterate_succ_apply' (mulZJet J u) s (truncZJet J [1]), getD_mulZJet_of_lt hj,
      List.take_of_length_le (l := powZJet J u s) (by rw [length_powZJet]), pow_succ']
    exact coeff_eq_below_mul (fun _ _ => rfl) (fun i hi => by rw [coeff_ofCoeffList, ih hi]) j hj

private lemma rowEntry_evalParityFactorJet_eq {J ℓ j s : ℕ} (hj : j < J) (hs : s < ℓ)
    (Δ : ℤ) (yJet : List ℤ) :
    rowEntry (evalParityFactorJet J ℓ Δ yJet) j s =
      (ParityFactorEval.colJet J ℓ Δ yJet (parityLinearCoeffs ℓ)
        (mulZJet J (truncZJet J yJet) (polyAdd (truncZJet J yJet) [-Δ])) s).getD j 0 := by
  rw [evalParityFactorJet, rowEntry_tabulateTable_of_lt _ hj hs, rowEntry, ParityFactorEval.cols,
    List.getD_map_range _ [] hs]

private lemma row_sum_evalParityFactorJet {J ℓ j : ℕ} (hj : j < J) (Δ : ℤ) (yJet : List ℤ) :
    ((evalParityFactorJet J ℓ Δ yJet).getD j []).sum =
      ∑ s ∈ Finset.range ℓ, rowEntry (evalParityFactorJet J ℓ Δ yJet) j s := by
  have hshape := isTableShape_evalParityFactorJet J ℓ Δ yJet
  have hjlen : j < (evalParityFactorJet J ℓ Δ yJet).length := hshape.1.symm ▸ hj
  have hrow_len : ((evalParityFactorJet J ℓ Δ yJet).getD j []).length = ℓ := by
    rw [List.getD_eq_getElem _ [] hjlen]
    exact hshape.2 _ (List.getElem_mem hjlen)
  conv_lhs => rw [eq_map_range_getD hrow_len]
  exact sum_map_range_eq_finset ℓ _

/-- **Polynomial-in-$z$ specification of `evalParityFactorJet`** modulo $z^J$. -/
theorem evalParityFactorJet_entry_eq_coeff {J ℓ j s : ℕ} (hj : j < J) (hs : s < ℓ)
    (Δ : ℤ) (yJet : List ℤ) :
    rowEntry (evalParityFactorJet J ℓ Δ yJet) j s =
      let ab := (parityLinearCoeffs ℓ).getD s (0, 0)
      let Y := ofCoeffList (yJet.take J)
      (C (Δ ^ (2 * (ℓ - 1 - s))) *
        ((C (Δ * ab.1) + C ab.2 * Y) * (Y * (Y - C Δ)) ^ s)).coeff j := by
  rw [rowEntry_evalParityFactorJet_eq hj hs Δ yJet]; dsimp only [ParityFactorEval.colJet]
  set ab := (parityLinearCoeffs ℓ).getD s (0, 0); set Y := ofCoeffList (yJet.take J)
  set hJet := mulZJet J (truncZJet J yJet) (polyAdd (truncZJet J yJet) [-Δ])
  have hc (z : ℤ) : ofCoeffList [z] = C z := by
    simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero]
  have hlin : ofCoeffList (polyAdd [Δ * ab.1] (polyMul [ab.2] (truncZJet J yJet))) =
      C (Δ * ab.1) + C ab.2 * Y := by
    rw [ofCoeffList_polyAdd, ofCoeffList_polyMul, ofCoeffList_truncZJet, hc, hc]
  have hh (i : ℕ) (hi : i < J) : (ofCoeffList hJet).coeff i = (Y * (Y - C Δ)).coeff i := by
    rw [coeff_ofCoeffList_mulZJet hi, ofCoeffList_polyAdd, ofCoeffList_truncZJet, hc, map_neg,
      sub_eq_add_neg]
  have hpow : ∀ r, ∀ i < J, (ofCoeffList (hJet.take J) ^ r).coeff i =
      ((Y * (Y - C Δ)) ^ r).coeff i := by
    intro r; rw [List.take_of_length_le (l := hJet) (by rw [length_mulZJet])]
    induction r with
    | zero => intro _ _; simp only [pow_zero]
    | succ r ihr => intro i hi; rw [pow_succ', pow_succ']; exact coeff_eq_below_mul hh ihr i hi
  rw [← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet hj, hc]
  refine coeff_eq_below_mul (fun _ _ => rfl) (fun i hi => ?_) j hj
  rw [coeff_ofCoeffList_mulZJet hi, hlin]
  exact coeff_eq_below_mul (fun _ _ => rfl)
    (fun k hk => by rw [coeff_ofCoeffList, getD_powZJet_of_lt hk, hpow s k hk]) i hi

/-- **Stage-2 to Stage-3 bridge** ([OpenAI2026ETH], §5.4 and Appendix B.2): for every $j < J$ and
all $\ell, s \in \mathbb{N}$, entry $(j, s)$ of `evalParityFactorJet J ℓ Δ yJet` equals the $z^j$
coefficient of the $V^s$ coefficient of `Cslib.BitString.parityFactorCleared`. -/
theorem evalParityFactorJet_entry_eq_parityFactorCleared {J j : ℕ} (hj : j < J) (ℓ s : ℕ)
    (Δ : ℤ) (yJet : List ℤ) :
    rowEntry (evalParityFactorJet J ℓ Δ yJet) j s =
      ((Cslib.BitString.parityFactorCleared ℓ (C Δ) (ofCoeffList (yJet.take J))).coeff s).coeff
        j := by
  by_cases hs : s < ℓ
  · rw [evalParityFactorJet_entry_eq_coeff hj hs Δ yJet, Cslib.BitString.coeff_parityFactorCleared,
      ite_eq_left hs]
    dsimp only
    rw [getD_parityLinearCoeffs_eq_parityBaseDigit, Cslib.BitString.parityBaseDigitCleared,
      Cslib.BitString.hPolyCleared]
    dsimp only
    refine congrArg (fun P : ℤ[X] => P.coeff j) ?_
    have hcast (c : ℤ) : (c : ℤ[X]) = C c := (eq_intCast C c).symm
    rw [hcast, hcast, ← C_pow, C_mul]
    ring
  · rw [rowEntry_eq_zero_of_isTableShape (isTableShape_evalParityFactorJet J ℓ Δ yJet) (by omega),
      Cslib.BitString.coeff_parityFactorCleared, ite_eq_right hs, coeff_zero]

private lemma map_intCast_C (z : ℤ) : (C z : ℤ[X]).map (Int.castRingHom ℚ) = C (z : ℚ) := by
  simpa only [eq_intCast] using Polynomial.map_C (Int.castRingHom ℚ) (a := z)

/-- **Rational $z$-jet homogenization identity** ([OpenAI2026ETH], Appendix B.2) for $\Delta \ne 0$
and $Y_{\mathbb{Q}}(z) = \Delta^{-1} \widetilde{Y}(z) \in \mathbb{Q}[X]$. -/
theorem evalParityFactorJet_entry_cast_rat {J ℓ j s : ℕ} (hℓ : 1 ≤ ℓ) (hj : j < J) (hs : s < ℓ)
    {Δ : ℤ} (hΔ : Δ ≠ 0) (yJet : List ℤ) :
    let ab := (parityLinearCoeffs ℓ).getD s (0, 0)
    let YQ : ℚ[X] := C (Δ : ℚ)⁻¹ * (ofCoeffList (yJet.take J)).map (Int.castRingHom ℚ)
    ((rowEntry (evalParityFactorJet J ℓ Δ yJet) j s : ℤ) : ℚ) =
      (C ((Δ : ℚ) ^ (2 * ℓ - 1)) *
        ((C (ab.1 : ℚ) + C (ab.2 : ℚ) * YQ) * (YQ * (YQ - 1)) ^ s)).coeff j := by
  dsimp only; rw [evalParityFactorJet_entry_eq_coeff hj hs Δ yJet]; dsimp only
  set ab := (parityLinearCoeffs ℓ).getD s (0, 0); set Y := ofCoeffList (yJet.take J)
  set Y' : ℚ[X] := Y.map (Int.castRingHom ℚ); set δ : ℚ := (Δ : ℚ); set YQ : ℚ[X] := C δ⁻¹ * Y'
  have hδ : δ ≠ 0 := Int.cast_ne_zero.mpr hΔ
  have hY' : Y' = C δ * YQ := by
    dsimp only [YQ]; rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hδ, map_one, one_mul]
  let P : ℤ[X] := C (Δ ^ (2 * (ℓ - 1 - s))) * ((C (Δ * ab.1) + C ab.2 * Y) * (Y * (Y - C Δ)) ^ s)
  have hcast : ((P.coeff j : ℤ) : ℚ) = (P.map (Int.castRingHom ℚ)).coeff j := by
    simp only [Polynomial.coeff_map, eq_intCast]
  change ((P.coeff j : ℤ) : ℚ) = _; rw [hcast]; congr 2
  have hPmap : P.map (Int.castRingHom ℚ) =
      C (δ ^ (2 * (ℓ - 1 - s))) * ((C (δ * ab.1) + C (ab.2 : ℚ) * Y') * (Y' * (Y' - C δ)) ^ s) := by
    dsimp only [P]; simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, map_intCast_C, Int.cast_pow, Int.cast_mul]; rfl
  have hhq : C δ * YQ * (C δ * YQ - C δ) = C (δ ^ 2) * (YQ * (YQ - 1)) := by
    rw [pow_two, C_mul]; ring
  rw [hPmap, hY', show C (δ * ab.1) + C (ab.2 : ℚ) * (C δ * YQ) =
      C δ * (C (ab.1 : ℚ) + C (ab.2 : ℚ) * YQ) by rw [C_mul]; ring,
    show (C δ * YQ * (C δ * YQ - C δ)) ^ s = C (δ ^ (2 * s)) * (YQ * (YQ - 1)) ^ s by
      rw [hhq, mul_pow, ← C_pow, ← pow_mul]]
  have hC : C (δ ^ (2 * (ℓ - 1 - s))) * C δ * C (δ ^ (2 * s)) = C (δ ^ (2 * ℓ - 1)) := by
    rw [← C_mul, ← C_mul, ← pow_succ, ← pow_add,
      show 2 * (ℓ - 1 - s) + 1 + 2 * s = 2 * ℓ - 1 by omega]
  calc C (δ ^ (2 * (ℓ - 1 - s))) *
        (C δ * (C (ab.1 : ℚ) + C (ab.2 : ℚ) * YQ) * (C (δ ^ (2 * s)) * (YQ * (YQ - 1)) ^ s))
      = (C (δ ^ (2 * (ℓ - 1 - s))) * C δ * C (δ ^ (2 * s))) *
          ((C (ab.1 : ℚ) + C (ab.2 : ℚ) * YQ) * (YQ * (YQ - 1)) ^ s) := by ring
    _ = C (δ ^ (2 * ℓ - 1)) * ((C (ab.1 : ℚ) + C (ab.2 : ℚ) * YQ) * (YQ * (YQ - 1)) ^ s) := by
          rw [hC]

/-- Summing row $j < J$ of `evalParityFactorJet` ($V = 1$) gives the $z^j$ coefficient of
$\Delta^{2 \ell - 1} p_\ell(Y_{\mathbb{Q}}(z))$ over $\mathbb{Q}[X]$. -/
theorem evalParityFactorJet_row_sum_cast_rat {J ℓ j : ℕ} (hℓ : 1 ≤ ℓ) (hj : j < J)
    {Δ : ℤ} (hΔ : Δ ≠ 0) (yJet : List ℤ) :
    let YQ : ℚ[X] := C (Δ : ℚ)⁻¹ * (ofCoeffList (yJet.take J)).map (Int.castRingHom ℚ)
    ((((evalParityFactorJet J ℓ Δ yJet).getD j []).sum : ℤ) : ℚ) =
      (C ((Δ : ℚ) ^ (2 * ℓ - 1)) *
        ((ofCoeffList (parityPolyCoeffs ℓ)).map (Int.castRingHom ℚ)).comp YQ).coeff j := by
  dsimp only; set YQ : ℚ[X] := C (Δ : ℚ)⁻¹ * (ofCoeffList (yJet.take J)).map (Int.castRingHom ℚ)
  rw [row_sum_evalParityFactorJet hj Δ yJet, Int.cast_sum]
  have hterms :
      ∑ s ∈ Finset.range ℓ, ((rowEntry (evalParityFactorJet J ℓ Δ yJet) j s : ℤ) : ℚ) =
        ∑ s ∈ Finset.range ℓ,
          (C ((Δ : ℚ) ^ (2 * ℓ - 1)) *
            ((C (((parityLinearCoeffs ℓ).getD s (0, 0)).1 : ℚ) +
              C (((parityLinearCoeffs ℓ).getD s (0, 0)).2 : ℚ) * YQ) *
                (YQ * (YQ - 1)) ^ s)).coeff j :=
    Finset.sum_congr rfl fun s hs =>
      evalParityFactorJet_entry_cast_rat hℓ hj (Finset.mem_range.mp hs) hΔ yJet
  rw [hterms, ← finsetSum_coeff, ← Finset.mul_sum]; congr 3
  rw [ofCoeffList_parityPolyCoeffs_eq_sum ℓ, Polynomial.map_sum, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    map_intCast_C, Polynomial.map_X, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp,
    Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  congr 2; ring

/-- **Constant-in-$z$ ($j = 0$) integer specialization** when $\text{yJet}[0] = \Delta y$. -/
theorem evalParityFactorJet_row_zero_entry {J ℓ s : ℕ} (hJ : 1 ≤ J) (hs : s < ℓ)
    (Δ y : ℤ) {yJet : List ℤ} (hy0 : yJet.getD 0 0 = Δ * y) :
    let ab := (parityLinearCoeffs ℓ).getD s (0, 0)
    rowEntry (evalParityFactorJet J ℓ Δ yJet) 0 s =
      Δ ^ (2 * ℓ - 1) * ((ab.1 + ab.2 * y) * (y * (y - 1)) ^ s) := by
  dsimp only; rw [evalParityFactorJet_entry_eq_coeff (by omega : 0 < J) hs Δ yJet]; dsimp only
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_C, ← Polynomial.coeff_zero_eq_eval_zero,
    coeff_ofCoeffList, getD_take_of_lt yJet (by omega : 0 < J), hy0]
  set ab := (parityLinearCoeffs ℓ).getD s (0, 0)
  rw [show Δ * ab.1 + ab.2 * (Δ * y) = Δ * (ab.1 + ab.2 * y) by ring,
    show (Δ * y * (Δ * y - Δ)) ^ s = Δ ^ (2 * s) * (y * (y - 1)) ^ s by
      rw [show Δ * y * (Δ * y - Δ) = Δ ^ 2 * (y * (y - 1)) by ring, mul_pow, ← pow_mul]]
  calc Δ ^ (2 * (ℓ - 1 - s)) * (Δ * (ab.1 + ab.2 * y) * (Δ ^ (2 * s) * (y * (y - 1)) ^ s))
      = (Δ ^ (2 * (ℓ - 1 - s)) * Δ * Δ ^ (2 * s)) * ((ab.1 + ab.2 * y) * (y * (y - 1)) ^ s) := by
        ring
    _ = Δ ^ (2 * ℓ - 1) * ((ab.1 + ab.2 * y) * (y * (y - 1)) ^ s) := by
        rw [← pow_succ, ← pow_add, show 2 * (ℓ - 1 - s) + 1 + 2 * s = 2 * ℓ - 1 by omega]

/-- Summing row $0$ when $\text{yJet}[0] = \Delta y$ gives $\Delta^{2 \ell - 1} p_\ell(y)$. -/
theorem evalParityFactorJet_row_zero_sum {J ℓ : ℕ} (hJ : 1 ≤ J) (Δ y : ℤ)
    {yJet : List ℤ} (hy0 : yJet.getD 0 0 = Δ * y) :
    ((evalParityFactorJet J ℓ Δ yJet).getD 0 []).sum =
      Δ ^ (2 * ℓ - 1) * evalParityAmplifier ℓ y := by
  rw [row_sum_evalParityFactorJet (by omega : 0 < J) Δ yJet, evalParityAmplifier,
    sum_map_range_eq_finset, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s hs =>
    evalParityFactorJet_row_zero_entry hJ (Finset.mem_range.mp hs) Δ y hy0

/-! ### Prefix $\ell_1$-norm and bit-length bounds for `evalParityFactorJet` (Appendix B.2) -/

/-- `truncZJet` preserves the prefix $\ell_1$-norm. -/
theorem polyNorm1_truncZJet (J : ℕ) (u : List ℤ) :
    polyNorm1 (truncZJet J u) = polyNorm1 (u.take J) := by
  induction J generalizing u with
  | zero => simp only [truncZJet, List.range_zero, List.map_nil, List.take_zero, polyNorm1_nil]
  | succ J ih =>
    cases u with
    | nil =>
      rw [List.take_nil, polyNorm1_nil, polyNorm1]; apply List.sum_eq_zero
      intro _ hx; obtain ⟨_, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hz; simp only [List.getD_nil, Int.natAbs_zero]
    | cons a rest =>
      rw [truncZJet, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero, List.map_map,
        List.take_succ_cons, polyNorm1_cons, polyNorm1_cons,
        show (List.range J).map ((fun j => (a :: rest).getD j 0) ∘ Nat.succ) = truncZJet J rest from
          List.map_congr_left fun j _ => by
            simp only [Function.comp_apply, Nat.succ_eq_add_one, List.getD_cons_succ],
        ih rest]

/-- Powering bound for `powZJet` under `polyNorm1`. -/
theorem polyNorm1_powZJet_le (J : ℕ) (u : List ℤ) (s : ℕ) :
    polyNorm1 (powZJet J u s) ≤ (polyNorm1 (u.take J)) ^ s := by
  induction s with
  | zero =>
    rw [powZJet, Function.iterate_zero, id_eq, polyNorm1_truncZJet, pow_zero]
    exact (polyNorm1_take_le [1] J).trans (by simp only [polyNorm1_cons, polyNorm1_nil,
      Int.natAbs_one, add_zero, le_rfl])
  | succ s ih =>
    simp only [powZJet, Function.iterate_succ_apply'] at ih ⊢
    exact (polyNorm1_mulZJet_le _ _ _).trans
      ((Nat.mul_le_mul_left _ ((polyNorm1_take_le _ J).trans ih)).trans_eq (pow_succ' _ s).symm)

private lemma polyNorm1_parityFactorColJet_le {J ℓ s : ℕ} (hs : s < ℓ) (Δ : ℤ) (yJet : List ℤ) :
    polyNorm1 (ParityFactorEval.colJet J ℓ Δ yJet (parityLinearCoeffs ℓ)
      (mulZJet J (truncZJet J yJet) (polyAdd (truncZJet J yJet) [-Δ])) s) ≤
        2 ^ (7 * ℓ ^ 2) * (polyNorm1 (yJet.take J) + Δ.natAbs + 2) ^ (2 * ℓ - 1) := by
  set yT := truncZJet J yJet; set B := polyNorm1 (yJet.take J); set M := B + Δ.natAbs + 2
  set ab := (parityLinearCoeffs ℓ).getD s (0, 0); set hJet := mulZJet J yT (polyAdd yT [-Δ])
  have hyT : polyNorm1 yT = B := polyNorm1_truncZJet J yJet
  have hc (z : ℤ) : polyNorm1 [z] = z.natAbs := by
    simp only [polyNorm1_cons, polyNorm1_nil, add_zero]
  have hab := natAbs_getD_parityLinearCoeffs_le ℓ s
  have hlin : polyNorm1 (polyAdd [Δ * ab.1] (polyMul [ab.2] yT)) ≤ 2 ^ (7 * ℓ ^ 2) * M := by
    calc polyNorm1 (polyAdd [Δ * ab.1] (polyMul [ab.2] yT))
        ≤ (Δ * ab.1).natAbs + polyNorm1 [ab.2] * polyNorm1 yT :=
          (polyNorm1_polyAdd_le _ _).trans (Nat.add_le_add (by rw [hc]) (polyNorm1_polyMul_le _ _))
      _ = Δ.natAbs * ab.1.natAbs + ab.2.natAbs * B := by rw [Int.natAbs_mul, hc, hyT]
      _ ≤ Δ.natAbs * 2 ^ (7 * ℓ ^ 2) + 2 ^ (7 * ℓ ^ 2) * B :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hab.1) (Nat.mul_le_mul_right _ hab.2)
      _ ≤ 2 ^ (7 * ℓ ^ 2) * M := by
          rw [show Δ.natAbs * 2 ^ (7 * ℓ ^ 2) + 2 ^ (7 * ℓ ^ 2) * B =
            2 ^ (7 * ℓ ^ 2) * (B + Δ.natAbs) by ring]; exact Nat.mul_le_mul_left _ (by omega)
  have hh : polyNorm1 hJet ≤ M ^ 2 := by
    have hsub : polyNorm1 (polyAdd yT [-Δ]) ≤ B + Δ.natAbs :=
      (polyNorm1_polyAdd_le _ _).trans_eq (by rw [hyT, hc, Int.natAbs_neg])
    exact (polyNorm1_mulZJet_le _ _ _).trans
      ((Nat.mul_le_mul ((polyNorm1_take_le _ J).trans_eq hyT)
        ((polyNorm1_take_le _ J).trans hsub)).trans
        ((Nat.mul_le_mul (by omega) (by omega)).trans_eq (pow_two M).symm))
  have hpow : polyNorm1 (powZJet J hJet s) ≤ M ^ (2 * s) :=
    (polyNorm1_powZJet_le _ _ _).trans
      ((Nat.pow_le_pow_left ((polyNorm1_take_le _ J).trans hh) s).trans_eq (pow_mul M 2 s).symm)
  have hmul : polyNorm1 (mulZJet J (polyAdd [Δ * ab.1] (polyMul [ab.2] yT)) (powZJet J hJet s)) ≤
      2 ^ (7 * ℓ ^ 2) * M ^ (2 * s + 1) :=
    (polyNorm1_mulZJet_le _ _ _).trans
      ((Nat.mul_le_mul ((polyNorm1_take_le _ J).trans hlin)
        ((polyNorm1_take_le _ J).trans hpow)).trans_eq (by rw [pow_succ']; ring))
  have hscale : polyNorm1 ([Δ ^ (2 * (ℓ - 1 - s))].take J) ≤ M ^ (2 * (ℓ - 1 - s)) :=
    (polyNorm1_take_le _ J).trans ((hc _).trans_le (Int.natAbs_pow_le (by omega) (by omega) le_rfl))
  dsimp only [ParityFactorEval.colJet]
  refine (polyNorm1_mulZJet_le _ _ _).trans
    ((Nat.mul_le_mul hscale ((polyNorm1_take_le _ J).trans hmul)).trans_eq ?_)
  rw [show M ^ (2 * (ℓ - 1 - s)) * (2 ^ (7 * ℓ ^ 2) * M ^ (2 * s + 1)) =
      2 ^ (7 * ℓ ^ 2) * (M ^ (2 * (ℓ - 1 - s)) * M ^ (2 * s + 1)) by ring,
    ← pow_add, show 2 * (ℓ - 1 - s) + (2 * s + 1) = 2 * ℓ - 1 by omega]

/-- **Total factor-table $\ell_1$-norm bound** ([OpenAI2026ETH], Appendix B.2, bound $B_1$). -/
theorem jetL1Norm_evalParityFactorJet_le (J ℓ : ℕ) (Δ : ℤ) (yJet : List ℤ) :
    jetL1Norm (evalParityFactorJet J ℓ Δ yJet) ≤
      ℓ * 2 ^ (7 * ℓ ^ 2) * (polyNorm1 (yJet.take J) + Δ.natAbs + 2) ^ (2 * ℓ - 1) := by
  set hJet := mulZJet J (truncZJet J yJet) (polyAdd (truncZJet J yJet) [-Δ])
  have hswap : jetL1Norm (evalParityFactorJet J ℓ Δ yJet) =
      ∑ s ∈ Finset.range ℓ,
        polyNorm1 (ParityFactorEval.colJet J ℓ Δ yJet (parityLinearCoeffs ℓ) hJet s) := by
    rw [evalParityFactorJet, jetL1Norm_tabulateTable, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hslt : s < ℓ := Finset.mem_range.mp hs
    set col := ParityFactorEval.colJet J ℓ Δ yJet (parityLinearCoeffs ℓ) hJet s
    have hcol_eq : (ParityFactorEval.cols J ℓ Δ yJet).getD s [] = col := by
      rw [ParityFactorEval.cols, List.getD_map_range _ [] hslt]
    have hlen : col.length = J := by simp only [col, ParityFactorEval.colJet, length_mulZJet]
    unfold polyNorm1 rowEntry
    conv_rhs => rw [eq_map_range_getD hlen]
    simp only [hcol_eq, List.map_map, Function.comp_def, sum_map_range_eq_finset]
  rw [hswap]
  refine (Finset.sum_le_sum fun s hs =>
    polyNorm1_parityFactorColJet_le (Finset.mem_range.mp hs) Δ yJet).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

private lemma polyNorm1_mem_le_jetL1Norm {rows : List (List ℤ)} {r : List ℤ} (hr : r ∈ rows) :
    polyNorm1 r ≤ jetL1Norm rows := by
  rw [jetL1Norm_eq_sum_map_polyNorm1]
  exact List.le_sum_of_mem (List.mem_map_of_mem hr)

/-- Prefix-sum magnitude bound for every row of `evalParityFactorJet` ([OpenAI2026ETH],
Appendix B.2). -/
theorem natAbs_row_take_sum_evalParityFactorJet_le {J ℓ : ℕ} {Δ : ℤ} {yJet r : List ℤ}
    (hr : r ∈ evalParityFactorJet J ℓ Δ yJet) (m : ℕ) :
    (r.take m).sum.natAbs ≤
      ℓ * 2 ^ (7 * ℓ ^ 2) * (polyNorm1 (yJet.take J) + Δ.natAbs + 2) ^ (2 * ℓ - 1) :=
  (natAbs_sum_le_polyNorm1 (r.take m)).trans
    ((polyNorm1_take_le r m).trans
      ((polyNorm1_mem_le_jetL1Norm hr).trans (jetL1Norm_evalParityFactorJet_le J ℓ Δ yJet)))

private lemma factorJet_cap_le_two_pow (J ℓ : ℕ) (Δ : ℤ) (yJet : List ℤ) :
    ℓ * 2 ^ (7 * ℓ ^ 2) * (polyNorm1 (yJet.take J) + Δ.natAbs + 2) ^ (2 * ℓ - 1) ≤
      2 ^ (8 * ℓ ^ 2 + 2 * ℓ * (polyNorm1 (yJet.take J) + Δ.natAbs + 2).size) := by
  set M := polyNorm1 (yJet.take J) + Δ.natAbs + 2
  have hMpow : M ^ (2 * ℓ - 1) ≤ 2 ^ (2 * ℓ * M.size) :=
    (Nat.pow_le_pow_left (Nat.lt_size_self M).le _).trans
      ((Nat.pow_le_pow_right Nat.one_le_two_pow (by omega : 2 * ℓ - 1 ≤ 2 * ℓ)).trans_eq
        (by rw [← pow_mul]; congr 1; ring))
  have hexp : ℓ + 7 * ℓ ^ 2 ≤ 8 * ℓ ^ 2 := by
    rcases eq_or_ne ℓ 0 with rfl | h0
    · norm_num
    · exact (Nat.add_le_add_right
        (Nat.le_mul_of_pos_left ℓ (by omega : 0 < ℓ)) _).trans_eq (by ring)
  calc ℓ * 2 ^ (7 * ℓ ^ 2) * M ^ (2 * ℓ - 1)
      ≤ 2 ^ ℓ * 2 ^ (7 * ℓ ^ 2) * 2 ^ (2 * ℓ * M.size) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le) hMpow
    _ = 2 ^ (ℓ + 7 * ℓ ^ 2 + 2 * ℓ * M.size) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ (8 * ℓ ^ 2 + 2 * ℓ * M.size) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hexp _)

/-- **Entry and row-prefix bit-length bound** ([OpenAI2026ETH], Appendix B.2): every entry and row
prefix sum uses $O(\ell^2 + \ell \log(\|\widetilde{y}\|_1 + |\Delta| + 2))$ bits under
`encIntBin`. -/
theorem length_encIntBin_evalParityFactorJet_le {J ℓ : ℕ} {Δ : ℤ} {yJet r : List ℤ}
    (hr : r ∈ evalParityFactorJet J ℓ Δ yJet) (m : ℕ) :
    (encIntBin (r.take m).sum).length ≤
        8 * ℓ ^ 2 + 2 * ℓ * (polyNorm1 (yJet.take J) + Δ.natAbs + 2).size + 2 ∧
      ∀ z ∈ r, (encIntBin z).length ≤
        8 * ℓ ^ 2 + 2 * ℓ * (polyNorm1 (yJet.take J) + Δ.natAbs + 2).size + 2 := by
  have hcap := factorJet_cap_le_two_pow J ℓ Δ yJet
  refine ⟨length_encIntBin_le_of_natAbs_le
    ((natAbs_row_take_sum_evalParityFactorJet_le hr m).trans hcap), fun z hz => ?_⟩
  exact length_encIntBin_le_of_natAbs_le
    (((natAbs_le_jetL1Norm_of_mem hr hz).trans
      (jetL1Norm_evalParityFactorJet_le J ℓ Δ yJet)).trans hcap)

/-! ### Plain polynomial-time certificates (`ComputableInPolyTime`) -/

section PolyTime

open Turing MultiTapeTM MultiTapeTM.ComputableInPolyTime

variable {α : Type} {encIn : α ↪ List Bool}

@[local fun_prop]
private theorem length_listIntBin {l : α → List ℤ}
    (hl : ComputableInPolyTime l encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => (l x).length) encIn encUnary :=
  (length_list encIntBin).comp hl

private theorem cons_polytime {β : Type} {encB : β ↪ List Bool} {head : α → β} {tail : α → List β}
    (hh : ComputableInPolyTime head encIn encB)
    (ht : ComputableInPolyTime tail encIn (encList encB)) :
    ComputableInPolyTime (fun x => head x :: tail x) encIn (encList encB) :=
  (show ComputableInPolyTime (fun p : β × List β => p.1 :: p.2)
    (encPair encB (encList encB)) (encList encB) by fun_prop).comp (hh.prod ht)

private theorem listAppend_polytime {β : Type} {encB : β ↪ List Bool} {l r : α → List β}
    (hl : ComputableInPolyTime l encIn (encList encB))
    (hr : ComputableInPolyTime r encIn (encList encB)) :
    ComputableInPolyTime (fun x => l x ++ r x) encIn (encList encB) :=
  (show ComputableInPolyTime (fun p : List β × List β => p.1 ++ p.2)
    (encPair (encList encB) (encList encB)) (encList encB) by fun_prop).comp (hl.prod hr)

private theorem intBin_pow_polytime {base : α → ℤ} {exp : α → ℕ}
    (hb : ComputableInPolyTime base encIn encIntBin)
    (he : ComputableInPolyTime exp encIn encUnary) :
    ComputableInPolyTime (fun x => base x ^ exp x) encIn encIntBin :=
  (show ComputableInPolyTime (fun p : ℤ × ℕ => p.1 ^ p.2)
    (encPair encIntBin encUnary) encIntBin by fun_prop).comp (hb.prod he)

/-- `polyNorm1 l` is bounded exponentially in `(encList encIntBin l).length`. -/
theorem polyNorm1_le_two_pow_encList (l : List ℤ) :
    polyNorm1 l ≤ 2 ^ (2 * (encList encIntBin l).length) := by
  set L := (encList encIntBin l).length
  have helem (z : ℤ) (hz : z ∈ l) : z.natAbs ≤ 2 ^ L := by
    have hmem := length_le_encList_of_mem encIntBin hz
    rw [length_encIntBin] at hmem; exact (Nat.size_le.mp (by omega : z.natAbs.size ≤ L)).le
  calc polyNorm1 l ≤ l.length * 2 ^ L := polyNorm1_le_length_mul helem
    _ ≤ L * 2 ^ L := Nat.mul_le_mul_right _ (length_le_length_encList encIntBin l)
    _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (2 * L) := by rw [← pow_add]; congr 1; omega

/-- Polynomial-time certificate for `polyAdd`. -/
@[fun_prop] theorem computableInPolyTime_polyAdd {p q : α → List ℤ}
    (hp : ComputableInPolyTime p encIn (encList encIntBin))
    (hq : ComputableInPolyTime q encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => polyAdd (p x) (q x)) encIn (encList encIntBin) := by
  unfold polyAdd; fun_prop

/-- Polynomial-time certificate for `cauchyCoeff`. -/
@[fun_prop] theorem computableInPolyTime_cauchyCoeff {p q : α → List ℤ} {k : α → ℕ}
    (hp : ComputableInPolyTime p encIn (encList encIntBin))
    (hq : ComputableInPolyTime q encIn (encList encIntBin))
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => cauchyCoeff (p x) (q x) (k x)) encIn encIntBin := by
  unfold cauchyCoeff; fun_prop

/-- Compositional plain polynomial-time certificate for `mulZJet`. -/
@[fun_prop] theorem computableInPolyTime_mulZJet {J : α → ℕ} {u v : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hu : ComputableInPolyTime u encIn (encList encIntBin))
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => mulZJet (J x) (u x) (v x)) encIn (encList encIntBin) := by
  unfold mulZJet; fun_prop

/-- Polynomial-time certificate for `polyMul`. -/
@[fun_prop] theorem computableInPolyTime_polyMul {p q : α → List ℤ}
    (hp : ComputableInPolyTime p encIn (encList encIntBin))
    (hq : ComputableInPolyTime q encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => polyMul (p x) (q x)) encIn (encList encIntBin) :=
  computableInPolyTime_mulZJet (by fun_prop) hp hq

/-- Polynomial-time certificate for monic division by $Y^2 - Y$ (`divModByH`). -/
@[fun_prop] theorem computableInPolyTime_divModByH {p : α → List ℤ}
    (hp : ComputableInPolyTime p encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => divModByH (p x))
      encIn (encPair (encList encIntBin) (encPair encIntBin encIntBin)) := by
  unfold divModByH
  have hrev : ComputableInPolyTime (fun x => (p x).reverse) encIn (encList encIntBin) := by
    fun_prop
  have hstep : ComputableInPolyTime
      (fun p : (List ℤ × (ℤ × ℤ)) × ℤ => ParityFactorEval.divModByHStep p.1 p.2)
      (encPair (encPair (encList encIntBin) (encPair encIntBin encIntBin)) encIntBin)
      (encPair (encList encIntBin) (encPair encIntBin encIntBin)) := by
    unfold ParityFactorEval.divModByHStep; fun_prop
  let bound (L : ℕ) : ℕ := 2 * (L * (4 * L + 5)) + 6 * L + 8
  have hL := hp.polyBounded_length
  have hpoly : PolyBounded (fun x => (encIn x).length)
      (fun x => bound (encList encIntBin (p x)).length) :=
    (((PolyBounded.const 2).mul (hL.mul (((PolyBounded.const 4).mul hL).add (.const 5)))).add
      ((PolyBounded.const 6).mul hL)).add (.const 8)
  refine foldl' hrev (const ([], (0, 0))) hstep hpoly fun x i _ => ?_
  set L := (encList encIntBin (p x)).length; set w := (p x).reverse.take i
  obtain ⟨hlen_st, hrem_st, hmem_st⟩ := foldl_divModByHStep_bounds w
  set st := w.foldl ParityFactorEval.divModByHStep ([], (0, 0))
  change st.2.1.natAbs + st.2.2.natAbs ≤ polyNorm1 w at hrem_st
  have hw_len : w.length ≤ L :=
    (List.length_take_le' i (p x).reverse).trans
      (List.length_reverse.trans_le (length_le_length_encList encIntBin (p x)))
  have hw_norm : polyNorm1 w ≤ 2 ^ (2 * L) :=
    ((polyNorm1_take_le (p x).reverse i).trans_eq (polyNorm1_reverse (p x))).trans
      (polyNorm1_le_two_pow_encList (p x))
  have hq_enc : (encList encIntBin st.1).length ≤ L * (4 * L + 5) :=
    (length_encList_le encIntBin st.1 fun z hz =>
      length_encIntBin_le_of_natAbs_le ((hmem_st z hz).trans hw_norm)).trans
      (by rw [hlen_st, show 2 * (2 * L + 2) + 1 = 4 * L + 5 by omega]
          exact Nat.mul_le_mul_right _ hw_len)
  have ha_enc := length_encIntBin_le_of_natAbs_le (by omega : st.2.1.natAbs ≤ 2 ^ (2 * L))
  have hb_enc := length_encIntBin_le_of_natAbs_le (by omega : st.2.2.natAbs ≤ 2 ^ (2 * L))
  rw [length_encPair, length_encPair]; dsimp only [bound]; omega

private theorem taylorInvOneSubPow_polytime {ℓ : α → ℕ}
    (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime
      (fun x => ParityFactorEval.taylorInvOneSubPow (ℓ x)) encIn (encList encIntBin) := by
  unfold ParityFactorEval.taylorInvOneSubPow
  have hcnt := unary_sub.comp (hℓ.prod (const 1))
  have hinit : ComputableInPolyTime (fun x => List.replicate (ℓ x) (1 : ℤ))
      encIn (encList encIntBin) := by fun_prop
  have hstep : ComputableInPolyTime ParityFactorEval.prefixSumPoly
      (encList encIntBin) (encList encIntBin) := by
    unfold ParityFactorEval.prefixSumPoly; fun_prop
  let bound (k : ℕ) : ℕ := k * (4 * k + 5)
  have hpoly : PolyBounded (fun x => (encIn x).length) (fun x => bound (ℓ x)) :=
    hℓ.polyBounded.mul (((PolyBounded.const 4).mul hℓ.polyBounded).add (.const 5))
  refine iterate hcnt hinit hstep hpoly fun x i hi => ?_
  obtain ⟨hlen, hmem, -⟩ := length_and_norm_taylorIterate (ℓ x) i hi
  exact (length_encList_le encIntBin _ fun z hz =>
    length_encIntBin_le_of_natAbs_le (hmem z hz)).trans_eq
    (by rw [hlen]; dsimp only [bound]; ring)

private theorem oneSubPow_polytime {ℓ : α → ℕ}
    (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime
      (fun x => ParityFactorEval.oneSubPow (ℓ x)) encIn (encList encIntBin) := by
  unfold ParityFactorEval.oneSubPow
  have hstep := computableInPolyTime_polyMul (const [1, -1]) id'
  let bound (k : ℕ) : ℕ := (2 * k + 1) * (2 * k + 5)
  have hpoly : PolyBounded (fun x => (encIn x).length) (fun x => bound (ℓ x)) :=
    (((PolyBounded.const 2).mul hℓ.polyBounded).add (.const 1)).mul
      (((PolyBounded.const 2).mul hℓ.polyBounded).add (.const 5))
  refine iterate hℓ (const [1]) hstep hpoly fun x i hi => ?_
  change (encList encIntBin (ParityFactorEval.oneSubPow i)).length ≤ bound (ℓ x)
  refine (length_encList_le encIntBin _ fun z hz => length_encIntBin_le_of_natAbs_le
    ((natAbs_mem_le_polyNorm1 hz).trans
      ((polyNorm1_oneSubPow_le i).trans (Nat.pow_le_pow_right (by norm_num) hi)))).trans ?_
  rw [length_oneSubPow]; exact Nat.mul_le_mul (by omega) (by omega)

/-- Polynomial-time certificate for `parityPolyCoeffs`. -/
@[fun_prop] theorem computableInPolyTime_parityPolyCoeffs {ℓ : α → ℕ}
    (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime (fun x => parityPolyCoeffs (ℓ x)) encIn (encList encIntBin) := by
  simp_rw [show ∀ k, parityPolyCoeffs k =
      if decide (k = 0) then []
      else polyMul (ParityFactorEval.oneSubPow k) (ParityFactorEval.taylorInvOneSubPow k) from
    fun k => by simp only [parityPolyCoeffs, decide_eq_true_eq]]
  exact (decide_eq' hℓ (const 0)).ite' (const [])
    (computableInPolyTime_polyMul (oneSubPow_polytime hℓ) (taylorInvOneSubPow_polytime hℓ))

/-- Compositional plain polynomial-time certificate for `parityLinearCoeffs`. -/
@[fun_prop] theorem computableInPolyTime_parityLinearCoeffs {ℓ : α → ℕ}
    (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime (fun x => parityLinearCoeffs (ℓ x))
      encIn (encList (encPair encIntBin encIntBin)) := by
  have hpoly_coeffs := computableInPolyTime_parityPolyCoeffs hℓ
  unfold parityLinearCoeffs
  have hdm : ComputableInPolyTime (fun s : List ℤ × List (ℤ × ℤ) => divModByH s.1)
      (encPair (encList encIntBin) (encList (encPair encIntBin encIntBin)))
      (encPair (encList encIntBin) (encPair encIntBin encIntBin)) :=
    computableInPolyTime_divModByH (fst _ _)
  have hstep : ComputableInPolyTime ParityFactorEval.parityDivStep
      (encPair (encList encIntBin) (encList (encPair encIntBin encIntBin)))
      (encPair (encList encIntBin) (encList (encPair encIntBin encIntBin))) :=
    hdm.fst'.prod (listAppend_polytime (snd _ _) (cons_polytime hdm.snd' (const [])))
  let bElem (k : ℕ) : ℕ := 7 * (k * k) + 2
  let bound (k : ℕ) : ℕ :=
    2 * (4 * k * (2 * bElem k + 1)) + 1 + k * (2 * (3 * bElem k + 1) + 1)
  have hk := hℓ.polyBounded
  have hpb_elem := ((PolyBounded.const 7).mul (hk.mul hk)).add (.const 2)
  have hpb_bound : PolyBounded (fun x => (encIn x).length) (fun x => bound (ℓ x)) :=
    (((PolyBounded.const 2).mul (((PolyBounded.const 4).mul hk).mul
      (((PolyBounded.const 2).mul hpb_elem).add (.const 1)))).add (.const 1)).add
      (hk.mul (((PolyBounded.const 2).mul
        (((PolyBounded.const 3).mul hpb_elem).add (.const 1))).add (.const 1)))
  refine (iterate hℓ (hpoly_coeffs.prod (const [])) hstep hpb_bound fun x s hs => ?_).snd'
  set k := ℓ x; set st := ParityFactorEval.parityDivStep^[s] (parityPolyCoeffs k, [])
  obtain ⟨hlen1, hlen2, hnorm1, hmem2⟩ := parityDivStep_iterate_bounds k s hs
  have hsq : 7 * k ^ 2 + 2 = bElem k := by dsimp only [bElem]; ring
  have hcap : polyNorm1 st.1 ≤ 2 ^ (7 * k ^ 2) := hnorm1.trans (pow_four_mul_le_seven_sq hs)
  have hst1_enc : (encList encIntBin st.1).length ≤ 4 * k * (2 * bElem k + 1) :=
    (length_encList_le encIntBin st.1 fun z hz =>
      hsq ▸ length_encIntBin_le_of_natAbs_le ((natAbs_mem_le_polyNorm1 hz).trans hcap)).trans
      (Nat.mul_le_mul_right _ hlen1)
  have hst2_enc :
      (encList (encPair encIntBin encIntBin) st.2).length ≤ k * (2 * (3 * bElem k + 1) + 1) := by
    refine (length_encList_le _ st.2 fun ab hab => ?_).trans
      (Nat.mul_le_mul_right _ (hlen2.trans_le hs))
    obtain ⟨ha, hb⟩ := hmem2 ab hab
    have ha' : (encIntBin ab.1).length ≤ bElem k := hsq ▸ length_encIntBin_le_of_natAbs_le ha
    have hb' : (encIntBin ab.2).length ≤ bElem k := hsq ▸ length_encIntBin_le_of_natAbs_le hb
    rw [length_encPair]; omega
  rw [length_encPair]; dsimp only [bound]; omega

/-- Standalone plain polynomial-time certificate for `parityLinearCoeffs` on unary $\ell$. -/
theorem parityLinearCoeffs_polytime :
    ComputableInPolyTime parityLinearCoeffs encUnary (encList (encPair encIntBin encIntBin)) :=
  computableInPolyTime_parityLinearCoeffs id'

/-- Compositional polynomial-time certificate for `truncZJet`. -/
@[fun_prop] theorem computableInPolyTime_truncZJet {J : α → ℕ} {u : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hu : ComputableInPolyTime u encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => truncZJet (J x) (u x)) encIn (encList encIntBin) := by
  unfold truncZJet; fun_prop

/-- Compositional plain polynomial-time certificate for `powZJet`. -/
@[fun_prop] theorem computableInPolyTime_powZJet {J s : α → ℕ} {u : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hu : ComputableInPolyTime u encIn (encList encIntBin))
    (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime (fun x => powZJet (J x) (u x) (s x)) encIn (encList encIntBin) := by
  have hinit := computableInPolyTime_truncZJet hJ (const [1])
  unfold powZJet
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × List ℤ) × List ℤ => mulZJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encIntBin)) (encList encIntBin)) (encList encIntBin) :=
    computableInPolyTime_mulZJet (fst _ _).fst' (fst _ _).snd' (snd _ _)
  let bElem (Lu k : ℕ) : ℕ := 2 * Lu * k + 2
  let bound (n Lu k : ℕ) : ℕ := n * (2 * bElem Lu k + 1)
  have hpb_bound : PolyBounded (fun x => (encIn x).length)
      (fun x => bound (J x) (encList encIntBin (u x)).length (s x)) :=
    hJ.polyBounded.mul (((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul hu.polyBounded_length).mul hs.polyBounded).add (.const 2))).add
      (.const 1))
  refine iterateWith (step := fun par acc => mulZJet par.1 par.2 acc)
    (hJ.prod hu) hs hinit hstep hpb_bound fun x i hi => ?_
  change (encList encIntBin (powZJet (J x) (u x) i)).length ≤
    bound (J x) (encList encIntBin (u x)).length (s x)
  set Lu := (encList encIntBin (u x)).length
  have hnorm : polyNorm1 (powZJet (J x) (u x) i) ≤ 2 ^ (2 * Lu * s x) :=
    (polyNorm1_powZJet_le _ _ _).trans
      (((Nat.pow_le_pow_left ((polyNorm1_take_le _ _).trans (polyNorm1_le_two_pow_encList (u x)))
        i).trans (Nat.pow_le_pow_right Nat.one_le_two_pow hi)).trans_eq
        (pow_mul 2 (2 * Lu) (s x)).symm)
  simpa only [length_powZJet] using length_encList_le encIntBin _ fun z hz =>
    length_encIntBin_le_of_natAbs_le ((natAbs_mem_le_polyNorm1 hz).trans hnorm)

/-- Wrapping a binary integer into a singleton list is polynomial-time. -/
theorem singleton_intBin_polytime {z : α → ℤ}
    (hz : ComputableInPolyTime z encIn encIntBin) :
    ComputableInPolyTime (fun x => [z x]) encIn (encList encIntBin) :=
  cons_polytime hz (const [])

private theorem parityFactorColJet_polytime {J ℓ s : α → ℕ} {Δ : α → ℤ}
    {yJet hJet : α → List ℤ} {coeffs : α → List (ℤ × ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hΔ : ComputableInPolyTime Δ encIn encIntBin)
    (hyJet : ComputableInPolyTime yJet encIn (encList encIntBin))
    (hcoeffs : ComputableInPolyTime coeffs encIn (encList (encPair encIntBin encIntBin)))
    (hhJet : ComputableInPolyTime hJet encIn (encList encIntBin))
    (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime
      (fun x => ParityFactorEval.colJet (J x) (ℓ x) (Δ x) (yJet x) (coeffs x) (hJet x) (s x))
      encIn (encList encIntBin) := by
  have hab : ComputableInPolyTime (fun x => (coeffs x).getD (s x) (0, 0))
      encIn (encPair encIntBin encIntBin) :=
    listGetDWithInput hcoeffs hs (0, 0)
  have hexp : ComputableInPolyTime (fun x => 2 * (ℓ x - 1 - s x)) encIn encUnary :=
    (show ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
      (encPair encUnary encUnary) encUnary by fun_prop).comp
      ((const 2).prod (unary_sub.comp ((unary_sub.comp (hℓ.prod (const 1))).prod hs)))
  have hscale := singleton_intBin_polytime (intBin_pow_polytime hΔ hexp)
  have hlin := computableInPolyTime_polyAdd
    (singleton_intBin_polytime (intBin_mul' hΔ hab.fst'))
    (computableInPolyTime_polyMul (singleton_intBin_polytime hab.snd')
      (computableInPolyTime_truncZJet hJ hyJet))
  unfold ParityFactorEval.colJet
  exact computableInPolyTime_mulZJet hJ hscale
    (computableInPolyTime_mulZJet hJ hlin (computableInPolyTime_powZJet hJ hhJet hs))

private theorem parityFactorCols_polytime {J ℓ : α → ℕ} {Δ : α → ℤ} {yJet : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hΔ : ComputableInPolyTime Δ encIn encIntBin)
    (hyJet : ComputableInPolyTime yJet encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => ParityFactorEval.cols (J x) (ℓ x) (Δ x) (yJet x))
      encIn (encList (encList encIntBin)) := by
  have hcoeffs := computableInPolyTime_parityLinearCoeffs hℓ
  have hyT := computableInPolyTime_truncZJet hJ hyJet
  have hnegΔ := (show ComputableInPolyTime (fun z : ℤ => -z)
    encIntBin encIntBin by fun_prop).comp hΔ
  have hhJet := computableInPolyTime_mulZJet hJ hyT
    (computableInPolyTime_polyAdd hyT (singleton_intBin_polytime hnegΔ))
  have hp1 : ComputableInPolyTime (Prod.fst (α := α) (β := ℕ))
      (encPair encIn encUnary) encIn := fst _ _
  have hstep := parityFactorColJet_polytime
    (hJ.comp hp1) (hℓ.comp hp1) (hΔ.comp hp1) (hyJet.comp hp1)
    (hcoeffs.comp hp1) (hhJet.comp hp1) (snd _ _)
  exact mapWithInput (range.comp hℓ) hstep

/-- **Compositional plain polynomial-time certificate for `evalParityFactorJet`**
([OpenAI2026ETH], Appendix B.2) on unary $(J, \ell)$ and binary $(\Delta, \text{yJet})$. -/
@[fun_prop] theorem computableInPolyTime_evalParityFactorJet {J ℓ : α → ℕ} {Δ : α → ℤ}
    {yJet : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hΔ : ComputableInPolyTime Δ encIn encIntBin)
    (hyJet : ComputableInPolyTime yJet encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => evalParityFactorJet (J x) (ℓ x) (Δ x) (yJet x))
      encIn (encList (encList encIntBin)) := by
  have _ := parityFactorCols_polytime hJ hℓ hΔ hyJet
  unfold evalParityFactorJet; fun_prop

/-- **Standalone plain polynomial-time certificate for `evalParityFactorJet`** on unary $(J, \ell)$
and binary $(\Delta, \text{yJet})$. -/
theorem evalParityFactorJet_polytime :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (ℤ × List ℤ) => evalParityFactorJet p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encUnary) (encPair encIntBin (encList encIntBin)))
      (encList (encList encIntBin)) := by fun_prop

end PolyTime

end Cslib
