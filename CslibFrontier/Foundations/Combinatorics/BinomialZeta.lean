/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Pi.Interval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial zeta transforms and convolution of vectors

Vectors `x : ι → ℕ` are multisets on the finite set `ι`: `x i` is the multiplicity of `i`, the
pointwise order is inclusion of multisets and `∑ i, x i` is the size. The **vector convolution**
`vecConvolution f g c = ∑_{a ≤ c} f a * g (c - a)` sums `f a * g b` over the pairs with `a + b = c`;
this is the convolution of [ChanItakuraMaYu2026], Problem 3.1, and for `0/1` vectors it is the
subset convolution.

The paper reduces it to subset convolution on `d r` coordinates by replacing each vector by the
sets with the same multiplicities, weighted by the product of the factorials of the multiplicities
(proof of Theorem 3.3), and runs the trimmed transforms on one representative per class
(Lemma 3.2). Here the same computation is stated directly on vectors. The zeta transform of a
weight function that only depends on multiplicities, read at a set with multiplicities `x`, is
`∑_{y ≤ x} (∏ i, (x i choose y i)) F y`, because a multiset `y ≤ x` is the multiplicity vector of
`∏ i, (x i choose y i)` subsets of a set with multiplicities `x`. This is the **binomial
transform** `binomTransform 1 F`; with signs `(-1) ^ (x i - y i)` it is the binomial Möbius
transform `binomTransform (-1)`.

* `binomTransform (-1) (binomTransform 1 F * binomTransform 1 G)` is the **binomial convolution**
  `∑_{a ≤ c} (∏ i, (c i choose a i)) F a G (c - a)` when `F` is supported on vectors of size `t₁`,
  `G` on vectors of size `t₂` and `c` has size `t₁ + t₂`
  (`binomTransform_neg_one_mul_eq_binomConvolution`). This is the ranked covering-product
  identity of [ChanItakuraMaYu2026], Theorem 2.2, for multisets. In one coordinate it is the
  finite-difference identity `∑_k (-1) ^ (c - k) (c choose k) (k choose a) (k choose b) = 0` for
  `c > a + b` and `= (c choose a)` for `c = a + b` (`altChooseSum_eq_zero`, `altChooseSum_add`),
  the `c`-th difference of a polynomial of degree `a + b`.
* Weighting by factorials turns the binomial convolution into `(∏ i, (c i)!)` times the vector
  convolution (`binomConvolution_factorial`), as in the proof of Theorem 3.3.
* The binomial transform is computed coordinate by coordinate (`binomPass`,
  `foldl_binomPass`), each pass at `x` reading only vectors `y ≤ x` (`binomPass_congr`). This is
  what the trimmed passes of `CslibFrontier.Algorithms.Lean.VectorConvolution` run.

## Main definitions

* `Cslib.vecChoose`: `∏ i, (x i choose a i)`.
* `Cslib.binomTransform`: the binomial zeta (`u = 1`) and Möbius (`u = -1`) transforms.
* `Cslib.binomConvolution`, `Cslib.vecConvolution`: binomial and plain convolution of vectors.
* `Cslib.binomPass`: one coordinate of the binomial transform.

## Main results

* `Cslib.binomTransform_neg_one_mul_eq_binomConvolution`: the ranked identity.
* `Cslib.binomConvolution_factorial`: factorial weights.
* `Cslib.foldl_binomPass`: the passes compute the binomial transform.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib

open Finset Nat

/-! ### One coordinate -/

/-- The alternating sum `∑_{k ≤ c} (-1) ^ (c - k) (c choose k) (k choose a) (k choose b)`, the
`c`-th forward difference at `0` of `k ↦ (k choose a) (k choose b)`. -/
@[expose] def altChooseSum (c a b : ℕ) : ℤ :=
  ∑ k ∈ range (c + 1), (-1 : ℤ) ^ (c - k) * c.choose k * (k.choose a * k.choose b)

private theorem altChooseSum_mul_factorial (c a b : ℕ) :
    (altChooseSum c a b : ℚ) * (a ! * b ! : ℚ) =
      (fwdDiff 1)^[c] (descPochhammer ℚ a * descPochhammer ℚ b).eval 0 := by
  rw [fwdDiff_iter_eq_sum_shift, altChooseSum, Int.cast_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  simp only [zero_add, nsmul_eq_mul, mul_one, Polynomial.eval_mul,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, zsmul_eq_mul]
  push_cast
  ring

private theorem natDegree_descPochhammer_mul (a b : ℕ) :
    (descPochhammer ℚ a * descPochhammer ℚ b).natDegree = a + b := by
  rw [Polynomial.natDegree_mul (Polynomial.Monic.ne_zero (monic_descPochhammer ℚ a))
    (Polynomial.Monic.ne_zero (monic_descPochhammer ℚ b)),
    descPochhammer_natDegree, descPochhammer_natDegree]

/-- The `c`-th difference of a polynomial of degree `a + b < c` vanishes. -/
theorem altChooseSum_eq_zero {a b c : ℕ} (h : a + b < c) : altChooseSum c a b = 0 := by
  have key := altChooseSum_mul_factorial c a b
  rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (by rw [natDegree_descPochhammer_mul]; exact h)] at key
  have hne : (a ! * b ! : ℚ) ≠ 0 := by positivity
  exact_mod_cast (mul_eq_zero.mp key).resolve_right hne

/-- The `(a + b)`-th difference of `k ↦ (k choose a) (k choose b)` is `(a + b choose a)`. -/
theorem altChooseSum_add (a b : ℕ) : altChooseSum (a + b) a b = (a + b).choose a := by
  have key := altChooseSum_mul_factorial (a + b) a b
  have hdeg := (descPochhammer ℚ a * descPochhammer ℚ b).fwdDiff_iter_degree_eq_factorial
  rw [natDegree_descPochhammer_mul,
    Polynomial.Monic.leadingCoeff
      (Polynomial.Monic.mul (monic_descPochhammer ℚ a) (monic_descPochhammer ℚ b))] at hdeg
  rw [hdeg] at key
  have hfac : ((a + b).choose a : ℚ) * (a ! * b ! : ℚ) = (a + b)! := by
    have h := add_choose_mul_factorial_mul_factorial b a
    rw [add_comm b a] at h
    have h' : ((a + b).choose a : ℚ) * (b ! : ℚ) * (a ! : ℚ) = ((a + b)! : ℚ) := by exact_mod_cast h
    rw [← h']
    ring
  have hne : (a ! * b ! : ℚ) ≠ 0 := by positivity
  have : (altChooseSum (a + b) a b : ℚ) = (a + b).choose a := by
    refine mul_right_cancel₀ hne ?_
    rw [key, hfac]
    simp
  exact_mod_cast this

/-! ### Vectors -/

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The product of binomial coefficients `∏ i, (x i choose a i)`: the number of subsets with
multiplicities `a` of a set with multiplicities `x`. -/
@[expose] def vecChoose (x a : ι → ℕ) : ℕ := ∏ i, (x i).choose (a i)

/-- The product of factorials `∏ i, (x i)!`. -/
@[expose] def vecFactorial (x : ι → ℕ) : ℕ := ∏ i, (x i)!

/-- The **binomial transform** with coefficient `u`:
`∑_{y ≤ x} (∏ i, u ^ (x i - y i) (x i choose y i)) F y`. For `u = 1` this is the binomial zeta
transform, for `u = -1` the binomial Möbius transform. -/
@[expose] def binomTransform (u : R) (F : (ι → ℕ) → R) (x : ι → ℕ) : R :=
  ∑ y ∈ Iic x, (∏ i, u ^ (x i - y i) * ((x i).choose (y i) : R)) * F y

/-- The **binomial convolution** `∑_{a ≤ c} (∏ i, (c i choose a i)) F a G (c - a)`. -/
@[expose] def binomConvolution (F G : (ι → ℕ) → R) (c : ι → ℕ) : R :=
  ∑ a ∈ Iic c, (vecChoose c a : R) * (F a * G (c - a))

/-- The **vector convolution** `(f ⋆ g) c = ∑_{a + b = c} f a g b`
([ChanItakuraMaYu2026], Problem 3.1). -/
@[expose] def vecConvolution (f g : (ι → ℕ) → R) (c : ι → ℕ) : R :=
  ∑ a ∈ Iic c, f a * g (c - a)

/-- The vectors below `x` are the product of the ranges `[0, x i]`. -/
theorem Iic_eq_piFinset_range (x : ι → ℕ) :
    Iic x = Fintype.piFinset fun i => range (x i + 1) := by
  ext y
  simp only [mem_Iic, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff, Pi.le_def]

omit [DecidableEq ι] in
private theorem vecChoose_eq_zero {x a : ι → ℕ} (h : ¬ a ≤ x) : vecChoose x a = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i < a i := by
    by_contra hno
    push Not at hno
    exact h fun i => hno i
  exact prod_eq_zero (mem_univ i) (Nat.choose_eq_zero_of_lt hi)

/-- Below `c`, the binomial zeta transform at `y` is a sum over all `a ≤ c`. -/
theorem binomTransform_one_eq_sum {y c : ι → ℕ} (hy : y ≤ c) (F : (ι → ℕ) → R) :
    binomTransform 1 F y = ∑ a ∈ Iic c, (vecChoose y a : R) * F a := by
  rw [binomTransform]
  refine sum_subset (Iic_subset_Iic.mpr hy) (fun a _ ha => ?_) |>.trans
    (sum_congr rfl fun a _ => ?_)
  · rw [mem_Iic] at ha
    have := vecChoose_eq_zero ha
    simp only [one_pow, one_mul, ← Nat.cast_prod]
    rw [show ∏ i, (y i).choose (a i) = vecChoose y a from rfl, this, Nat.cast_zero, zero_mul]
  · simp [vecChoose]

/-- The binomial Möbius transform at `c` of the product of two functions, summed against pairs. -/
private theorem binomTransform_neg_one_eq (F G : (ι → ℕ) → R) (c : ι → ℕ) :
    binomTransform (-1) (fun x => binomTransform 1 F x * binomTransform 1 G x) c =
      ∑ a ∈ Iic c, ∑ b ∈ Iic c, (∏ i, (altChooseSum (c i) (a i) (b i) : R)) * (F a * G b) := by
  rw [binomTransform]
  have hstep : ∀ y ∈ Iic c, (∏ i, (-1 : R) ^ (c i - y i) * ((c i).choose (y i) : R)) *
      (binomTransform 1 F y * binomTransform 1 G y) =
      ∑ a ∈ Iic c, ∑ b ∈ Iic c, (∏ i, ((-1 : R) ^ (c i - y i) * ((c i).choose (y i) : R) *
        (((y i).choose (a i) : R) * ((y i).choose (b i) : R)))) * (F a * G b) := by
    intro y hy
    rw [binomTransform_one_eq_sum (mem_Iic.mp hy), binomTransform_one_eq_sum (mem_Iic.mp hy),
      sum_mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    simp only [vecChoose, Nat.cast_prod, prod_mul_distrib]
    ring
  rw [sum_congr rfl hstep, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul]
  congr 1
  rw [Iic_eq_piFinset_range]
  refine (prod_univ_sum (fun i => range (c i + 1)) fun i k => (-1 : R) ^ (c i - k) *
    ((c i).choose k : R) * (((k.choose (a i) : ℕ) : R) * ((k.choose (b i) : ℕ) : R))).symm.trans ?_
  refine prod_congr rfl fun i _ => ?_
  simp only [altChooseSum, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]

/-- **The ranked identity for vectors**: if `F` is supported on vectors of size `t₁`, `G` on
vectors of size `t₂` and `c` has size `t₁ + t₂`, the binomial Möbius transform of the product of
the binomial zeta transforms is the binomial convolution at `c`. -/
theorem binomTransform_neg_one_mul_eq_binomConvolution {t₁ t₂ : ℕ} {F G : (ι → ℕ) → R}
    (hF : ∀ a, F a ≠ 0 → ∑ i, a i = t₁) (hG : ∀ b, G b ≠ 0 → ∑ i, b i = t₂) {c : ι → ℕ}
    (hc : ∑ i, c i = t₁ + t₂) :
    binomTransform (-1) (fun x => binomTransform 1 F x * binomTransform 1 G x) c =
      binomConvolution F G c := by
  rw [binomTransform_neg_one_eq, binomConvolution]
  refine sum_congr rfl fun a ha => ?_
  have hac : a ≤ c := mem_Iic.mp ha
  rw [sum_eq_single (c - a)]
  · rw [vecChoose, Nat.cast_prod]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    have : c i = a i + (c - a) i := (Nat.add_sub_cancel' (hac i)).symm
    rw [this, altChooseSum_add, Int.cast_natCast]
  · intro b _ hb
    by_cases h0 : F a * G b = 0
    · rw [h0, mul_zero]
    have hFa : F a ≠ 0 := left_ne_zero_of_mul h0
    have hGb : G b ≠ 0 := right_ne_zero_of_mul h0
    obtain ⟨i, hi⟩ : ∃ i, a i + b i < c i := by
      by_contra hno
      push Not at hno
      have hsum : ∑ i, c i = ∑ i, (a i + b i) := by
        rw [sum_add_distrib, hF a hFa, hG b hGb, hc]
      have heq := (sum_eq_sum_iff_of_le fun i _ => hno i).mp hsum
      exact hb (funext fun i => by
        have := heq i (mem_univ i); simp only [Pi.sub_apply]; omega)
    rw [prod_eq_zero (mem_univ i) (by rw [altChooseSum_eq_zero hi, Int.cast_zero]), zero_mul]
  · intro h
    exact absurd (mem_Iic.mpr fun i => Nat.sub_le _ _) h

/-- **Factorial weights** (proof of [ChanItakuraMaYu2026], Theorem 3.3): weighting `f` and `g` by
the factorials of the multiplicities turns their binomial convolution into `∏ i, (c i)!` times
their vector convolution. -/
theorem binomConvolution_factorial (f g : (ι → ℕ) → R) (c : ι → ℕ) :
    binomConvolution (fun a => (vecFactorial a : R) * f a) (fun b => (vecFactorial b : R) * g b)
      c = (vecFactorial c : R) * vecConvolution f g c := by
  rw [binomConvolution, vecConvolution, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  have hac : a ≤ c := mem_Iic.mp ha
  have hfac : vecChoose c a * vecFactorial a * vecFactorial (c - a) = vecFactorial c := by
    simp only [vecChoose, vecFactorial, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by
      simpa only [Pi.sub_apply] using choose_mul_factorial_mul_factorial (hac i)
  rw [← hfac]
  push_cast
  ring

/-! ### Passes -/

/-- One coordinate of the binomial transform: `∑_{k ≤ x i} u ^ (x i - k) (x i choose k) F x'`,
where `x'` is `x` with coordinate `i` replaced by `k`. -/
@[expose] def binomPass (u : R) (i : ι) (F : (ι → ℕ) → R) (x : ι → ℕ) : R :=
  ∑ k ∈ range (x i + 1), u ^ (x i - k) * ((x i).choose k : R) * F (Function.update x i k)

omit [Fintype ι] in
/-- A pass at `x` only reads vectors below `x`. -/
theorem binomPass_congr (u : R) (i : ι) {F F' : (ι → ℕ) → R} {x : ι → ℕ}
    (h : ∀ y ≤ x, F y = F' y) : binomPass u i F x = binomPass u i F' x := by
  refine sum_congr rfl fun k hk => ?_
  rw [h]
  intro j
  rcases eq_or_ne j i with rfl | hj
  · simpa [Nat.lt_succ_iff] using hk
  · simp [Function.update_of_ne hj]

private theorem foldl_binomPass_apply (u : R) :
    ∀ (l : List ι), l.Nodup → ∀ (F : (ι → ℕ) → R) (x : ι → ℕ),
      l.foldl (fun G i => binomPass u i G) F x =
        ∑ y ∈ Fintype.piFinset (fun i => if i ∈ l then range (x i + 1) else {x i}),
          (∏ i ∈ l.toFinset, u ^ (x i - y i) * ((x i).choose (y i) : R)) * F y
  | [], _, F, x => by
    simp only [List.not_mem_nil, ite_false, Fintype.piFinset_singleton, sum_singleton,
      List.toFinset_nil, prod_empty, one_mul, List.foldl_nil]
  | i :: l, hl, F, x => by
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    rw [List.foldl_cons, foldl_binomPass_apply u l (List.nodup_cons.mp hl).2]
    have hxi : ∀ y ∈ Fintype.piFinset (fun j => if j ∈ l then range (x j + 1) else {x j}),
        y i = x i := fun y hy => by
      have := Fintype.mem_piFinset.mp hy i
      simpa [hi] using this
    rw [sum_congr rfl fun y hy => by rw [binomPass, hxi y hy, mul_sum], ← sum_product']
    refine sum_nbij' (fun p => Function.update p.1 i p.2)
      (fun z => (Function.update z i (x i), z i)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨y, k⟩ hp
      obtain ⟨hy, hk⟩ := mem_product.mp hp
      refine Fintype.mem_piFinset.mpr fun j => ?_
      rcases eq_or_ne j i with rfl | hj
      · simpa using hk
      · have := Fintype.mem_piFinset.mp hy j
        simpa [Function.update_of_ne hj, hj] using this
    · intro z hz
      refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simp [hi]
        · have := Fintype.mem_piFinset.mp hz j
          simpa [Function.update_of_ne hj, hj] using this
      · simpa using Fintype.mem_piFinset.mp hz i
    · rintro ⟨y, k⟩ hp
      obtain ⟨hy, -⟩ := mem_product.mp hp
      simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
      rw [← hxi y hy, Function.update_eq_self]
    · intro z _
      simp
    · rintro ⟨y, k⟩ _
      simp only
      rw [List.toFinset_cons, prod_insert (by simpa using hi), Function.update_self]
      have : ∏ j ∈ l.toFinset, u ^ (x j - Function.update y i k j) *
          ((x j).choose (Function.update y i k j) : R) =
          ∏ j ∈ l.toFinset, u ^ (x j - y j) * ((x j).choose (y j) : R) :=
        prod_congr rfl fun j hj => by
          rw [Function.update_of_ne (by rintro rfl; exact hi (List.mem_toFinset.mp hj))]
      rw [this]
      ring

/-- **The passes compute the binomial transform**: running `binomPass u i` for every coordinate
`i` of a duplicate-free list `l` of all coordinates gives `binomTransform u`. -/
theorem foldl_binomPass {l : List ι} (hl : l.Nodup) (hall : ∀ i, i ∈ l) (u : R)
    (F : (ι → ℕ) → R) : l.foldl (fun G i => binomPass u i G) F = binomTransform u F := by
  funext x
  rw [foldl_binomPass_apply u l hl, binomTransform, Iic_eq_piFinset_range]
  have hl' : l.toFinset = univ := eq_univ_of_forall fun i => List.mem_toFinset.mpr (hall i)
  simp only [hall, ite_true, hl']

end Cslib
