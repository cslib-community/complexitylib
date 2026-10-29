/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.FieldTheory.Finite.Subfield
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linearized and subspace polynomials over fields of characteristic two

A polynomial over a field of characteristic two is *linearized* when every exponent occurring in it
is a power of two. Such a polynomial evaluates to an additive, hence `𝔽₂`-linear, function. The
*subspace polynomial* `∏_{c ∈ 𝔽₂ᵐ} (X - ∑ cₗ bₗ)` of a family `b` is linearized, monic of degree
`2 ^ m`, and its roots are the `𝔽₂`-span of `b` [Ore1933].

Over a finite field `F` with `2 ^ n` elements every `𝔽₂`-subspace `W` of dimension `d` is the image
of a monic linearized polynomial of degree `2 ^ (n - d)`, its *image-subspace polynomial*
[BenSassonKopparty2012, Lemma 3.7]. Writing that polynomial as `∑_{j ∈ ℤ/n} a j X ^ 2 ^ j`, the
coefficients vanish at the `d - 1` positions above the leading one; the *structural lemma*
[BenSassonKopparty2012, Lemma 3.10] says that, apart from this canonical run, no `d - 1`
consecutive coefficients vanish unless `W` lies in a multiple of a proper subfield. We record it
for subspaces of dimension larger than every proper subfield, which is how it is used for
composite-degree fields.

## Main definitions

* `Cslib.IsLinearized`: every exponent of a polynomial is a power of two.
* `Cslib.IsLinearized.toLinearMap`: the `𝔽₂`-linear map given by evaluating a linearized
  polynomial.
* `Cslib.subspacePoly`: the subspace polynomial of a finite family.
* `Cslib.linearizedEval`: evaluation of a coefficient vector indexed by `ZMod n`.
* `Cslib.CoeffPattern`: the zero pattern of an image-subspace polynomial.

## Main results

* `Cslib.isLinearized_subspacePoly`, `Cslib.eval_subspacePoly_eq_zero_iff`: subspace polynomials
  are linearized and vanish exactly on the span.
* `Cslib.exists_isLinearized_range_eq`: the image-subspace polynomial.
* `Cslib.eq_zero_of_linearizedEval_eq_zero`: a nonzero linearized function of `2`-degree below `m`
  has fewer than `2 ^ m` roots.
* `Cslib.exists_coeffPattern`: the structural lemma, for subspaces of dimension larger than every
  proper subfield.

## References

* [O. Ore, *On a special class of polynomials*][Ore1933]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib

open Polynomial Module

variable {F : Type*} [Field F]

/-! ### Linearized polynomials -/

/-- A polynomial is *linearized* (over `𝔽₂`) when every exponent with a nonzero coefficient is a
power of two. Over a field of characteristic two it evaluates to an additive function. -/
def IsLinearized (P : F[X]) : Prop :=
  ∀ i ∈ P.support, ∃ j, i = 2 ^ j

namespace IsLinearized

variable {P Q : F[X]}

/-- The zero polynomial is linearized. -/
theorem zero : IsLinearized (0 : F[X]) := by
  intro i hi
  simp at hi

/-- A sum of linearized polynomials is linearized. -/
theorem add (hP : IsLinearized P) (hQ : IsLinearized Q) : IsLinearized (P + Q) := by
  intro i hi
  rcases Finset.mem_union.1 (support_add hi) with h | h
  exacts [hP i h, hQ i h]

/-- A constant multiple `C c * P` of a linearized polynomial is linearized. -/
theorem C_mul (hP : IsLinearized P) (c : F) : IsLinearized (C c * P) := by
  intro i hi
  rw [Polynomial.mem_support_iff, coeff_C_mul] at hi
  exact hP i (Polynomial.mem_support_iff.2 (right_ne_zero_of_mul hi))

/-- The monomial `X ^ 2 ^ j` is linearized. -/
theorem X_pow_two_pow (j : ℕ) : IsLinearized (X ^ 2 ^ j : F[X]) := by
  intro i hi
  rw [Polynomial.mem_support_iff, coeff_X_pow] at hi
  split_ifs at hi with h
  · exact ⟨j, h⟩
  · exact absurd rfl hi

/-- In characteristic two, the square of a linearized polynomial is linearized. -/
theorem sq [CharP F 2] (hP : IsLinearized P) : IsLinearized (P ^ 2) := by
  intro i hi
  rw [← map_frobenius_expand 2, Polynomial.mem_support_iff, coeff_map, coeff_expand two_pos] at hi
  split_ifs at hi with h
  · obtain ⟨j, hj⟩ := hP (i / 2) (Polynomial.mem_support_iff.2 fun h0 => hi (by rw [h0, map_zero]))
    exact ⟨j + 1, by rw [pow_succ, ← hj, Nat.div_mul_cancel h]⟩
  · exact absurd (map_zero _) hi

/-- A linearized polynomial has constant coefficient `0`. -/
theorem coeff_zero (hP : IsLinearized P) : P.coeff 0 = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := hP 0 (Polynomial.mem_support_iff.2 h)
  exact pow_ne_zero j two_ne_zero hj.symm

/-- A linearized polynomial composes additively. -/
theorem comp_add [CharP F 2] (hP : IsLinearized P) (f g : F[X]) :
    P.comp (f + g) = P.comp f + P.comp g := by
  simp only [comp_eq_sum_left, Polynomial.sum_def, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨j, rfl⟩ := hP i hi
  rw [add_pow_char_pow]

/-- In characteristic two, a linearized polynomial composes subtractively:
`P.comp (f - g) = P.comp f - P.comp g`. -/
theorem comp_sub [CharP F 2] (hP : IsLinearized P) (f g : F[X]) :
    P.comp (f - g) = P.comp f - P.comp g := by
  rw [eq_sub_iff_add_eq, ← hP.comp_add, sub_add_cancel]

/-- In characteristic two, a linearized polynomial evaluates additively:
`P.eval (x + y) = P.eval x + P.eval y`. -/
theorem eval_add [CharP F 2] (hP : IsLinearized P) (x y : F) :
    P.eval (x + y) = P.eval x + P.eval y := by
  have h := hP.comp_add (C x) (C y)
  rw [← C_add, comp_C, comp_C, comp_C, ← C_add] at h
  exact C_injective h

/-- A linearized polynomial vanishes at `0`. -/
theorem eval_zero (hP : IsLinearized P) : P.eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, hP.coeff_zero]

end IsLinearized

/-- The `𝔽₂`-linear map given by evaluating a linearized polynomial. -/
def IsLinearized.toLinearMap [Algebra (ZMod 2) F] {P : F[X]} (hP : IsLinearized P) :
    F →ₗ[ZMod 2] F :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := P.eval
      map_zero' := hP.eval_zero
      map_add' := hP.eval_add }

/-- The linear map of a linearized polynomial `P` sends `x` to `P.eval x`. -/
@[simp]
theorem IsLinearized.toLinearMap_apply [Algebra (ZMod 2) F] {P : F[X]} (hP : IsLinearized P)
    (x : F) : hP.toLinearMap x = P.eval x :=
  rfl

/-! ### Subspace polynomials -/

variable [Algebra (ZMod 2) F]

/-- The *subspace polynomial* `∏_{c ∈ 𝔽₂ᵐ} (X - ∑ₗ cₗ bₗ)` of a family `b` of `m` elements. -/
noncomputable def subspacePoly {m : ℕ} (b : Fin m → F) : F[X] :=
  ∏ c : Fin m → ZMod 2, (X - C (∑ l, c l • b l))

/-- The subspace polynomial is monic. -/
theorem monic_subspacePoly {m : ℕ} (b : Fin m → F) : (subspacePoly b).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- The subspace polynomial of a family of `m` elements has degree `2 ^ m`. -/
theorem natDegree_subspacePoly {m : ℕ} (b : Fin m → F) :
    (subspacePoly b).natDegree = 2 ^ m := by
  rw [subspacePoly, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-- The subspace polynomial of `Fin.snoc b v` is `P * P.comp (X - C v)` for `P` the subspace
polynomial of `b`. -/
theorem subspacePoly_snoc {m : ℕ} (b : Fin m → F) (v : F) :
    subspacePoly (Fin.snoc b v : Fin (m + 1) → F) =
      subspacePoly b * (subspacePoly b).comp (X - C v) := by
  rw [subspacePoly, ← (Fin.snocEquiv fun _ => ZMod 2).prod_comp, Fintype.prod_prod_type]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.prod_pair (by decide), subspacePoly, prod_comp]
  congr 1
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [Fin.snocEquiv, Fin.sum_univ_castSucc]
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, one_smul, sub_comp, X_comp, C_comp, C_add]
    ring

/-- Subspace polynomials are linearized [Ore1933]. -/
theorem isLinearized_subspacePoly {m : ℕ} (b : Fin m → F) : IsLinearized (subspacePoly b) := by
  induction m with
  | zero =>
    have : subspacePoly b = X := by simp [subspacePoly]
    rw [this, ← pow_one X, ← pow_zero 2]
    exact IsLinearized.X_pow_two_pow 0
  | succ m ih =>
    rw [← Fin.snoc_init_self b, subspacePoly_snoc]
    set P := subspacePoly (Fin.init b)
    have hP : IsLinearized P := ih _
    have hcomp : P.comp (X - C (b (Fin.last m))) = P + C (P.eval (-b (Fin.last m))) := by
      rw [sub_eq_add_neg, ← C_neg, hP.comp_add, comp_X, comp_C]
    rw [hcomp, mul_add, ← pow_two, mul_comm]
    exact hP.sq.add (hP.C_mul _)

/-- The roots of the subspace polynomial of `b` are the `𝔽₂`-span of `b`. -/
theorem eval_subspacePoly_eq_zero_iff {m : ℕ} (b : Fin m → F) (x : F) :
    (subspacePoly b).eval x = 0 ↔ x ∈ Submodule.span (ZMod 2) (Set.range b) := by
  rw [Submodule.mem_span_range_iff_exists_fun, subspacePoly, eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, eval_sub, eval_X, eval_C]
  exact exists_congr fun c => by rw [sub_eq_zero, eq_comm]

/-- Every `𝔽₂`-subspace `U` of `F` is the kernel of a monic linearized polynomial of degree
`2 ^ dim U`. -/
private theorem exists_isLinearized_ker_eq [Finite F] (U : Submodule (ZMod 2) F) :
    ∃ (P : F[X]) (hP : IsLinearized P), P.Monic ∧
      P.natDegree = 2 ^ finrank (ZMod 2) U ∧ LinearMap.ker hP.toLinearMap = U := by
  cases nonempty_fintype F
  obtain ⟨b, -, hb₀, -⟩ := Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (U : Set F)
  have hb := hb₀.trans (Submodule.span_eq U)
  refine ⟨subspacePoly b, isLinearized_subspacePoly b, monic_subspacePoly b, ?_, ?_⟩
  · rw [natDegree_subspacePoly, Submodule.span_eq]
  · ext x
    rw [LinearMap.mem_ker, IsLinearized.toLinearMap_apply, eval_subspacePoly_eq_zero_iff, hb]

/-- If `P` and `Q` are monic linearized polynomials whose degrees multiply to `|F|` and `Q`
vanishes on the values of `P`, then `P ∘ Q = X ^ |F| - X`. -/
private theorem comp_eq_X_pow_card_sub_X [Fintype F] {P Q : F[X]}
    (hP : IsLinearized P) (hPm : P.Monic) (hQm : Q.Monic)
    (hPdeg : P.natDegree ≠ 0) (hdeg : Q.natDegree * P.natDegree = Fintype.card F)
    (hker : ∀ x, Q.eval (P.eval x) = 0) :
    P.comp Q = X ^ Fintype.card F - X := by
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  -- `Q ∘ P = X ^ q - X`
  have hQP : Q.comp P = X ^ Fintype.card F - X := by
    have hmon : IsMonicOfDegree (Q.comp P) (Fintype.card F) :=
      ⟨by rw [natDegree_comp, hdeg], hQm.comp hPm hPdeg⟩
    have hX : IsMonicOfDegree (X ^ Fintype.card F - X : F[X]) (Fintype.card F) := by
      rw [isMonicOfDegree_iff]
      refine ⟨(natDegree_X_pow_sub_X (R := F) hq1).le, ?_⟩
      have h1 : (1 : ℕ) ≠ Fintype.card F := hq1.ne
      simp [coeff_X, h1]
    rw [← sub_eq_zero]
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id) Function.injective_id
      (fun x => by simp [eval_comp, hker x, FiniteField.pow_card])
      (hmon.natDegree_sub_lt hq1.ne_bot hX)
  -- hence `P ∘ Q = X ^ q - X`
  have h1 : (P.comp Q).comp P = (X ^ Fintype.card F - X : F[X]).comp P := by
    rw [comp_assoc, hQP, hP.comp_sub, ← expand_eq_comp_X_pow,
      FiniteField.Polynomial.expand_card, comp_X, sub_comp, X_pow_comp, X_comp]
  have h2 : (P.comp Q - (X ^ Fintype.card F - X)).comp P = 0 := by
    rw [sub_comp, h1, sub_self]
  rcases comp_eq_zero_iff.1 h2 with h | ⟨-, h⟩
  · exact sub_eq_zero.1 h
  · have := congrArg natDegree h
    rw [natDegree_C] at this
    exact absurd this hPdeg

/-- **Image-subspace polynomial** [BenSassonKopparty2012, Lemma 3.7]: every `𝔽₂`-subspace `W` of a
finite field `F` is the image of a monic linearized polynomial of degree
`2 ^ (dim F - dim W)`. -/
theorem exists_isLinearized_range_eq [Finite F] (W : Submodule (ZMod 2) F) :
    ∃ Q : F[X], IsLinearized Q ∧ Q.Monic ∧
      Q.natDegree = 2 ^ (finrank (ZMod 2) F - finrank (ZMod 2) W) ∧
      ∀ y, y ∈ W ↔ ∃ x, Q.eval x = y := by
  classical
  cases nonempty_fintype F
  have hcard : Fintype.card F = 2 ^ finrank (ZMod 2) F := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F), ZMod.card]
  have hdn : finrank (ZMod 2) W ≤ finrank (ZMod 2) F := Submodule.finrank_le W
  -- the kernel-subspace polynomial `P` of `W`
  obtain ⟨P, hP, hPm, hPdeg, hkerP⟩ := exists_isLinearized_ker_eq W
  -- `Q` is the kernel-subspace polynomial of the image of `P`
  have hK' : finrank (ZMod 2) (LinearMap.range hP.toLinearMap) =
      finrank (ZMod 2) F - finrank (ZMod 2) W := by
    have := LinearMap.finrank_range_add_finrank_ker hP.toLinearMap
    rw [hkerP] at this
    omega
  obtain ⟨Q, hQ, hQm, hQdeg₀, hkerQ⟩ := exists_isLinearized_ker_eq (LinearMap.range hP.toLinearMap)
  have hQdeg : Q.natDegree = 2 ^ (finrank (ZMod 2) F - finrank (ZMod 2) W) := hK' ▸ hQdeg₀
  refine ⟨Q, hQ, hQm, hQdeg, ?_⟩
  -- `P ∘ Q = X ^ q - X`
  have hPQ : P.comp Q = X ^ Fintype.card F - X :=
    comp_eq_X_pow_card_sub_X hP hPm hQm (hPdeg ▸ pow_ne_zero _ two_ne_zero)
      (by rw [hQdeg, hPdeg, ← pow_add, hcard, Nat.sub_add_cancel hdn]) fun x => by
        have hx : P.eval x ∈ LinearMap.range hP.toLinearMap := ⟨x, rfl⟩
        rwa [← hkerQ, LinearMap.mem_ker, IsLinearized.toLinearMap_apply] at hx
  have hrange : ∀ x, Q.eval x ∈ W := fun x => by
    rw [← hkerP, LinearMap.mem_ker, IsLinearized.toLinearMap_apply, ← eval_comp, hPQ]
    simp [FiniteField.pow_card]
  -- the image of `Q` is all of `W`, by counting
  have hle : LinearMap.range hQ.toLinearMap ≤ W := by
    rintro _ ⟨x, rfl⟩
    exact hrange x
  have heq : LinearMap.range hQ.toLinearMap = W := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have := LinearMap.finrank_range_add_finrank_ker hQ.toLinearMap
    rw [hkerQ] at this
    omega
  intro y
  refine ⟨fun hy => ?_, fun ⟨x, hx⟩ => hx ▸ hrange x⟩
  rw [← heq] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

/-! ### Coefficient vectors indexed by `ZMod n` -/

/-- Evaluation of the linearized function `x ↦ ∑_{j ∈ ℤ/n} a j * x ^ 2 ^ j`. Over a field with
`2 ^ n` elements every linearized polynomial function has this form. -/
def linearizedEval {n : ℕ} [NeZero n] (a : ZMod n → F) (x : F) : F :=
  ∑ j, a j * x ^ 2 ^ j.val

/-- Frobenius periodicity: in a field with `2 ^ n` elements, `x ^ 2 ^ m` depends only on
`m % n`. -/
theorem pow_two_pow_mod [Finite F] {n : ℕ} (hn : finrank (ZMod 2) F = n) (x : F) (m : ℕ) :
    x ^ 2 ^ m = x ^ 2 ^ (m % n) := by
  cases nonempty_fintype F
  have hcard : Fintype.card F = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F), ZMod.card, hn]
  have key : ∀ q r : ℕ, x ^ 2 ^ (n * q + r) = x ^ 2 ^ r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show n * (q + 1) + r = (n * q + r) + n by ring, pow_add, pow_mul, ih, ← hcard,
        FiniteField.pow_card]
  conv_lhs => rw [← Nat.div_add_mod m n]
  exact key _ _

/-- Raising a linearized function to the power `2 ^ k` rotates its coefficient vector. -/
theorem linearizedEval_pow_two_pow [Finite F] {n : ℕ} [NeZero n] (hn : finrank (ZMod 2) F = n)
    (a : ZMod n → F) (k : ℕ) (x : F) :
    linearizedEval a x ^ 2 ^ k = linearizedEval (fun j => a (j - (k : ZMod n)) ^ 2 ^ k) x := by
  rw [linearizedEval, sum_pow_char_pow, linearizedEval]
  refine Fintype.sum_equiv (Equiv.addRight (k : ZMod n)) _ _ fun j => ?_
  rw [Equiv.coe_addRight, add_sub_cancel_right, mul_pow, ← pow_mul, ← pow_add,
    pow_two_pow_mod hn x (j.val + k), ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

omit [Algebra (ZMod 2) F] in
theorem linearizedEval_sub_mul {n : ℕ} [NeZero n] (a b : ZMod n → F) (c x : F) :
    linearizedEval (fun j => b j - c * a j) x = linearizedEval b x - c * linearizedEval a x := by
  simp only [linearizedEval, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

omit [Algebra (ZMod 2) F] in
/-- **Root bound for linearized functions**: if the coefficients of `b` vanish from position `m`
on and the function vanishes on at least `2 ^ m` points, then `b = 0`. -/
theorem eq_zero_of_linearizedEval_eq_zero {n : ℕ} [NeZero n] {b : ZMod n → F} {m : ℕ}
    (hb : ∀ j, m ≤ j.val → b j = 0) (S : Finset F) (hS : 2 ^ m ≤ S.card)
    (h : ∀ x ∈ S, linearizedEval b x = 0) : b = 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · funext j
    exact hb j (Nat.zero_le _)
  set p : F[X] := ∑ j, C (b j) * X ^ 2 ^ j.val with hp
  have heval : ∀ x, p.eval x = linearizedEval b x := fun x => by
    simp [hp, linearizedEval, eval_finsetSum]
  have hdeg : p.natDegree < S.card := by
    have : p.natDegree ≤ 2 ^ (m - 1) := by
      refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      by_cases hj : b j = 0
      · simp [hj]
      · have : j.val < m := not_le.1 fun h => hj (hb j h)
        exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.pow_le_pow_right two_pos (by omega))
    calc p.natDegree ≤ 2 ^ (m - 1) := this
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ S.card := hS
  have hp0 : p = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := ((↑) : S → F))
      Subtype.val_injective (fun x => ?_) (by simpa using hdeg)
    rw [heval]
    exact h x x.2
  funext j
  have := congrArg (fun q => q.coeff (2 ^ j.val)) hp0
  simp only [hp, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single j] at this
  · simpa using this
  · intro j' _ hj'
    rw [ite_eq_right_iff]
    intro h
    exact absurd (ZMod.val_injective _ (Nat.pow_right_injective le_rfl h).symm) hj'
  · simp

/-- If every element `y` of a subspace `W` satisfies `y ^ 2 ^ k = c * y` with `0 < k < n`, then
`W` embeds into the proper subfield fixed by the `k`-th power of Frobenius. -/
theorem exists_subfield_card_le [Finite F] {n k : ℕ} (hn : finrank (ZMod 2) F = n) (hk0 : 0 < k)
    (hkn : k < n) (W : Submodule (ZMod 2) F) (c : F) (h : ∀ y ∈ W, y ^ 2 ^ k = c * y) :
    ∃ K : Subfield F, K ≠ ⊤ ∧ Nat.card W ≤ Nat.card K := by
  classical
  cases nonempty_fintype F
  let K := RingHom.eqLocusField (iterateFrobenius F 2 k) (RingHom.id F)
  have hmem : ∀ x, x ∈ K ↔ x ^ 2 ^ k = x := fun x => by
    simp [K, RingHom.eqLocusField, iterateFrobenius_def]
  refine ⟨K, fun hK => ?_, ?_⟩
  · have hall : ∀ x : F, x ^ 2 ^ k = x := fun x => (hmem x).1 (hK ▸ Subfield.mem_top x)
    have h1 : 1 < 2 ^ k := Nat.one_lt_two_pow hk0.ne'
    have hcard : Fintype.card F = 2 ^ n := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F), ZMod.card, hn]
    refine X_pow_sub_X_ne_zero (R := F) h1
      (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id) Function.injective_id
        (fun x => by simp [hall x]) ?_)
    rw [natDegree_X_pow_sub_X (R := F) h1, hcard]
    exact Nat.pow_lt_pow_right (by norm_num) hkn
  · by_cases hW : ∃ y₀ ∈ W, y₀ ≠ 0
    · obtain ⟨y₀, hy₀W, hy₀⟩ := hW
      have hc : c ≠ 0 := by
        rintro rfl
        have := h y₀ hy₀W
        rw [zero_mul] at this
        exact hy₀ (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 this)
      let f : W → K := fun y => ⟨y / y₀, (hmem _).2 (by
        rw [div_pow, h y y.2, h y₀ hy₀W, mul_div_mul_left _ _ hc])⟩
      exact Nat.card_le_card_of_injective f fun y y' hyy' =>
        Subtype.ext ((div_left_inj' hy₀).1 (congrArg Subtype.val hyy'))
    · push Not at hW
      have : Nat.card W = 1 := Nat.card_eq_one_iff_unique.2
        ⟨⟨fun y y' => Subtype.ext (by rw [hW y y.2, hW y' y'.2])⟩, ⟨0⟩⟩
      rw [this]
      exact Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'

/-- The zero pattern of the coefficient vector `a` of an image-subspace polynomial of a
`d`-dimensional subspace that lies in no multiple of a proper subfield
[BenSassonKopparty2012, Lemma 3.10]: the leading coefficient sits at `n - d`, the `d - 1`
positions above it vanish, the constant coefficient is nonzero, and every window of
`d - 1` consecutive positions starting in `[1, n - d]` meets a nonzero coefficient. -/
structure CoeffPattern (n d : ℕ) [NeZero n] (a : ZMod n → F) : Prop where
  /-- The dimension is at most the degree of the field. -/
  le : d ≤ n
  /-- The leading coefficient sits at position `n - d`. -/
  lead : a ((n - d : ℕ) : ZMod n) ≠ 0
  /-- The `d - 1` positions above the leading one vanish. -/
  canonical : ∀ c, 1 ≤ c → c < d → a ((n - d + c : ℕ) : ZMod n) = 0
  /-- The constant coefficient is nonzero. -/
  zero_ne : a 0 ≠ 0
  /-- Every window of `d - 1` consecutive positions starting in `[1, n - d]` meets a nonzero
  coefficient. -/
  gap : ∀ ρ : ℕ, 1 ≤ ρ → ρ + d ≤ n → ∃ c < d - 1, a ((ρ + c : ℕ) : ZMod n) ≠ 0

omit [Algebra (ZMod 2) F] in
/-- A linearized polynomial of degree below `2 ^ n` evaluates as `linearizedEval` of its
`2 ^ j`-th coefficients. -/
private theorem IsLinearized.eval_eq_linearizedEval {n : ℕ} [NeZero n] {Q : F[X]}
    (hQ : IsLinearized Q) (hdeg : Q.natDegree < 2 ^ n) (x : F) :
    Q.eval x = linearizedEval (fun j : ZMod n => Q.coeff (2 ^ j.val)) x := by
  let a : ZMod n → F := fun j => Q.coeff (2 ^ j.val)
  have hpoly : Q = ∑ j : ZMod n, C (a j) * X ^ 2 ^ j.val := by
    ext i
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    by_cases hi : ∃ e < n, i = 2 ^ e
    · obtain ⟨e, he, rfl⟩ := hi
      rw [Finset.sum_eq_single (e : ZMod n)]
      · simp [a, ZMod.val_cast_of_lt he]
      · intro j _ hj
        rw [ite_eq_right_iff]
        intro h
        exact absurd (by rw [Nat.pow_right_injective le_rfl h, ZMod.natCast_zmod_val]) hj
      · simp
    · push Not at hi
      rw [Finset.sum_eq_zero fun j _ =>
        ite_eq_right_iff.2 fun h => absurd h (hi j.val (ZMod.val_lt j))]
      by_contra hne
      obtain ⟨e, rfl⟩ := hQ i (Polynomial.mem_support_iff.2 hne)
      exact hi e ((Nat.pow_lt_pow_iff_right (by norm_num)).1
        ((le_natDegree_of_ne_zero hne).trans_lt hdeg)) rfl
  conv_lhs => rw [hpoly]
  simp [a, linearizedEval, eval_finsetSum]

/-- If `a` has leading coefficient `1` at `n - d`, vanishes at the `d - 1` positions above
`n - d`, and has at least `2 ^ (n - d)` roots, then `a 0 ≠ 0`. -/
private theorem coeffPattern_zero_ne [Finite F] {n d : ℕ} [NeZero n]
    (hn : finrank (ZMod 2) F = n) (hdn : d ≤ n) {a : ZMod n → F}
    (hlead : a ((n - d : ℕ) : ZMod n) = 1)
    (hcan : ∀ c, 1 ≤ c → c < d → a ((n - d + c : ℕ) : ZMod n) = 0)
    {S : Finset F} (hScard : 2 ^ (n - d) ≤ S.card)
    (hSzero : ∀ x ∈ S, linearizedEval a x = 0) : a 0 ≠ 0 := by
  intro h0
  set b : ZMod n → F := fun j => a (j - ((n - 1 : ℕ) : ZMod n)) ^ 2 ^ (n - 1)
  have hshift : ∀ j : ZMod n, j - ((n - 1 : ℕ) : ZMod n) = j + 1 := fun j => by
    rw [Nat.cast_sub NeZero.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, sub_neg_eq_add]
  have hb : ∀ j : ZMod n, n - d ≤ j.val → b j = 0 := by
    intro j hj
    simp only [b, hshift]
    have hjn := ZMod.val_lt j
    rcases Nat.lt_or_ge (j.val + 1) n with hlt | hge
    · have : j + 1 = ((n - d + (j.val + 1 - (n - d)) : ℕ) : ZMod n) := by
        rw [show n - d + (j.val + 1 - (n - d)) = j.val + 1 by omega, Nat.cast_add,
          ZMod.natCast_zmod_val, Nat.cast_one]
      rw [this, hcan _ (by omega) (by omega)]
      exact zero_pow (pow_ne_zero _ two_ne_zero)
    · have : j + 1 = 0 := by
        rw [← ZMod.natCast_zmod_val j, ← Nat.cast_one, ← Nat.cast_add,
          show j.val + 1 = n by omega, ZMod.natCast_self]
      rw [this, h0]
      exact zero_pow (pow_ne_zero _ two_ne_zero)
  have hb0 := eq_zero_of_linearizedEval_eq_zero hb S hScard fun x hx => by
    rw [← linearizedEval_pow_two_pow hn, hSzero x hx]
    exact zero_pow (pow_ne_zero _ two_ne_zero)
  have := congrFun hb0 (((n - d : ℕ) : ZMod n) + ((n - 1 : ℕ) : ZMod n))
  simp only [b, add_sub_cancel_right, hlead, one_pow, Pi.zero_apply] at this
  exact one_ne_zero this

/-- If `a` has a gap of `d - 1` zeros starting at `ρ`, rotating by `k = n - d + 1 - ρ` makes
`linearizedEval a x ^ 2 ^ k` a constant multiple of `linearizedEval a x`. -/
private theorem linearizedEval_pow_eq_mul_of_gap [Finite F] {n d ρ : ℕ} [NeZero n]
    (hn : finrank (ZMod 2) F = n) (hρ1 : 1 ≤ ρ) (hρd : ρ + d ≤ n) {a : ZMod n → F}
    (hlead : a ((n - d : ℕ) : ZMod n) = 1)
    (hcan : ∀ c, 1 ≤ c → c < d → a ((n - d + c : ℕ) : ZMod n) = 0)
    {S : Finset F} (hScard : 2 ^ (n - d) ≤ S.card)
    (hSzero : ∀ x ∈ S, linearizedEval a x = 0)
    (hall : ∀ c < d - 1, a ((ρ + c : ℕ) : ZMod n) = 0) :
    ∃ c₀ : F, ∀ x, linearizedEval a x ^ 2 ^ (n - d + 1 - ρ) = c₀ * linearizedEval a x := by
  set k := n - d + 1 - ρ
  set b : ZMod n → F := fun j => a (j - (k : ZMod n)) ^ 2 ^ k
  set c₀ := b ((n - d : ℕ) : ZMod n)
  have hb : ∀ j : ZMod n, n - d ≤ j.val → b j - c₀ * a j = 0 := by
    intro j hj
    have hjn := ZMod.val_lt j
    rcases Nat.eq_or_lt_of_le hj with heq | hlt
    · have : j = ((n - d : ℕ) : ZMod n) := by rw [heq, ZMod.natCast_zmod_val]
      rw [this, hlead, mul_one, sub_self]
    · have hj' : j = ((n - d + (j.val - (n - d)) : ℕ) : ZMod n) := by
        rw [show n - d + (j.val - (n - d)) = j.val by omega, ZMod.natCast_zmod_val]
      have haj : a j = 0 := hj' ▸ hcan _ (by omega) (by omega)
      have hbj : b j = 0 := by
        simp only [b]
        have : j - (k : ZMod n) = ((ρ + (j.val - (n - d) - 1) : ℕ) : ZMod n) := by
          rw [sub_eq_iff_eq_add, ← Nat.cast_add]
          conv_lhs => rw [← ZMod.natCast_zmod_val j]
          congr 1
          omega
        rw [this, hall _ (by omega)]
        exact zero_pow (pow_ne_zero _ two_ne_zero)
      rw [haj, hbj, mul_zero, sub_zero]
  have hb0 := eq_zero_of_linearizedEval_eq_zero (b := fun j => b j - c₀ * a j) hb S hScard
    fun x hx => by
      rw [linearizedEval_sub_mul, hSzero x hx, mul_zero, sub_zero,
        ← linearizedEval_pow_two_pow hn, hSzero x hx]
      exact zero_pow (pow_ne_zero _ two_ne_zero)
  refine ⟨c₀, fun x => ?_⟩
  have := congrArg (fun f => linearizedEval f x) hb0
  simp only [linearizedEval_sub_mul] at this
  rw [linearizedEval_pow_two_pow hn]
  simpa [linearizedEval, sub_eq_zero] using this

/-- When `W` has dimension `d > s` above every proper subfield and lies in the range of
`linearizedEval a`, every window of `d - 1` coefficients starting in `[1, n - d]` contains a
nonzero coefficient. -/
private theorem coeffPattern_gap [Finite F] {n s d : ℕ} [NeZero n]
    (hn : finrank (ZMod 2) F = n) (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s)
    {W : Submodule (ZMod 2) F} (hd : finrank (ZMod 2) W = d) (hsW : s < d) {a : ZMod n → F}
    (hWa : ∀ y ∈ W, ∃ x, linearizedEval a x = y)
    (hlead : a ((n - d : ℕ) : ZMod n) = 1)
    (hcan : ∀ c, 1 ≤ c → c < d → a ((n - d + c : ℕ) : ZMod n) = 0)
    {S : Finset F} (hScard : 2 ^ (n - d) ≤ S.card)
    (hSzero : ∀ x ∈ S, linearizedEval a x = 0)
    (ρ : ℕ) (hρ1 : 1 ≤ ρ) (hρd : ρ + d ≤ n) :
    ∃ c < d - 1, a ((ρ + c : ℕ) : ZMod n) ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨c₀, hc₀⟩ := linearizedEval_pow_eq_mul_of_gap hn hρ1 hρd hlead hcan hScard hSzero hall
  have hW' : ∀ y ∈ W, y ^ 2 ^ (n - d + 1 - ρ) = c₀ * y := by
    intro y hy
    obtain ⟨x, rfl⟩ := hWa y hy
    exact hc₀ x
  obtain ⟨K, hK, hcard⟩ := exists_subfield_card_le hn (by omega) (by omega) W c₀ hW'
  have hWcard : Nat.card W = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod, hd]
  have := (hWcard ▸ hcard).trans (hs K hK)
  exact absurd ((Nat.pow_le_pow_iff_right (by norm_num)).1 this) (by omega)

/-- **Structural lemma** [BenSassonKopparty2012, Lemma 3.10], for subspaces larger than every
proper subfield: a subspace `W` of dimension greater than `s`, where every proper subfield
has at most `2 ^ s` elements, is the image of a linearized function whose coefficient vector has
the zero pattern `CoeffPattern`. -/
theorem exists_coeffPattern [Finite F] {n s : ℕ} [NeZero n] (hn : finrank (ZMod 2) F = n)
    (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s) (W : Submodule (ZMod 2) F)
    (hsW : s < finrank (ZMod 2) W) :
    ∃ a : ZMod n → F, (∀ x, linearizedEval a x ∈ W) ∧ CoeffPattern n (finrank (ZMod 2) W) a := by
  classical
  cases nonempty_fintype F
  obtain ⟨Q, hQ, hQm, hQdeg, hQW⟩ := exists_isLinearized_range_eq W
  obtain ⟨d, hd⟩ : ∃ d, finrank (ZMod 2) W = d := ⟨_, rfl⟩
  rw [hd] at hQdeg hsW ⊢
  rw [hn] at hQdeg
  have hdn : d ≤ n := hd ▸ hn ▸ Submodule.finrank_le W
  -- the coefficient vector of `Q`
  let a : ZMod n → F := fun j => Q.coeff (2 ^ j.val)
  have hQa : ∀ x, Q.eval x = linearizedEval a x :=
    hQ.eval_eq_linearizedEval (hQdeg ▸ Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hlead : a ((n - d : ℕ) : ZMod n) = 1 := by
    simp only [a, ZMod.val_cast_of_lt (show n - d < n by omega)]
    exact hQdeg ▸ hQm
  have hcan : ∀ c, 1 ≤ c → c < d → a ((n - d + c : ℕ) : ZMod n) = 0 := by
    intro c hc1 hcd
    simp only [a, ZMod.val_cast_of_lt (show n - d + c < n by omega)]
    exact coeff_eq_zero_of_natDegree_lt (hQdeg ▸ Nat.pow_lt_pow_right (by norm_num) (by omega))
  -- the kernel of `Q` has `2 ^ (n - d)` elements
  set S : Finset F := Finset.univ.filter fun x => Q.eval x = 0 with hSdef
  have hScard : S.card = 2 ^ (n - d) := by
    have hrange : LinearMap.range hQ.toLinearMap = W := by
      ext y
      rw [LinearMap.mem_range, hQW y]
      rfl
    have hker : finrank (ZMod 2) (LinearMap.ker hQ.toLinearMap) = n - d := by
      have := LinearMap.finrank_range_add_finrank_ker hQ.toLinearMap
      rw [hrange, hd, hn] at this
      omega
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker hQ.toLinearMap)
    rw [ZMod.card, hker] at h1
    rw [← h1, hSdef, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp)
  have hSzero : ∀ x ∈ S, linearizedEval a x = 0 := fun x hx =>
    hQa x ▸ (Finset.mem_filter.1 hx).2
  have hmemW : ∀ x, linearizedEval a x ∈ W := fun x =>
    (hQW _).2 ⟨x, hQa x⟩
  refine ⟨a, hmemW, ⟨hdn, hlead ▸ one_ne_zero, hcan, ?_, ?_⟩⟩
  · -- the constant coefficient is nonzero
    exact coeffPattern_zero_ne hn hdn hlead hcan hScard.ge hSzero
  · -- the gap property
    refine coeffPattern_gap hn hs hd hsW ?_ hlead hcan hScard.ge hSzero
    intro y hy
    obtain ⟨x, rfl⟩ := (hQW y).1 hy
    exact ⟨x, (hQa x).symm⟩

end Cslib
