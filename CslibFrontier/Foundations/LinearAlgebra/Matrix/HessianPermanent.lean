/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Hessians of the generic permanent)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.HessianDeterminant
import CslibFrontier.Foundations.GroupTheory.Perm.Fixing
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Module

/-!
# The Mignon–Ressayre Hessian of the permanent

Fix `o : ι` and let `N = card ι`. The *Mignon–Ressayre point* is the all-ones `ι × ι` matrix with
`1 - N` at `(o, o)`. The generic permanent vanishes there, and its Hessian at entries `(r, c)` and
`(r', c')` is
`(N - 2)! · [r ≠ r'][c ≠ c'] - N · (N - 3)! · [r, r', o distinct][c, c', o distinct]`.
This matrix is `p • (J - 1) ⊗ (J - 1) + s • (D (J - 1) D) ⊗ (D (J - 1) D)`, where `J` is the
all-ones matrix and `D` the diagonal projection away from `o`. The algebraic identities
`J J = N J`, `J D J = (N - 1) J` and `D D = D` show that it is invertible when `N - 1`, `p` and
`p + s` are nonzero. Here `p = (N - 2)!` and `p + s = -2 · (N - 3)!` for `N ≥ 3`, and `2` divides
`(N - 1)!`. So the Hessian has full rank `N ^ 2` whenever `(N - 1)! ≠ 0` in the field, that is,
in characteristic `0` or in a characteristic at least `N`
[Mignon and Ressayre][MignonRessayre2004].

Together with the upper bound `Matrix.rank_hessian_det_le`, this gives the Mignon–Ressayre
inequality: if the generic `N × N` permanent is the determinant of a `κ × κ` matrix of affine
polynomials, then `N ^ 2 ≤ 2 · card κ`.

Mignon and Ressayre state the result over fields of characteristic zero. The proof here only
uses `(N - 1)! ≠ 0`, that is, characteristic `0` or a characteristic at least `N`. Cai, Chen and
Li extend the bound to every characteristic other than `2` by a different point; that extension
is not formalized here.

## Main definitions

* `Matrix.mignonRessayrePoint`: the all-ones matrix with `1 - card ι` at `(o, o)`.

## Main results

* `Matrix.eval_permanent_mignonRessayrePoint`: the generic permanent vanishes at the point.
* `Matrix.hessian_permanent_mignonRessayrePoint`: the entries of the Hessian there.
* `Matrix.rank_hessian_permanent_mignonRessayrePoint`: the Hessian has full rank `N ^ 2`.
* `Matrix.card_mul_card_le_two_mul_card_of_permanent_eq_det`: the Mignon–Ressayre inequality.

## References

* [T. Mignon, N. Ressayre, *A quadratic bound for the determinant and permanent
  problem*][MignonRessayre2004]
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], chapter "Determinantal Complexity Lower Bounds",
  Lemma `lem:MR-perm-lb` and Theorem `thm:Mignon-Ressayre-mainthm`.
-/

public section

open MvPolynomial Equiv Finset

/-- If `J J = N J`, `J D J = (N - 1) J`, `D D = D`, and `N - 1`, `p` and `p + s` are nonzero, then
`X ↦ p • (J - 1) X (J - 1) + s • (D (J - 1) D) X (D (J - 1) D)` is injective. -/
private theorem sandwich_eq_zero {K R : Type*} [Field K] [Ring R] [Algebra K R] {J D X : R}
    {N p s : K} (hJJ : J * J = N • J) (hJDJ : J * D * J = (N - 1) • J) (hDD : D * D = D)
    (hN : N - 1 ≠ 0) (hp : p ≠ 0) (hps : p + s ≠ 0)
    (h : p • ((J - 1) * X * (J - 1)) + s • ((D * (J - 1) * D) * X * (D * (J - 1) * D)) = 0) :
    X = 0 := by
  have hJJ' : ∀ Y, J * (J * Y) = N • (J * Y) := fun Y => by rw [← mul_assoc, hJJ, smul_mul_assoc]
  have hJDJ' : ∀ Y, J * (D * (J * Y)) = (N - 1) • (J * Y) := fun Y => by
    rw [← mul_assoc, ← mul_assoc, hJDJ, smul_mul_assoc]
  have hDD' : ∀ Y, D * (D * Y) = D * Y := fun Y => by rw [← mul_assoc, hDD]
  have cancel : ∀ {c : K} {Y : R}, c ≠ 0 → c • Y = 0 → Y = 0 := by
    intro c Y hc hY
    rw [← one_smul K Y, ← inv_mul_cancel₀ hc, mul_smul, hY, smul_zero]
  set E := (N - 1) • D - D * J * D with hE
  have h1 : (p * (N - 1) ^ 2) • (D * X * D) + s • (E * X * E) = 0 := by
    have key := congrArg (fun Z => D * (J - (N - 1) • 1) * Z * ((J - (N - 1) • 1) * D)) h
    simp only [mul_zero, zero_mul] at key
    rw [← key, hE]
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one,
      one_mul, mul_assoc, smul_add, smul_sub, smul_smul, hJJ', hJDJ', hDD, hDD']
    module
  have h2 : E * X * E = 0 := by
    have key := congrArg (fun Z => E * Z * E) h1
    simp only [mul_zero, zero_mul] at key
    refine cancel (mul_ne_zero hps (pow_ne_zero 2 hN)) (Eq.trans ?_ key)
    rw [hE]
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one,
      one_mul, mul_assoc, smul_add, smul_sub, smul_smul, hJDJ', hDD, hDD']
    module
  have h3 : D * X * D = 0 := by
    rw [h2, smul_zero, add_zero] at h1
    exact cancel (mul_ne_zero hp (pow_ne_zero 2 hN)) h1
  have h4 : (J - 1) * X * (J - 1) = 0 := by
    have hB : (D * (J - 1) * D) * X * (D * (J - 1) * D) =
        D * (J - 1) * (D * X * D) * (J - 1) * D := by
      simp only [mul_assoc]
    rw [hB, h3, mul_zero, zero_mul, zero_mul, smul_zero, add_zero] at h
    exact cancel hp h
  have key := congrArg (fun Z => (J - (N - 1) • 1) * Z * (J - (N - 1) • 1)) h4
  simp only [mul_zero, zero_mul] at key
  refine cancel (pow_ne_zero 2 hN) (Eq.trans ?_ key)
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one,
    one_mul, mul_assoc, smul_sub, smul_smul, hJJ, hJJ']
  module

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

private theorem sum_ite_eq_zero_else_one (o : ι) :
    ∑ k : ι, (if k = o then (0 : K) else 1) = (Fintype.card ι : K) - 1 := by
  have : ∀ k : ι, (if k = o then (0 : K) else 1) = 1 - if k = o then 1 else 0 := fun k => by
    split_ifs <;> simp
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The structured matrix behind the Mignon–Ressayre Hessian is invertible. -/
private theorem rank_of_ite_sandwich (o : ι) {p s : K} (hN : (Fintype.card ι : K) - 1 ≠ 0)
    (hp : p ≠ 0) (hps : p + s ≠ 0) :
    (Matrix.of fun a b : ι × ι =>
        p * ((if a.1 = b.1 then 0 else 1) * (if b.2 = a.2 then 0 else 1)) +
          s * ((if a.1 = b.1 ∨ a.1 = o ∨ b.1 = o then 0 else 1) *
            (if b.2 = a.2 ∨ b.2 = o ∨ a.2 = o then 0 else 1))).rank =
      Fintype.card ι * Fintype.card ι := by
  set J : Matrix ι ι K := Matrix.of fun _ _ => 1 with hJ
  set D : Matrix ι ι K := Matrix.diagonal fun i => if i = o then 0 else 1 with hD
  have hJJ : J * J = (Fintype.card ι : K) • J := by
    ext i j
    simp [hJ, Matrix.mul_apply]
  have hJDJ : J * D * J = ((Fintype.card ι : K) - 1) • J := by
    ext i j
    simp only [hJ, hD]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.of_apply, one_mul, mul_one, Matrix.smul_apply,
      smul_eq_mul]
    exact sum_ite_eq_zero_else_one (K := K) o
  have hDD : D * D = D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1 with i : 1
    split_ifs <;> simp
  have hA : ∀ i j, (J - 1) i j = if i = j then 0 else 1 := fun i j => by
    by_cases h : i = j <;> simp [hJ, h]
  have hB : ∀ i j, (D * (J - 1) * D) i j = if i = j ∨ i = o ∨ j = o then 0 else 1 :=
    fun i j => by
      rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, hA]
      by_cases h : i = j <;> by_cases hi : i = o <;> by_cases hj : j = o <;> simp [h, hi, hj]
  set H := Matrix.of fun a b : ι × ι =>
        p * ((if a.1 = b.1 then 0 else 1) * (if b.2 = a.2 then 0 else 1)) +
          s * ((if a.1 = b.1 ∨ a.1 = o ∨ b.1 = o then 0 else 1) *
            (if b.2 = a.2 ∨ b.2 = o ∨ a.2 = o then 0 else 1)) with hH
  have hmul : ∀ u : ι × ι → K, ∀ r c, H.mulVec u (r, c) =
      (p • ((J - 1) * Matrix.of (fun r c => u (r, c)) * (J - 1)) +
        s • ((D * (J - 1) * D) * Matrix.of (fun r c => u (r, c)) * (D * (J - 1) * D))) r c := by
    intro u r c
    simp only [hH, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.add_apply,
      Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul, hA, hB,
      Finset.sum_mul, Finset.mul_sum, add_mul, Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) ?_ ?_ <;> rw [Finset.sum_comm] <;>
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hinj : Function.Injective H.mulVec := by
    intro u w huw
    have h0 : H.mulVec (u - w) = 0 := by rw [Matrix.mulVec_sub, huw, sub_self]
    have hX := sandwich_eq_zero hJJ hJDJ hDD hN hp hps
      (X := Matrix.of fun r c => (u - w) (r, c)) (by
        ext r c
        rw [← hmul, h0]
        rfl)
    funext ⟨r, c⟩
    have := congrFun (congrFun hX r) c
    simp only [Matrix.of_apply, Pi.sub_apply, Matrix.zero_apply] at this
    exact sub_eq_zero.1 this
  rw [Matrix.rank_of_isUnit _ (Matrix.mulVec_injective_iff_isUnit.1 hinj), Fintype.card_prod]

/-- The Mignon–Ressayre point: the all-ones matrix with `1 - card ι` at `(o, o)`. -/
def mignonRessayrePoint (o : ι) : ι × ι → K := fun p =>
  if p = (o, o) then 1 - Fintype.card ι else 1

theorem mignonRessayrePoint_apply (o : ι) (p : ι × ι) :
    mignonRessayrePoint (K := K) o p = if p = (o, o) then 1 - (Fintype.card ι : K) else 1 := by
  unfold mignonRessayrePoint
  rfl

private theorem prod_mignonRessayrePoint (o : ι) (σ : Perm ι) (S : Finset ι) :
    ∏ i ∈ S, mignonRessayrePoint (K := K) o (σ i, i) =
      if o ∈ S ∧ σ o = o then 1 - (Fintype.card ι : K) else 1 := by
  simp only [mignonRessayrePoint_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem o h.1 fun i _ hi =>
      ite_eq_right fun he => hi (congrArg Prod.snd he)]
    rw [ite_eq_left (by rw [h.2])]
  · refine Finset.prod_eq_one fun i hi => ite_eq_right fun he => h ?_
    have hi' : i = o := congrArg Prod.snd he
    subst hi'
    exact ⟨hi, congrArg Prod.fst he⟩

/-- The generic permanent vanishes at the Mignon–Ressayre point. -/
theorem eval_permanent_mignonRessayrePoint (o : ι) :
    eval (mignonRessayrePoint (K := K) o) (mvPolynomialX ι ι K).permanent = 0 := by
  rw [Matrix.permanent]
  simp only [mvPolynomialX_apply, map_sum, map_prod, eval_X, prod_mignonRessayrePoint, mem_univ,
    true_and]
  have hterm : ∀ σ : Perm ι, (if σ o = o then 1 - (Fintype.card ι : K) else 1) =
      1 + (-(Fintype.card ι : K)) * (if σ o = o then 1 else 0) := fun σ => by
    split_ifs <;> ring
  have hcard : #{σ : Perm ι | σ o = o} = (Fintype.card ι - 1).factorial := by
    simpa using Perm.card_filter_forall_eq_self {o}
  have : Nonempty ι := ⟨o⟩
  have hN : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, hcard, Finset.sum_const, card_univ, Fintype.card_perm,
    ← Nat.mul_factorial_pred hN]
  ring

private theorem card_perm_two (r c r' c' : ι) :
    #{σ : Perm ι | c ≠ c' ∧ σ c = r ∧ σ c' = r'} =
      if r = r' ∨ c' = c then 0 else (Fintype.card ι - 2).factorial := by
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro σ - ⟨hcc, hr, hr'⟩
    rcases h with h | h
    · exact hcc (σ.injective (hr.trans (h.trans hr'.symm)))
    · exact hcc h.symm
  · push Not at h
    obtain ⟨hrr, hcc⟩ := h
    have := Perm.card_filter_forall_eq_of_injOn {c, c'} (fun i => if i = c then r else r') (by
      intro x hx y hy hxy
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
        simp [hrr, hcc, Ne.symm hrr] at hxy ⊢)
    rw [card_pair (Ne.symm hcc)] at this
    rw [← this]
    congr 1
    ext σ
    simp [hcc, Ne.symm hcc]

private theorem card_perm_three (o r c r' c' : ι) :
    #{σ : Perm ι | (c ≠ c' ∧ σ c = r ∧ σ c' = r') ∧ (o ≠ c ∧ o ≠ c' ∧ σ o = o)} =
      if r = r' ∨ r = o ∨ r' = o ∨ c' = c ∨ c' = o ∨ c = o then 0
      else (Fintype.card ι - 3).factorial := by
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro σ - ⟨⟨hcc, hr, hr'⟩, hoc, hoc', ho⟩
    rcases h with h | h | h | h | h | h
    · exact hcc (σ.injective (hr.trans (h.trans hr'.symm)))
    · exact hoc (σ.injective (ho.trans (h.symm.trans hr.symm)))
    · exact hoc' (σ.injective (ho.trans (h.symm.trans hr'.symm)))
    · exact hcc h.symm
    · exact hoc' h.symm
    · exact hoc h.symm
  · push Not at h
    obtain ⟨hrr, hro, hr'o, hcc, hc'o, hco⟩ := h
    have := Perm.card_filter_forall_eq_of_injOn {c, c', o}
      (fun i => if i = c then r else if i = c' then r' else o) (by
      intro x hx y hy hxy
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢ <;>
        simp [hrr, hro, hr'o, hcc, Ne.symm hrr, Ne.symm hro, Ne.symm hr'o, Ne.symm hc'o,
          Ne.symm hco] at hxy ⊢)
    rw [card_insert_of_notMem (by simp [Ne.symm hcc, hco]), card_pair hc'o] at this
    rw [← this]
    congr 1
    ext σ
    simp [hcc, Ne.symm hcc, Ne.symm hco, Ne.symm hc'o, and_assoc]

/-- **The Hessian of the permanent at the Mignon–Ressayre point**: with `N = card ι`, its entry at
`(r, c)` and `(r', c')` is `(N - 2)! · [r ≠ r'][c ≠ c'] - N · (N - 3)! · [r, r', o distinct]
[c, c', o distinct]`. -/
theorem hessian_permanent_mignonRessayrePoint (o : ι) (a b : ι × ι) :
    hessian (mignonRessayrePoint (K := K) o) (mvPolynomialX ι ι K).permanent a b =
      ((Fintype.card ι - 2).factorial : K) *
          ((if a.1 = b.1 then 0 else 1) * (if b.2 = a.2 then 0 else 1)) +
        (-(Fintype.card ι : K) * ((Fintype.card ι - 3).factorial : K)) *
          ((if a.1 = b.1 ∨ a.1 = o ∨ b.1 = o then 0 else 1) *
            (if b.2 = a.2 ∨ b.2 = o ∨ a.2 = o then 0 else 1)) := by
  obtain ⟨r, c⟩ := a
  obtain ⟨r', c'⟩ := b
  rw [permanent_mvPolynomialX_eq_sum, hessian_sum_smul_prod_X]
  dsimp only
  have hterm : ∀ σ : Perm ι, (if c ≠ c' ∧ σ c = r ∧ σ c' = r' then
      (1 : K) * ∏ i ∈ (univ.erase c').erase c, mignonRessayrePoint o (σ i, i) else 0) =
      (if c ≠ c' ∧ σ c = r ∧ σ c' = r' then 1 else 0) +
        (-(Fintype.card ι : K)) * (if (c ≠ c' ∧ σ c = r ∧ σ c' = r') ∧
          (o ≠ c ∧ o ≠ c' ∧ σ o = o) then 1 else 0) := fun σ => by
    rw [prod_mignonRessayrePoint]
    simp only [mem_erase, mem_univ, and_true]
    split_ifs <;> first | ring1 | (exfalso; tauto)
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, card_perm_two, card_perm_three]
  split_ifs <;> first | (push_cast; ring1) | (exfalso; tauto)

/-- **Mignon–Ressayre lower bound for the permanent**: the Hessian of the generic `N × N`
permanent at the Mignon–Ressayre point has full rank `N ^ 2`, provided `N ≥ 2` and
`(N - 1)! ≠ 0` in `K` (characteristic `0` or at least `N`)
[Mignon and Ressayre][MignonRessayre2004]. -/
theorem rank_hessian_permanent_mignonRessayrePoint (o : ι)
    (hfact : ((Fintype.card ι - 1).factorial : K) ≠ 0) (hN : 2 ≤ Fintype.card ι) :
    (hessian (mignonRessayrePoint (K := K) o) (mvPolynomialX ι ι K).permanent).rank =
      Fintype.card ι * Fintype.card ι := by
  have hH : hessian (mignonRessayrePoint (K := K) o) (mvPolynomialX ι ι K).permanent =
      Matrix.of fun a b : ι × ι => ((Fintype.card ι - 2).factorial : K) *
          ((if a.1 = b.1 then 0 else 1) * (if b.2 = a.2 then 0 else 1)) +
        (-(Fintype.card ι : K) * ((Fintype.card ι - 3).factorial : K)) *
          ((if a.1 = b.1 ∨ a.1 = o ∨ b.1 = o then 0 else 1) *
            (if b.2 = a.2 ∨ b.2 = o ∨ a.2 = o then 0 else 1)) := by
    ext a b
    exact hessian_permanent_mignonRessayrePoint o a b
  rw [hH]
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 2 := ⟨_, (Nat.sub_add_cancel hN).symm⟩
  have h2 : ∀ j, k = j + 1 → (2 : K) ≠ 0 := fun j hj h2 => hfact (by
    obtain ⟨c, hc⟩ := Nat.dvd_factorial two_pos (show 2 ≤ Fintype.card ι - 1 by omega)
    rw [hc, Nat.cast_mul, Nat.cast_two, h2, zero_mul])
  rw [hk, show k + 2 - 1 = k + 1 from rfl, Nat.factorial_succ, Nat.cast_mul] at hfact
  obtain ⟨hk1, hkf⟩ := mul_ne_zero_iff.1 hfact
  refine rank_of_ite_sandwich o ?_ ?_ ?_
  · rw [hk]
    push_cast at hk1 ⊢
    convert hk1 using 1
    ring
  · rw [hk]
    exact hkf
  · rw [hk]
    rcases k with _ | j
    · norm_num
    · rw [show j + 1 + 2 - 2 = j + 1 from rfl, show j + 1 + 2 - 3 = j from rfl,
        Nat.factorial_succ]
      rw [Nat.factorial_succ, Nat.cast_mul] at hkf
      have hj : (j.factorial : K) ≠ 0 := right_ne_zero_of_mul hkf
      convert mul_ne_zero (neg_ne_zero.2 (h2 j rfl)) hj using 1
      push_cast
      ring

/-- **Mignon–Ressayre inequality**: if the generic `N × N` permanent is the determinant of a
`κ × κ` matrix of affine polynomials, then `N ^ 2 ≤ 2 · card κ`, provided `(N - 1)! ≠ 0` in `K`
(characteristic `0` or at least `N`) [Mignon and Ressayre][MignonRessayre2004]. -/
theorem card_mul_card_le_two_mul_card_of_permanent_eq_det {κ : Type*} [Fintype κ]
    [DecidableEq κ] (hfact : ((Fintype.card ι - 1).factorial : K) ≠ 0)
    (A : Matrix κ κ (MvPolynomial (ι × ι) K)) (hA : ∀ i j, (A i j).totalDegree ≤ 1)
    (hperm : (mvPolynomialX ι ι K).permanent = A.det) :
    Fintype.card ι * Fintype.card ι ≤ 2 * Fintype.card κ := by
  rcases Nat.lt_or_ge (Fintype.card ι) 2 with hN | hN
  · rcases Nat.lt_or_ge (Fintype.card ι) 1 with h0 | h1
    · have : Fintype.card ι = 0 := by omega
      simp [this]
    · have hN1 : Fintype.card ι = 1 := by omega
      rw [hN1]
      by_contra hκ
      have hκ0 : Fintype.card κ = 0 := by omega
      have : IsEmpty κ := Fintype.card_eq_zero_iff.1 hκ0
      obtain ⟨o⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
      have h0 := congrArg (eval (0 : ι × ι → K)) hperm
      rw [Matrix.det_isEmpty, map_one, Matrix.permanent] at h0
      simp only [map_sum, map_prod, mvPolynomialX_apply, eval_X, Pi.zero_apply] at h0
      rw [Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (mem_univ o) rfl] at h0
      exact zero_ne_one h0
  · obtain ⟨o⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hx : eval (mignonRessayrePoint (K := K) o) A.det = 0 := by
      rw [← hperm]
      exact eval_permanent_mignonRessayrePoint o
    have := rank_hessian_det_le A hA hx
    rwa [← hperm, rank_hessian_permanent_mignonRessayrePoint o hfact hN] at this

end Matrix
