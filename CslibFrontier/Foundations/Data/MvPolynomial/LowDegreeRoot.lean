/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.Shift
public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
public import CslibFrontier.Foundations.Data.MvPolynomial.TruncateTotalDegree
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.GeomSum

/-!
# The structure of a low-degree root of a polynomial equation

Let `P (x, y)` be a polynomial over a field and `f (x)` a polynomial of total degree at most
`d + 1` with `P (x, f) = 0`. Write `α = f (0)` and `gᵢ (x)` for the coefficient of `Tⁱ` in
`P (x, α + T)`. If `g₁ (0) ≠ 0`, that is, if `α` is a simple root of `P (0, y)`, then

`f = α + (A (g₀ - g₀ (0), …, g_{d+1} - g_{d+1} (0)))_{≤ d + 1}`

for a polynomial `A` of total degree at most `d + 1` in `d + 2` variables that depends only on
the constants `gᵢ (0)` (`MvPolynomial.exists_eq_truncate_aeval_of_root`); the subscript is the
truncation to total degree at most `d + 1` (`MvPolynomial.truncateTotalDegree`). So the root is
determined by `d + 2` coefficients of `P` in `y`, however large the degree of `P` in `y` is.
This is the structural statement behind the bounds on the complexity of roots of Dvir, Shpilka
and Yehudayoff [DvirShpilkaYehudayoff2009] and of Chou, Kumar and Solomon
[ChouKumarSolomon2019, Lemmas 5.1–5.3].

## Proof

"Vanishing to order `n` at the origin" is membership in the `n`-th power of Mathlib's
`MvPolynomial.idealOfVars`.

* *Universal root* (`exists_universalRoot`). For constants `c₀ = 0`, `c₁ ≠ 0`, `c₂, …` there is
  `A ∈ F[w₀, …, w_{d+1}]` without constant term, of degree at most `d + 1`, with
  `∑ᵢ (cᵢ + wᵢ) Aⁱ` vanishing to order `d + 2`. It is built degree by degree: the Newton step
  subtracts `c₁⁻¹` times the homogeneous component of lowest degree of the defect.
* *Uniqueness* (`sub_mem_pow_idealOfVars_of_roots`). Two polynomials without constant term
  that both solve `∑ᵢ gᵢ tⁱ = 0` to order `d + 2`, with `g₁ (0) ≠ 0`, agree to order `d + 2`:
  the difference of the two sums is the difference of the solutions times a polynomial with
  constant term `g₁ (0)`.
* Substituting `wᵢ ↦ gᵢ - gᵢ (0)` in `A` gives a solution of `∑ᵢ gᵢ tⁱ = 0` to order `d + 2`,
  because substituting polynomials without constant term preserves the order of vanishing
  (`aeval_mem_pow_idealOfVars`); and `t = f - α` is one too, the terms `gᵢ tⁱ` with `i > d + 1`
  vanishing to order `d + 2`.
* A root that is not simple at the origin (`exists_shift_eq_truncate_aeval_of_root`): in
  characteristic zero some iterated `y`-derivative of `P` has `f` as a root with nonvanishing
  next derivative; shifting `x` to a point where that derivative is not zero at `f` reduces to
  the simple case.

## Main results

* `MvPolynomial.exists_universalRoot`, `MvPolynomial.sub_mem_pow_idealOfVars_of_roots`.
* `MvPolynomial.exists_eq_truncate_aeval_of_root`: the structure of a root of degree at most
  `d + 1`.
* `MvPolynomial.exists_shift_eq_truncate_aeval_of_root`: the same for any root of a nonzero
  polynomial in characteristic zero, after differentiating in `y` and shifting `x`.

## References

* [Z. Dvir, A. Shpilka, A. Yehudayoff, *Hardness-randomness tradeoffs for bounded depth
  arithmetic circuits*][DvirShpilkaYehudayoff2009]
* [C.-N. Chou, M. Kumar, N. Solomon, *Closure results for polynomial
  factorization*][ChouKumarSolomon2019], §5
-/

public section

namespace MvPolynomial

open Finset

variable {σ τ F : Type*} [Field F]

/-! ### Order of vanishing at the origin -/

/-- A polynomial is in the ideal of the variables exactly when it has no constant term. -/
theorem mem_idealOfVars_iff_constantCoeff {p : MvPolynomial σ F} :
    p ∈ idealOfVars σ F ↔ constantCoeff p = 0 := by
  have h := mem_pow_idealOfVars_iff' (σ := σ) (R := F) 1 p
  rw [pow_one] at h
  rw [h, constantCoeff_eq]
  refine ⟨fun hp => hp 0 (by simp), fun hp x hx => ?_⟩
  obtain rfl : x = 0 := by
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
    exact hx
  exact hp

/-- A polynomial agrees with its truncation to degree at most `d` to order `d + 1`. -/
theorem sub_truncateTotalDegree_mem (d : ℕ) (p : MvPolynomial σ F) :
    p - truncateTotalDegree d p ∈ idealOfVars σ F ^ (d + 1) := by
  rw [mem_pow_idealOfVars_iff']
  intro x hx
  simp [coeff_truncateTotalDegree, Nat.lt_succ_iff.1 hx]

/-- Polynomials that agree to order `d + 1` have the same truncation to degree at most `d`. -/
theorem truncateTotalDegree_eq_of_sub_mem {d : ℕ} {p q : MvPolynomial σ F}
    (h : p - q ∈ idealOfVars σ F ^ (d + 1)) :
    truncateTotalDegree d p = truncateTotalDegree d q := by
  rw [mem_pow_idealOfVars_iff'] at h
  ext x
  rw [coeff_truncateTotalDegree, coeff_truncateTotalDegree]
  split_ifs with hx
  · have := h x (Nat.lt_succ_of_le hx)
    rwa [coeff_sub, sub_eq_zero] at this
  · rfl

/-- A polynomial vanishing to order `n` differs from its homogeneous component of degree `n` by
a polynomial vanishing to order `n + 1`. -/
theorem sub_homogeneousComponent_mem {n : ℕ} {p : MvPolynomial σ F}
    (hp : p ∈ idealOfVars σ F ^ n) :
    p - homogeneousComponent n p ∈ idealOfVars σ F ^ (n + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hp ⊢
  intro x hx
  rw [coeff_sub, coeff_homogeneousComponent]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    exact hp x (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx) h)

/-- The homogeneous component of degree `n` vanishes to order `n`. -/
theorem homogeneousComponent_mem_pow_idealOfVars (n : ℕ) (p : MvPolynomial σ F) :
    homogeneousComponent n p ∈ idealOfVars σ F ^ n := by
  rw [mem_pow_idealOfVars_iff']
  intro x hx
  simp [coeff_homogeneousComponent, hx.ne]

/-- Substituting polynomials without constant term preserves the order of vanishing. -/
theorem aeval_mem_pow_idealOfVars {g : σ → MvPolynomial τ F} (hg : ∀ i, g i ∈ idealOfVars τ F)
    {n : ℕ} {p : MvPolynomial σ F} (hp : p ∈ idealOfVars σ F ^ n) :
    aeval g p ∈ idealOfVars τ F ^ n := by
  have hle : (idealOfVars σ F).map (aeval g : MvPolynomial σ F →ₐ[F] MvPolynomial τ F) ≤
      idealOfVars τ F := by
    rw [idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [aeval_X]
    exact hg i
  have h := Ideal.mem_map_of_mem (aeval g : MvPolynomial σ F →ₐ[F] MvPolynomial τ F) hp
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hle n h

/-! ### Two solutions of one equation -/

private theorem constantCoeff_geom_sum₂ {t t' : MvPolynomial τ F}
    (ht : constantCoeff t = 0) (ht' : constantCoeff t' = 0) (i : ℕ) :
    constantCoeff (∑ j ∈ range i, t ^ j * t' ^ (i - 1 - j)) = if i = 1 then 1 else 0 := by
  rw [map_sum]
  simp only [map_mul, map_pow, ht, ht']
  rcases i with _ | _ | i
  · simp
  · simp
  · simp only [show ¬ (i + 1 + 1 = 1) by omega, ↓reduceIte]
    refine sum_eq_zero fun j hj => ?_
    rcases j with _ | j
    · rw [pow_zero, one_mul, zero_pow (by omega)]
    · rw [zero_pow (Nat.succ_ne_zero j), zero_mul]

/-- The difference of `∑ᵢ aᵢ tⁱ` at two polynomials without constant term is their difference
times a polynomial whose constant term is that of `a₁`. -/
private theorem exists_sum_mul_pow_sub {d : ℕ} (a : Fin (d + 2) → MvPolynomial τ F)
    {t t' : MvPolynomial τ F} (ht : t ∈ idealOfVars τ F) (ht' : t' ∈ idealOfVars τ F) :
    ∃ U : MvPolynomial τ F, U - C (constantCoeff (a 1)) ∈ idealOfVars τ F ∧
      ∑ i, a i * t ^ (i : ℕ) - ∑ i, a i * t' ^ (i : ℕ) = U * (t - t') := by
  refine ⟨∑ i : Fin (d + 2), a i * ∑ j ∈ range (i : ℕ), t ^ j * t' ^ ((i : ℕ) - 1 - j), ?_, ?_⟩
  · rw [mem_idealOfVars_iff_constantCoeff, map_sub, constantCoeff_C, map_sum, sub_eq_zero,
      sum_eq_single (1 : Fin (d + 2))]
    · rw [map_mul, constantCoeff_geom_sum₂ (mem_idealOfVars_iff_constantCoeff.1 ht)
        (mem_idealOfVars_iff_constantCoeff.1 ht')]
      simp
    · intro i _ hi
      rw [map_mul, constantCoeff_geom_sum₂ (mem_idealOfVars_iff_constantCoeff.1 ht)
        (mem_idealOfVars_iff_constantCoeff.1 ht')]
      simp [show ¬ ((i : ℕ) = 1) from fun h => hi (Fin.ext (by rw [h, Fin.val_one]))]
    · exact fun h => absurd (mem_univ _) h
  · rw [← sum_sub_distrib, sum_mul]
    exact sum_congr rfl fun i _ => by rw [mul_assoc, geom_sum₂_mul, mul_sub]

/-- **Uniqueness of a root to a given order.** If `t` and `t'` have no constant term and both
`∑ᵢ gᵢ tⁱ` and `∑ᵢ gᵢ t'ⁱ` vanish to order `d + 2`, and `g₁` has a nonzero constant term, then
`t` and `t'` agree to order `d + 2`. -/
theorem sub_mem_pow_idealOfVars_of_roots {d : ℕ} {g : Fin (d + 2) → MvPolynomial τ F}
    (hg1 : constantCoeff (g 1) ≠ 0) {t t' : MvPolynomial τ F} (ht : t ∈ idealOfVars τ F)
    (ht' : t' ∈ idealOfVars τ F)
    (h : ∑ i, g i * t ^ (i : ℕ) ∈ idealOfVars τ F ^ (d + 2))
    (h' : ∑ i, g i * t' ^ (i : ℕ) ∈ idealOfVars τ F ^ (d + 2)) :
    t - t' ∈ idealOfVars τ F ^ (d + 2) := by
  obtain ⟨U, hU, hUeq⟩ := exists_sum_mul_pow_sub g ht ht'
  have hUD : U * (t - t') ∈ idealOfVars τ F ^ (d + 2) := hUeq ▸ Ideal.sub_mem _ h h'
  have key : ∀ e, e ≤ d + 1 → t - t' ∈ idealOfVars τ F ^ (e + 1) := by
    intro e
    induction e with
    | zero =>
      intro _
      rw [zero_add, pow_one]
      exact Ideal.sub_mem _ ht ht'
    | succ e ih =>
      intro he
      have hD := ih (by omega)
      have h1 : (U - C (constantCoeff (g 1))) * (t - t') ∈ idealOfVars τ F ^ (e + 1 + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul hU hD
      have h2 : U * (t - t') ∈ idealOfVars τ F ^ (e + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega) hUD
      have h3 : C (constantCoeff (g 1)) * (t - t') ∈ idealOfVars τ F ^ (e + 1 + 1) := by
        have := Ideal.sub_mem _ h2 h1
        rwa [← sub_mul, sub_sub_cancel] at this
      have h4 := Ideal.mul_mem_left _ (C (constantCoeff (g 1))⁻¹) h3
      rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hg1, C_1, one_mul] at h4
  exact key (d + 1) le_rfl

/-! ### The universal root -/

/-- **The universal root.** For constants `c₀ = 0`, `c₁ ≠ 0`, `c₂, …, c_{d+1}` there is a
polynomial `A` in `d + 2` variables without constant term, of total degree at most `d + 1`,
such that `∑ᵢ (cᵢ + wᵢ) Aⁱ` vanishes to order `d + 2`. -/
theorem exists_universalRoot {d : ℕ} (c : Fin (d + 2) → F) (hc0 : c 0 = 0) (hc1 : c 1 ≠ 0) :
    ∃ A : MvPolynomial (Fin (d + 2)) F, A ∈ idealOfVars (Fin (d + 2)) F ∧
      A.totalDegree ≤ d + 1 ∧
      ∑ i, (C (c i) + X i) * A ^ (i : ℕ) ∈ idealOfVars (Fin (d + 2)) F ^ (d + 2) := by
  have key : ∀ e : ℕ, ∃ A : MvPolynomial (Fin (d + 2)) F, A ∈ idealOfVars (Fin (d + 2)) F ∧
      A.totalDegree ≤ e ∧
      ∑ i, (C (c i) + X i) * A ^ (i : ℕ) ∈ idealOfVars (Fin (d + 2)) F ^ (e + 1) := by
    intro e
    induction e with
    | zero =>
      refine ⟨0, zero_mem _, by simp, ?_⟩
      rw [zero_add, pow_one, mem_idealOfVars_iff_constantCoeff, Fin.sum_univ_succ]
      simp [hc0]
    | succ e ih =>
      obtain ⟨A, hA, hAdeg, hS⟩ := ih
      set S := ∑ i, (C (c i) + X i) * A ^ (i : ℕ) with hSdef
      set δ := C (-(c 1)⁻¹) * homogeneousComponent (e + 1) S with hδ
      have hδmem : δ ∈ idealOfVars (Fin (d + 2)) F ^ (e + 1) :=
        Ideal.mul_mem_left _ _ (homogeneousComponent_mem_pow_idealOfVars _ _)
      have hδ1 : δ ∈ idealOfVars (Fin (d + 2)) F := by
        have := Ideal.pow_le_pow_right (I := idealOfVars (Fin (d + 2)) F)
          (Nat.succ_le_succ (Nat.zero_le e)) hδmem
        rwa [pow_one] at this
      have hA' : A + δ ∈ idealOfVars (Fin (d + 2)) F := Ideal.add_mem _ hA hδ1
      obtain ⟨U, hU, hUeq⟩ := exists_sum_mul_pow_sub (fun i => C (c i) + X i) hA' hA
      simp only [map_add, constantCoeff_C, constantCoeff_X, add_zero, add_sub_cancel_left]
        at hU hUeq
      refine ⟨A + δ, hA', ?_, ?_⟩
      · refine (totalDegree_add _ _).trans (max_le (hAdeg.trans (Nat.le_succ e)) ?_)
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        exact (homogeneousComponent_isHomogeneous _ _).totalDegree_le
      · have h1 : S - homogeneousComponent (e + 1) S ∈
            idealOfVars (Fin (d + 2)) F ^ (e + 1 + 1) := sub_homogeneousComponent_mem hS
        have h2 : (U - C (c 1)) * δ ∈ idealOfVars (Fin (d + 2)) F ^ (e + 1 + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul hU hδmem
        have h3 : homogeneousComponent (e + 1) S + C (c 1) * δ = 0 := by
          rw [hδ, ← mul_assoc, ← C_mul, mul_neg, mul_inv_cancel₀ hc1, C_neg, C_1, neg_one_mul,
            add_neg_cancel]
        have hsum : ∑ i, (C (c i) + X i) * (A + δ) ^ (i : ℕ) =
            (S - homogeneousComponent (e + 1) S) + (U - C (c 1)) * δ +
              (homogeneousComponent (e + 1) S + C (c 1) * δ) := by
          have hSA : ∑ i, (C (c i) + X i) * (A + δ) ^ (i : ℕ) = S + U * δ := by
            rw [← hUeq]
            ring
          rw [hSA]
          ring
        rw [hsum, h3, add_zero]
        exact Ideal.add_mem _ h1 h2
  obtain ⟨A, hA, hAdeg, hS⟩ := key (d + 1)
  exact ⟨A, hA, hAdeg, hS⟩

/-! ### The structure of a root -/

/-- **The structure of a low-degree root.** Let `P` be a polynomial in `y` over `F[x]` and `f`
a polynomial of total degree at most `d + 1` with `P (f) = 0`. Let `α` be the constant term of
`f` and `gᵢ` the coefficient of `Tⁱ` in `P (α + T)`. If the constant term of `g₁` is not zero,
then `f = α + (A (gᵢ - gᵢ (0)))_{≤ d + 1}` for a polynomial `A` of total degree at most `d + 1`
in `d + 2` variables. -/
theorem exists_eq_truncate_aeval_of_root {P : Polynomial (MvPolynomial σ F)}
    {f : MvPolynomial σ F} {d : ℕ} (hf : f.totalDegree ≤ d + 1) (hroot : P.eval f = 0)
    (hder : constantCoeff
      ((Polynomial.taylor (C (constantCoeff f)) P).coeff 1) ≠ 0) :
    ∃ A : MvPolynomial (Fin (d + 2)) F, A.totalDegree ≤ d + 1 ∧
      f = C (constantCoeff f) + truncateTotalDegree (d + 1) (aeval (fun i : Fin (d + 2) =>
        (Polynomial.taylor (C (constantCoeff f)) P).coeff i -
          C (constantCoeff ((Polynomial.taylor (C (constantCoeff f)) P).coeff i))) A) := by
  classical
  set α := constantCoeff f with hα
  set Q := Polynomial.taylor (C α) P with hQ
  set g : Fin (d + 2) → MvPolynomial σ F := fun i => Q.coeff i with hg
  set t := f - C α with ht
  have htmem : t ∈ idealOfVars σ F := by
    rw [mem_idealOfVars_iff_constantCoeff, ht, map_sub, constantCoeff_C, sub_self]
  -- `t` solves the equation to order `d + 2`
  have hQt : Q.eval t = 0 := by
    rw [hQ, Polynomial.taylor_eval, ht, sub_add_cancel, hroot]
  have hsum : ∑ i, g i * t ^ (i : ℕ) ∈ idealOfVars σ F ^ (d + 2) := by
    set N := max (Q.natDegree + 1) (d + 2) with hN
    have h1 : Q.eval t = ∑ i ∈ range N, Q.coeff i * t ^ i :=
      Polynomial.eval_eq_sum_range' (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)) t
    rw [hQt, ← sum_range_add_sum_Ico _ (le_max_right _ _ : d + 2 ≤ N)] at h1
    have h2 : ∑ i, g i * t ^ (i : ℕ) = ∑ i ∈ range (d + 2), Q.coeff i * t ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => Q.coeff i * t ^ i) (d + 2)
    rw [h2, eq_neg_of_add_eq_zero_left h1.symm]
    refine Ideal.neg_mem_iff _ |>.2 (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_)
    exact Ideal.pow_le_pow_right (mem_Ico.1 hi).1 (Ideal.pow_mem_pow htmem i)
  have hg0 : constantCoeff (g 0) = 0 := by
    have h := mem_idealOfVars_iff_constantCoeff.1
      (Ideal.pow_le_self (Nat.succ_ne_zero (d + 1)) hsum)
    rw [map_sum, Fin.sum_univ_succ] at h
    simpa [mem_idealOfVars_iff_constantCoeff.1 htmem] using h
  obtain ⟨A, hA, hAdeg, hSA⟩ :=
    exists_universalRoot (fun i => constantCoeff (g i)) hg0 hder
  set h : Fin (d + 2) → MvPolynomial σ F := fun i => g i - C (constantCoeff (g i)) with hh
  have hhmem : ∀ i, h i ∈ idealOfVars σ F := fun i => by
    rw [mem_idealOfVars_iff_constantCoeff, hh, map_sub, constantCoeff_C, sub_self]
  set t' := aeval h A with ht'
  have ht'mem : t' ∈ idealOfVars σ F := by
    have := aeval_mem_pow_idealOfVars hhmem (n := 1) (by rwa [pow_one])
    rwa [pow_one] at this
  have hsum' : ∑ i, g i * t' ^ (i : ℕ) ∈ idealOfVars σ F ^ (d + 2) := by
    have := aeval_mem_pow_idealOfVars hhmem hSA
    simpa [hh, ht'] using this
  have hsub := sub_mem_pow_idealOfVars_of_roots hder htmem ht'mem hsum hsum'
  refine ⟨A, hAdeg, ?_⟩
  have htdeg : t.totalDegree ≤ d + 1 := by
    refine (totalDegree_sub _ _).trans (max_le hf ?_)
    rw [totalDegree_C]
    exact Nat.zero_le _
  rw [← truncateTotalDegree_eq_of_sub_mem hsub, truncateTotalDegree_eq_self htdeg, ht,
    add_sub_cancel]

/-! ### Roots that are not simple at the origin -/

/-- In characteristic zero a root `f` of a nonzero polynomial `P` is a root of some iterated
derivative of `P` whose next derivative does not vanish at `f`. -/
theorem exists_iterate_derivative_eval_ne_zero [CharZero F] {P : Polynomial (MvPolynomial σ F)}
    (hP : P ≠ 0) {f : MvPolynomial σ F} (hroot : P.eval f = 0) :
    ∃ j : ℕ, (Polynomial.derivative^[j] P).eval f = 0 ∧
      (Polynomial.derivative^[j + 1] P).eval f ≠ 0 := by
  have hk : 0 < P.rootMultiplicity f := (Polynomial.rootMultiplicity_pos hP).2 hroot
  refine ⟨P.rootMultiplicity f - 1, ?_, ?_⟩
  · exact (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).1
      (Nat.sub_lt hk Nat.one_pos) _ le_rfl
  · intro h0
    refine lt_irrefl (P.rootMultiplicity f)
      ((Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).2 fun m hm => ?_)
    rcases Nat.lt_or_ge m (P.rootMultiplicity f) with hlt | hge
    · exact (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).1 hlt m le_rfl
    · obtain rfl : m = P.rootMultiplicity f - 1 + 1 := by omega
      exact h0

/-- **The structure of a low-degree root, in general.** Let `P ≠ 0` be a polynomial in `y` over
`F[x]`, in characteristic zero, and `f` a polynomial of total degree at most `d + 1` with
`P (f) = 0`. Then for some `j` and some point `x₀`, with `Q` the `j`-th `y`-derivative
of `P` shifted by `x₀`, `α = f (x₀)` and `gᵢ` the coefficient of `Tⁱ` in `Q (α + T)`, the
shifted root is `f (x + x₀) = α + (A (gᵢ - gᵢ (0)))_{≤ d + 1}` for a polynomial `A` of total
degree at most `d + 1` in `d + 2` variables. -/
theorem exists_shift_eq_truncate_aeval_of_root [CharZero F]
    {P : Polynomial (MvPolynomial σ F)} (hP : P ≠ 0) {f : MvPolynomial σ F} {d : ℕ}
    (hf : f.totalDegree ≤ d + 1) (hroot : P.eval f = 0) :
    ∃ (j : ℕ) (x₀ : σ → F) (A : MvPolynomial (Fin (d + 2)) F), A.totalDegree ≤ d + 1 ∧
      shift x₀ f = C (eval x₀ f) + truncateTotalDegree (d + 1) (aeval (fun i : Fin (d + 2) =>
        (Polynomial.taylor (C (eval x₀ f))
          ((Polynomial.derivative^[j] P).map (shift x₀ : _ →ₐ[F] _).toRingHom)).coeff i -
        C (constantCoeff ((Polynomial.taylor (C (eval x₀ f))
          ((Polynomial.derivative^[j] P).map (shift x₀ : _ →ₐ[F] _).toRingHom)).coeff i))) A) := by
  classical
  have : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨j, hj0, hj1⟩ := exists_iterate_derivative_eval_ne_zero hP hroot
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : σ → F,
      eval x₀ ((Polynomial.derivative^[j + 1] P).eval f) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hj1 (funext fun x => by rw [hall x, map_zero])
  set φ : MvPolynomial σ F →+* MvPolynomial σ F := (shift x₀ : _ →ₐ[F] _).toRingHom with hφ
  have hcc : ∀ p : MvPolynomial σ F, constantCoeff (φ p) = eval x₀ p := fun p => by
    have h := eval_shift x₀ 0 p
    simp only [Pi.zero_apply, zero_add] at h
    exact (RingHom.congr_fun eval_zero (φ p)).symm.trans h
  have hα : constantCoeff (shift x₀ f) = eval x₀ f := hcc f
  have hmapeval : ∀ R : Polynomial (MvPolynomial σ F),
      (R.map φ).eval (shift x₀ f) = φ (R.eval f) := fun R => by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom φ f
  set Q := (Polynomial.derivative^[j] P).map φ with hQ
  have hQroot : Q.eval (shift x₀ f) = 0 := by rw [hQ, hmapeval, hj0, map_zero]
  have hder : constantCoeff
      ((Polynomial.taylor (C (constantCoeff (shift x₀ f))) Q).coeff 1) ≠ 0 := by
    rw [Polynomial.taylor_coeff_one, hQ, ← Polynomial.iterate_derivative_map,
      ← Function.iterate_succ_apply' Polynomial.derivative, Polynomial.iterate_derivative_map]
    have hcceval : ∀ (R : Polynomial (MvPolynomial σ F)) (z : MvPolynomial σ F),
        constantCoeff (R.eval z) = (R.map constantCoeff).eval (constantCoeff z) := fun R z => by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    have hev : constantCoeff (((Polynomial.derivative^[j + 1] P).map φ).eval
        (C (constantCoeff (shift x₀ f)))) =
        constantCoeff (((Polynomial.derivative^[j + 1] P).map φ).eval (shift x₀ f)) := by
      rw [hcceval, hcceval, constantCoeff_C]
    rw [hev, hmapeval, hcc]
    exact hx₀
  have hdeg : (shift x₀ f).totalDegree ≤ d + 1 :=
    (totalDegree_aeval_le (fun i => (totalDegree_add _ _).trans
      (max_le (totalDegree_X i).le (by rw [totalDegree_C]; exact Nat.zero_le _))) f).trans hf
  obtain ⟨A, hAdeg, hA⟩ := exists_eq_truncate_aeval_of_root (f := shift x₀ f) hdeg hQroot hder
  rw [hα] at hA
  exact ⟨j, x₀, A, hAdeg, hA⟩

end MvPolynomial
