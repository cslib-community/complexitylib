/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases

/-!
# Sums of products of affine forms over the Boolean cube

Let `R` be a commutative `𝔽₂`-algebra. For affine forms `Lₚ(c) = aₚ + ∑ᵥ cᵥ • bₚᵥ` in Boolean
variables `c : κ → 𝔽₂`, the sum of `∏ₚ Lₚ(c)` over the whole cube is the `|κ|`-th mixed finite
difference of the product. Expanding the product, a monomial survives the summation exactly when
it involves every variable, since a missing variable doubles its contribution. Hence the sum is
a sum over the assignments `ℓ : P → Option κ` of factors to variables (or to their constant term)
that cover every variable.

Two consequences are used for affine dispersers. If every covering assignment meets a vanishing
coefficient, the sum is zero. If there are as many factors as variables, the covering
assignments are the bijections, and the sum is the permanent of the coefficient matrix.

## Main results

* `Cslib.sum_cube_prod_affine`: the expansion over covering assignments.
* `Cslib.sum_cube_prod_affine_eq_zero`: vanishing when every covering assignment meets a zero
  coefficient.
* `Cslib.sum_cube_prod_affine_eq_permanent`: with as many factors as variables, the sum is the
  permanent of the coefficient matrix.
* `Cslib.prod_sub_mul_eq_sum`, `Cslib.prod_sub_eq_sum`: Boolean-cube expansion of a product of
  differences `∏ i, (f i - c * g i)` over any commutative ring.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib

variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R] {κ P : Type*} [Fintype κ] [DecidableEq κ]
  [Fintype P]

omit [Fintype κ] [DecidableEq κ] [Fintype P] in
/-- An affine form in Boolean variables, split over its constant term (`none`) and its variables:
the coefficient times the indicator of the chosen variable. -/
private theorem elim_smul_eq_mul (a : R) (b : κ → R) (c : κ → ZMod 2) (o : Option κ) :
    o.elim a (fun v => c v • b v) =
      o.elim a b * o.elim 1 (fun v => algebraMap (ZMod 2) R (c v)) := by
  cases o with
  | none => simp
  | some v => simp [Algebra.smul_def, mul_comm]

omit [Fintype P] in
private theorem prod_elim_algebraMap (ℓ : P → Option κ) [Fintype P] (c : κ → ZMod 2) :
    ∏ p, (ℓ p).elim 1 (fun v => algebraMap (ZMod 2) R (c v)) =
      if ∀ p v, ℓ p = some v → c v = 1 then 1 else 0 := by
  split_ifs with h
  · refine Finset.prod_eq_one fun p _ => ?_
    cases hp : ℓ p with
    | none => rfl
    | some v => simp [h p v hp]
  · push Not at h
    obtain ⟨p, v, hp, hv⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ p) ?_
    have : c v = 0 := by
      generalize c v = x at hv ⊢
      fin_cases x
      · rfl
      · exact absurd rfl hv
    simp [hp, this]

omit [DecidableEq κ] in
/-- The number of Boolean points that are `1` on every variable used by `ℓ` is even unless `ℓ`
uses every variable. -/
private theorem sum_cube_ite (ℓ : P → Option κ) [DecidableEq κ] :
    ∑ c : κ → ZMod 2, (if ∀ p v, ℓ p = some v → c v = 1 then (1 : R) else 0) =
      if ∀ v, ∃ p, ℓ p = some v then 1 else 0 := by
  classical
  let T : Finset κ := Finset.univ.filter fun v => ∃ p, ℓ p = some v
  let t : κ → Finset (ZMod 2) := fun v => if v ∈ T then {1} else Finset.univ
  have hmem : ∀ c : κ → ZMod 2,
      (∀ p v, ℓ p = some v → c v = 1) ↔ c ∈ Fintype.piFinset t := fun c => by
    rw [Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v ∈ T
      · obtain ⟨p, hp⟩ := (Finset.mem_filter.1 hv).2
        simp [t, hv, h p v hp]
      · simp [t, hv]
    · intro h p v hp
      have hv : v ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ v, p, hp⟩
      simpa [t, hv] using h v
  simp_rw [hmem]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Fintype.card_piFinset]
  have hprod : ∏ v, (t v).card = 2 ^ (Finset.univ.filter fun v => v ∉ T).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v ∈ T <;> simp [t, hv, ZMod.card]
  rw [hprod]
  split_ifs with hcov
  · have : (Finset.univ.filter fun v => v ∉ T) = ∅ := by
      refine Finset.filter_false_of_mem fun v _ => ?_
      simpa [T] using hcov v
    simp [this]
  · push Not at hcov
    obtain ⟨v, hv⟩ := hcov
    have hpos : 0 < (Finset.univ.filter fun v => v ∉ T).card :=
      Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, by simpa [T] using hv⟩⟩
    have h2 : (2 : R) = 0 := by
      rw [← map_ofNat (algebraMap (ZMod 2) R) 2, show (2 : ZMod 2) = 0 from rfl, map_zero]
    rw [Nat.cast_pow, Nat.cast_ofNat, h2, zero_pow hpos.ne']

/-- **Cube sum of a product of affine forms**: summing `∏ₚ (aₚ + ∑ᵥ cᵥ • bₚᵥ)` over the Boolean
cube leaves the assignments `ℓ` of factors to variables, or to the constant term (`none`), that
cover every variable; each contributes the product of the chosen coefficients. -/
theorem sum_cube_prod_affine [DecidableEq P] (a : P → R) (b : P → κ → R) :
    ∑ c : κ → ZMod 2, ∏ p, (a p + ∑ v, c v • b p v) =
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ : P → Option κ => ∀ v, ∃ p, ℓ p = some v),
        ∏ p, (ℓ p).elim (a p) (b p) := by
  have hsplit : ∀ c : κ → ZMod 2, ∀ p, a p + ∑ v, c v • b p v =
      ∑ o : Option κ, o.elim (a p) (fun v => c v • b p v) := fun c p => by
    rw [Fintype.sum_option]
    rfl
  simp_rw [hsplit, Fintype.prod_sum, elim_smul_eq_mul, Finset.prod_mul_distrib]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.mul_sum]
  simp_rw [prod_elim_algebraMap]
  rw [sum_cube_ite, mul_ite, mul_one, mul_zero]

/-- If every assignment covering all variables uses a vanishing coefficient, the cube sum of the
product of affine forms is zero. -/
theorem sum_cube_prod_affine_eq_zero (a : P → R) (b : P → κ → R)
    (h : ∀ ℓ : P → Option κ, (∀ v, ∃ p, ℓ p = some v) → ∃ p v, ℓ p = some v ∧ b p v = 0) :
    ∑ c : κ → ZMod 2, ∏ p, (a p + ∑ v, c v • b p v) = 0 := by
  classical
  rw [sum_cube_prod_affine]
  refine Finset.sum_eq_zero fun ℓ hℓ => ?_
  obtain ⟨p, v, hp, hv⟩ := h ℓ (Finset.mem_filter.1 hℓ).2
  exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp, hv])

/-- With as many affine factors as Boolean variables, the cube sum of their product is the
permanent of the matrix of linear coefficients: the constant terms do not contribute. -/
theorem sum_cube_prod_affine_eq_permanent (a : κ → R) (b : κ → κ → R) :
    ∑ c : κ → ZMod 2, ∏ p, (a p + ∑ v, c v • b p v) = (Matrix.of b).permanent := by
  classical
  rw [sum_cube_prod_affine]
  have himage : (Finset.univ.filter fun ℓ : κ → Option κ => ∀ v, ∃ p, ℓ p = some v) =
      Finset.univ.image fun π : Equiv.Perm κ => fun p => some (π p) := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hcov
      choose sec hsec using hcov
      have hinj : Function.Injective sec := fun v v' h => by
        have := (hsec v).symm.trans ((congrArg ℓ h).trans (hsec v'))
        exact Option.some_injective _ this
      have hbij : Function.Bijective sec := Finite.injective_iff_bijective.1 hinj
      refine ⟨(Equiv.ofBijective sec hbij).symm, funext fun p => ?_⟩
      obtain ⟨v, rfl⟩ := hbij.2 p
      rw [hsec v]
      congr 1
      exact (Equiv.ofBijective sec hbij).symm_apply_apply v
    · rintro ⟨π, rfl⟩ v
      exact ⟨π.symm v, by simp⟩
  rw [himage, Finset.sum_image fun π _ π' _ h => Equiv.ext fun p =>
    Option.some_injective _ (congrFun h p)]
  rw [Matrix.permanent, ← Equiv.sum_comp (Equiv.inv (Equiv.Perm κ))]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Equiv.prod_comp π]
  simp

/-- Expanding a product of `(f i - c * g i)` over Boolean choices pulls out `(-c)` to the number of
true bits. -/
theorem prod_sub_mul_eq_sum {R : Type*} [CommRing R] {n : ℕ} (f g : Fin n → R) (c : R) :
    (∏ i, (f i - c * g i)) = ∑ w : Fin n → Bool,
      (-c) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i := by
  have h (w : Fin n → Bool) :
      (∏ i, if w i then -(c * g i) else f i) =
        (-c) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i := by
    calc
      _ = ∏ i, (if w i then -c else 1) * (if w i then g i else f i) := by
        apply Finset.prod_congr rfl
        intro i _
        cases w i <;> simp
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite]
        simp only [Finset.prod_const, one_pow, mul_one, List.countP_ofFn, Finset.card_filter, id_eq]
  simp_rw [← h]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b then -(c * g i) else f i)]
  simp [sub_eq_add_neg, add_comm]

/-- Expanding a product of differences over Boolean choices: each term selects `g i` where `w i` is
true and `f i` where `w i` is false, weighted by `(-1)` to the number of true bits. -/
theorem prod_sub_eq_sum {R : Type*} [CommRing R] {n : ℕ} (f g : Fin n → R) :
    (∏ i, (f i - g i)) = ∑ w : Fin n → Bool,
      (-1 : R) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i := by
  simpa using prod_sub_mul_eq_sum f g 1

end Cslib
