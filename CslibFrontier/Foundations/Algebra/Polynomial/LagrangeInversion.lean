/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, Lagrange inversion for a fixed point of a polynomial)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Lagrange inversion for a fixed point of a polynomial

Let `R` be a commutative algebra over a field `F` of characteristic zero, `J` an ideal of `R`
and `G ∈ R[y]` a polynomial whose coefficients of `1` and `y` lie in `J`. If `f ∈ J` is a fixed
point of `G`, that is `G (f) = f`, then

`f ≡ ∑ m ∈ {1, …, N}, (1 / m) [y ^ (m - 1)] G ^ m   (mod J ^ e)`   whenever `2 e ≤ N`

(`Polynomial.sub_sum_coeff_pow_mem_of_eval_eq`), where `[y ^ j] Q` is the coefficient of `y ^ j`
in `Q`. So the fixed point is given, to any order, by coefficients of powers of `G`. This is the
Lagrange inversion formula in its implicit form ([Stanley1999, Theorem 5.4.2 and
Exercise 5.59]), stated with the `J`-adic error made explicit instead of with power series, and
it is the description of power-series roots that Bhattacharjee, Kumar, Rai, Ramanathan,
Saptharishi and Saraf [BhattacharjeeEtAl2025, Corollary 3.3] derive from a theorem of
Furstenberg.

More generally, for every polynomial `H`
(`Polynomial.sum_coeff_mul_pow_sub_eval_mem`, the Lagrange–Good form):

`H (f) ≡ ∑ n ∈ {0, …, N}, [y ^ n] (H (1 - G') G ^ n)   (mod J ^ e)`.

## Proof

The proof is finite and uses no power series. Write `T (Q) = ∑ n ≤ N, [y ^ n] (Q G ^ n)`.

* *Telescoping* (`sum_coeff_X_sub_mul`): `T ((y - G) K) = - [y ^ N] (K G ^ (N + 1))`.
* *The constant* (`sum_coeff_one_sub_derivative`):
  `T (1 - G') = 1 - [y ^ (N + 1)] G ^ (N + 1)`, because `(n + 1) [y ^ n] (G' G ^ n)` is
  `(n + 1) [y ^ (n + 1)] G ^ (n + 1)`.
* *Weights* (`HasWeight`). Give `c y ^ j` with `c ∈ J ^ a` the weight `2 a + j`, and say that
  `Q` has weight at least `n` if each of its terms has. Weights add under multiplication, `G`
  has weight at least `2`, and the coefficient of `y ^ j` in a polynomial of weight at least `n`
  lies in `J ^ ⌈(n - j) / 2⌉`. So the two error terms above lie in a high power of `J`.
* Since `G (f) = f`, `y - G = (y - f) (1 - D)` for a polynomial `D` of weight at least `1`, and
  so `(y - f) K = (y - G) K (1 + D + ⋯ + D ^ (M - 1)) + (y - f) D ^ M K`. The first part is
  handled by telescoping and the second has large weight. Hence `T ((y - f) K) ≡ 0`, and
  `T (H (1 - G')) ≡ H (f) T (1 - G') ≡ H (f)`.

For `H = y` the sum rearranges to `∑ m, (1 / m) [y ^ (m - 1)] G ^ m` up to one more term of
large weight.

## Main definitions

* `Polynomial.HasWeight`: the weight filtration of `R[y]` attached to an ideal of `R`.

## Main results

* `Polynomial.sum_coeff_mul_pow_sub_eval_mem`: the Lagrange–Good form.
* `Polynomial.sub_sum_coeff_pow_mem_of_eval_eq`: the fixed point as a sum of coefficients of
  powers.

## References

* [R. P. Stanley, *Enumerative Combinatorics, Volume 2*][Stanley1999], Theorem 5.4.2 and
  Exercise 5.59
* [S. Bhattacharjee, M. Kumar, S. Rai, V. Ramanathan, R. Saptharishi, S. Saraf, *Closure under
  factorization from a result of Furstenberg*][BhattacharjeeEtAl2025], Corollary 3.3
  (unrefereed preprint). The finite proof given here is not the proof of either source.
-/

@[expose] public section

namespace Polynomial

open Finset

variable {F R : Type*} [CommRing R] (J : Ideal R)

/-! ### The weight filtration -/

/-- `Q` has weight at least `n` for the ideal `J`: the coefficient of `y ^ j` lies in
`J ^ ⌈(n - j) / 2⌉`. A term `c y ^ j` with `c ∈ J ^ a` has weight `2 a + j`. -/
def HasWeight (n : ℕ) (Q : R[X]) : Prop :=
  ∀ j, Q.coeff j ∈ J ^ ((n - j + 1) / 2)

variable {J}

theorem hasWeight_zero (Q : R[X]) : HasWeight J 0 Q := fun j => by
  simp

theorem HasWeight.mul {m n : ℕ} {Q Q' : R[X]} (h : HasWeight J m Q) (h' : HasWeight J n Q') :
    HasWeight J (m + n) (Q * Q') := fun j => by
  rw [coeff_mul]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hx' := mem_antidiagonal.1 hx
  have hmul := Ideal.mul_mem_mul (h x.1) (h' x.2)
  rw [← pow_add] at hmul
  exact Ideal.pow_le_pow_right (by omega) hmul

theorem HasWeight.pow {n : ℕ} {Q : R[X]} (h : HasWeight J n Q) (k : ℕ) :
    HasWeight J (n * k) (Q ^ k) := by
  induction k with
  | zero => exact hasWeight_zero _
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact ih.mul h

/-- A polynomial whose coefficients of `1` and `y` lie in `J` has weight at least `2`. -/
theorem hasWeight_two_of_coeff_mem {G : R[X]} (h0 : G.coeff 0 ∈ J) (h1 : G.coeff 1 ∈ J) :
    HasWeight J 2 G := fun j => by
  rcases j with _ | _ | j
  · simpa using h0
  · simpa using h1
  · simp

/-- A polynomial whose constant coefficient lies in `J` has weight at least `1`. -/
theorem hasWeight_one_of_coeff_mem {D : R[X]} (h0 : D.coeff 0 ∈ J) : HasWeight J 1 D :=
  fun j => by
  rcases j with _ | j
  · simpa using h0
  · simp

/-! ### Telescoping -/

/-- `∑ n ≤ N, [y ^ n] ((y - G) K G ^ n) = - [y ^ N] (K G ^ (N + 1))`. -/
theorem sum_coeff_X_sub_mul (G K : R[X]) (N : ℕ) :
    ∑ n ∈ range (N + 1), ((X - G) * K * G ^ n).coeff n = -(K * G ^ (N + 1)).coeff N := by
  have hterm : ∀ n, ((X - G) * K * G ^ n).coeff n =
      (X * (K * G ^ n)).coeff n - (K * G ^ (n + 1)).coeff n := fun n => by
    have h : (X - G) * K * G ^ n = X * (K * G ^ n) - K * G ^ (n + 1) := by ring
    rw [h, coeff_sub]
  have h1 : ∑ n ∈ range (N + 1), (X * (K * G ^ n)).coeff n =
      ∑ n ∈ range N, (K * G ^ (n + 1)).coeff n := by
    rw [sum_range_succ', coeff_X_mul_zero, add_zero]
    exact sum_congr rfl fun n _ => coeff_X_mul _ _
  simp only [hterm, sum_sub_distrib]
  rw [h1, sum_range_succ (fun n => (K * G ^ (n + 1)).coeff n)]
  ring

/-! ### The constant -/

/-- `(n + 1) [y ^ j] (G' G ^ n) = (j + 1) [y ^ (j + 1)] G ^ (n + 1)`. -/
private theorem coeff_derivative_mul_pow (G : R[X]) (n j : ℕ) :
    ((n : R) + 1) * (derivative G * G ^ n).coeff j =
      (G ^ (n + 1)).coeff (j + 1) * ((j : R) + 1) := by
  have h := congrArg (fun Q : R[X] => Q.coeff j) (derivative_pow_succ G n)
  simp only [coeff_derivative] at h
  rw [h, mul_assoc, coeff_C_mul, mul_comm (G ^ n)]

variable (F) in
/-- `∑ n ≤ N, [y ^ n] ((1 - G') G ^ n) = 1 - [y ^ (N + 1)] G ^ (N + 1)`, over an algebra over a
field `F` of characteristic zero. -/
theorem sum_coeff_one_sub_derivative [Field F] [CharZero F] [Algebra F R] (G : R[X]) (N : ℕ) :
    ∑ n ∈ range (N + 1), ((1 - derivative G) * G ^ n).coeff n =
      1 - (G ^ (N + 1)).coeff (N + 1) := by
  have hterm : ∀ n, ((1 - derivative G) * G ^ n).coeff n =
      (G ^ n).coeff n - (G ^ (n + 1)).coeff (n + 1) := fun n => by
    rw [sub_mul, one_mul, coeff_sub]
    congr 1
    have h := coeff_derivative_mul_pow G n n
    have hn : ((n : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h' : ((n : F) + 1) • (derivative G * G ^ n).coeff n =
        ((n : F) + 1) • (G ^ (n + 1)).coeff (n + 1) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_add, map_natCast, map_one, h, mul_comm]
    have h'' := congrArg (fun x => ((n : F) + 1)⁻¹ • x) h'
    simpa [smul_smul, inv_mul_cancel₀ hn] using h''
  simp only [hterm]
  rw [sum_range_sub' (fun n => (G ^ n).coeff n)]
  simp

/-! ### The fixed point -/

/-- The sum `∑ n ≤ N, [y ^ n] (Q G ^ n)` is small when `Q` has large weight. -/
private theorem sum_coeff_mul_pow_mem {G : R[X]} (hG : HasWeight J 2 G) {M : ℕ} {Q : R[X]}
    (hQ : HasWeight J M Q) (N : ℕ) :
    ∑ n ∈ range (N + 1), (Q * G ^ n).coeff n ∈ J ^ ((M + 1) / 2) :=
  Submodule.sum_mem _ fun n _ =>
    Ideal.pow_le_pow_right (by omega) ((hQ.mul (hG.pow n)) n)

/-- **Lagrange inversion, Lagrange–Good form.** Let `G` be a polynomial whose coefficients of
`1` and `y` lie in the ideal `J`, and `f ∈ J` with `G (f) = f`. Then for every polynomial `H`,
`∑ n ≤ N, [y ^ n] (H (1 - G') G ^ n) ≡ H (f)` modulo `J ^ e`, as soon as `2 e ≤ N`. -/
theorem sum_coeff_mul_pow_sub_eval_mem [Field F] [CharZero F] [Algebra F R] {G : R[X]}
    (h0 : G.coeff 0 ∈ J) (h1 : G.coeff 1 ∈ J) {f : R} (hf : f ∈ J) (hfix : G.eval f = f)
    (H : R[X]) {e N : ℕ} (hN : 2 * e ≤ N) :
    ∑ n ∈ range (N + 1), (H * (1 - derivative G) * G ^ n).coeff n - H.eval f ∈ J ^ e := by
  have hG : HasWeight J 2 G := hasWeight_two_of_coeff_mem h0 h1
  -- `G - f = (y - f) D` with `D` of weight at least one
  obtain ⟨D, hD⟩ : X - C f ∣ G - C f := by
    have h := X_sub_C_dvd_sub_C_eval (a := f) (p := G)
    rwa [hfix] at h
  have hD0 : D.coeff 0 ∈ J := by
    have h := congrArg (fun Q : R[X] => Q.coeff 1) hD
    simp only [coeff_sub, coeff_C_succ, sub_zero, sub_mul, coeff_X_mul, coeff_C_mul] at h
    have h' : D.coeff 0 = G.coeff 1 + f * D.coeff 1 := by rw [h]; ring
    rw [h']
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_right _ _ hf)
  have hDw : HasWeight J 1 D := hasWeight_one_of_coeff_mem hD0
  have hfac : X - G = (X - C f) * (1 - D) := by
    have : G = C f + (X - C f) * D := by rw [← hD]; ring
    rw [this]
    ring
  -- `H = H (f) + (y - f) K`
  obtain ⟨K, hK⟩ : X - C f ∣ H - C (H.eval f) := X_sub_C_dvd_sub_C_eval
  set E := ∑ i ∈ range (2 * e), D ^ i with hE
  have hgeom : (X - C f) * K * (1 - derivative G) =
      (X - G) * (K * (1 - derivative G) * E) +
        (X - C f) * K * (1 - derivative G) * D ^ (2 * e) := by
    have h : (1 - D) * E = 1 - D ^ (2 * e) := by
      rw [hE]
      exact mul_neg_geom_sum D (2 * e)
    rw [hfac]
    linear_combination (-((X - C f) * K * (1 - derivative G))) * h
  have hH : H * (1 - derivative G) = C (H.eval f) * (1 - derivative G) +
      ((X - G) * (K * (1 - derivative G) * E) +
        (X - C f) * K * (1 - derivative G) * D ^ (2 * e)) := by
    rw [← hgeom, ← hK]
    ring
  have hsum : ∑ n ∈ range (N + 1), (H * (1 - derivative G) * G ^ n).coeff n =
      H.eval f * (1 - (G ^ (N + 1)).coeff (N + 1)) +
        (-(K * (1 - derivative G) * E * G ^ (N + 1)).coeff N +
          ∑ n ∈ range (N + 1),
            ((X - C f) * K * (1 - derivative G) * D ^ (2 * e) * G ^ n).coeff n) := by
    rw [← sum_coeff_one_sub_derivative F G N, ← sum_coeff_X_sub_mul, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [hH, add_mul, add_mul, coeff_add, coeff_add, mul_assoc (C _), coeff_C_mul]
  rw [hsum]
  have e1 : (G ^ (N + 1)).coeff (N + 1) ∈ J ^ e :=
    Ideal.pow_le_pow_right (by omega) ((hG.pow (N + 1)) (N + 1))
  have e2 : (K * (1 - derivative G) * E * G ^ (N + 1)).coeff N ∈ J ^ e :=
    Ideal.pow_le_pow_right (by omega)
      (((hasWeight_zero (J := J) (K * (1 - derivative G) * E)).mul (hG.pow (N + 1))) N)
  have e3 : ∑ n ∈ range (N + 1),
      ((X - C f) * K * (1 - derivative G) * D ^ (2 * e) * G ^ n).coeff n ∈ J ^ e := by
    have hw : HasWeight J (0 + 1 * (2 * e)) ((X - C f) * K * (1 - derivative G) * D ^ (2 * e)) :=
      (hasWeight_zero _).mul (hDw.pow (2 * e))
    exact Ideal.pow_le_pow_right (by omega) (sum_coeff_mul_pow_mem hG hw N)
  have key : H.eval f * (1 - (G ^ (N + 1)).coeff (N + 1)) +
      (-(K * (1 - derivative G) * E * G ^ (N + 1)).coeff N +
        ∑ n ∈ range (N + 1),
          ((X - C f) * K * (1 - derivative G) * D ^ (2 * e) * G ^ n).coeff n) - H.eval f =
      -(H.eval f * (G ^ (N + 1)).coeff (N + 1)) +
        (-(K * (1 - derivative G) * E * G ^ (N + 1)).coeff N +
          ∑ n ∈ range (N + 1),
            ((X - C f) * K * (1 - derivative G) * D ^ (2 * e) * G ^ n).coeff n) := by ring
  rw [key]
  exact Ideal.add_mem _ (Ideal.neg_mem_iff _ |>.2 (Ideal.mul_mem_left _ _ e1))
    (Ideal.add_mem _ (Ideal.neg_mem_iff _ |>.2 e2) e3)

/-- **Lagrange inversion for a fixed point.** Let `G` be a polynomial whose coefficients of `1`
and `y` lie in the ideal `J`, and `f ∈ J` with `G (f) = f`. Then
`f ≡ ∑ m ∈ {1, …, N}, (1 / m) [y ^ (m - 1)] G ^ m` modulo `J ^ e`, as soon as `2 e ≤ N`. -/
theorem sub_sum_coeff_pow_mem_of_eval_eq [Field F] [CharZero F] [Algebra F R] {G : R[X]}
    (h0 : G.coeff 0 ∈ J) (h1 : G.coeff 1 ∈ J) {f : R} (hf : f ∈ J) (hfix : G.eval f = f)
    {e N : ℕ} (hN : 2 * e ≤ N) :
    f - ∑ m ∈ range N, ((m : F) + 1)⁻¹ • (G ^ (m + 1)).coeff m ∈ J ^ e := by
  have hG : HasWeight J 2 G := hasWeight_two_of_coeff_mem h0 h1
  have hmain := sum_coeff_mul_pow_sub_eval_mem (F := F) h0 h1 hf hfix X hN
  rw [eval_X] at hmain
  -- the terms of the Lagrange–Good sum for `H = y`
  have hterm : ∀ n, (X * (1 - derivative G) * G ^ (n + 1)).coeff (n + 1) =
      (G ^ (n + 1)).coeff n -
        (((n : F) + 1) * ((n : F) + 2)⁻¹) • (G ^ (n + 2)).coeff (n + 1) := fun n => by
    have h := coeff_derivative_mul_pow G (n + 1) n
    have hn : ((n : F) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    have h' : (derivative G * G ^ (n + 1)).coeff n =
        (((n : F) + 1) * ((n : F) + 2)⁻¹) • (G ^ (n + 2)).coeff (n + 1) := by
      have h2 : ((n : F) + 2) • (derivative G * G ^ (n + 1)).coeff n =
          ((n : F) + 1) • (G ^ (n + 2)).coeff (n + 1) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_add, map_add, map_natCast, map_one,
          map_ofNat, mul_comm _ ((G ^ (n + 2)).coeff (n + 1)), ← h]
        push_cast
        ring
      have h3 := congrArg (fun x => ((n : F) + 2)⁻¹ • x) h2
      simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at h3
      rw [h3, mul_comm]
    have hx : X * (1 - derivative G) * G ^ (n + 1) =
        X * (G ^ (n + 1) - derivative G * G ^ (n + 1)) := by ring
    rw [hx, coeff_X_mul, coeff_sub, h']
  have hsum : ∑ n ∈ range (N + 1), (X * (1 - derivative G) * G ^ n).coeff n =
      ∑ m ∈ range N, ((m : F) + 1)⁻¹ • (G ^ (m + 1)).coeff m -
        (((N : F)) * ((N : F) + 1)⁻¹) • (G ^ (N + 1)).coeff N := by
    rw [sum_range_succ', mul_assoc, coeff_X_mul_zero, add_zero]
    simp only [hterm, sum_sub_distrib]
    have hshift : ∑ n ∈ range N,
        (((n : F) + 1) * ((n : F) + 2)⁻¹) • (G ^ (n + 2)).coeff (n + 1) =
        ∑ n ∈ range N, ((n : F) * ((n : F) + 1)⁻¹) • (G ^ (n + 1)).coeff n +
          ((N : F) * ((N : F) + 1)⁻¹) • (G ^ (N + 1)).coeff N := by
      have h := sum_range_succ' (fun n => ((n : F) * ((n : F) + 1)⁻¹) • (G ^ (n + 1)).coeff n) N
      rw [sum_range_succ] at h
      simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, Nat.cast_add, Nat.cast_one,
        add_assoc, one_add_one_eq_two] at h
      exact h.symm
    rw [hshift, ← sub_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    have hm : ((m : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [← one_smul F ((G ^ (m + 1)).coeff m), smul_smul, smul_smul, ← sub_smul, mul_one, mul_one]
    congr 1
    calc (1 : F) - (m : F) * ((m : F) + 1)⁻¹
        = (((m : F) + 1) - (m : F)) * ((m : F) + 1)⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hm]
      _ = ((m : F) + 1)⁻¹ := by rw [add_sub_cancel_left, one_mul]
  rw [hsum] at hmain
  have htail : (((N : F)) * ((N : F) + 1)⁻¹) • (G ^ (N + 1)).coeff N ∈ J ^ e :=
    Submodule.smul_of_tower_mem _ _
      (Ideal.pow_le_pow_right (by omega) ((hG.pow (N + 1)) N))
  have hres := Ideal.sub_mem _ (Ideal.neg_mem_iff _ |>.2 hmain) htail
  have heq : f - ∑ m ∈ range N, ((m : F) + 1)⁻¹ • (G ^ (m + 1)).coeff m =
      -(∑ m ∈ range N, ((m : F) + 1)⁻¹ • (G ^ (m + 1)).coeff m -
        (((N : F)) * ((N : F) + 1)⁻¹) • (G ^ (N + 1)).coeff N - f) -
        (((N : F)) * ((N : F) + 1)⁻¹) • (G ^ (N + 1)).coeff N := by ring
  rw [heq]
  exact hres

end Polynomial
