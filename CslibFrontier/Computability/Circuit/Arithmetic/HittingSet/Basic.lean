/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.AlgebraicIndependent
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.DerivativeClosed
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Polynomial hitting sets for small partial-derivative spaces

A finite set `H` of points is a *hitting set* for a class of polynomials if every nonzero
polynomial of the class is nonzero at some point of `H`. Over a field `F` of characteristic zero,
[Bhardwaj et al.][BhardwajEtAl2026] give an explicit hitting set of size
`poly (n, d, r)` for the `n`-variate polynomials of degree at most `d` that lie in a space of
dimension at most `r` closed under all partial derivatives; in particular for those whose space
of all partial derivatives has dimension at most `r`.

The generator is the curve `Gᵢ = ln (1 + (i + 1) t)` truncated below degree `B = n r ^ 2 + r`
(`logCurve`). A nonzero polynomial `f` of the class has `f (G) ≠ 0` (`aeval_logCurve_ne_zero`,
Theorem 1.1 of the source), because `f` of the untruncated series is not divisible by `t ^ B`.
Since `f (G)` is a univariate polynomial of degree at most `d B`, it is nonzero at one of the
points `t = 0, 1, …, d B`, which gives the hitting set `logHittingSet` of `d B + 1` points.

A sum of `s` `d`-th powers of linear forms lies in the span of the powers `ℓₖ ^ e`, `e ≤ d`,
which is closed under partial derivatives and has dimension at most `s (d + 1)`. So such sums
have a hitting set of size polynomial in `n`, `d` and `s` (`isHittingSet_sum_pow`).

## Main definitions

* `IsHittingSet`: a finite set of points that hits every nonzero polynomial of a class.
* `logCurve`: the truncated logarithmic curve.
* `logHittingSet`: the points of the curve at `t = 0, …, d (n r ^ 2 + r)`.

## Main results

* `aeval_logCurve_ne_zero`: Theorem 1.1 of the source.
* `isHittingSet_logHittingSet`, `card_logHittingSet_le`: the hitting set and its size.
* `isHittingSet_sum_pow`: sums of powers of linear forms.

## References

* [S. Bhardwaj, F. Lakhani, P. Mukhopadhyay, R. Saptharishi, P. Shastri,
  A. K. Sinhababu, *Hitting sets from derivations: Waring rank and noncommutative
  ABPs*][BhardwajEtAl2026], Theorem 1.1
-/

@[expose] public section

open scoped Polynomial PowerSeries

namespace Cslib.Circuits.Arithmetic

open Finset

/-- A finite set of points is a hitting set for a class of polynomials if every nonzero
polynomial of the class is nonzero at one of the points. -/
def IsHittingSet {F σ : Type*} [CommSemiring F] (H : Finset (σ → F))
    (𝒞 : Set (MvPolynomial σ F)) : Prop :=
  ∀ f ∈ 𝒞, f ≠ 0 → ∃ a ∈ H, MvPolynomial.eval a f ≠ 0

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The logarithmic curve truncated below degree `B`. -/
noncomputable def logCurve (B : ℕ) (i : Fin n) : F[X] := PowerSeries.trunc B (logSeries F n i)

open scoped Classical in
/-- The points of the truncated logarithmic curve at `t = 0, 1, …, d * (n * r ^ 2 + r)`. -/
noncomputable def logHittingSet (r d : ℕ) : Finset (Fin n → F) :=
  (range (d * (n * r ^ 2 + r) + 1)).image fun (k : ℕ) (i : Fin n) =>
    (logCurve F n (n * r ^ 2 + r) i).eval (k : F)

variable {F n}

theorem card_logHittingSet_le (r d : ℕ) :
    (logHittingSet F n r d).card ≤ d * (n * r ^ 2 + r) + 1 := by
  classical
  exact card_image_le.trans_eq (card_range _)

/-- Truncating the curve changes `f` of the curve only by a multiple of `t ^ B`. -/
private theorem X_pow_dvd_aeval_logCurve_sub (B : ℕ) (f : MvPolynomial (Fin n) F) :
    (PowerSeries.X : F⟦X⟧) ^ B ∣
      ((MvPolynomial.aeval (logCurve F n B) f : F[X]) : F⟦X⟧) -
        MvPolynomial.aeval (logSeries F n) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.coe_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Polynomial.coe_mul]
    have hi : (PowerSeries.X : F⟦X⟧) ^ B ∣
        ((logCurve F n B i : F[X]) : F⟦X⟧) - logSeries F n i := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, Polynomial.coeff_coe, logCurve, PowerSeries.coeff_trunc, ite_eq_left hm,
        sub_self]
    have h := dvd_add
      (Dvd.dvd.mul_left hi ((MvPolynomial.aeval (logCurve F n B) p : F[X]) : F⟦X⟧))
      (Dvd.dvd.mul_right hp (logSeries F n i))
    convert h using 1
    ring

variable {V : Submodule F (MvPolynomial (Fin n) F)}

/-- **Theorem 1.1 of the source.** A nonzero polynomial in a derivative-closed space of dimension
at most `r` does not vanish on the logarithmic curve truncated below degree `n * r ^ 2 + r`. -/
theorem aeval_logCurve_ne_zero (hV : ∀ i, ∀ p ∈ V, MvPolynomial.pderiv i p ∈ V)
    [Module.Finite F V] {r : ℕ} (hr : Module.finrank F V ≤ r) {f : MvPolynomial (Fin n) F}
    (hf : f ∈ V) (hf0 : f ≠ 0) :
    MvPolynomial.aeval (logCurve F n (n * r ^ 2 + r)) f ≠ 0 := by
  intro h0
  have h := X_pow_dvd_aeval_logCurve_sub (n * r ^ 2 + r) f
  rw [h0, Polynomial.coe_zero, zero_sub, dvd_neg] at h
  refine not_X_pow_dvd_aeval_logSeries (algebraicIndependent_logSeries F n) hV hf hf0
    ((pow_dvd_pow _ ?_).trans h)
  gcongr

private theorem natDegree_aeval_logCurve_le (B : ℕ) (f : MvPolynomial (Fin n) F) :
    (MvPolynomial.aeval (logCurve F n B) f).natDegree ≤ f.totalDegree * B := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hB (i : Fin n) : (logCurve F n B i).natDegree ≤ B := by
    rw [logCurve]
    cases B with
    | zero => simp
    | succ B => exact (PowerSeries.natDegree_trunc_lt _ B).le
  calc ∑ i, (logCurve F n B i ^ m i).natDegree
      ≤ ∑ i, m i * B := sum_le_sum fun i _ =>
        Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hB i))
    _ = (∑ i, m i) * B := (sum_mul _ _ _).symm
    _ ≤ f.totalDegree * B := by
        refine Nat.mul_le_mul_right _ ?_
        have h := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ fun _ => rfl] at h

private theorem eval_aeval_logCurve (B : ℕ) (f : MvPolynomial (Fin n) F) (x : F) :
    (MvPolynomial.aeval (logCurve F n B) f).eval x =
      MvPolynomial.eval (fun i => (logCurve F n B i).eval x) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The points of the logarithmic curve form a hitting set for the polynomials of degree at most
`d` that lie in a derivative-closed space of dimension at most `r`. -/
theorem isHittingSet_logHittingSet (r d : ℕ) :
    IsHittingSet (logHittingSet F n r d)
      {f | f.totalDegree ≤ d ∧ ∃ V : Submodule F (MvPolynomial (Fin n) F),
        (∀ i, ∀ p ∈ V, MvPolynomial.pderiv i p ∈ V) ∧ Module.Finite F V ∧
          Module.finrank F V ≤ r ∧ f ∈ V} := by
  rintro f ⟨hd, V, hV, hfin, hr, hf⟩ hf0
  classical
  set B := n * r ^ 2 + r with hB
  have hne := aeval_logCurve_ne_zero hV hr hf hf0
  have hdeg : (MvPolynomial.aeval (logCurve F n B) f).natDegree < d * B + 1 :=
    Nat.lt_succ_of_le ((natDegree_aeval_logCurve_le B f).trans (Nat.mul_le_mul_right _ hd))
  by_contra hall
  refine hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    ((range (d * B + 1)).image fun k : ℕ => (k : F)) ?_ ?_)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    rw [eval_aeval_logCurve]
    exact not_not.1 fun h => hall ⟨_, mem_image.2 ⟨k, hk, rfl⟩, h⟩
  · rwa [card_image_of_injective _ Nat.cast_injective, card_range]

/-- Sums of `s` `d`-th powers of linear forms in `n` variables have a hitting set of
`d * (n * (s * (d + 1)) ^ 2 + s * (d + 1)) + 1` points. -/
theorem isHittingSet_sum_pow (s d : ℕ) :
    IsHittingSet (logHittingSet F n (s * (d + 1)) d)
      {f | ∃ (c : Fin s → F) (a : Fin s → Fin n → F),
        f = ∑ k, c k • (∑ i, a k i • MvPolynomial.X i) ^ d} := by
  rintro f ⟨c, a, rfl⟩ hf0
  classical
  set ℓ : Fin s → MvPolynomial (Fin n) F := fun k => ∑ i, a k i • MvPolynomial.X i with hℓ
  set b : Fin s × Fin (d + 1) → MvPolynomial (Fin n) F := fun ke => ℓ ke.1 ^ (ke.2 : ℕ) with hb
  set V := Submodule.span F (Set.range b) with hVdef
  have hmem (k : Fin s) (e : ℕ) (he : e ≤ d) : ℓ k ^ e ∈ V :=
    Submodule.subset_span ⟨(k, ⟨e, Nat.lt_succ_of_le he⟩), rfl⟩
  have hpd (i : Fin n) (k : Fin s) : MvPolynomial.pderiv i (ℓ k) = MvPolynomial.C (a k i) := by
    simp only [hℓ, map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp
  refine isHittingSet_logHittingSet (s * (d + 1)) d _ ⟨?_, V, ?_, ?_, ?_, ?_⟩ hf0
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.totalDegree_smul_le _ _).trans
      ((MvPolynomial.totalDegree_pow _ _).trans ?_)
    have h1 : (ℓ k).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ =>
        (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X i).le)
    simpa using Nat.mul_le_mul_left d h1
  · intro i p hp
    refine Submodule.span_induction (p := fun q _ => MvPolynomial.pderiv i q ∈ V) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨⟨k, e⟩, rfl⟩
      simp only [hb, Derivation.leibniz_pow, hpd]
      refine V.smul_of_tower_mem _ ?_
      rw [smul_eq_mul, mul_comm, ← MvPolynomial.smul_eq_C_mul]
      exact V.smul_mem _ (hmem k _ (by have := e.2; omega))
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact V.add_mem hx hy
    · intro r x _ hx; rw [Derivation.map_smul]; exact V.smul_mem _ hx
  · exact Module.Finite.span_of_finite F (Set.finite_range b)
  · exact (finrank_range_le_card b).trans_eq (by simp)
  · exact V.sum_mem fun k _ => V.smul_mem _ (hmem k d le_rfl)

end Cslib.Circuits.Arithmetic
