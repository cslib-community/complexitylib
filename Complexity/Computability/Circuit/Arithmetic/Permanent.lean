/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.Arithmetic.VNP
import Complexity.Foundations.Data.Matrix.Ryser
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# The permanent belongs to VNP

The permanent family `permFamily K` belongs to the existing nonuniform class `VNP K` over every
commutative ring `K`. Its witness is the inner polynomial of Ryser's formula
[Schauz, Theorem 1.2, p. 3][Schauz2006]:

`(∏ j, (2 * Y j - 1)) * ∏ i, ∑ j, Y j * X (i, j)`.

The first `n * n` variables are matrix entries in row-major order; the last `n` are Boolean
column selectors. The witness has degree at most `3 * n` and an arithmetic circuit with at most
`2 * n ^ 2 + 4 * n + 5` gates, constants included. Substituting Boolean selectors and summing
with the existing `booleanSum` yields the generic permanent as a formal polynomial. No field,
nontriviality or characteristic assumption is needed.

The witness is certified through the existing synthesis API. Only nonuniform circuit existence
and gate counts are proved; construction runtime is not certified. Valiant's VNP-hardness of
the permanent, including its restriction on characteristic, remains unproved here.

## Main definitions

* `Cslib.Circuits.Arithmetic.ryserPoly`: the explicit witness polynomial.

## Main results

* `Cslib.Circuits.Arithmetic.totalDegree_ryserPoly_le`: degree at most `3 * n`.
* `Cslib.Circuits.Arithmetic.exists_circuit_ryserPoly`: a quadratic gate bound for the witness.
* `Cslib.Circuits.Arithmetic.booleanSum_ryserPoly`: summing over selectors gives the permanent.
* `Cslib.Circuits.Arithmetic.permFamily_mem_VNP`: the permanent family is in `VNP`.

## References

* [U. Schauz, *Colorings and orientations of matrices and graphs*][Schauz2006], Theorem 1.2
* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]

The witness and Boolean substitution proof adapt the saved Complexitylib development at
revision `5b8acca7`; the synthesis proof and explicit gate bound are new.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

universe u

variable {R : Type u} [CommRing R]

/-- The inner polynomial of Ryser's formula in `n * n + n` variables: the first `n * n` variables
are the entries of `genericMatrix R n` and the last `n` variables are `{0, 1}`-valued column
indicators. -/
noncomputable def ryserPoly (R : Type u) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n * n + n)) R :=
  (∏ j : Fin n, (2 * X (Fin.natAdd (n * n) j) - 1)) *
    ∏ i : Fin n, ∑ j : Fin n,
      X (Fin.natAdd (n * n) j) * X (Fin.castAdd n (finProdFinEquiv (i, j)))

private theorem totalDegree_X_le' {σ : Type*} (i : σ) :
    (X i : MvPolynomial σ R).totalDegree ≤ 1 :=
  (totalDegree_monomial_le _ _).trans (by simp)

/-- The Ryser inner polynomial has total degree at most `3 * n`. -/
theorem totalDegree_ryserPoly_le (n : ℕ) : (ryserPoly R n).totalDegree ≤ 3 * n := by
  rw [ryserPoly]
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (∏ j : Fin n, (2 * X (Fin.natAdd (n * n) j) - 1 :
      MvPolynomial (Fin (n * n + n)) R)).totalDegree ≤ n := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => ?_
      _ = n := by simp
    rw [sub_eq_add_neg, show (2 : MvPolynomial (Fin (n * n + n)) R) = C 2 from (map_ofNat C 2).symm]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using totalDegree_X_le' _)
    · rw [← map_one C, ← map_neg C, totalDegree_C]
      omega
  have h2 : (∏ i : Fin n, ∑ j : Fin n,
      (X (Fin.natAdd (n * n) j) * X (Fin.castAdd n (finProdFinEquiv (i, j))) :
        MvPolynomial (Fin (n * n + n)) R)).totalDegree ≤ 2 * n := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum fun i _ => ?_
      _ = 2 * n := by simp [mul_comm]
    refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    exact Nat.add_le_add (totalDegree_X_le' _) (totalDegree_X_le' _)
  omega

/-- The polynomial family of Ryser inner polynomials over `R`. -/
private noncomputable def ryserFamily (R : Type u) [CommRing R] : PolynomialFamily R where
  vars n := n * n + n
  poly n := ryserPoly R n

/-- The Ryser inner polynomial family is a p-family. -/
private theorem isPFamily_ryserFamily : (ryserFamily R).IsPFamily :=
  ⟨(PolynomiallyBounded.id.mul PolynomiallyBounded.id).add PolynomiallyBounded.id,
    ((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).mono_of_le
      (totalDegree_ryserPoly_le (R := R))⟩

private noncomputable abbrev interp (n : ℕ) :=
  arithInterpretationWith R (C : R → MvPolynomial (Fin n) R)

private theorem synthesis_prod {N : ℕ}
    {s : Set ((Fin N → MvPolynomial (Fin N) R) → MvPolynomial (Fin N) R)}
    {ι : Type*} (indices : Finset ι)
    (factor : ι → (Fin N → MvPolynomial (Fin N) R) → MvPolynomial (Fin N) R)
    (cost : ι → ℕ) (hone : (fun _ => 1) ∈ s)
    (h : ∀ i ∈ indices, Synthesis (interp (R := R) N) s {factor i} (cost i)) :
    Synthesis (interp (R := R) N) s {fun x => ∏ i ∈ indices, factor i x}
      (∑ i ∈ indices, (cost i + 1)) := by
  have := Synthesis.finset_fold (· * ·) 1
    (fun f g => Synthesis.arith_mul (Set.mem_insert f {g}) (Set.mem_insert_of_mem f rfl))
    indices (Synthesis.of_mem hone) h
  simpa only [Finset.prod_eq_fold, Nat.add_zero] using this

private noncomputable abbrev witness (n : ℕ)
    (x : Fin (n * n + n) → MvPolynomial (Fin (n * n + n)) R) :=
  (∏ j : Fin n, (C 2 * x (Fin.natAdd (n * n) j) + C (-1))) *
    ∏ i : Fin n, ∑ j : Fin n,
      x (Fin.natAdd (n * n) j) * x (Fin.castAdd n (finProdFinEquiv (i, j)))

private theorem witness_X (n : ℕ) : witness (R := R) n X = ryserPoly R n := by
  simp only [witness, ryserPoly, map_ofNat, map_neg, map_one, sub_eq_add_neg]

private theorem synthesis_ryserPoly (n : ℕ) :
    Synthesis (interp (R := R) (n * n + n)) (inputs (n * n + n)) {witness (R := R) n}
      (2 * n ^ 2 + 4 * n + 5) := by
  let constants : Set ((Fin (n * n + n) → MvPolynomial (Fin (n * n + n)) R) →
      MvPolynomial (Fin (n * n + n)) R) :=
    (({fun _ => 0} ∪ {fun _ => 1}) ∪ {fun _ => C 2}) ∪ {fun _ => C (-1)}
  let s := inputs (n * n + n) ∪ constants
  have h0 : (fun _ => 0) ∈ s := by simp [s, constants]
  have h1 : (fun _ => 1) ∈ s := by simp [s, constants]
  have h2 : (fun _ => C (2 : R)) ∈ s := by simp [s, constants]
  have hn : (fun _ => C (-1 : R)) ∈ s := by simp [s, constants]
  have hx (i : Fin (n * n + n)) : (fun x => x i) ∈ s := Or.inl ⟨i, rfl⟩
  have hsign (j : Fin n) : Synthesis (interp (R := R) (n * n + n)) s
      {fun x => C 2 * x (Fin.natAdd (n * n) j) + C (-1)} 2 := by
    have hmul := Synthesis.arith_mul (constant := C) h2 (hx (Fin.natAdd (n * n) j))
    exact hmul.trans (Synthesis.arith_add (Set.mem_union_right _ rfl)
      (Set.mem_union_left _ hn))
  have hsigns := synthesis_prod univ _ (fun _ : Fin n => 2) h1 (fun j _ => hsign j)
  have hrow (i : Fin n) : Synthesis (interp (R := R) (n * n + n)) s
      {fun x => ∑ j : Fin n,
        x (Fin.natAdd (n * n) j) * x (Fin.castAdd n (finProdFinEquiv (i, j)))} (2 * n) := by
    have := Synthesis.arith_sum (constant := C) univ
      (fun j x => x (Fin.natAdd (n * n) j) * x (Fin.castAdd n (finProdFinEquiv (i, j))))
      (fun _ : Fin n => 1) h0
      (fun j _ => Synthesis.arith_mul (hx (Fin.natAdd (n * n) j))
        (hx (Fin.castAdd n (finProdFinEquiv (i, j)))))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_comm] using this
  have hrows := synthesis_prod univ _ (fun _ : Fin n => 2 * n) h1 (fun i _ => hrow i)
  have hbody := hsigns.combine hrows
    (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
  have hc0 : Synthesis (interp (R := R) (n * n + n)) (inputs (n * n + n)) {fun _ => 0} 1 := by
    simpa only [map_zero] using Synthesis.arith_const (constant := C) (0 : R)
  have hc1 : Synthesis (interp (R := R) (n * n + n)) (inputs (n * n + n)) {fun _ => 1} 1 := by
    simpa only [map_one] using Synthesis.arith_const (constant := C) (1 : R)
  have hc2 : Synthesis (interp (R := R) (n * n + n)) (inputs (n * n + n))
      {fun _ => C (2 : R)} 1 := Synthesis.arith_const 2
  have hcn : Synthesis (interp (R := R) (n * n + n)) (inputs (n * n + n))
      {fun _ => C (-1 : R)} 1 := Synthesis.arith_const (-1)
  have hc : Synthesis (interp (R := R) (n * n + n)) (inputs (n * n + n)) constants 4 :=
    ((hc0.union hc1).union hc2).union hcn
  refine (hc.trans hbody).mono Set.Subset.rfl Set.Subset.rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith

/-- A circuit computing the Ryser witness with at most `2 * n ^ 2 + 4 * n + 5` gates,
including constants. Only nonuniform existence and gate count are certified. -/
theorem exists_circuit_ryserPoly (n : ℕ) :
    ∃ c : Circuit (arithSignature R) (n * n + n) 1,
      c.polynomial 0 = ryserPoly R n ∧ c.size ≤ 2 * n ^ 2 + 4 * n + 5 := by
  obtain ⟨c, hc, hs⟩ := (synthesis_ryserPoly (R := R) n).exists_circuit_polynomial
  exact ⟨c, hc.trans (witness_X n), hs⟩

private theorem ryserFamily_mem_VP : ryserFamily R ∈ VP R :=
  VP.of_synthesis isPFamily_ryserFamily
    ((((PolynomiallyBounded.const 2).mul (PolynomiallyBounded.id.pow 2)).add
      ((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id)).add (PolynomiallyBounded.const 5))
    (witness (R := R)) witness_X synthesis_ryserPoly

/-- Summing `ryserPoly R n` over all `{0, 1}` assignments to the `n` indicator variables yields
the permanent of `genericMatrix R n`. -/
theorem booleanSum_ryserPoly (n : ℕ) :
    booleanSum n (ryserPoly R n) = (genericMatrix R n).permanent := by
  rw [Matrix.permanent_eq_ryser_bool, booleanSum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ryserPoly, map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_mul, map_ofNat, map_one, projection_X]
    simp only [booleanAssignment, Fin.append_right, Sum.elim_inr]
    cases e j <;> norm_num
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, projection_X, projection_X]
    simp only [booleanAssignment, Fin.append_right, Fin.append_left, Sum.elim_inr, Sum.elim_inl]
    cases e j <;> simp [genericMatrix]

/-- **The permanent family belongs to `VNP`** over every commutative ring `R`.
The witness has `n` selectors and is computed by polynomial-size arithmetic circuits. This
is the membership direction of Valiant's completeness theorem; no hardness is asserted. -/
theorem permFamily_mem_VNP : permFamily R ∈ VNP R :=
  ⟨fun n => n, ryserPoly R, ryserFamily_mem_VP, fun n => (booleanSum_ryserPoly n).symm⟩

end Cslib.Circuits.Arithmetic
