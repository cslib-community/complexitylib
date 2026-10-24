/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SumOfTerms
public import Complexity.Computability.Circuit.Arithmetic.Waring.Basic
public import Complexity.Foundations.Data.MvPolynomial.Catalecticant
public import Mathlib.Data.Nat.Choose.Central
import Complexity.Foundations.LinearAlgebra.Matrix.Rank
import Complexity.Foundations.LinearAlgebra.Rank
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finset.Powerset

/-!
# Waring term counts for a squarefree monomial

A sum of scaled `d`-th powers of linear forms representing the product of `d` variables needs
at least `choose d k` terms, for every split `k`. At degree `2*n`, the middle split gives the
central binomial coefficient. The field may be any characteristic-zero field.

Restrict the normalized coefficient matrix to squarefree row exponents of degree `k` and
complemented column exponents. Each power term gives rank at most one; the target gives a
nonzero scalar identity. The finite-sum endpoint needs no circuit encoding. The circuit endpoint
uses native circuits adding dictionary terms, with free additions and wiring. A reused term
gate is charged once. These are bounds for this restricted representation model, not for
unrestricted arithmetic circuits. All computation premises are formal polynomial equalities.

## Main results

* `Cslib.Circuits.Waring.choose_le_card`, `Cslib.Circuits.Waring.centralBinom_le_card`:
  lower bounds for ordinary finite sums.
* `Cslib.Circuits.Waring.choose_le_cost`, `Cslib.Circuits.Waring.centralBinom_le_cost`:
  lower bounds for any selected output of a zero-input sum-of-terms circuit.

## References

* Ported from LowerBound/Fusion/SumOfTerms/Waring.lean, its `Rectangular.lean` extension,
  and Applications/Waring.lean in [S. Schlesinger, *Algebraic circuit formalizations in
  Complexitylib*][Schlesinger2026Algebraic].
* [J. M. Landsberg and Z. Teitler, *On the ranks and border ranks of symmetric
  tensors*][LandsbergTeitler2009], equation (1) and Remark 6.5. We use a squarefree restriction
  of the catalecticant argument; this does not identify the exact Waring rank or formalize
  the paper's border-rank and singularity bounds.
-/

@[expose] public section

namespace Cslib.Circuits.Waring

open MvPolynomial

private abbrev Layer (d k : ℕ) := ↥(Finset.powersetCard k (Finset.univ : Finset (Fin d)))

private noncomputable def exponent {d : ℕ} (s : Finset (Fin d)) : Fin d →₀ ℕ :=
  Finsupp.indicator s fun _ _ => 1

private theorem exponent_apply {d : ℕ} (s : Finset (Fin d)) (i : Fin d) :
    exponent s i = if i ∈ s then 1 else 0 := by
  simp [exponent, Finsupp.indicator_apply]

private theorem exponent_sum {d : ℕ} (s : Finset (Fin d)) :
    (exponent s).sum (fun _ e => e) = s.card := by
  rw [exponent, Finsupp.sum_indicator_index (fun _ => (1 : ℕ)) (by intros; rfl)]
  simp

private theorem exponent_add_compl_eq_univ_iff {d k : ℕ} (r c : Layer d k) :
    exponent r.1 + exponent c.1ᶜ = exponent Finset.univ ↔ r = c := by
  constructor
  · intro h
    apply Subtype.ext
    ext i
    have hi := DFunLike.congr_fun h i
    by_cases hr : i ∈ r.1 <;> by_cases hc : i ∈ c.1 <;>
      simp [exponent_apply, hr, hc] at hi ⊢
  · rintro rfl
    ext i
    by_cases hi : i ∈ r.1 <;> simp [exponent_apply, hi]

private theorem exponent_add_compl_sum {d k : ℕ} (r c : Layer d k) :
    (exponent r.1 + exponent c.1ᶜ).sum (fun _ e => e) = d := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), exponent_sum, exponent_sum,
    Finset.card_compl, Fintype.card_fin]
  have hr := (Finset.mem_powersetCard.mp r.2).2
  have hc := (Finset.mem_powersetCard.mp c.2).2
  have hle := Finset.card_le_univ r.1
  simp only [Fintype.card_fin] at hle
  lia

private noncomputable def feature (K : Type*) [Field K] (d k : ℕ) :
    MvPolynomial (Fin d) K →ₗ[K] (Layer d k → K) →ₗ[K] Layer d k → K :=
  Matrix.toLin'.toLinearMap.comp
    (catalecticant (fun r : Layer d k => exponent r.1) (fun c : Layer d k => exponent c.1ᶜ))

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

private theorem rank_feature_term_le (t : Term K d) (k : ℕ) :
    (feature K d k t.polynomial).rank ≤ 1 := by
  rw [Term.polynomial, ← smul_eq_C_mul, map_smul]
  apply (LinearMap.rank_smul_le _ _).trans
  change (Matrix.toLin' (catalecticant _ _ _)).rank ≤ 1
  rw [catalecticant_linearCombination_pow _ _ _ _ exponent_add_compl_sum,
    ← Matrix.natCast_rank_eq_rank_toLin']
  exact_mod_cast Matrix.rank_vecMulVec_le _ _

private theorem rank_feature_prod_X (d k : ℕ) :
    (feature K d k (∏ i : Fin d, X i)).rank = (d.choose k : Cardinal) := by
  have htarget : (∏ i : Fin d, (X i : MvPolynomial (Fin d) K)) =
      monomial (exponent Finset.univ) 1 := by
    simpa [exponent] using prod_X_pow (R := K) (fun _ : Fin d => 1) Finset.univ
  have hmatrix : catalecticant (fun r : Layer d k => exponent r.1)
      (fun c : Layer d k => exponent c.1ᶜ) (∏ i : Fin d, (X i : MvPolynomial (Fin d) K)) =
      ((exponent (Finset.univ : Finset (Fin d))).multinomial : K)⁻¹ •
        (1 : Matrix (Layer d k) (Layer d k) K) := by
    ext r c
    rw [catalecticant_apply, htarget]
    by_cases h : r = c
    · subst c
      simp [(exponent_add_compl_eq_univ_iff r r).mpr rfl]
    · have he := mt (exponent_add_compl_eq_univ_iff r c).mp h
      simp [Ne.symm he, h]
  change (Matrix.toLin' _).rank = _
  rw [hmatrix, ← Matrix.natCast_rank_eq_rank_toLin',
    Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero
      (inv_ne_zero ((exponent Finset.univ).cast_multinomial_ne_zero (K := K)))), Matrix.rank_one]
  simp [Layer]

/-- Every split of the degree gives a term-count bound for an ordinary sum of scaled powers.
The premise is equality of formal polynomials. -/
theorem choose_le_card {ι : Type*} (k : ℕ) (indices : Finset ι)
    (scale : ι → K) (coefficients : ι → Fin d → K)
    (hcompute : ∑ i ∈ indices, C (scale i) * (∑ j, C (coefficients i j) * X j) ^ d =
      ∏ j : Fin d, X j) : d.choose k ≤ indices.card := by
  classical
  let terms (i : ι) : Term K d := ⟨scale i, coefficients i⟩
  have hsum : ∑ i ∈ indices, (terms i).polynomial = ∏ j : Fin d, X j := by
    simpa [terms, Term.polynomial, smul_eq_C_mul] using hcompute
  have h := (LinearMap.rank_finsetSum_le indices
    (fun i => feature K d k (terms i).polynomial)).trans
      (Finset.sum_le_sum fun i _ => rank_feature_term_le (terms i) k)
  rw [← map_sum, hsum, rank_feature_prod_X] at h
  simpa using h

/-- The middle split gives a central-binomial lower bound for a sum of even-degree powers. -/
theorem centralBinom_le_card {ι : Type*} (n : ℕ) (indices : Finset ι)
    (scale : ι → K) (coefficients : ι → Fin (2 * n) → K)
    (hcompute : ∑ i ∈ indices, C (scale i) * (∑ j, C (coefficients i j) * X j) ^ (2 * n) =
      ∏ j : Fin (2 * n), X j) : Nat.centralBinom n ≤ indices.card :=
  choose_le_card n indices scale coefficients hcompute

/-- A sum-of-terms circuit for the squarefree monomial needs at least `choose d k` term gates.
Additions and wiring are free, and shared gates are charged once. -/
theorem choose_le_cost {m : ℕ} (c : Circuit (SumOfTerms.signature (Term K d)) 0 m)
    (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      ∏ i : Fin d, X i) : d.choose k ≤ c.program.cost SumOfTerms.termCost := by
  have h := SumOfTerms.rank_trace_le c.program Term.polynomial (feature K d k)
    (fun _ => 1) (fun t => rank_feature_term_le t k) Fin.elim0 (fun i => i.elim0) (c.outputs j)
  change (feature K d k (c.eval _ _ j)).rank ≤ _ at h
  rw [hcompute, rank_feature_prod_X] at h
  exact_mod_cast h

/-- The central-binomial term count for any selected output of an even-degree Waring circuit. -/
theorem centralBinom_le_cost {m : ℕ} (n : ℕ)
    (c : Circuit (SumOfTerms.signature (Term K (2 * n))) 0 m) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      ∏ i : Fin (2 * n), X i) : Nat.centralBinom n ≤ c.program.cost SumOfTerms.termCost :=
  choose_le_cost c n j hcompute

/-- An exponential lower bound on Waring term count, using the central-binomial estimate. -/
theorem four_pow_lt_mul_cost {m : ℕ} {n : ℕ} (hn : 4 ≤ n)
    (c : Circuit (SumOfTerms.signature (Term K (2 * n))) 0 m) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      ∏ i : Fin (2 * n), X i) : 4 ^ n < n * c.program.cost SumOfTerms.termCost :=
  (Nat.four_pow_lt_mul_centralBinom n hn).trans_le
    (Nat.mul_le_mul_left n (centralBinom_le_cost n c j hcompute))

end Cslib.Circuits.Waring
