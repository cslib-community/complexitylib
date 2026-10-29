/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Init
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Auxiliary exchange matrices and low-degree polynomial replacement rows

Given integer parameters `Q` and `r`, let `AuxLabel Q r = (Fin Q → Fin r) × (Fin Q → Fin r)` be
the complete auxiliary label array of cardinality `D = r ^ (2 * Q)`, with elements written
`u = (u.1, u.2)`.

This module constructs the auxiliary exchange matrix `M0`, the `{0, 1, -1}`-valued measurement
matrix `measurementMatrix` (`C^B`), the mismatch-annihilating polynomials `mismatchAnnihilator`
(`φ_{u,y}(T)`), and the low-degree auxiliary replacement rows `auxReplacementRow` (`P⃗_u(T)`) from
Sections 4.1–4.3 (pp. 26–30) and the common-denominator clearing of Section 4.6 (p. 33) of the
manuscript *The Exponential Time Hypothesis is False* (`openai/math@7ef5c0cc`):

1. **Coordinate-pair swap operators and `{0, 1, -1}`-eigenbasis (Lemma 4.1, pp. 27–28):**
   - For `s : Fin Q`, `slotSwap s` exchanges `u.1 s` and `u.2 s`, with permutation matrix
     `slotSwapMatrix Q r K s` (`Π_s`); `fullSwap` exchanges `u.1` and `u.2` across all slots,
     with permutation matrix `fullSwapMatrix Q r K` (`V_0 = ∏_s Π_s`).
   - `twoW0 Q r K = ∑ s : Fin Q, (1 - slotSwapMatrix Q r K s)` and
     `W0 Q r = (1 / 2 : ℚ) • twoW0 Q r ℚ`.
   - For an interval `I = Finset.Ico A₀ (A₀ + R)`, `fI A₀ R : ℚ[X]` is the degree-`(≤ R - 1)`
     polynomial interpolating `(-1)^k` on `k ∈ I`, and `M0 Q r A₀ R` is `V_0 f_I(W_0)`.
   - The tensor-product vectors `eigenvec K β` (`ψ_β`, indexed by `β : AuxLabel Q r`) have entries
     in `{0, 1, -1}`, form a pairwise orthogonal basis of `AuxLabel Q r → ℚ`, and are simultaneous
     eigenvectors of `slotSwapMatrix`, `fullSwapMatrix`, `W0`, and `M0`, with `M0`-eigenvalue `1`
     whenever `antisymCount β ∈ Finset.Ico A₀ (A₀ + R)`.
   - Consequently, if a vector `ξ : AuxLabel Q r → ℚ` lies in the kernel of `measurementMatrix`
     (the rows `eigenvec ℚ β` with `antisymCount β ∉ Finset.Ico A₀ (A₀ + R)`), then
     `(M0 Q r A₀ R).mulVec ξ = ξ`.

2. **Mismatch support bound (Lemma 4.2, pp. 28–29):**
   - Every factor `twoW0 Q r ℚ - c • 1` alters the first component `z.1` in at most one slot
     `s : Fin Q`. Since `fI A₀ R` is a sum of products of at most `R - 1` such factors and
     `fullSwapMatrix` swaps `u.1` with `u.2`, any nonzero entry `M0 Q r A₀ R u y ≠ 0` satisfies
     `#(mismatchSet u y) ≤ R - 1`, where `mismatchSet u y = {s : Fin Q | y.1 s ≠ u.2 s}`.

3. **Auxiliary polynomial replacement rows (Lemma 4.3, pp. 29–30):**
   - With `nodePoint s = (s.1 : ℚ) + 1` and
     `mismatchAnnihilator u y = ∏ s ∈ mismatchSet u y, (1 - C (nodePoint s)⁻¹ * X)`, the row
     `auxReplacementRow Q r A₀ R u y` has degree at most `R - 1`, evaluates at `T = 0` to `δ_u`,
     and at `T = nodePoint s` depends only on `ζ` restricted to
     `auxGroup s (u.2 s) = {y | y.1 s = u.2 s}` and `(measurementMatrix Q r A₀ R ℚ).mulVec ζ`.
   - In particular, if `g ≠ u.2 s` and `ξ` is supported on `auxGroup s g` with
     `(measurementMatrix Q r A₀ R ℚ).mulVec ξ = 0`, then
     `evalAuxReplacementRow Q r A₀ R u (nodePoint s) ξ = 0`.

4. **Common denominator clearing (Lemma 4.6, p. 33):**
   - With `commonDenom Q R = (R - 1).factorial * Q.factorial`, scaling
     `auxReplacementRow Q r A₀ R u y` by `commonDenom Q R` yields the explicit integer polynomial
     `auxReplacementRowScaledInt Q r A₀ R u y : ℤ[X]`.

## Main definitions

* `Cslib.LinearAlgebra.AuxLabel`: auxiliary coordinate space `(Fin Q → Fin r) × (Fin Q → Fin r)`.
* `Cslib.LinearAlgebra.subsetSwap`, `Cslib.LinearAlgebra.slotSwap`, `Cslib.LinearAlgebra.fullSwap`:
  coordinate-pair swap involutions.
* `Cslib.LinearAlgebra.slotSwapMatrix`, `Cslib.LinearAlgebra.fullSwapMatrix`,
  `Cslib.LinearAlgebra.twoW0`, `Cslib.LinearAlgebra.W0`: swap permutation matrices and `W₀`.
* `Cslib.LinearAlgebra.fI`, `Cslib.LinearAlgebra.M0`: parity interpolant on `I` and matrix `M₀`.
* `Cslib.LinearAlgebra.eigenvecInt`, `Cslib.LinearAlgebra.eigenvec`,
  `Cslib.LinearAlgebra.measurementIndices`, `Cslib.LinearAlgebra.measurementMatrix`:
  the `{0, 1, -1}`-valued orthogonal eigenbasis and measurement matrix `C^B`.
* `Cslib.LinearAlgebra.mismatchSet`, `Cslib.LinearAlgebra.mismatchAnnihilator`,
  `Cslib.LinearAlgebra.auxReplacementRow`, `Cslib.LinearAlgebra.evalAuxReplacementRow`:
  mismatch set `E_{u,y}`, annihilator polynomial `φ_{u,y}(T)`, and replacement row `P⃗_u(T)`.
* `Cslib.LinearAlgebra.commonDenom`, `Cslib.LinearAlgebra.auxReplacementRowScaledInt`:
  common denominator `d_den = (R - 1)! Q!` and cleared integer replacement rows.

## Main results

* `Cslib.LinearAlgebra.M0_mulVec_eq_self_of_measurementMatrix_mulVec_eq_zero`:
  Lemma 4.1 kernel invariance.
* `Cslib.LinearAlgebra.card_mismatchSet_le_of_M0_ne_zero`: Lemma 4.2 mismatch support bound.
* `Cslib.LinearAlgebra.natDegree_auxReplacementRow_le`,
  `Cslib.LinearAlgebra.evalAuxReplacementRow_zero`,
  `Cslib.LinearAlgebra.evalAuxReplacementRow_nodePoint_eq_zero_of_kernel`,
  `Cslib.LinearAlgebra.evalAuxReplacementRow_nodePoint_eq_of_eq_on_auxGroup`:
  Lemma 4.3 replacement row properties.
* `Cslib.LinearAlgebra.map_auxReplacementRowScaledInt`: Lemma 4.6 common-denominator clearing.

## References

* [OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.LinearAlgebra

open Finset Matrix Polynomial

/-! ### 1. Auxiliary coordinate space and coordinate-pair swap operators -/

/-- The auxiliary coordinate space `B = ([r]^Q)²` of pairs of length-`Q` sequences in `Fin r`. -/
abbrev AuxLabel (Q r : ℕ) : Type := (Fin Q → Fin r) × (Fin Q → Fin r)

/-- The cardinality of `AuxLabel Q r` is `D = r ^ (2 * Q)`. -/
theorem card_auxLabel (Q r : ℕ) : Fintype.card (AuxLabel Q r) = r ^ (2 * Q) := by
  simp [AuxLabel, Fintype.card_prod, Fintype.card_fin, two_mul, pow_add]

/-- Swap `u.1 s` and `u.2 s` at all coordinates `s ∈ J`, leaving `s ∉ J` unchanged. -/
def subsetSwap {Q r : ℕ} (J : Finset (Fin Q)) (u : AuxLabel Q r) : AuxLabel Q r :=
  (fun s => if s ∈ J then u.2 s else u.1 s,
   fun s => if s ∈ J then u.1 s else u.2 s)

/-- Swap `u.1 s` and `u.2 s` at a single slot `s : Fin Q` (`ϑ_s` in Section 4.2). -/
def slotSwap {Q r : ℕ} (s : Fin Q) (u : AuxLabel Q r) : AuxLabel Q r :=
  subsetSwap {s} u

/-- Swap the complete sequences `u.1` and `u.2` (`u ↦ ū`). -/
def fullSwap {Q r : ℕ} (u : AuxLabel Q r) : AuxLabel Q r :=
  subsetSwap univ u

@[simp]
theorem subsetSwap_empty {Q r : ℕ} (u : AuxLabel Q r) : subsetSwap ∅ u = u := by
  ext s <;> simp [subsetSwap]

theorem subsetSwap_subsetSwap {Q r : ℕ} (J₁ J₂ : Finset (Fin Q)) (u : AuxLabel Q r) :
    subsetSwap J₁ (subsetSwap J₂ u) = subsetSwap (symmDiff J₁ J₂) u := by
  ext s <;> by_cases h1 : s ∈ J₁ <;> by_cases h2 : s ∈ J₂ <;>
    simp [subsetSwap, mem_symmDiff, h1, h2]

@[simp]
theorem subsetSwap_self {Q r : ℕ} (J : Finset (Fin Q)) (u : AuxLabel Q r) :
    subsetSwap J (subsetSwap J u) = u := by
  ext s <;> by_cases hs : s ∈ J <;> simp [subsetSwap, hs]

@[simp]
theorem slotSwap_self {Q r : ℕ} (s : Fin Q) (u : AuxLabel Q r) :
    slotSwap s (slotSwap s u) = u :=
  subsetSwap_self {s} u

@[simp]
theorem fullSwap_fst {Q r : ℕ} (u : AuxLabel Q r) : (fullSwap u).1 = u.2 := by
  ext s; simp [fullSwap, subsetSwap]

@[simp]
theorem fullSwap_snd {Q r : ℕ} (u : AuxLabel Q r) : (fullSwap u).2 = u.1 := by
  ext s; simp [fullSwap, subsetSwap]

@[simp]
theorem fullSwap_self {Q r : ℕ} (u : AuxLabel Q r) : fullSwap (fullSwap u) = u :=
  subsetSwap_self univ u

/-- Permutation matrix on `AuxLabel Q r` associated to `subsetSwap J`. -/
def subsetSwapMatrix (Q r : ℕ) (K : Type*) [CommRing K] (J : Finset (Fin Q)) :
    Matrix (AuxLabel Q r) (AuxLabel Q r) K :=
  fun u y => if y = subsetSwap J u then 1 else 0

/-- The single-slot exchange matrix `Π_s` on `AuxLabel Q r`. -/
def slotSwapMatrix (Q r : ℕ) (K : Type*) [CommRing K] (s : Fin Q) :
    Matrix (AuxLabel Q r) (AuxLabel Q r) K :=
  subsetSwapMatrix Q r K {s}

/-- The full-swap permutation matrix `V_0` on `AuxLabel Q r`. -/
def fullSwapMatrix (Q r : ℕ) (K : Type*) [CommRing K] :
    Matrix (AuxLabel Q r) (AuxLabel Q r) K :=
  subsetSwapMatrix Q r K univ

@[simp]
theorem subsetSwapMatrix_empty (Q r : ℕ) (K : Type*) [CommRing K] :
    subsetSwapMatrix Q r K (∅ : Finset (Fin Q)) =
      (1 : Matrix (AuxLabel Q r) (AuxLabel Q r) K) := by
  ext u y
  simp [subsetSwapMatrix, Matrix.one_apply, eq_comm]

@[simp]
theorem subsetSwapMatrix_mulVec (Q r : ℕ) (K : Type*) [CommRing K] (J : Finset (Fin Q))
    (ζ : AuxLabel Q r → K) (u : AuxLabel Q r) :
    (subsetSwapMatrix Q r K J).mulVec ζ u = ζ (subsetSwap J u) := by
  simp [Matrix.mulVec, dotProduct, subsetSwapMatrix]

@[simp]
theorem slotSwapMatrix_mulVec (Q r : ℕ) (K : Type*) [CommRing K] (s : Fin Q)
    (ζ : AuxLabel Q r → K) (u : AuxLabel Q r) :
    (slotSwapMatrix Q r K s).mulVec ζ u = ζ (slotSwap s u) :=
  subsetSwapMatrix_mulVec Q r K {s} ζ u

@[simp]
theorem fullSwapMatrix_mulVec (Q r : ℕ) (K : Type*) [CommRing K]
    (ζ : AuxLabel Q r → K) (u : AuxLabel Q r) :
    (fullSwapMatrix Q r K).mulVec ζ u = ζ (fullSwap u) :=
  subsetSwapMatrix_mulVec Q r K univ ζ u

theorem subsetSwapMatrix_mul (Q r : ℕ) (K : Type*) [CommRing K] (J₁ J₂ : Finset (Fin Q)) :
    subsetSwapMatrix Q r K J₁ * subsetSwapMatrix Q r K J₂ =
      subsetSwapMatrix Q r K (symmDiff J₁ J₂) := by
  ext u z
  simp only [Matrix.mul_apply, subsetSwapMatrix, boole_mul]
  rw [sum_ite_eq']
  simp only [mem_univ, ↓reduceIte]
  rw [subsetSwap_subsetSwap J₂ J₁ u, symmDiff_comm]

@[simp]
theorem subsetSwapMatrix_mul_self (Q r : ℕ) (K : Type*) [CommRing K] (J : Finset (Fin Q)) :
    subsetSwapMatrix Q r K J * subsetSwapMatrix Q r K J = 1 := by
  rw [subsetSwapMatrix_mul, symmDiff_self, bot_eq_empty, subsetSwapMatrix_empty]

@[simp]
theorem slotSwapMatrix_mul_self (Q r : ℕ) (K : Type*) [CommRing K] (s : Fin Q) :
    slotSwapMatrix Q r K s * slotSwapMatrix Q r K s = 1 :=
  subsetSwapMatrix_mul_self Q r K {s}

theorem slotSwapMatrix_comm (Q r : ℕ) (K : Type*) [CommRing K] (s t : Fin Q) :
    slotSwapMatrix Q r K s * slotSwapMatrix Q r K t =
      slotSwapMatrix Q r K t * slotSwapMatrix Q r K s := by
  simp only [slotSwapMatrix, subsetSwapMatrix_mul, symmDiff_comm]

theorem fullSwapMatrix_mul_subsetSwapMatrix (Q r : ℕ) (K : Type*) [CommRing K]
    (J : Finset (Fin Q)) :
    fullSwapMatrix Q r K * subsetSwapMatrix Q r K J = subsetSwapMatrix Q r K Jᶜ := by
  rw [fullSwapMatrix, subsetSwapMatrix_mul]
  congr 1
  ext s
  simp [mem_symmDiff]

@[simp]
theorem fullSwapMatrix_mul_apply (Q r : ℕ) (K : Type*) [CommRing K]
    (A : Matrix (AuxLabel Q r) (AuxLabel Q r) K) (u y : AuxLabel Q r) :
    (fullSwapMatrix Q r K * A) u y = A (fullSwap u) y := by
  simp [Matrix.mul_apply, fullSwapMatrix, subsetSwapMatrix, fullSwap]

/-- The integer-valued operator `2 W_0 = ∑ s : Fin Q, (I - Π_s)` (eq. 4.6). -/
def twoW0 (Q r : ℕ) (K : Type*) [CommRing K] : Matrix (AuxLabel Q r) (AuxLabel Q r) K :=
  ∑ s : Fin Q, (1 - slotSwapMatrix Q r K s)

/-- The operator `W_0 = (1/2) ∑ s : Fin Q, (I - Π_s)` over `ℚ` (eq. 4.6). -/
def W0 (Q r : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℚ :=
  (2⁻¹ : ℚ) • twoW0 Q r ℚ

theorem two_smul_W0 (Q r : ℕ) : (2 : ℚ) • W0 Q r = twoW0 Q r ℚ := by
  simp [W0, smul_smul]

/-! ### 2. Parity interpolation polynomial `f_I` and exchange matrix `M_0` -/

/-- The `j`-th polynomial factor `(-1)^(A₀ + j) ∏_{a < j} (2 X - 2 (A₀ + a))`
appearing in the numerator of `f_I(X)` (eq. 4.7 and Lemma 4.6). -/
noncomputable def fallingTermPoly (A₀ j : ℕ) : ℚ[X] :=
  C ((-1 : ℚ) ^ (A₀ + j)) * ∏ a ∈ range j, (C 2 * X - C (2 * ((A₀ : ℚ) + a)))

/-- The parity interpolation polynomial
`f_I(z) = (-1)^{A₀} ∑_{j=0}^{R-1} (-2)^j choose(z - A₀, j)` over `ℚ` (eq. 4.7). -/
noncomputable def fI (A₀ R : ℕ) : ℚ[X] :=
  ∑ j ∈ range R, C ((j.factorial : ℚ)⁻¹) * fallingTermPoly A₀ j

theorem natDegree_fallingTermPoly_le (A₀ j : ℕ) :
    (fallingTermPoly A₀ j).natDegree ≤ j := by
  unfold fallingTermPoly
  refine Polynomial.natDegree_mul_le.trans ?_
  simp only [natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h1 : ∀ a ∈ range j, (C (2 : ℚ) * X - C (2 * ((A₀ : ℚ) + a))).natDegree ≤ 1 := by
    intro a _
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_mul_le.trans ?_
      simp
    · rw [natDegree_C]
      exact Nat.zero_le 1
  exact (sum_le_sum h1).trans (by simp)

/-- The parity interpolation polynomial `fI A₀ R` has degree at most `R - 1` (eq. 4.7, p. 28). -/
theorem natDegree_fI_le (A₀ R : ℕ) : (fI A₀ R).natDegree ≤ R - 1 := by
  unfold fI
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun j hj => ?_⟩
  refine Polynomial.natDegree_mul_le.trans ?_
  simp only [natDegree_C, zero_add]
  exact (natDegree_fallingTermPoly_le A₀ j).trans (Nat.le_sub_one_of_lt (mem_range.1 hj))

/-- Product of the `j` integer matrix factors `∏_{a < j} (2 W_0 - 2 (A₀ + a) I)`. -/
def fallingProdMatrixInt (Q r A₀ j : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ :=
  ((List.range j).map fun a : ℕ => twoW0 Q r ℤ - (2 * ((A₀ : ℤ) + a)) • 1).prod

/-- The `j`-th integer matrix term `(-1)^(A₀ + j) ∏_{a < j} (2 W_0 - 2 (A₀ + a) I)`
from the proof of Lemma 4.6 (p. 33). -/
def fallingTermMatrixInt (Q r A₀ j : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ :=
  (-1 : ℤ) ^ (A₀ + j) • fallingProdMatrixInt Q r A₀ j

/-- The auxiliary exchange matrix `M_0 = V_0 f_I(W_0)` over `ℚ` (eq. 4.7). -/
def M0 (Q r A₀ R : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℚ :=
  fullSwapMatrix Q r ℚ *
    ∑ j ∈ range R,
      ((j.factorial : ℚ)⁻¹) • (fallingTermMatrixInt Q r A₀ j).map (Int.cast : ℤ → ℚ)

/-- The scaled integer exchange matrix `(R - 1)! M_0` over `ℤ` (Lemma 4.6, p. 33). -/
def M0ScaledInt (Q r A₀ R : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ :=
  fullSwapMatrix Q r ℤ *
    ∑ j ∈ range R, (((R - 1).factorial / j.factorial : ℕ) : ℤ) • fallingTermMatrixInt Q r A₀ j

private theorem prod_range_sub_eq_descFactorial (q j : ℕ) :
    (∏ a ∈ range j, ((q : ℚ) - a)) = (q.descFactorial j : ℚ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, ih, Nat.descFactorial_succ, Nat.cast_mul]
    by_cases h : j ≤ q
    · rw [Nat.cast_sub h, mul_comm]
    · push Not at h
      have hdesc : q.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.2 h
      simp [hdesc]

theorem eval_fallingTermPoly_add (A₀ q j : ℕ) :
    (fallingTermPoly A₀ j).eval ((A₀ + q : ℕ) : ℚ) =
      (-1 : ℚ) ^ A₀ * (-2 : ℚ) ^ j * (j.factorial : ℚ) * (q.choose j : ℚ) := by
  unfold fallingTermPoly
  rw [eval_mul, eval_C, eval_prod]
  have hprod :
      (∏ a ∈ range j, (C (2 : ℚ) * X - C (2 * ((A₀ : ℚ) + (a : ℚ)))).eval ((A₀ + q : ℕ) : ℚ)) =
        (2 : ℚ) ^ j * ((j.factorial : ℚ) * (q.choose j : ℚ)) := by
    have h1 :
        (∏ a ∈ range j,
            (C (2 : ℚ) * X - C (2 * ((A₀ : ℚ) + (a : ℚ)))).eval ((A₀ + q : ℕ) : ℚ)) =
          ∏ a ∈ range j, ((2 : ℚ) * ((q : ℚ) - (a : ℚ))) := by
      refine prod_congr rfl fun a _ => ?_
      simp only [eval_sub, eval_mul, eval_C, eval_X, Nat.cast_add]
      ring
    rw [h1, prod_mul_distrib, prod_const, card_range, prod_range_sub_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [hprod, pow_add]
  have hneg2 : (-1 : ℚ) ^ j * (2 : ℚ) ^ j = (-2 : ℚ) ^ j := by
    rw [← mul_pow]
    ring
  calc
    (-1 : ℚ) ^ A₀ * (-1 : ℚ) ^ j * ((2 : ℚ) ^ j * ((j.factorial : ℚ) * (q.choose j : ℚ))) =
        (-1 : ℚ) ^ A₀ * ((-1 : ℚ) ^ j * (2 : ℚ) ^ j) *
          (j.factorial : ℚ) * (q.choose j : ℚ) := by ring
    _ = (-1 : ℚ) ^ A₀ * (-2 : ℚ) ^ j * (j.factorial : ℚ) * (q.choose j : ℚ) := by rw [hneg2]

/-- On the interval `I = Finset.Ico A₀ (A₀ + R)`, the polynomial `fI A₀ R` evaluates to `(-1)^k`. -/
theorem eval_fI_of_mem_Ico {A₀ R k : ℕ} (hk : k ∈ Ico A₀ (A₀ + R)) :
    (fI A₀ R).eval (k : ℚ) = (-1 : ℚ) ^ k := by
  rw [mem_Ico] at hk
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk.1
  have hq : q < R := by omega
  rw [fI, Polynomial.eval_finsetSum]
  have hterm :
      ∀ j ∈ range R,
        (C ((j.factorial : ℚ)⁻¹) * fallingTermPoly A₀ j).eval ((A₀ + q : ℕ) : ℚ) =
          (-1 : ℚ) ^ A₀ * ((-2 : ℚ) ^ j * (q.choose j : ℚ)) := by
    intro j _
    rw [eval_mul, eval_C, eval_fallingTermPoly_add]
    have hfac : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    calc
      (j.factorial : ℚ)⁻¹ *
          ((-1 : ℚ) ^ A₀ * (-2 : ℚ) ^ j * (j.factorial : ℚ) * (q.choose j : ℚ)) =
        ((j.factorial : ℚ)⁻¹ * (j.factorial : ℚ)) *
          ((-1 : ℚ) ^ A₀ * ((-2 : ℚ) ^ j * (q.choose j : ℚ))) := by ring
      _ = (-1 : ℚ) ^ A₀ * ((-2 : ℚ) ^ j * (q.choose j : ℚ)) := by
        rw [inv_mul_cancel₀ hfac, one_mul]
  rw [sum_congr rfl hterm, ← mul_sum]
  have hsub :
      ∑ j ∈ range R, (-2 : ℚ) ^ j * (q.choose j : ℚ) =
        ∑ j ∈ range (q + 1), (-2 : ℚ) ^ j * (q.choose j : ℚ) := by
    refine (sum_subset (range_mono (by omega)) fun j _ hj => ?_).symm
    rw [mem_range, not_lt] at hj
    simp [Nat.choose_eq_zero_of_lt (by omega : q < j)]
  have hbin : ∑ j ∈ range (q + 1), (-2 : ℚ) ^ j * (q.choose j : ℚ) = (-1 : ℚ) ^ q := by
    have h := add_pow (-2 : ℚ) 1 q
    simp only [one_pow, mul_one] at h
    rw [show (-2 : ℚ) + 1 = -1 by norm_num] at h
    exact h.symm
  rw [hsub, hbin, ← pow_add]

/-! ### 3. Explicit `{0, 1, -1}`-eigenbasis and Lemma 4.1 -/

/-- Indicator of the ordered pair `(a, b) ∈ Fin r × Fin r`. -/
def pairInd {r : ℕ} (a b x y : Fin r) : ℤ :=
  if x = a ∧ y = b then 1 else 0

/-- 1-slot orthogonal basis function on `Fin r × Fin r` with values in `{0, 1, -1}`
(Proof of Lemma 4.1, p. 28). -/
def pairBasis {r : ℕ} (α δ x y : Fin r) : ℤ :=
  if α = δ then
    pairInd α α x y
  else if α < δ then
    pairInd α δ x y + pairInd δ α x y
  else
    pairInd δ α x y - pairInd α δ x y

/-- Swap eigenvalue of `pairBasis α δ`: `-1` when `δ < α` and `+1` otherwise. -/
def pairSign {r : ℕ} (α δ : Fin r) : ℤ :=
  if δ < α then -1 else 1

/-- Squared `ℓ₂`-norm of `pairBasis α δ`: `1` on the diagonal `α = δ` and `2` off the diagonal. -/
def pairNormSq {r : ℕ} (α δ : Fin r) : ℤ :=
  if α = δ then 1 else 2

theorem pairNormSq_pos {r : ℕ} (α δ : Fin r) : 0 < pairNormSq α δ := by
  unfold pairNormSq; split_ifs <;> omega

theorem pairInd_swap {r : ℕ} (a b x y : Fin r) : pairInd a b y x = pairInd b a x y := by
  simp [pairInd, and_comm]

theorem pairBasis_swap {r : ℕ} (α δ x y : Fin r) :
    pairBasis α δ y x = pairSign α δ * pairBasis α δ x y := by
  unfold pairBasis pairSign
  rcases lt_trichotomy α δ with hlt | rfl | hgt
  · have hne : α ≠ δ := ne_of_lt hlt
    have hnot : ¬ δ < α := not_lt_of_gt hlt
    simp [hne, hlt, hnot, pairInd_swap, add_comm]
  · simp [pairInd_swap]
  · have hne : α ≠ δ := ne_of_gt hgt
    have hnot : ¬ α < δ := not_lt_of_gt hgt
    simp only [hne, hnot, hgt, ↓reduceIte, pairInd_swap]
    ring

theorem pairBasis_mem {r : ℕ} (α δ x y : Fin r) :
    pairBasis α δ x y = 0 ∨ pairBasis α δ x y = 1 ∨ pairBasis α δ x y = -1 := by
  unfold pairBasis pairInd
  split_ifs <;> omega

private theorem sum_pairInd_mul_pairInd {r : ℕ} (a b a' b' : Fin r) :
    (∑ x : Fin r, ∑ y : Fin r, pairInd a b x y * pairInd a' b' x y) =
      if a = a' ∧ b = b' then 1 else 0 := by
  have h1 :
      ∀ x : Fin r,
        (∑ y : Fin r, pairInd a b x y * pairInd a' b' x y) =
          if x = a then (if x = a' ∧ b = b' then 1 else 0) else 0 := by
    intro x
    simp only [pairInd]
    have hsum :
        (∑ y : Fin r, (if x = a ∧ y = b then (1 : ℤ) else 0) *
            if x = a' ∧ y = b' then 1 else 0) =
          ∑ y : Fin r, if y = b then (if x = a ∧ x = a' ∧ y = b' then 1 else 0) else 0 := by
      refine sum_congr rfl fun y _ => ?_
      split_ifs <;> omega
    rw [hsum, sum_ite_eq']
    simp only [mem_univ, ↓reduceIte]
    split_ifs <;> omega
  simp_rw [h1]
  rw [sum_ite_eq']
  simp

theorem sum_pairBasis_mul_pairBasis {r : ℕ} (α δ α' δ' : Fin r) :
    (∑ x : Fin r, ∑ y : Fin r, pairBasis α δ x y * pairBasis α' δ' x y) =
      if α = α' ∧ δ = δ' then pairNormSq α δ else 0 := by
  unfold pairBasis pairNormSq
  rcases lt_trichotomy α δ with h1 | rfl | h2 <;>
    rcases lt_trichotomy α' δ' with h1' | rfl | h2'
  · have hne : α ≠ δ := ne_of_lt h1
    have hne' : α' ≠ δ' := ne_of_lt h1'
    simp only [hne, h1, hne', h1', ↓reduceIte, add_mul, mul_add, sum_add_distrib,
      sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · have hne : α ≠ δ := ne_of_lt h1
    simp only [hne, h1, ↓reduceIte, add_mul, sum_add_distrib, sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · have hne : α ≠ δ := ne_of_lt h1
    have hne' : α' ≠ δ' := ne_of_gt h2'
    have hnot' : ¬ α' < δ' := not_lt_of_gt h2'
    simp only [hne, h1, hne', hnot', ↓reduceIte, add_mul, mul_sub, sum_add_distrib,
      sum_sub_distrib, sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · have hne' : α' ≠ δ' := ne_of_lt h1'
    simp only [hne', h1', ↓reduceIte, mul_add, sum_add_distrib, sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · simp only [↓reduceIte, sum_pairInd_mul_pairInd]
  · have hne' : α' ≠ δ' := ne_of_gt h2'
    have hnot' : ¬ α' < δ' := not_lt_of_gt h2'
    simp only [hne', hnot', ↓reduceIte, mul_sub, sum_sub_distrib, sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · have hne : α ≠ δ := ne_of_gt h2
    have hnot : ¬ α < δ := not_lt_of_gt h2
    have hne' : α' ≠ δ' := ne_of_lt h1'
    simp only [hne, hnot, hne', h1', ↓reduceIte, sub_mul, mul_add, sum_add_distrib,
      sum_sub_distrib, sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · have hne : α ≠ δ := ne_of_gt h2
    have hnot : ¬ α < δ := not_lt_of_gt h2
    simp only [hne, hnot, ↓reduceIte, sub_mul, sum_sub_distrib, sum_pairInd_mul_pairInd]
    split_ifs <;> omega
  · have hne : α ≠ δ := ne_of_gt h2
    have hnot : ¬ α < δ := not_lt_of_gt h2
    have hne' : α' ≠ δ' := ne_of_gt h2'
    have hnot' : ¬ α' < δ' := not_lt_of_gt h2'
    simp only [hne, hnot, hne', hnot', ↓reduceIte, sub_mul, mul_sub, sum_sub_distrib,
      sum_pairInd_mul_pairInd]
    split_ifs <;> omega

/-- The integer-valued simultaneous eigenvector `ψ_β` on `AuxLabel Q r` (Proof of Lemma 4.1). -/
def eigenvecInt {Q r : ℕ} (β u : AuxLabel Q r) : ℤ :=
  ∏ s : Fin Q, pairBasis (β.1 s) (β.2 s) (u.1 s) (u.2 s)

/-- The simultaneous eigenvector `ψ_β` over any commutative ring `K`. -/
def eigenvec {Q r : ℕ} (K : Type*) [CommRing K] (β : AuxLabel Q r) : AuxLabel Q r → K :=
  fun u => (eigenvecInt β u : K)

/-- The number of antisymmetric factors (`j(β)`) in `eigenvec K β`, i.e., slots `s` with
`β.2 s < β.1 s`. -/
def antisymCount {Q r : ℕ} (β : AuxLabel Q r) : ℕ :=
  #{s : Fin Q | β.2 s < β.1 s}

/-- Squared `ℓ₂`-norm of `eigenvecInt β`. -/
def eigenNormSq {Q r : ℕ} (β : AuxLabel Q r) : ℤ :=
  ∏ s : Fin Q, pairNormSq (β.1 s) (β.2 s)

theorem eigenNormSq_pos {Q r : ℕ} (β : AuxLabel Q r) : 0 < eigenNormSq β := by
  unfold eigenNormSq
  induction (univ : Finset (Fin Q)) using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    rw [prod_insert hs]
    exact mul_pos (pairNormSq_pos (β.1 s) (β.2 s)) ih

/-- Every entry of `eigenvecInt β` belongs to `{0, 1, -1}`. -/
theorem eigenvecInt_mem {Q r : ℕ} (β u : AuxLabel Q r) :
    eigenvecInt β u = 0 ∨ eigenvecInt β u = 1 ∨ eigenvecInt β u = -1 := by
  unfold eigenvecInt
  induction (univ : Finset (Fin Q)) using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    rw [prod_insert hs]
    rcases pairBasis_mem (β.1 s) (β.2 s) (u.1 s) (u.2 s) with h1 | h1 | h1 <;>
      rcases ih with h2 | h2 | h2 <;> simp [h1, h2]

theorem abs_eigenvecInt_le_one {Q r : ℕ} (β u : AuxLabel Q r) : |eigenvecInt β u| ≤ 1 := by
  rcases eigenvecInt_mem β u with h | h | h <;> simp [h]

theorem eigenvecInt_slotSwap {Q r : ℕ} (s : Fin Q) (β u : AuxLabel Q r) :
    eigenvecInt β (slotSwap s u) = pairSign (β.1 s) (β.2 s) * eigenvecInt β u := by
  unfold eigenvecInt
  rw [← mul_prod_erase univ _ (mem_univ s), ← mul_prod_erase univ _ (mem_univ s)]
  have h_at_s :
      pairBasis (β.1 s) (β.2 s) ((slotSwap s u).1 s) ((slotSwap s u).2 s) =
        pairSign (β.1 s) (β.2 s) * pairBasis (β.1 s) (β.2 s) (u.1 s) (u.2 s) := by
    simp only [slotSwap, subsetSwap, mem_singleton, ↓reduceIte]
    exact pairBasis_swap (β.1 s) (β.2 s) (u.1 s) (u.2 s)
  have h_rest :
      (∏ t ∈ univ.erase s,
          pairBasis (β.1 t) (β.2 t) ((slotSwap s u).1 t) ((slotSwap s u).2 t)) =
        ∏ t ∈ univ.erase s, pairBasis (β.1 t) (β.2 t) (u.1 t) (u.2 t) := by
    refine prod_congr rfl fun t ht => ?_
    have hts : t ≠ s := ne_of_mem_erase ht
    simp [slotSwap, subsetSwap, hts]
  rw [h_at_s, h_rest, mul_assoc]

theorem slotSwapMatrix_mulVec_eigenvec (Q r : ℕ) (K : Type*) [CommRing K]
    (s : Fin Q) (β : AuxLabel Q r) :
    (slotSwapMatrix Q r K s).mulVec (eigenvec K β) =
      (pairSign (β.1 s) (β.2 s) : K) • eigenvec K β := by
  ext u
  simp [eigenvec, eigenvecInt_slotSwap]

theorem prod_pairSign_eq_neg_one_pow_antisymCount {Q r : ℕ} (β : AuxLabel Q r) :
    (∏ s : Fin Q, pairSign (β.1 s) (β.2 s)) = (-1 : ℤ) ^ antisymCount β := by
  unfold pairSign antisymCount
  rw [prod_ite, prod_const, prod_const_one, mul_one]

theorem eigenvecInt_fullSwap {Q r : ℕ} (β u : AuxLabel Q r) :
    eigenvecInt β (fullSwap u) = (-1 : ℤ) ^ antisymCount β * eigenvecInt β u := by
  unfold eigenvecInt
  have h1 :
      (∏ s : Fin Q, pairBasis (β.1 s) (β.2 s) ((fullSwap u).1 s) ((fullSwap u).2 s)) =
        ∏ s : Fin Q, (pairSign (β.1 s) (β.2 s) * pairBasis (β.1 s) (β.2 s) (u.1 s) (u.2 s)) := by
    refine prod_congr rfl fun s _ => ?_
    simp only [fullSwap, subsetSwap, mem_univ, ↓reduceIte]
    exact pairBasis_swap (β.1 s) (β.2 s) (u.1 s) (u.2 s)
  rw [h1, prod_mul_distrib, prod_pairSign_eq_neg_one_pow_antisymCount]

theorem fullSwapMatrix_mulVec_eigenvec (Q r : ℕ) (K : Type*) [CommRing K]
    (β : AuxLabel Q r) :
    (fullSwapMatrix Q r K).mulVec (eigenvec K β) =
      ((-1 : K) ^ antisymCount β) • eigenvec K β := by
  ext u
  simp [eigenvec, eigenvecInt_fullSwap]

theorem sum_one_sub_pairSign {Q r : ℕ} (β : AuxLabel Q r) :
    (∑ s : Fin Q, (1 - pairSign (β.1 s) (β.2 s))) = 2 * (antisymCount β : ℤ) := by
  have hterm :
      ∀ s : Fin Q, (1 - pairSign (β.1 s) (β.2 s)) = if β.2 s < β.1 s then (2 : ℤ) else 0 := by
    intro s
    unfold pairSign
    split_ifs <;> omega
  simp_rw [hterm]
  rw [sum_ite, sum_const, sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]
  rfl

theorem twoW0_mulVec_eigenvec (Q r : ℕ) (K : Type*) [CommRing K] (β : AuxLabel Q r) :
    (twoW0 Q r K).mulVec (eigenvec K β) = (2 * (antisymCount β : K)) • eigenvec K β := by
  ext u
  have h1 :
      (twoW0 Q r K).mulVec (eigenvec K β) u =
        ∑ s : Fin Q, ((1 : K) - (pairSign (β.1 s) (β.2 s) : K)) * eigenvec K β u := by
    simp [twoW0, Matrix.sum_mulVec, Matrix.sub_mulVec, slotSwapMatrix_mulVec_eigenvec, sub_mul]
  rw [h1, ← sum_mul]
  have hsum :
      (∑ s : Fin Q, ((1 : K) - (pairSign (β.1 s) (β.2 s) : K))) =
        2 * (antisymCount β : K) := by
    have hZ := congrArg (Int.cast : ℤ → K) (sum_one_sub_pairSign β)
    push_cast at hZ
    exact hZ
  rw [hsum, Pi.smul_apply, smul_eq_mul]

theorem W0_mulVec_eigenvec {Q r : ℕ} (β : AuxLabel Q r) :
    (W0 Q r).mulVec (eigenvec ℚ β) = (antisymCount β : ℚ) • eigenvec ℚ β := by
  rw [W0, Matrix.smul_mulVec, twoW0_mulVec_eigenvec, smul_smul]
  ring_nf

private theorem fallingProdMatrixInt_mulVec_eigenvec (Q r A₀ j : ℕ) (β : AuxLabel Q r) :
    (fallingProdMatrixInt Q r A₀ j).mulVec (eigenvec ℤ β) =
      (∏ a ∈ range j, (2 * (antisymCount β : ℤ) - 2 * ((A₀ : ℤ) + a))) • eigenvec ℤ β := by
  unfold fallingProdMatrixInt
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, twoW0_mulVec_eigenvec,
      Matrix.smul_mulVec, Matrix.one_mulVec, ← sub_smul, Matrix.mulVec_smul, ih, smul_smul,
      prod_range_succ, mul_comm]

theorem fallingTermMatrixInt_mulVec_eigenvec (Q r A₀ j : ℕ) (β : AuxLabel Q r) :
    (fallingTermMatrixInt Q r A₀ j).mulVec (eigenvec ℤ β) =
      ((-1 : ℤ) ^ (A₀ + j) *
          ∏ a ∈ range j, (2 * (antisymCount β : ℤ) - 2 * ((A₀ : ℤ) + a))) •
        eigenvec ℤ β := by
  unfold fallingTermMatrixInt
  rw [Matrix.smul_mulVec, fallingProdMatrixInt_mulVec_eigenvec, smul_smul]

theorem fallingTermMatrix_map_mulVec_eigenvec (Q r A₀ j : ℕ) (β : AuxLabel Q r) :
    ((fallingTermMatrixInt Q r A₀ j).map (Int.cast : ℤ → ℚ)).mulVec (eigenvec ℚ β) =
      (fallingTermPoly A₀ j).eval (antisymCount β : ℚ) • eigenvec ℚ β := by
  ext u
  have hZ := congrFun (fallingTermMatrixInt_mulVec_eigenvec Q r A₀ j β) u
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hZ
  have hQ := congrArg (Int.cast : ℤ → ℚ) hZ
  push_cast at hQ
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, eigenvec, Pi.smul_apply, smul_eq_mul,
    fallingTermPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact hQ

theorem M0_mulVec_eigenvec {Q r A₀ R : ℕ} (β : AuxLabel Q r) :
    (M0 Q r A₀ R).mulVec (eigenvec ℚ β) =
      ((-1 : ℚ) ^ antisymCount β * (fI A₀ R).eval (antisymCount β : ℚ)) • eigenvec ℚ β := by
  rw [M0, ← Matrix.mulVec_mulVec, Matrix.sum_mulVec]
  have hsum :
      (∑ j ∈ range R,
          (((j.factorial : ℚ)⁻¹) •
            (fallingTermMatrixInt Q r A₀ j).map (Int.cast : ℤ → ℚ)).mulVec (eigenvec ℚ β)) =
        (fI A₀ R).eval (antisymCount β : ℚ) • eigenvec ℚ β := by
    rw [fI, Polynomial.eval_finsetSum, sum_smul]
    refine sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mulVec, fallingTermMatrix_map_mulVec_eigenvec, eval_mul, eval_C, smul_smul]
  rw [hsum, Matrix.mulVec_smul, fullSwapMatrix_mulVec_eigenvec, smul_smul,
    mul_comm ((-1 : ℚ) ^ antisymCount β)]

/-- When `antisymCount β ∈ Finset.Ico A₀ (A₀ + R)`, `M0 Q r A₀ R` fixes `eigenvec ℚ β`. -/
theorem M0_mulVec_eigenvec_of_mem_Ico {Q r A₀ R : ℕ} {β : AuxLabel Q r}
    (hβ : antisymCount β ∈ Ico A₀ (A₀ + R)) :
    (M0 Q r A₀ R).mulVec (eigenvec ℚ β) = eigenvec ℚ β := by
  rw [M0_mulVec_eigenvec, eval_fI_of_mem_Ico hβ, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_smul]

/-- Orthogonality of the `{0, 1, -1}`-eigenbasis `eigenvecInt` on `AuxLabel Q r`. -/
theorem sum_eigenvecInt_mul_eigenvecInt {Q r : ℕ} (β β' : AuxLabel Q r) :
    (∑ u : AuxLabel Q r, eigenvecInt β u * eigenvecInt β' u) =
      if β = β' then eigenNormSq β else 0 := by
  unfold eigenvecInt eigenNormSq
  simp_rw [← prod_mul_distrib]
  let e : (Fin Q → Fin r × Fin r) ≃ AuxLabel Q r :=
    { toFun := fun f => (fun s => (f s).1, fun s => (f s).2)
      invFun := fun u s => (u.1 s, u.2 s)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.sum_comp]
  let g : Fin Q → Fin r × Fin r → ℤ := fun s p =>
    pairBasis (β.1 s) (β.2 s) p.1 p.2 * pairBasis (β'.1 s) (β'.2 s) p.1 p.2
  have he :
      ∀ f : Fin Q → Fin r × Fin r,
        (∏ s : Fin Q,
            pairBasis (β.1 s) (β.2 s) ((e f).1 s) ((e f).2 s) *
              pairBasis (β'.1 s) (β'.2 s) ((e f).1 s) ((e f).2 s)) =
          ∏ s : Fin Q, g s (f s) :=
    fun _ => rfl
  simp_rw [he]
  rw [← Fintype.prod_sum g]
  have hslot :
      ∀ s : Fin Q,
        (∑ p : Fin r × Fin r, g s p) =
          if β.1 s = β'.1 s ∧ β.2 s = β'.2 s then pairNormSq (β.1 s) (β.2 s) else 0 := by
    intro s
    rw [Fintype.sum_prod_type, sum_pairBasis_mul_pairBasis]
  simp_rw [hslot]
  by_cases h : β = β'
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    have hnotall : ¬ ∀ s : Fin Q, β.1 s = β'.1 s ∧ β.2 s = β'.2 s := by
      intro hall
      exact h (Prod.ext (funext fun s => (hall s).1) (funext fun s => (hall s).2))
    push Not at hnotall
    obtain ⟨s, hs⟩ := hnotall
    refine prod_eq_zero (mem_univ s) ?_
    have hnot : ¬ (β.1 s = β'.1 s ∧ β.2 s = β'.2 s) := fun hboth => hs hboth.1 hboth.2
    simp [hnot]

/-- The square matrix whose `β`-th row is `eigenvec ℚ β`. -/
def eigenMatrix (Q r : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℚ :=
  fun β u => eigenvec ℚ β u

/-- The inverse diagonal norm matrix matching `eigenMatrix Q r`. -/
def invNormDiag (Q r : ℕ) : Matrix (AuxLabel Q r) (AuxLabel Q r) ℚ :=
  diagonal (fun β => (eigenNormSq β : ℚ)⁻¹)

private theorem invNormDiag_mul_eigenMatrix_apply (Q r : ℕ) (β u : AuxLabel Q r) :
    (invNormDiag Q r * eigenMatrix Q r) β u = (eigenNormSq β : ℚ)⁻¹ * eigenvec ℚ β u := by
  simp [invNormDiag, eigenMatrix, Matrix.mul_apply, Matrix.diagonal_apply]

theorem invNormDiag_mul_eigenMatrix_mul_transpose (Q r : ℕ) :
    (invNormDiag Q r * eigenMatrix Q r) * (eigenMatrix Q r)ᵀ = 1 := by
  ext β β'
  rw [Matrix.mul_apply]
  have hrow :
      ∀ u : AuxLabel Q r,
        (invNormDiag Q r * eigenMatrix Q r) β u * (eigenMatrix Q r)ᵀ u β' =
          (eigenNormSq β : ℚ)⁻¹ * ((eigenvecInt β u : ℚ) * (eigenvecInt β' u : ℚ)) := by
    intro u
    rw [invNormDiag_mul_eigenMatrix_apply, transpose_apply, eigenMatrix, eigenvec, eigenvec,
      mul_assoc]
  simp_rw [hrow, ← mul_sum]
  have horth := congrArg (Int.cast : ℤ → ℚ) (sum_eigenvecInt_mul_eigenvecInt β β')
  push_cast at horth
  rw [horth, Matrix.one_apply]
  split_ifs with h
  · have hne : (eigenNormSq β : ℚ) ≠ 0 := by exact_mod_cast (eigenNormSq_pos β).ne'
    exact inv_mul_cancel₀ hne
  · simp

theorem transpose_eigenMatrix_mul_invNormDiag_mul_eigenMatrix (Q r : ℕ) :
    (eigenMatrix Q r)ᵀ * (invNormDiag Q r * eigenMatrix Q r) = 1 :=
  mul_eq_one_comm.1 (invNormDiag_mul_eigenMatrix_mul_transpose Q r)

/-- Orthogonal basis expansion of any vector `ξ : AuxLabel Q r → ℚ` in terms of `eigenvec ℚ β`. -/
theorem eq_sum_eigenvec (Q r : ℕ) (ξ : AuxLabel Q r → ℚ) :
    ξ = ∑ β : AuxLabel Q r,
      ((eigenNormSq β : ℚ)⁻¹ * dotProduct (eigenvec ℚ β) ξ) • eigenvec ℚ β := by
  ext u
  have h := congrFun (congrArg (fun A => A.mulVec ξ)
    (transpose_eigenMatrix_mul_invNormDiag_mul_eigenMatrix Q r)) u
  rw [Matrix.one_mulVec] at h
  rw [← h, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, transpose_apply, eigenMatrix,
    invNormDiag_mul_eigenMatrix_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← mul_sum]
  refine sum_congr rfl fun β _ => ?_
  ring

/-- The set of basis indices `β : AuxLabel Q r` whose antisymmetric count `j(β)` lies outside the
interval `I = Finset.Ico A₀ (A₀ + R)`. -/
def measurementIndices (Q r A₀ R : ℕ) : Finset (AuxLabel Q r) :=
  univ.filter (fun β => antisymCount β ∉ Ico A₀ (A₀ + R))

/-- The number of measurement rows `#(measurementIndices Q r A₀ R)` plus the number of fixed
basis indices in `I = Finset.Ico A₀ (A₀ + R)` equals `D = r ^ (2 * Q)`. -/
theorem card_measurementIndices_add_card_mem_Ico (Q r A₀ R : ℕ) :
    #(measurementIndices Q r A₀ R) +
        #(univ.filter fun β : AuxLabel Q r => antisymCount β ∈ Ico A₀ (A₀ + R)) =
      r ^ (2 * Q) := by
  rw [measurementIndices, add_comm, card_filter_add_card_filter_not, card_univ, card_auxLabel]

/-- At each slot, the number of antisymmetric pairs `(α, δ) ∈ Fin r × Fin r` with `δ < α` satisfies
`2 * #{p : Fin r × Fin r | p.2 < p.1} + r = r ^ 2` (i.e., `r * (r - 1) / 2` pairs with eigenvalue
`-1` and `r * (r + 1) / 2` pairs with eigenvalue `+1`, Proof of Lemma 4.1, p. 28). -/
theorem two_mul_card_antisymPair_add_eq_sq (r : ℕ) :
    2 * #{p : Fin r × Fin r | p.2 < p.1} + r = r ^ 2 := by
  have hswap :
      #{p : Fin r × Fin r | p.2 < p.1} = #{p : Fin r × Fin r | p.1 < p.2} := by
    refine card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact hp
  have hdiag : #{p : Fin r × Fin r | p.1 = p.2} = r := by
    refine (card_bij (fun i : Fin r => fun _ => (i, i)) ?_ ?_ ?_).symm.trans
      (by rw [card_univ, Fintype.card_fin])
    · intro i _; simp
    · intro i₁ _ i₂ _ h; exact (Prod.mk.inj h).1
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact ⟨p.1, mem_univ _, Prod.ext rfl hp⟩
  have hpart :
      #{p : Fin r × Fin r | p.2 < p.1} +
          #{p : Fin r × Fin r | p.1 < p.2} +
          #{p : Fin r × Fin r | p.1 = p.2} =
        r ^ 2 := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin r × Fin r)))
      (p := fun p : Fin r × Fin r => p.1 = p.2)
    have h2 :
        (univ.filter fun p : Fin r × Fin r => ¬ p.1 = p.2) =
          (univ.filter fun p : Fin r × Fin r => p.2 < p.1) ∪
            (univ.filter fun p : Fin r × Fin r => p.1 < p.2) := by
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    have hdisj :
        Disjoint (univ.filter fun p : Fin r × Fin r => p.2 < p.1)
          (univ.filter fun p : Fin r × Fin r => p.1 < p.2) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [mem_filter, mem_univ, true_and] at hp1 hp2
      omega
    rw [h2, card_union_of_disjoint hdisj, card_univ, Fintype.card_prod, Fintype.card_fin,
      ← sq] at h1
    omega
  omega

/-- The `{0, 1, -1}`-valued measurement matrix `C^B` of Lemma 4.1 (p. 28), whose rows are the
transposes of `eigenvec K β` for `β ∈ measurementIndices Q r A₀ R`. -/
def measurementMatrix (Q r A₀ R : ℕ) (K : Type*) [CommRing K] :
    Matrix (measurementIndices Q r A₀ R) (AuxLabel Q r) K :=
  fun β u => eigenvec K β.1 u

theorem measurementMatrix_entry_mem (Q r A₀ R : ℕ) (β : measurementIndices Q r A₀ R)
    (u : AuxLabel Q r) :
    measurementMatrix Q r A₀ R ℤ β u = 0 ∨
      measurementMatrix Q r A₀ R ℤ β u = 1 ∨
      measurementMatrix Q r A₀ R ℤ β u = -1 :=
  eigenvecInt_mem β.1 u

theorem measurementMatrix_mulVec_eq_zero_iff (Q r A₀ R : ℕ) (K : Type*) [CommRing K]
    (ξ : AuxLabel Q r → K) :
    (measurementMatrix Q r A₀ R K).mulVec ξ = 0 ↔
      ∀ β : AuxLabel Q r, antisymCount β ∉ Ico A₀ (A₀ + R) → dotProduct (eigenvec K β) ξ = 0 := by
  constructor
  · intro h β hβ
    have hmem : β ∈ measurementIndices Q r A₀ R := mem_filter.2 ⟨mem_univ β, hβ⟩
    exact congrFun h ⟨β, hmem⟩
  · intro h
    ext ⟨β, hβ⟩
    exact h β (mem_filter.1 hβ).2

/-- **Lemma 4.1 (Kernel invariance, p. 28)**: if `(measurementMatrix Q r A₀ R ℚ).mulVec ξ = 0`,
then `M0 Q r A₀ R` fixes `ξ`. -/
theorem M0_mulVec_eq_self_of_measurementMatrix_mulVec_eq_zero {Q r A₀ R : ℕ}
    {ξ : AuxLabel Q r → ℚ} (hker : (measurementMatrix Q r A₀ R ℚ).mulVec ξ = 0) :
    (M0 Q r A₀ R).mulVec ξ = ξ := by
  rw [measurementMatrix_mulVec_eq_zero_iff] at hker
  conv_lhs => rw [eq_sum_eigenvec Q r ξ]
  conv_rhs => rw [eq_sum_eigenvec Q r ξ]
  rw [Matrix.mulVec_sum]
  refine sum_congr rfl fun β _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases hβ : antisymCount β ∈ Ico A₀ (A₀ + R)
  · rw [M0_mulVec_eigenvec_of_mem_Ico hβ]
  · rw [hker β hβ, mul_zero, zero_smul, zero_smul]

/-! ### 4. Mismatch support bound (Lemma 4.2, pp. 28–29) -/

/-- The mismatch set `E_{u,y} = {s : Fin Q | y.1 s ≠ u.2 s}` (eq. 4.9). -/
def mismatchSet {Q r : ℕ} (u y : AuxLabel Q r) : Finset (Fin Q) :=
  univ.filter (fun s => y.1 s ≠ u.2 s)

/-- First-component disagreement set `{s : Fin Q | y.1 s ≠ z.1 s}` used to track support width
across matrix products in `f_I(W_0)`. -/
private def firstDiffSet {Q r : ℕ} (z y : AuxLabel Q r) : Finset (Fin Q) :=
  univ.filter (fun s => y.1 s ≠ z.1 s)

private theorem firstDiffSet_self {Q r : ℕ} (z : AuxLabel Q r) :
    firstDiffSet z z = ∅ := by
  ext s; simp [firstDiffSet]

private theorem firstDiffSet_fullSwap {Q r : ℕ} (u y : AuxLabel Q r) :
    firstDiffSet (fullSwap u) y = mismatchSet u y := by
  ext s; simp [firstDiffSet, mismatchSet]

private theorem card_firstDiffSet_triangle {Q r : ℕ} (z w y : AuxLabel Q r) :
    #(firstDiffSet z y) ≤ #(firstDiffSet z w) + #(firstDiffSet w y) := by
  have hsub : firstDiffSet z y ⊆ firstDiffSet z w ∪ firstDiffSet w y := by
    intro s hs
    simp only [firstDiffSet, mem_filter, mem_univ, true_and, mem_union] at hs ⊢
    by_contra h
    push Not at h
    exact hs (h.2.trans h.1)
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- A matrix `A` has first-component disagreement bounded by `k` on all nonzero entries. -/
private def HasFirstDiffBound (Q r : ℕ) (K : Type*) [CommRing K] (k : ℕ)
    (A : Matrix (AuxLabel Q r) (AuxLabel Q r) K) : Prop :=
  ∀ z y, A z y ≠ 0 → #(firstDiffSet z y) ≤ k

private theorem hasFirstDiffBound_mono {Q r : ℕ} {K : Type*} [CommRing K] {k k' : ℕ}
    {A : Matrix (AuxLabel Q r) (AuxLabel Q r) K} (h : HasFirstDiffBound Q r K k A) (hle : k ≤ k') :
    HasFirstDiffBound Q r K k' A :=
  fun z y hne => (h z y hne).trans hle

private theorem hasFirstDiffBound_one (Q r : ℕ) (K : Type*) [CommRing K] (k : ℕ) :
    HasFirstDiffBound Q r K k 1 := by
  intro z y hne
  have hzy : z = y := by
    by_contra h
    exact hne (Matrix.one_apply_ne h)
  subst hzy
  simp [firstDiffSet_self]

private theorem hasFirstDiffBound_slotSwapMatrix (Q r : ℕ) (K : Type*) [CommRing K] (s : Fin Q) :
    HasFirstDiffBound Q r K 1 (slotSwapMatrix Q r K s) := by
  intro z y hne
  have hy : y = slotSwap s z := by
    by_contra h
    have h' : y ≠ subsetSwap {s} z := h
    exact hne (by simp [slotSwapMatrix, subsetSwapMatrix, h'])
  subst hy
  have hsub : firstDiffSet z (slotSwap s z) ⊆ {s} := by
    intro t ht
    simp only [firstDiffSet, slotSwap, subsetSwap, mem_filter, mem_univ, true_and,
      mem_singleton] at ht ⊢
    by_contra hts
    exact ht (by simp [hts])
  exact (card_le_card hsub).trans (by simp)

private theorem hasFirstDiffBound_add {Q r : ℕ} {K : Type*} [CommRing K] {k : ℕ}
    {A B : Matrix (AuxLabel Q r) (AuxLabel Q r) K}
    (hA : HasFirstDiffBound Q r K k A) (hB : HasFirstDiffBound Q r K k B) :
    HasFirstDiffBound Q r K k (A + B) := by
  intro z y hne
  by_cases hAz : A z y = 0
  · refine hB z y ?_
    intro hBz
    exact hne (by simp [hAz, hBz])
  · exact hA z y hAz

private theorem hasFirstDiffBound_sub {Q r : ℕ} {K : Type*} [CommRing K] {k : ℕ}
    {A B : Matrix (AuxLabel Q r) (AuxLabel Q r) K}
    (hA : HasFirstDiffBound Q r K k A) (hB : HasFirstDiffBound Q r K k B) :
    HasFirstDiffBound Q r K k (A - B) := by
  intro z y hne
  by_cases hAz : A z y = 0
  · refine hB z y ?_
    intro hBz
    exact hne (by simp [hAz, hBz])
  · exact hA z y hAz

private theorem hasFirstDiffBound_smul {Q r : ℕ} {K : Type*} [CommRing K] {k : ℕ} (c : K)
    {A : Matrix (AuxLabel Q r) (AuxLabel Q r) K} (hA : HasFirstDiffBound Q r K k A) :
    HasFirstDiffBound Q r K k (c • A) := by
  intro z y hne
  refine hA z y ?_
  intro hAz
  exact hne (by simp [hAz])

private theorem hasFirstDiffBound_sum {Q r : ℕ} {K : Type*} [CommRing K] {ι : Type*}
    (s : Finset ι) (k : ℕ) (f : ι → Matrix (AuxLabel Q r) (AuxLabel Q r) K)
    (hf : ∀ i ∈ s, HasFirstDiffBound Q r K k (f i)) :
    HasFirstDiffBound Q r K k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z y hne
    exfalso
    exact hne (by simp)
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact hasFirstDiffBound_add (hf i (mem_insert_self i s))
      (ih fun j hj => hf j (mem_insert_of_mem hj))

private theorem hasFirstDiffBound_mul {Q r : ℕ} {K : Type*} [CommRing K] {k₁ k₂ : ℕ}
    {A B : Matrix (AuxLabel Q r) (AuxLabel Q r) K}
    (hA : HasFirstDiffBound Q r K k₁ A) (hB : HasFirstDiffBound Q r K k₂ B) :
    HasFirstDiffBound Q r K (k₁ + k₂) (A * B) := by
  intro z y hne
  rw [Matrix.mul_apply] at hne
  obtain ⟨w, -, hw⟩ := exists_ne_zero_of_sum_ne_zero hne
  have hAw : A z w ≠ 0 := left_ne_zero_of_mul hw
  have hBw : B w y ≠ 0 := right_ne_zero_of_mul hw
  exact (card_firstDiffSet_triangle z w y).trans (Nat.add_le_add (hA z w hAw) (hB w y hBw))

private theorem hasFirstDiffBound_fallingTermMatrixInt (Q r A₀ j : ℕ) :
    HasFirstDiffBound Q r ℤ j (fallingTermMatrixInt Q r A₀ j) := by
  unfold fallingTermMatrixInt fallingProdMatrixInt
  refine hasFirstDiffBound_smul _ ?_
  induction j with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    exact hasFirstDiffBound_one Q r ℤ 0
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton]
    refine hasFirstDiffBound_mul ih ?_
    refine hasFirstDiffBound_sub ?_ (hasFirstDiffBound_smul _ (hasFirstDiffBound_one Q r ℤ 1))
    exact hasFirstDiffBound_sum univ 1 _ fun s _ =>
      hasFirstDiffBound_sub (hasFirstDiffBound_one Q r ℤ 1)
        (hasFirstDiffBound_slotSwapMatrix Q r ℤ s)

/-- **Lemma 4.2 (Mismatch support bound, pp. 28–29)**: if `M0 Q r A₀ R u y ≠ 0`, then
`#{s : Fin Q | y.1 s ≠ u.2 s} ≤ R - 1`. -/
theorem card_mismatchSet_le_of_M0_ne_zero {Q r A₀ R : ℕ} {u y : AuxLabel Q r}
    (hne : M0 Q r A₀ R u y ≠ 0) :
    #(mismatchSet u y) ≤ R - 1 := by
  rw [M0, fullSwapMatrix_mul_apply] at hne
  have hbound :
      HasFirstDiffBound Q r ℚ (R - 1)
        (∑ j ∈ range R,
          ((j.factorial : ℚ)⁻¹) • (fallingTermMatrixInt Q r A₀ j).map (Int.cast : ℤ → ℚ)) := by
    refine hasFirstDiffBound_sum (range R) (R - 1) _ fun j hj => ?_
    refine hasFirstDiffBound_smul _ ?_
    intro z w hzw
    have hzwInt : fallingTermMatrixInt Q r A₀ j z w ≠ 0 := by
      intro h0
      exact hzw (by simp [h0])
    exact (hasFirstDiffBound_fallingTermMatrixInt Q r A₀ j z w hzwInt).trans
      (Nat.le_sub_one_of_lt (mem_range.1 hj))
  rw [← firstDiffSet_fullSwap]
  exact hbound (fullSwap u) y hne

/-- Integer counterpart of Lemma 4.2 for `M0ScaledInt Q r A₀ R`. -/
theorem card_mismatchSet_le_of_M0ScaledInt_ne_zero {Q r A₀ R : ℕ} {u y : AuxLabel Q r}
    (hne : M0ScaledInt Q r A₀ R u y ≠ 0) :
    #(mismatchSet u y) ≤ R - 1 := by
  rw [M0ScaledInt, fullSwapMatrix_mul_apply] at hne
  have hbound :
      HasFirstDiffBound Q r ℤ (R - 1)
        (∑ j ∈ range R,
          (((R - 1).factorial / j.factorial : ℕ) : ℤ) • fallingTermMatrixInt Q r A₀ j) := by
    refine hasFirstDiffBound_sum (range R) (R - 1) _ fun j hj => ?_
    exact hasFirstDiffBound_smul _
      (hasFirstDiffBound_mono (hasFirstDiffBound_fallingTermMatrixInt Q r A₀ j)
        (Nat.le_sub_one_of_lt (mem_range.1 hj)))
  rw [← firstDiffSet_fullSwap]
  exact hbound (fullSwap u) y hne

/-! ### 5. Auxiliary polynomial replacement rows (Lemma 4.3, pp. 29–30) -/

/-- The 1-based evaluation node `t = s.1 + 1 ∈ {1, ..., Q}` associated to `s : Fin Q`. -/
def nodePoint {Q : ℕ} (s : Fin Q) : ℚ :=
  (s.1 : ℚ) + 1

theorem nodePoint_pos {Q : ℕ} (s : Fin Q) : 0 < nodePoint s := by
  unfold nodePoint; positivity

theorem nodePoint_ne_zero {Q : ℕ} (s : Fin Q) : nodePoint s ≠ 0 :=
  (nodePoint_pos s).ne'

/-- The Lagrange mismatch annihilator polynomial
`φ_{u,y}(T) = ∏_{s ∈ E_{u,y}} (1 - T / (s.1 + 1)) ∈ ℚ[X]` (eq. 4.9). -/
noncomputable def mismatchAnnihilator {Q r : ℕ} (u y : AuxLabel Q r) : ℚ[X] :=
  ∏ s ∈ mismatchSet u y, (1 - C (nodePoint s)⁻¹ * X)

@[simp]
theorem eval_mismatchAnnihilator_zero {Q r : ℕ} (u y : AuxLabel Q r) :
    (mismatchAnnihilator u y).eval 0 = 1 := by
  simp [mismatchAnnihilator, eval_prod]

theorem eval_mismatchAnnihilator_nodePoint_of_ne {Q r : ℕ} {u y : AuxLabel Q r} {s : Fin Q}
    (hne : y.1 s ≠ u.2 s) :
    (mismatchAnnihilator u y).eval (nodePoint s) = 0 := by
  unfold mismatchAnnihilator
  rw [eval_prod]
  refine prod_eq_zero (mem_filter.2 ⟨mem_univ s, hne⟩) ?_
  simp [inv_mul_cancel₀ (nodePoint_ne_zero s)]

theorem natDegree_mismatchAnnihilator_le {Q r : ℕ} (u y : AuxLabel Q r) :
    (mismatchAnnihilator u y).natDegree ≤ #(mismatchSet u y) := by
  unfold mismatchAnnihilator
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h1 : ∀ s ∈ mismatchSet u y, (1 - C (nodePoint s)⁻¹ * X).natDegree ≤ 1 := by
    intro s _
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    refine max_le (by simp) ?_
    refine Polynomial.natDegree_mul_le.trans ?_
    simp
  exact (sum_le_sum h1).trans (by simp)

/-- The auxiliary replacement polynomial row `P⃗_u(T) ∈ (AuxLabel Q r → ℚ[X])` (eq. 4.10):
`P⃗_u(T)_y = (I - M_0)[u, y] + M_0[u, y] φ_{u,y}(T)`. -/
noncomputable def auxReplacementRow (Q r A₀ R : ℕ) (u y : AuxLabel Q r) : ℚ[X] :=
  C ((1 - M0 Q r A₀ R) u y) + C (M0 Q r A₀ R u y) * mismatchAnnihilator u y

/-- Pairing `⟨P⃗_u(t), ζ⟩` of `auxReplacementRow Q r A₀ R u` with `ζ : AuxLabel Q r → ℚ`
at `T = t` (eq. 4.11). -/
noncomputable def evalAuxReplacementRow (Q r A₀ R : ℕ) (u : AuxLabel Q r) (t : ℚ)
    (ζ : AuxLabel Q r → ℚ) : ℚ :=
  ∑ y : AuxLabel Q r, (auxReplacementRow Q r A₀ R u y).eval t * ζ y

/-- The auxiliary coordinate group `S^B_{s, g} = {y : AuxLabel Q r | y.1 s = g}` (eq. 4.3). -/
def auxGroup {Q r : ℕ} (s : Fin Q) (g : Fin r) : Finset (AuxLabel Q r) :=
  univ.filter (fun y => y.1 s = g)

@[simp]
theorem mem_auxGroup {Q r : ℕ} {s : Fin Q} {g : Fin r} {y : AuxLabel Q r} :
    y ∈ auxGroup s g ↔ y.1 s = g := by
  simp [auxGroup]

theorem disjoint_auxGroup {Q r : ℕ} (s : Fin Q) {g₁ g₂ : Fin r} (hne : g₁ ≠ g₂) :
    Disjoint (auxGroup (r := r) s g₁) (auxGroup (r := r) s g₂) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  rw [mem_auxGroup] at hy1 hy2
  exact hne (hy1.symm.trans hy2)

theorem biUnion_auxGroup {Q r : ℕ} (s : Fin Q) :
    univ.biUnion (auxGroup (Q := Q) (r := r) s) = univ := by
  ext y
  simp [mem_biUnion]

/-- Restriction of a vector `ζ : AuxLabel Q r → K` to `auxGroup s g`, extended by zero outside
`auxGroup s g` (Section 4.3, p. 29). -/
def auxGroupRestrict {Q r : ℕ} {K : Type*} [Zero K] (s : Fin Q) (g : Fin r)
    (ζ : AuxLabel Q r → K) : AuxLabel Q r → K :=
  fun y => if y ∈ auxGroup s g then ζ y else 0

theorem sum_auxGroupRestrict {Q r : ℕ} {K : Type*} [AddCommMonoid K] (s : Fin Q)
    (ζ : AuxLabel Q r → K) :
    (∑ g : Fin r, auxGroupRestrict s g ζ) = ζ := by
  ext y
  simp [auxGroupRestrict]

/-- **Equation (4.12) (p. 29)**: the measurement vector `C^B ζ` is the sum over `g : Fin r` of the
restricted measurement vectors `C^B (ζ|_{S^B_{s, g}})`. -/
theorem sum_measurementMatrix_mulVec_auxGroupRestrict (Q r A₀ R : ℕ) (K : Type*) [CommRing K]
    (s : Fin Q) (ζ : AuxLabel Q r → K) :
    (∑ g : Fin r, (measurementMatrix Q r A₀ R K).mulVec (auxGroupRestrict s g ζ)) =
      (measurementMatrix Q r A₀ R K).mulVec ζ := by
  rw [← Matrix.mulVec_sum, sum_auxGroupRestrict]

/-- **Lemma 4.3 (Degree bound, p. 29)**: every entry of `auxReplacementRow Q r A₀ R u` has degree
at most `R - 1`. -/
theorem natDegree_auxReplacementRow_le (Q r A₀ R : ℕ) (u y : AuxLabel Q r) :
    (auxReplacementRow Q r A₀ R u y).natDegree ≤ R - 1 := by
  unfold auxReplacementRow
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  by_cases hne : M0 Q r A₀ R u y = 0
  · simp [hne]
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp only [natDegree_C, zero_add]
    exact (natDegree_mismatchAnnihilator_le u y).trans (card_mismatchSet_le_of_M0_ne_zero hne)

/-- **Lemma 4.3 (Value at zero, p. 29)**: `P⃗_u(0) = δ_u`. -/
@[simp]
theorem eval_auxReplacementRow_zero (Q r A₀ R : ℕ) (u y : AuxLabel Q r) :
    (auxReplacementRow Q r A₀ R u y).eval 0 = if u = y then 1 else 0 := by
  unfold auxReplacementRow
  rw [eval_add, eval_mul, eval_C, eval_C, eval_mismatchAnnihilator_zero, mul_one,
    Matrix.sub_apply, Matrix.one_apply, sub_add_cancel]

/-- **Lemma 4.3 (Linear form at zero, p. 29)**: `⟨P⃗_u(0), ζ⟩ = ζ u`. -/
@[simp]
theorem evalAuxReplacementRow_zero (Q r A₀ R : ℕ) (u : AuxLabel Q r) (ζ : AuxLabel Q r → ℚ) :
    evalAuxReplacementRow Q r A₀ R u 0 ζ = ζ u := by
  simp [evalAuxReplacementRow]

/-- Equation (4.11) decomposition of `⟨P⃗_u(t), ζ⟩`. -/
theorem evalAuxReplacementRow_eq (Q r A₀ R : ℕ) (u : AuxLabel Q r) (t : ℚ)
    (ζ : AuxLabel Q r → ℚ) :
    evalAuxReplacementRow Q r A₀ R u t ζ =
      ((1 - M0 Q r A₀ R).mulVec ζ) u +
        ∑ y : AuxLabel Q r, M0 Q r A₀ R u y * (mismatchAnnihilator u y).eval t * ζ y := by
  unfold evalAuxReplacementRow auxReplacementRow
  simp only [eval_add, eval_mul, eval_C, add_mul, sum_add_distrib]
  rfl

/-- At `t = nodePoint s`, the sum in (4.11) ranges only over `y ∈ auxGroup s (u.2 s)`. -/
theorem evalAuxReplacementRow_nodePoint (Q r A₀ R : ℕ) (u : AuxLabel Q r) (s : Fin Q)
    (ζ : AuxLabel Q r → ℚ) :
    evalAuxReplacementRow Q r A₀ R u (nodePoint s) ζ =
      ((1 - M0 Q r A₀ R).mulVec ζ) u +
        ∑ y ∈ auxGroup s (u.2 s),
          M0 Q r A₀ R u y * (mismatchAnnihilator u y).eval (nodePoint s) * ζ y := by
  rw [evalAuxReplacementRow_eq]
  congr 1
  refine (sum_subset (subset_univ _) fun y _ hy => ?_).symm
  simp only [auxGroup, mem_filter, mem_univ, true_and] at hy
  rw [eval_mismatchAnnihilator_nodePoint_of_ne hy, mul_zero, zero_mul]

/-- **Lemma 4.3 (Restricted kernel vanishing, p. 29)**: for `g ≠ u.2 s`, if `ξ` is supported on
`auxGroup s g` and `(measurementMatrix Q r A₀ R ℚ).mulVec ξ = 0`, then
`⟨P⃗_u(nodePoint s), ξ⟩ = 0`. -/
theorem evalAuxReplacementRow_nodePoint_eq_zero_of_kernel
    (Q r A₀ R : ℕ) (u : AuxLabel Q r) (s : Fin Q) (g : Fin r) (hg : g ≠ u.2 s)
    (ξ : AuxLabel Q r → ℚ) (hsupp : ∀ y, y ∉ auxGroup s g → ξ y = 0)
    (hker : (measurementMatrix Q r A₀ R ℚ).mulVec ξ = 0) :
    evalAuxReplacementRow Q r A₀ R u (nodePoint s) ξ = 0 := by
  rw [evalAuxReplacementRow_nodePoint]
  have hM : ((1 - M0 Q r A₀ R).mulVec ξ) u = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec,
      M0_mulVec_eq_self_of_measurementMatrix_mulVec_eq_zero hker, sub_self, Pi.zero_apply]
  have hsum :
      (∑ y ∈ auxGroup s (u.2 s),
          M0 Q r A₀ R u y * (mismatchAnnihilator u y).eval (nodePoint s) * ξ y) = 0 := by
    refine sum_eq_zero fun y hy => ?_
    have hy_not : y ∉ auxGroup s g := by
      simp only [auxGroup, mem_filter, mem_univ, true_and] at hy ⊢
      rw [hy]
      exact hg.symm
    rw [hsupp y hy_not, mul_zero]
  rw [hM, hsum, add_zero]

/-- **Lemma 4.3 (Determination by assigned group and measurements, p. 29)**: at `t = nodePoint s`,
`⟨P⃗_u(nodePoint s), ζ⟩` is uniquely determined by `ζ` on `auxGroup s (u.2 s)` and
`(measurementMatrix Q r A₀ R ℚ).mulVec ζ`. -/
theorem evalAuxReplacementRow_nodePoint_eq_of_eq_on_auxGroup
    (Q r A₀ R : ℕ) (u : AuxLabel Q r) (s : Fin Q) (ζ₁ ζ₂ : AuxLabel Q r → ℚ)
    (hgroup : ∀ y ∈ auxGroup s (u.2 s), ζ₁ y = ζ₂ y)
    (hmeas : (measurementMatrix Q r A₀ R ℚ).mulVec ζ₁ =
      (measurementMatrix Q r A₀ R ℚ).mulVec ζ₂) :
    evalAuxReplacementRow Q r A₀ R u (nodePoint s) ζ₁ =
      evalAuxReplacementRow Q r A₀ R u (nodePoint s) ζ₂ := by
  rw [evalAuxReplacementRow_nodePoint, evalAuxReplacementRow_nodePoint]
  have hker : (measurementMatrix Q r A₀ R ℚ).mulVec (ζ₁ - ζ₂) = 0 := by
    rw [Matrix.mulVec_sub, hmeas, sub_self]
  have hdiff : ((1 - M0 Q r A₀ R).mulVec (ζ₁ - ζ₂)) u = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec,
      M0_mulVec_eq_self_of_measurementMatrix_mulVec_eq_zero hker, sub_self, Pi.zero_apply]
  have hM : ((1 - M0 Q r A₀ R).mulVec ζ₁) u = ((1 - M0 Q r A₀ R).mulVec ζ₂) u := by
    rw [Matrix.mulVec_sub, Pi.sub_apply, sub_eq_zero] at hdiff
    exact hdiff
  rw [hM]
  congr 1
  refine sum_congr rfl fun y hy => ?_
  rw [hgroup y hy]

/-! ### 6. Common-denominator clearing (Lemma 4.6, p. 33) -/

/-- The common denominator `d_den = (R - 1)! Q!` of Lemma 4.6 (p. 33). -/
def commonDenom (Q R : ℕ) : ℕ :=
  (R - 1).factorial * Q.factorial

theorem commonDenom_pos (Q R : ℕ) : 0 < commonDenom Q R :=
  Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

/-- The scaled integer polynomial `Q! φ_{u,y}(T) ∈ ℤ[X]` (Lemma 4.6, p. 33). -/
noncomputable def mismatchAnnihilatorScaledInt {Q r : ℕ} (u y : AuxLabel Q r) : ℤ[X] :=
  C (∏ s ∈ (mismatchSet u y)ᶜ, ((s.1 : ℤ) + 1)) *
    ∏ s ∈ mismatchSet u y, (C ((s.1 : ℤ) + 1) - X)

/-- The scaled integer replacement row `d_den P⃗_u(T)` (Lemma 4.6, p. 33). -/
noncomputable def auxReplacementRowScaledInt (Q r A₀ R : ℕ) (u y : AuxLabel Q r) : ℤ[X] :=
  C ((Q.factorial : ℤ) * ((if u = y then ((R - 1).factorial : ℤ) else 0) -
      M0ScaledInt Q r A₀ R u y)) +
    C (M0ScaledInt Q r A₀ R u y) * mismatchAnnihilatorScaledInt u y

private theorem prod_fin_add_one_eq_factorial (Q : ℕ) :
    (∏ s : Fin Q, ((s.1 : ℚ) + 1)) = (Q.factorial : ℚ) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

theorem map_mismatchAnnihilatorScaledInt {Q r : ℕ} (u y : AuxLabel Q r) :
    (mismatchAnnihilatorScaledInt u y).map (Int.castRingHom ℚ) =
      (Q.factorial : ℚ) • mismatchAnnihilator u y := by
  unfold mismatchAnnihilatorScaledInt mismatchAnnihilator
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, eq_intCast]
  push_cast
  have hfac :
      ∀ s ∈ mismatchSet u y,
        Polynomial.map (Int.castRingHom ℚ) (C ((s.1 : ℤ) + 1) - X) =
          C ((s.1 : ℚ) + 1) * (1 - C (nodePoint s)⁻¹ * X) := by
    intro s _
    rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, eq_intCast]
    push_cast
    have hs : nodePoint s ≠ 0 := nodePoint_ne_zero s
    have hns : ((s.1 : ℚ) + 1) * (nodePoint s)⁻¹ = 1 := mul_inv_cancel₀ hs
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, hns, C_1, one_mul]
  rw [prod_congr rfl hfac, prod_mul_distrib, ← map_prod C, ← mul_assoc, ← C_mul]
  have hcompl :
      (∏ s ∈ (mismatchSet u y)ᶜ, ((s.1 : ℚ) + 1)) *
          (∏ s ∈ mismatchSet u y, ((s.1 : ℚ) + 1)) =
        (Q.factorial : ℚ) := by
    rw [prod_compl_mul_prod, prod_fin_add_one_eq_factorial]
  rw [hcompl, Algebra.smul_def, algebraMap_eq]

theorem map_M0ScaledInt (Q r A₀ R : ℕ) :
    (M0ScaledInt Q r A₀ R).map (Int.cast : ℤ → ℚ) =
      ((R - 1).factorial : ℚ) • M0 Q r A₀ R := by
  ext u y
  rw [M0, M0ScaledInt, Matrix.map_apply, Matrix.smul_apply, fullSwapMatrix_mul_apply,
    fullSwapMatrix_mul_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjle : j ≤ R - 1 := Nat.le_sub_one_of_lt (mem_range.1 hj)
  have hdvd : j.factorial ∣ (R - 1).factorial := Nat.factorial_dvd_factorial hjle
  have hfac : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
  have hdiv :
      ((((R - 1).factorial / j.factorial : ℕ) : ℤ) : ℚ) =
        ((R - 1).factorial : ℚ) * (j.factorial : ℚ)⁻¹ := by
    have hmul :
        ((((R - 1).factorial / j.factorial : ℕ) : ℤ) : ℚ) * (j.factorial : ℚ) =
          ((R - 1).factorial : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    rw [← hmul, mul_assoc, mul_inv_cancel₀ hfac, mul_one]
  rw [hdiv, mul_assoc]

/-- **Lemma 4.6 (Common-denominator clearing, p. 33)**: multiplying `auxReplacementRow Q r A₀ R u y`
by `commonDenom Q R = (R - 1)! Q!` gives the integer polynomial
`auxReplacementRowScaledInt Q r A₀ R u y`. -/
theorem map_auxReplacementRowScaledInt (Q r A₀ R : ℕ) (u y : AuxLabel Q r) :
    (auxReplacementRowScaledInt Q r A₀ R u y).map (Int.castRingHom ℚ) =
      (commonDenom Q R : ℚ) • auxReplacementRow Q r A₀ R u y := by
  have hM0 : (M0ScaledInt Q r A₀ R u y : ℚ) = ((R - 1).factorial : ℚ) * M0 Q r A₀ R u y := by
    have h := congrFun (congrFun (map_M0ScaledInt Q r A₀ R) u) y
    simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using h
  unfold auxReplacementRowScaledInt auxReplacementRow commonDenom
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, eq_intCast,
    eq_intCast, map_mismatchAnnihilatorScaledInt]
  rw [smul_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, algebraMap_eq]
  congr 1
  · rw [← C_mul]
    congr 1
    push_cast
    rw [hM0]
    simp only [Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> ring
  · rw [← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul]
    congr 2
    push_cast
    rw [hM0]
    ring

end Cslib.LinearAlgebra
