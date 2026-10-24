/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Rectangular

/-!
# Rank of the padded test matrices

The reverse-Taylor test at a point is realised by a polynomial matrix `full M a` in a fresh
indeterminate `t`; zeroing its columns of index at least `N` gives `padded M N a`. Through the
embedding `t ↦ X` into Laurent series, the rectangular kernel theorem yields a lower bound
`q * N` on the rank of the block matrix formed from coefficient matrices and padded tests. The
padded entries are polynomials of degree at most `M - 1` and commute with coefficient maps.

## Main definitions

* `TestPolynomial.full`, `TestPolynomial.padded`: the full and padded reverse-Taylor test
  matrices over `K[X]`.
* `TestPolynomial.embed`: the embedding `K[X] →+* K⸨X⸩`.
* `PaddedRank.raw`: the block matrix `∑ᵢ Aᵢ ⊗ Rᵢ`, written entrywise.
* `PaddedRank.extend`: zero-padding of vectors from `N` to `M` columns per block.

## Main results

* `TestPolynomial.full_embed`: the embedded full test matrix is the matrix of `testMap`.
* `PaddedRank.rank_ge`: the padded block matrix has rank at least `q * N`.
* `PaddedRank.numeric_gap`: the arithmetic gap `(q - 1) * M < q * N`.
* `TestPolynomial.eval₂_padded`: padded tests commute with coefficient ring homomorphisms.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/PaddedRank.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.TestPolynomial
open Polynomial Matrix Module
open LaurentReduction SmallExpansion Rectangular RectangularExpansion
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

private lemma polynomialMap_single (M : ℕ) (b : Fin M) :
    polynomialMap M (Pi.single b (1 : K)) = X ^ b.val := by
  ext j
  by_cases hj : j < M
  · rw [polynomialMap_coeff M _ ⟨j, hj⟩, coeff_X_pow]
    simp [Pi.single_apply, Fin.ext_iff, eq_comm]
  · rw [polynomialMap_coeff_high M _ j (Nat.le_of_not_gt hj)]
    rw [coeff_X_pow]
    have hb : b.val ≠ j := by omega
    simp [Ne.symm hb]

/-- The inverse of `taylorCoordinates M a` is `taylorCoordinates M (-a)`. -/
lemma taylorCoordinates_symm (M : ℕ) (a : K) :
    (taylorCoordinates M a).symm = taylorCoordinates M (-a) := by
  ext x i
  rfl

/-- `(reverseCoordinates M).symm` reverses the index `j` to `j.rev`. -/
lemma reverseCoordinates_symm_apply (M : ℕ) (x : Fin M → K) :
    (reverseCoordinates M).symm x = fun j => x j.rev := rfl

/-- The `(i, j)` matrix entry of `(reverseTaylorCoordinates M a).symm` is the degree-`i`
coefficient of `(X + C (-a)) ^ j.rev`. -/
lemma reverseTaylor_symm_matrix (M : ℕ) (a : K) (i j : Fin M) :
    LinearMap.toMatrix' (reverseTaylorCoordinates M a).symm.toLinearMap i j =
      (((X + C (-a)) ^ j.rev.val : K[X]).coeff i.val) := by
  rw [LinearMap.toMatrix'_apply]
  simp only [reverseTaylorCoordinates, LinearEquiv.trans_symm,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, reverseCoordinates_symm_apply]
  rw [taylorCoordinates_symm]
  have he : (fun k : Fin M => (Pi.single j (1 : K) : Fin M → K) k.rev) =
      (Pi.single j.rev (1 : K) : Fin M → K) := by
    funext k
    simp only [Pi.single_apply]
    have hh : k.rev = j ↔ k = j.rev := by
      constructor <;> intro h
      · rw [← Fin.rev_rev k, h]
      · rw [h, Fin.rev_rev]
    congr 1
    exact propext hh
  rw [he, taylorCoordinates_apply, polynomialMap_single, taylor_X_pow]

/-- The reverse-Taylor test matrix over the univariate polynomial ring in t.
Summation over all M Taylor coordinates appends only zero terms. -/
def full (M : ℕ) (a : K) : Matrix (Fin M) (Fin M) K[X] := fun i j =>
  ∑ r : Fin M, C ((((X + C (-a)) ^ r.rev.val : K[X]).coeff i.val) *
    (((X + C a) ^ j.val : K[X]).coeff r.val)) * X ^ r.val

/-- The polynomial test matrix with columns above the threshold set to zero. -/
def padded (M N : ℕ) (a : K) : Matrix (Fin M) (Fin M) K[X] :=
  fun i j => if j.val < N then full M a i j else 0

/-- The original t indeterminate embeds into the fresh Laurent indeterminate. -/
def embed : K[X] →+* F K := Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single 1 1)

private lemma embed_C (a : K) : embed (C a) = HahnSeries.C a := by simp [embed]

private lemma embed_X_pow (a : ℕ) : embed ((X : K[X]) ^ a) = HahnSeries.single (a : ℤ) 1 := by
  simp [embed, HahnSeries.single_pow]

/-- Mapping `embed` over `full M a` gives the matrix of `testMap M a`. -/
lemma full_embed (M : ℕ) (a : K) :
    (embed.mapMatrix (full M a)) = LinearMap.toMatrix' (testMap M a) := by
  apply Matrix.ext
  intro i j
  change embed (full M a i j) = testMap M a (Pi.single j 1) i
  simp only [full, map_sum, map_mul, embed_C, embed_X_pow]
  change _ = liftMap (reverseTaylorCoordinates M a).symm.toLinearMap
    (weightMap Fin.val (liftMap (taylorCoordinates M a).toLinearMap (Pi.single j 1))) i
  rw [liftMap_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [reverseTaylor_symm_matrix]
  have hin : liftMap (taylorCoordinates M a).toLinearMap (Pi.single j (1 : F K)) r =
      HahnSeries.C ((((X + C a) ^ j.val : K[X]).coeff r.val)) := by
    rw [liftMap_apply]
    simp [Pi.single_apply, taylorCoordinates_apply, polynomialMap_single]
  simp only [weightMap, LinearMap.coe_mk, AddHom.coe_mk, hin]
  ring

private lemma full_natDegree_le (M : ℕ) (a : K) (i j : Fin M) :
    (full M a i j).natDegree ≤ M - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro r _
  apply (natDegree_C_mul_le _ _).trans
  simpa using Nat.le_sub_one_of_lt r.isLt

/-- Every entry of `padded M N a` has polynomial degree at most `M - 1`. -/
lemma padded_natDegree_le (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).natDegree ≤ M - 1 := by
  by_cases hj : j.val < N
  · simpa [padded, hj] using full_natDegree_le M a i j
  · simp [padded, hj]

end
end Rational.TestPolynomial

namespace Rational.PaddedRank
open Matrix Module
open TestPolynomial LaurentReduction SmallExpansion Rectangular RectangularExpansion
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The full block matrix formed from the coefficient and test matrices. -/
def raw {w q M : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (R : Fin w → Matrix (Fin M) (Fin M) (F K)) :
    Matrix (Fin q × Fin M) (Fin q × Fin M) (F K) :=
  fun a b => ∑ i, A i a.1 b.1 * R i a.2 b.2

omit [CharZero K] in
/-- Matrix-vector multiplication by `raw A R` expands blockwise over `i` and `γ`. -/
lemma raw_apply {w q M : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (R : Fin w → Matrix (Fin M) (Fin M) (F K)) (f : Fin q × Fin M → F K) (α : Fin q)
    (j : Fin M) :
    (raw A R).mulVec f (α, j) = ∑ i, ∑ γ, A i α γ * (R i).mulVec (fun b => f (γ, b)) j := by
  simp only [Matrix.mulVec, dotProduct, raw, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin w)))
    (t := (Finset.univ : Finset (Fin q)))]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Pad vectors in the truncated column space with zeros. -/
def extend (q M N : ℕ) : (Fin q × Fin N → F K) →ₗ[F K] (Fin q × Fin M → F K) where
  toFun f a := if h : a.2.val < N then f (a.1, ⟨a.2.val, h⟩) else 0
  map_add' f g := by funext a; by_cases h : a.2.val < N <;> simp [h]
  map_smul' c f := by funext a; by_cases h : a.2.val < N <;> simp [h]

omit [CharZero K] in
private lemma extend_low (q M N : ℕ) (f : Fin q × Fin N → F K) (α : Fin q) (j : Fin M) :
    N ≤ ↑j → extend q M N f (α, j) = 0 := by
  intro hj
  simp [extend, not_lt.mpr hj]

omit [CharZero K] in
/-- Zero-padding from `N` to `M` columns is injective when `N ≤ M`. -/
lemma extend_injective (q M N : ℕ) (hNM : N ≤ M) :
    Function.Injective (extend (K := K) q M N) := by
  intro f g h
  funext ⟨α, j⟩
  have hh := congrFun h (α, ⟨j.val, j.isLt.trans_le hNM⟩)
  simpa [extend, j.isLt] using hh

omit [CharZero K] in
private lemma padded_mulVec_low (M N : ℕ) (a : K) (f : Fin M → F K)
    (hf : ∀ (j : Fin M), N ≤ ↑j → f j = 0) :
    (embed.mapMatrix (padded M N a)).mulVec f = testMap M a f := by
  rw [← Matrix.toLin'_toMatrix' (testMap M a), ← full_embed M a, Matrix.toLin'_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < N
  · simp [padded, hj]
  · simp [padded, hj, hf j (Nat.le_of_not_gt hj)]

/-- The padded test matrices satisfy a rectangular rank lower bound,
using an invertible witness and the expansion theorem. -/
theorem rank_ge (w B M N q e : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2 * w ^ 3 * B) (hq : q ≤ B) (he : 0 < e)
    (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (X : Fin w → Matrix (Fin e) (Fin e) (F K))
    (hX : Function.Injective (blockEval A X)) :
    q * N ≤ (raw A (fun i => embed.mapMatrix (padded M N (points i)))).rank := by
  let R := fun i => embed.mapMatrix (padded M N (points i))
  let L := (raw A R).mulVecLin.comp (extend q M N)
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    let f : Fin q → Fin M → F K := fun α j => extend q M N v (α, j)
    have hf : ∀ α j, N ≤ j.val → f α j = 0 := extend_low q M N v
    have hker : ∀ α, ∑ i, ∑ γ, A i α γ • testMap M (points i) (f γ) = 0 := by
      intro α
      funext j
      have hh := congrFun hv (α, j)
      change (raw A R).mulVec (extend q M N v) (α, j) = 0 at hh
      rw [raw_apply] at hh
      simpa only [R, f, padded_mulVec_low M N _ _ (hf _),
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hh
    have hzero := rectangular_kernel_zero w B M N q e hw hN hMN hq he points hp A X hX f hf hker
    have hext : extend q M N v = 0 := by
      funext ⟨α, j⟩
      exact congrFun (congrFun hzero α) j
    apply extend_injective q M N (by omega)
    simpa only [map_zero] using hext
  let E := LinearMap.toMatrix' (extend (K := K) q M N)
  have hE : E.mulVecLin = extend q M N := Matrix.toLin'_toMatrix' _
  have hr : (raw A R * E).rank = q * N := by
    rw [Matrix.rank, Matrix.mulVecLin_mul, hE]
    rw [LinearMap.finrank_range_of_inj hi]
    simp
  exact hr ▸ Matrix.rank_mul_le_left (raw A R) E

/-- When `1 ≤ q ≤ B`, `M = N + 2 * w ^ 3 * B`, and `B * (2 * w ^ 3 * B) < M`, the rank threshold
satisfies `(q - 1) * M < q * N`. -/
lemma numeric_gap (w B M N q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hMN : M = N + 2 * w ^ 3 * B) (hM : B * (2 * w ^ 3 * B) < M) : (q - 1) * M < q * N := by
  have hh : q * (2 * w ^ 3 * B) < M := (Nat.mul_le_mul_right _ hqB).trans_lt hM
  have hq' : q - 1 + 1 = q := by omega
  have heq : q * M = (q - 1) * M + M := by
    calc
      _ = (q - 1 + 1) * M := by rw [hq']
      _ = _ := by ring
  have heq' : q * N + q * (2 * w ^ 3 * B) = (q - 1) * M + M := by
    calc
      _ = q * M := by rw [hMN]; ring
      _ = _ := heq
  omega

end
end Rational.PaddedRank

namespace Rational.TestPolynomial
open Polynomial Matrix
open LaurentReduction
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E]

private lemma map_taylor_coeff (φ : K →+* E) (a : K) (j r : ℕ) :
    φ (((X + C a) ^ j : K[X]).coeff r) = (((X + C (φ a)) ^ j : E[X]).coeff r) := by
  rw [← Polynomial.coeff_map]
  simp

private lemma full_map (φ : K →+* E) (M : ℕ) (a : K) (i j : Fin M) :
    (full M a i j).map φ = full M (φ a) i j := by
  unfold full
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul]
  rw [map_taylor_coeff φ (-a), map_taylor_coeff φ a, map_neg]

private lemma padded_map (φ : K →+* E) (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).map φ = padded M N (φ a) i j := by
  by_cases hj : j.val < N <;> simp [padded, hj, full_map]

/-- Evaluating `padded M N a i j` along `HahnSeries.C.comp φ` at `HahnSeries.single 1 1` equals
`embed (padded M N (φ a) i j)`. -/
lemma eval₂_padded (φ : K →+* E) (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).eval₂ (HahnSeries.C.comp φ) (HahnSeries.single 1 1) =
      embed (padded M N (φ a) i j) := by
  rw [← padded_map φ M N a i j]
  change (padded M N a i j).eval₂ ((HahnSeries.C : E →+* F E).comp φ)
      (HahnSeries.single (1 : ℤ) 1) =
    ((padded M N a i j).map φ).eval₂ HahnSeries.C (HahnSeries.single 1 1)
  rw [Polynomial.eval₂_map]

end
end Rational.TestPolynomial

end Cslib.Circuits
