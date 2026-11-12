/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ROABP
public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.ABP

/-!
# Hitting sets of matrices for non-commutative branching programs

A non-commutative polynomial is tested for zero on tuples of matrices: a tuple
`P : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) F` hits `f` if `FreeAlgebra.lift F P f ≠ 0`.
Over a field of characteristic zero there is an explicit set of such tuples that hits every
nonzero polynomial computed by a homogeneous layered non-commutative branching program of degree
`d` and width at most `W` in `n` variables (`exists_mem_noncommABPHittingSet_lift_ne_zero`).

## Proof

This is the reduction of Forbes and Shpilka [ForbesShpilka2013] to read-once oblivious programs.
For `a : Fin d → F` let the variable `x` be the matrix with entry `a k ^ x` at `(k, k + 1)` and
zero elsewhere (`superdiagPoint`). A word `x₀ ⋯ x_{d-1}` of length `d` is then the matrix whose
only nonzero entry, at `(0, d)`, is `∏ₖ a k ^ xₖ`, so the entry `(0, d)` of the image of a
polynomial `f = ∑ c_x x₀ ⋯ x_{d-1}` that is homogeneous of degree `d` is the value at `a` of the
commutative polynomial `g = ∑ c_x ∏ₖ Yₖ ^ xₖ`, which has the same coefficients. If `f` is computed
by a branching program of width at most `W` then `g` is computed by the read-once oblivious
program of width `W` that reads `Y₀, …, Y_{d-1}` in this order and whose `k`-th layer is
`∑ₓ Aₖₓ Yₖ ^ x`, with `Aₖₓ` the matrix of the coefficients of `x` on the edges of layer `k`; its
layers have degree at most `n - 1`. So a hitting set for these programs gives the tuples.

The hitting set for read-once oblivious programs used here is `roabpHittingSet`, the library's
adaptation of Agrawal, Gurjar, Korwar and Saxena [AgrawalGurjarKorwarSaxena2015], not the
generator of Forbes and Shpilka. That adaptation changes the weight family and the way the
levels are combined, so its size expression is not the paper's, and the size bound here
(`card_noncommABPHittingSet_le` with `card_roabpHittingSet_le`) is neither that of
[AgrawalGurjarKorwarSaxena2015] nor that of [ForbesShpilka2013, Corollary 4.7].

## Main definitions

* `superdiagPoint`: the tuple of matrices of a point `a : Fin d → F`.
* `noncommABPHittingSet`: the tuples of the points of `roabpHittingSet F d W (n - 1)`.

## Main results

* `exists_mem_noncommABPHittingSet_lift_ne_zero`: the set hits every nonzero polynomial computed
  by a non-commutative branching program of degree `d` and width at most `W`.
* `card_noncommABPHittingSet_le`: the set is no larger than `roabpHittingSet F d W (n - 1)`.

## References

* [M. A. Forbes, A. Shpilka, *Quasipolynomial-time identity testing of non-commutative and
  read-once oblivious algebraic branching programs*][ForbesShpilka2013] (arXiv:1209.2408v2):
  §1.1, pp. 2–3 (set-multilinear and univariate encodings); §4, Construction 4.1 and Lemma 4.2
  (p. 22), Lemma 4.3 (p. 23), Lemma 4.5 and Theorem 4.6 (p. 24), specialized to homogeneous
  layered programs. Their Corollary 4.7 (p. 25) uses a different generator and is not
  formalized
* [M. Agrawal, R. Gurjar, A. Korwar, N. Saxena, *Hitting-sets for ROABP and sum of
  set-multilinear circuits*][AgrawalGurjarKorwarSaxena2015], Theorem 1, in the adapted form of
  `isHittingSet_roabpHittingSet`
-/

public section

open scoped Polynomial

namespace Cslib.Circuits.Arithmetic

open FreeAlgebra

variable {F : Type*} [Field F] {n d : ℕ}

namespace NoncommABP

variable (A : NoncommABP F (Fin n) d) (W : ℕ)

/-- The coefficients of `x` on the edges of layer `k`, padded with zeros to a `W × W` matrix. -/
private def layer (k : ℕ) (x : Fin n) : Matrix (Fin W) (Fin W) F :=
  Matrix.of fun i j => if h : (i : ℕ) < A.width k ∧ (j : ℕ) < A.width (k + 1) then
    A.weight k x ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- A vector indexed by the vertices of layer `k`, padded with zeros to length `W`. -/
private def pad (k : ℕ) (f : Fin (A.width k) → F) : Fin W → F :=
  fun i => if h : (i : ℕ) < A.width k then f ⟨i, h⟩ else 0

private theorem sum_dite_mul {m : ℕ} (hm : m ≤ W) (f : Fin m → F) (g : Fin W → F) :
    ∑ i : Fin W, (if h : (i : ℕ) < m then f ⟨i, h⟩ else 0) * g i =
      ∑ i : Fin m, f i * g (Fin.castLE hm i) :=
  (Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _
    (fun i hi => by
      have : ¬ (i : ℕ) < m := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [this])
    (fun i => by simp)).symm

variable {W} in
/-- One layer: if `φ'` of a polynomial of layer `k` times `x` is `φ` of the polynomial times
`c x`, then the values of `φ'` on layer `k + 1` are those of `φ` on layer `k` times the matrix
`∑ x, c x • layer k x`. -/
private theorem pad_succ {k : ℕ} (hk : A.width k ≤ W) (φ φ' : FreeAlgebra F (Fin n) →ₗ[F] F)
    (c : Fin n → F) (h : ∀ i x, φ' (A.pre k i * ι F x) = φ (A.pre k i) * c x) :
    A.pad W (k + 1) (fun j => φ' (A.pre (k + 1) j)) =
      Matrix.vecMul (A.pad W k fun i => φ (A.pre k i)) (∑ x, c x • A.layer W k x) := by
  ext j
  change (if h : (j : ℕ) < A.width (k + 1) then φ' (A.pre (k + 1) ⟨j, h⟩) else 0) =
    ∑ i : Fin W, (if h : (i : ℕ) < A.width k then φ (A.pre k ⟨i, h⟩) else 0) *
      (∑ x, c x • A.layer W k x) i j
  rw [sum_dite_mul W hk fun i => φ (A.pre k i)]
  by_cases hj : (j : ℕ) < A.width (k + 1)
  · simp only [hj, layer, pre_succ, edge, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, h,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, Fin.val_castLE, Fin.is_lt, and_self,
      dite_true, Fin.eta, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  · simp [hj, layer, Matrix.sum_apply]

/-- **The shared computation.** Linear functionals `φ k` that are multiplicative along the
layers, with factor `c k x` for the variable `x` after layer `k`, send the computed polynomial to
an entry of the product of the matrices `∑ x, c k x • layer k x`. -/
private theorem apply_polynomial [NeZero W] (hW : ∀ k ≤ d, A.width k ≤ W)
    (φ : ℕ → FreeAlgebra F (Fin n) →ₗ[F] F) (c : ℕ → Fin n → F) (h0 : φ 0 1 = 1)
    (hφ : ∀ k < d, ∀ i x, φ (k + 1) (A.pre k i * ι F x) = φ k (A.pre k i) * c k x) :
    φ d A.polynomial =
      ((List.range d).map fun k => ∑ x, c k x • A.layer W k x).prod 0 0 := by
  have key : ∀ k ≤ d, A.pad W k (fun j => φ k (A.pre k j)) =
      Matrix.vecMul (Pi.single 0 1)
        ((List.range k).map fun k => ∑ x, c k x • A.layer W k x).prod := by
    intro k
    induction k with
    | zero =>
      intro _
      ext i
      simp [pad, pre_zero, h0, A.width_zero, Pi.single_apply, Fin.val_eq_zero_iff]
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ← Matrix.vecMul_vecMul, ← ih (by omega)]
      exact A.pad_succ (hW k (by omega)) _ _ _ (hφ k hk)
  have hd : (0 : ℕ) < A.width d := by simp [A.width_deg]
  have hsum : A.polynomial = A.pre d ⟨0, hd⟩ :=
    Fintype.sum_eq_single _ fun j hj =>
      absurd (Fin.ext (Nat.lt_one_iff.1 (j.2.trans_eq A.width_deg))) hj
  rw [hsum]
  simpa [pad, hd] using congrFun (key d le_rfl) 0

private theorem range_map_eq {α : Type*} (N : ℕ → α) (N' : Fin d → α)
    (h : ∀ k : Fin d, N k = N' k) : (List.range d).map N = (List.finRange d).map N' := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun k _ => h k

/-- The coefficient of a word of length `d` in the computed polynomial is an entry of the product
of the padded coefficient matrices of its letters. -/
private theorem coeff_polynomial [NeZero W] (hW : ∀ k ≤ d, A.width k ≤ W) (u : Fin d → Fin n) :
    coeff (FreeMonoid.ofFn u) A.polynomial =
      ((List.finRange d).map fun k : Fin d => A.layer W k (u k)).prod 0 0 := by
  classical
  have h := A.apply_polynomial W hW
    (fun k => coeff (FreeMonoid.ofList ((List.ofFn u).take k)))
    (fun k x => if h : k < d then (if x = u ⟨k, h⟩ then 1 else 0) else 0)
    (by simp [coeff_one]) fun k hk i x => ?_
  · rw [range_map_eq _ (fun k : Fin d => A.layer W k (u k)) fun k => by simp] at h
    have ht : (List.ofFn u).take d = List.ofFn u := List.take_of_length_le (by simp)
    rw [← h]
    change coeff (FreeMonoid.ofList (List.ofFn u)) _ =
      coeff (FreeMonoid.ofList ((List.ofFn u).take d)) _
    rw [ht]
  · have hlen : (FreeMonoid.ofList ((List.ofFn u).take k)).length = k := by
      simp [FreeMonoid.length, hk.le]
    rw [List.take_succ_eq_append_getElem (by simpa using hk), FreeMonoid.ofList_append,
      FreeMonoid.ofList_singleton, coeff_mul_mul_of_isHomogeneous _ _ _
        (by rw [hlen]; exact A.isHomogeneous_pre k i), coeff_ι]
    simp [hk, Finsupp.single_apply, FreeMonoid.of_injective.eq_iff]

end NoncommABP

/-- For `a : Fin d → F`, the matrix of the variable `x`: entry `a k ^ x` at `(k, k + 1)`, zero
elsewhere. -/
def superdiagPoint (a : Fin d → F) (x : Fin n) : Matrix (Fin (d + 1)) (Fin (d + 1)) F :=
  Matrix.of fun i j => if h : (j : ℕ) = i + 1 then a ⟨i, by omega⟩ ^ (x : ℕ) else 0

namespace NoncommABP

variable (A : NoncommABP F (Fin n) d) (W : ℕ)

/-- The entry `(0, d)` of the computed polynomial at the matrices of a point `a` is an entry of
the product of the matrices `∑ x, a k ^ x • layer k x`. -/
private theorem lift_superdiagPoint_polynomial [NeZero W] (hW : ∀ k ≤ d, A.width k ≤ W)
    (a : Fin d → F) :
    lift F (superdiagPoint a) A.polynomial 0 (Fin.last d) =
      ((List.finRange d).map fun k => ∑ x : Fin n, a k ^ (x : ℕ) • A.layer W k x).prod 0 0 := by
  have h := A.apply_polynomial W hW
    (fun k => if h : k ≤ d then
      (Matrix.entryLinearMap F F 0 ⟨k, Nat.lt_succ_of_le h⟩) ∘ₗ
        (lift F (superdiagPoint (n := n) a)).toLinearMap else 0)
    (fun k x => if h : k < d then a ⟨k, h⟩ ^ (x : ℕ) else 0) (by simp) fun k hk i x => ?_
  · rw [range_map_eq _ (fun k => ∑ x : Fin n, a k ^ (x : ℕ) • A.layer W k x) fun k => by simp]
      at h
    simpa [Fin.last] using h
  · have hk' : k + 1 ≤ d := hk
    simp only [hk.le, hk', hk, dite_true, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Matrix.entryLinearMap_apply, map_mul, lift_ι_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single ⟨k, by omega⟩]
    · simp [superdiagPoint]
    · intro c _ hc
      have : k ≠ (c : ℕ) := fun h => hc (Fin.ext h.symm)
      simp [superdiagPoint, this]
    · simp

/-- The layers of the read-once oblivious program of a non-commutative program: the `k`-th is
`∑ x, layer k x * X ^ x`. -/
private noncomputable def uniLayer (k : Fin d) : Matrix (Fin W) (Fin W) F[X] :=
  Matrix.of fun i j => ∑ x : Fin n, Polynomial.C (A.layer W k x i j) * Polynomial.X ^ (x : ℕ)

private theorem natDegree_uniLayer_le (k : Fin d) (i j : Fin W) :
    (A.uniLayer W k i j).natDegree ≤ n - 1 := by
  rw [uniLayer, Matrix.of_apply]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := x.2; omega)

end NoncommABP

open scoped Classical in
/-- The hitting set of matrix tuples for non-commutative branching programs of degree `d` and
width at most `W` in `n` variables: the tuples `superdiagPoint a` for the points `a` of the
hitting set `roabpHittingSet F d W (n - 1)` for read-once oblivious programs in `d` variables,
of width `W`, with layers of degree at most `n - 1`. -/
noncomputable def noncommABPHittingSet (F : Type*) [Field F] (n d W : ℕ) :
    Finset (Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) F) :=
  (roabpHittingSet F d W (n - 1)).image superdiagPoint

private theorem superdiagPoint_mem {W : ℕ} {a : Fin d → F}
    (ha : a ∈ roabpHittingSet F d W (n - 1)) :
    superdiagPoint a ∈ noncommABPHittingSet F n d W := by
  classical
  unfold noncommABPHittingSet
  exact Finset.mem_image.2 ⟨a, ha, rfl⟩

/-- **Hitting sets of matrices for non-commutative branching programs** (the reduction of
[ForbesShpilka2013] to read-once oblivious programs, with the hitting set of
[AgrawalGurjarKorwarSaxena2015]). Over a field of characteristic zero, a nonzero polynomial
computed by a homogeneous layered non-commutative branching program of degree `d` whose layers
`0, …, d` have at most `W` vertices is nonzero at a tuple of `(d + 1) × (d + 1)` matrices of
`noncommABPHittingSet F n d W`. -/
theorem exists_mem_noncommABPHittingSet_lift_ne_zero [CharZero F] {W : ℕ}
    (A : NoncommABP F (Fin n) d) (hW : ∀ k ≤ d, A.width k ≤ W) (hA : A.polynomial ≠ 0) :
    ∃ P ∈ noncommABPHittingSet F n d W, FreeAlgebra.lift F P A.polynomial ≠ 0 := by
  classical
  have : NeZero W := ⟨fun h => by
    have h0 := hW 0 (Nat.zero_le d)
    rw [A.width_zero, h] at h0
    exact absurd h0 (by decide)⟩
  have hg : roabpProd (A.uniLayer W) (List.finRange d) 0 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_coeff_ne_zero hA
    obtain ⟨u, rfl⟩ := FreeMonoid.exists_ofFn_eq w (A.isHomogeneous_polynomial w hw)
    intro h0
    refine hw ?_
    have hc := coeff_roabpProd (A.uniLayer W) (List.nodup_finRange d)
      (Finsupp.equivFunOnFinite.symm fun k => (u k : ℕ))
      (fun i hi => absurd (List.mem_finRange i) hi) 0 0
    have hl : ((List.finRange d).map fun k : Fin d => A.layer W k (u k)) =
        (List.finRange d).map fun k => layerCoeff (A.uniLayer W) k
          (Finsupp.equivFunOnFinite.symm (fun k => (u k : ℕ)) k) :=
      List.map_congr_left fun k _ => by
        ext i j
        simp [layerCoeff, NoncommABP.uniLayer, Polynomial.coeff_X_pow, Fin.val_inj]
    rw [A.coeff_polynomial W hW u, hl, ← hc, h0]
    simp
  have hR : IsROABP W (n - 1) (roabpProd (A.uniLayer W) (List.finRange d) 0 0) :=
    ⟨List.finRange d, A.uniLayer W, 0, 0, List.nodup_finRange d,
      A.natDegree_uniLayer_le W, rfl⟩
  obtain ⟨a, ha, hne⟩ := isHittingSet_roabpHittingSet (F := F) _ hR hg
  refine ⟨superdiagPoint a, superdiagPoint_mem ha, fun h0 => hne ?_⟩
  have hev : ∀ k : Fin d, (A.uniLayer W k).map (Polynomial.eval (a k)) =
      ∑ x : Fin n, a k ^ (x : ℕ) • A.layer W k x := fun k => by
    ext i j
    simp only [NoncommABP.uniLayer, Matrix.map_apply, Matrix.of_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [eval_roabpProd]
  simp only [hev]
  rw [← A.lift_superdiagPoint_polynomial W hW a, h0]
  exact Matrix.zero_apply _ _

/-- The hitting set for non-commutative branching programs is no larger than the hitting set for
read-once oblivious programs it is built from, which `card_roabpHittingSet_le` bounds by
`(⌈lg d⌉ + 1) p ^ ⌈lg d⌉ (d (n - 1) (B + p) ^ ⌈lg d⌉ + 1)`, with `p = roabpPrime d W (n - 1)`,
which is at most `2 (2 d² W⁸ + (n - 1) + 1)`, and `B = d (n - 1) p + 1`: quasipolynomial in
`n`, `d` and `W`. This is the bound of the library's adaptation of
[AgrawalGurjarKorwarSaxena2015] (`roabpHittingSet`), whose size expression is not the paper's;
it is not the bound of [ForbesShpilka2013, Corollary 4.7] either. -/
theorem card_noncommABPHittingSet_le (n d W : ℕ) :
    (noncommABPHittingSet F n d W).card ≤ (roabpHittingSet F d W (n - 1)).card := by
  classical
  unfold noncommABPHittingSet
  exact Finset.card_image_le

end Cslib.Circuits.Arithmetic
