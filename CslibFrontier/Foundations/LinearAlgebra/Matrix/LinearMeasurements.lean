/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.FiniteMagnitude
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Row-basis selection, the `(2n + 1)^r` measurement bound, and linear-measurement fibre identities

For any finite matrix `M : Matrix m col K` over a field, `Matrix.selectRowBasis M` extracts a
`Matrix.RowBasisSelection M` consisting of `r = M.rank` row indices whose rows form a basis of the
row space of `M`, together with a linear reconstruction map
`reconstruct : (Fin M.rank → K) →ₗ[K] (m → K)` recovering all row measurements `M *ᵥ x` from the
`r` selected measurements `(M.submatrix rowIdx id) *ᵥ x`
(`Matrix.RowBasisSelection.mulVec_eq_iff`).

When `M`'s entries lie in `{-1, 0, 1}` (`Matrix.IsUnitTrinary`), any `r` selected row measurements
of an `n`-bit vector (read either as `0/1` values via `Cslib.BitString.bitVal` or as `±1` signs
`(-1) ^ (x j).toNat`, or more generally any bounded-magnitude integer lift `|z j| ≤ 1`) take values
in `[-n, n]^r` and therefore attain at most `(2 * n + 1) ^ r` distinct vectors
(`Matrix.card_image_mulVec_le_two_mul_add_one_pow`,
`Matrix.card_image_submatrix_mulVec_bitVal_le`, `Matrix.card_image_submatrix_mulVec_sign_le`).
Combining row-basis reconstruction with this range bound shows that even the full `m`-row
measurement map `x ↦ M *ᵥ x` over any field (such as `ℚ`) attains at most `(2 * n + 1) ^ M.rank`
distinct values on `n`-bit vectors (`Matrix.card_image_mulVec_bitVal_le_pow_rank`,
`Matrix.card_image_mulVec_sign_le_pow_rank`), forcing a nonempty fibre of size at least
`⌈#X / (2 * n + 1) ^ M.rank⌉` by pigeonhole (`Matrix.exists_le_card_measurementFiber_bitVal`).

Finally, this module develops general fibre-partition and summation identities for arbitrary linear
measurements:
* Setwise disjoint partition into `Matrix.measurementFiber` over `Matrix.measurementValues`
  (`Matrix.biUnion_measurementFiber`, `Matrix.pairwiseDisjoint_measurementFiber`,
  `Matrix.sum_card_measurementFiber`);
* Factored fibre summation (`Matrix.sum_mul_comp_mulVec`) and compressed summation over the at most
  `(2 * n + 1) ^ M.rank` fibres of a selected row basis
  (`Matrix.RowBasisSelection.sum_mul_comp_mulVec`);
* Kernel-coset translation for full-space linear measurements
  (`Matrix.sum_filter_mulVec_eq_sum_ker`, `Matrix.card_filter_mulVec_eq_card_ker`);
* Fourier / character fibre-sum identities for finite abelian group homomorphisms
  (`AddChar.card_mul_sum_filter_eq`) and `𝔽₂` linear measurements
  (`Matrix.two_pow_mul_sum_filter_mulVec_zmodTwo`).

## Main definitions

* `Matrix.RowBasisSelection`, `Matrix.selectRowBasis`: row-space basis selection and linear
  measurement reconstruction.
* `Matrix.IsUnitTrinary`: matrices with entries in `{-1, 0, 1}`.
* `Matrix.measurementValues`, `Matrix.measurementFiber`: attained linear-measurement vectors and
  their fibres.

## Main results

* `Matrix.RowBasisSelection.rank_submatrix_eq`, `Matrix.RowBasisSelection.mulVec_eq_iff`:
  `M.rank` selected rows preserve rank and determine `M *ᵥ x` uniquely.
* `Matrix.card_image_mulVec_le_two_mul_add_one_pow`,
  `Matrix.card_image_submatrix_mulVec_bitVal_le`, `Matrix.card_image_submatrix_mulVec_sign_le`,
  `Matrix.card_image_mulVec_bitVal_le_pow_rank`, `Matrix.card_image_mulVec_sign_le_pow_rank`,
  `Matrix.exists_le_card_measurementFiber_bitVal`: `(2 * n + 1) ^ r` and `(2 * n + 1) ^ M.rank`
  value bounds and large-fibre existence.
* `Matrix.biUnion_measurementFiber`, `Matrix.pairwiseDisjoint_measurementFiber`,
  `Matrix.sum_mul_comp_mulVec`, `Matrix.RowBasisSelection.sum_mul_comp_mulVec`,
  `Matrix.sum_filter_mulVec_eq_sum_ker`, `AddChar.card_mul_sum_filter_eq`,
  `Matrix.two_pow_mul_sum_filter_mulVec_zmodTwo`: fibre partition and summation identities.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix

/-! ### Selecting a row-space basis from the rows of a matrix -/

section RowBasis

/-- A row-space basis extracted from the rows of `M : Matrix m col K`, packaging `M.rank` injective
row indices, linear independence and row-span equality, and a linear map reconstructing `M *ᵥ x`
from the `M.rank` selected row measurements. -/
structure RowBasisSelection {m col K : Type*} [Field K] [Fintype col] (M : Matrix m col K) where
  /-- Indices of the `M.rank` selected rows. -/
  rowIdx : Fin M.rank → m
  /-- Selected row indices are distinct. -/
  rowIdx_injective : Function.Injective rowIdx
  /-- Selected rows of `M` are linearly independent. -/
  linearIndependent_rows : LinearIndependent K (fun k => M.row (rowIdx k))
  /-- Selected rows span the full row space of `M`. -/
  span_eq : Submodule.span K (Set.range fun k => M.row (rowIdx k)) =
    Submodule.span K (Set.range M.row)
  /-- Linear reconstruction map from the selected row measurements to all `m` row measurements. -/
  reconstruct : (Fin M.rank → K) →ₗ[K] (m → K)
  /-- Applying `reconstruct` to `(M.submatrix rowIdx id) *ᵥ x` recovers `M *ᵥ x`. -/
  reconstruct_submatrix_mulVec : ∀ x : col → K,
    reconstruct ((M.submatrix rowIdx id) *ᵥ x) = M *ᵥ x

/-- Select a `RowBasisSelection` from the rows of any finite matrix `M` over a field `K` (including
`K = ℚ`). -/
noncomputable def selectRowBasis {m col K : Type*} [Field K] [Finite m] [Fintype col]
    (M : Matrix m col K) : RowBasisSelection M := by
  classical
  let hex := exists_linearIndependent' K M.row
  let κ := hex.choose
  let a : κ → m := hex.choose_spec.choose
  have ha : Function.Injective a := hex.choose_spec.choose_spec.1
  have hspan : Submodule.span K (Set.range (M.row ∘ a)) = Submodule.span K (Set.range M.row) :=
    hex.choose_spec.choose_spec.2.1
  have hli : LinearIndependent K (M.row ∘ a) := hex.choose_spec.choose_spec.2.2
  have : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = M.rank := by
    rw [rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let e : Fin M.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let idx : Fin M.rank → m := a ∘ e
  have hli_idx : LinearIndependent K (fun k => M.row (idx k)) :=
    hli.comp e e.injective
  have hrange : (Set.range fun k => M.row (idx k)) = Set.range (M.row ∘ a) := by
    ext v
    simp only [Set.mem_range, Function.comp_apply, idx]
    exact ⟨fun ⟨k, hk⟩ => ⟨e k, hk⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  have hspan_idx : Submodule.span K (Set.range fun k => M.row (idx k)) =
      Submodule.span K (Set.range M.row) := by
    rw [hrange, hspan]
  let b := Module.Basis.span hli_idx
  let rowMem (i : m) : Submodule.span K (Set.range fun k => M.row (idx k)) :=
    ⟨M.row i, hspan_idx.symm ▸ Submodule.subset_span ⟨i, rfl⟩⟩
  let C : Matrix m (Fin M.rank) K := of fun i k => b.repr (rowMem i) k
  refine
    { rowIdx := idx
      rowIdx_injective := ha.comp e.injective
      linearIndependent_rows := hli_idx
      span_eq := hspan_idx
      reconstruct := C.mulVecLin
      reconstruct_submatrix_mulVec := fun x => ?_ }
  funext i
  have hb : ∀ k : Fin M.rank, (b k : col → K) = M.row (idx k) := fun k => by
    simp [b, Module.Basis.span_apply]
  have hrepr := congrArg (fun v : Submodule.span K (Set.range fun k => M.row (idx k)) =>
      (v : col → K)) (b.sum_repr (rowMem i))
  simp only [Submodule.coe_sum, Submodule.coe_smul, hb] at hrepr
  have hi : ∀ j : col, (∑ k : Fin M.rank, b.repr (rowMem i) k * M (idx k) j) = M i j := by
    intro j
    simpa [rowMem, Pi.smul_apply, smul_eq_mul] using congrFun hrepr j
  calc (C.mulVecLin ((M.submatrix idx id) *ᵥ x)) i
      = ∑ k : Fin M.rank, b.repr (rowMem i) k * ∑ j : col, M (idx k) j * x j := by
          simp [C, mulVec, dotProduct]
    _ = ∑ j : col, (∑ k : Fin M.rank, b.repr (rowMem i) k * M (idx k) j) * x j := by
          simp_rw [mul_sum, sum_mul, mul_assoc]
          exact sum_comm
    _ = (M *ᵥ x) i := by
          simp only [hi, mulVec, dotProduct]

/-- The selected `M.rank`-row submatrix has the same rank `M.rank` as `M`. -/
@[simp]
theorem RowBasisSelection.rank_submatrix_eq {m col K : Type*} [Field K] [Fintype col]
    {M : Matrix m col K} (B : RowBasisSelection M) :
    (M.submatrix B.rowIdx id).rank = M.rank := by
  have hli : LinearIndependent K (M.submatrix B.rowIdx id).row := B.linearIndependent_rows
  simpa using hli.rank_matrix

/-- Two vectors have identical full measurements `M *ᵥ x = M *ᵥ y` if and only if they agree on the
`M.rank` selected basis rows `(M.submatrix B.rowIdx id) *ᵥ x = (M.submatrix B.rowIdx id) *ᵥ y`. -/
theorem RowBasisSelection.mulVec_eq_iff {m col K : Type*} [Field K] [Fintype col]
    {M : Matrix m col K} (B : RowBasisSelection M) (x y : col → K) :
    M *ᵥ x = M *ᵥ y ↔
      (M.submatrix B.rowIdx id) *ᵥ x = (M.submatrix B.rowIdx id) *ᵥ y := by
  constructor
  · intro h
    funext k
    exact congrFun h (B.rowIdx k)
  · intro h
    rw [← B.reconstruct_submatrix_mulVec x, ← B.reconstruct_submatrix_mulVec y, h]

end RowBasis

/-! ### Entries in `{-1, 0, 1}` and the `(2n + 1)^r` measurement value bound -/

section ValueBound

/-- Predicate asserting that every entry of `M` belongs to `{-1, 0, 1}`. -/
@[expose] def IsUnitTrinary {m col R : Type*} [Ring R] (M : Matrix m col R) : Prop :=
  ∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1

/-- Over `ℤ`, entries lie in `{-1, 0, 1}` if and only if their absolute values are at most `1`. -/
theorem isUnitTrinary_int_iff {m col : Type*} (A : Matrix m col ℤ) :
    IsUnitTrinary A ↔ ∀ i j, |A i j| ≤ 1 := by
  constructor
  · intro h i j
    rcases h i j with h1 | h0 | h1' <;> simp [*]
  · intro h i j
    have hij := h i j
    rw [abs_le] at hij
    omega

/-- Selecting rows preserves `IsUnitTrinary`. -/
theorem IsUnitTrinary.submatrix {m' col' m col R : Type*} [Ring R] {M : Matrix m col R}
    (hM : IsUnitTrinary M) (r : m' → m) (c : col' → col) :
    IsUnitTrinary (M.submatrix r c) :=
  fun i j => hM (r i) (c j)

/-- **Master `(2n + 1)^r` value bound**: if `M : Matrix (Fin r) (Fin n) R` has entries in
`{-1, 0, 1}` and every vector `φ x` (`x ∈ X`) lifts to an integer vector of `ℓ_∞`-norm at most `1`,
then `x ↦ M *ᵥ φ x` takes at most `(2 * n + 1) ^ r` distinct values on `X`. -/
theorem card_image_mulVec_le_two_mul_add_one_pow {α R : Type*} [Ring R] [DecidableEq R]
    {r n : ℕ} (M : Matrix (Fin r) (Fin n) R) (hM : IsUnitTrinary M)
    (X : Finset α) (φ : α → Fin n → R)
    (hφ : ∀ x ∈ X, ∃ z : Fin n → ℤ, (∀ j, (z j : R) = φ x j) ∧ ∀ j, |z j| ≤ 1) :
    #(X.image fun x => M *ᵥ φ x) ≤ (2 * n + 1) ^ r := by
  classical
  let A : Matrix (Fin r) (Fin n) ℤ := of fun i j =>
    if M i j = 1 then 1 else if M i j = -1 then -1 else 0
  have hA_cast : ∀ i j, (A i j : R) = M i j := by
    intro i j
    dsimp only [A, of_apply]
    by_cases h1 : M i j = 1
    · rw [ite_eq_left h1, h1]
      simp
    · rw [ite_eq_right h1]
      by_cases hm1 : M i j = -1
      · rw [ite_eq_left hm1, hm1]
        simp
      · rw [ite_eq_right hm1]
        rcases hM i j with h | h | h
        · exact absurd h hm1
        · simp [h]
        · exact absurd h h1
  have hA_abs : ∀ i j, |A i j| ≤ 1 := by
    intro i j
    dsimp only [A, of_apply]
    split_ifs <;> simp
  let box : Finset (Fin r → ℤ) := Fintype.piFinset fun _ : Fin r => Icc (-(n : ℤ)) (n : ℤ)
  have hsub : (X.image fun x => M *ᵥ φ x) ⊆ box.image (fun w i => (w i : R)) := by
    intro y hy
    rcases mem_image.mp hy with ⟨x, hx, rfl⟩
    obtain ⟨z, hz_cast, hz_abs⟩ := hφ x hx
    refine mem_image.mpr ⟨A *ᵥ z, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [mem_Icc, ← abs_le]
      have hb : |∑ j : Fin n, A i j * z j| ≤ (univ : Finset (Fin n)).card * (1 : ℤ) :=
        Finset.abs_sum_mul_le univ (fun j _ => hA_abs i j) (fun j _ => hz_abs j)
      simpa [mulVec, dotProduct] using hb
    · funext i
      simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hA_cast, hz_cast]
  calc #(X.image fun x => M *ᵥ φ x)
      ≤ #(box.image fun w i => (w i : R)) := card_le_card hsub
    _ ≤ #box := card_image_le
    _ = ∏ _i : Fin r, #(Icc (-(n : ℤ)) (n : ℤ)) := Fintype.card_piFinset _
    _ = (2 * n + 1) ^ r := by
        have hIcc : #(Icc (-(n : ℤ)) (n : ℤ)) = 2 * n + 1 := by
          rw [Int.card_Icc]
          omega
        simp [hIcc]

/-- **`(2n + 1)^r` value bound for `r` selected `{0, 1}`-bit measurements**: for any `M` with
entries in `{-1, 0, 1}` and any `r` selected rows `sel : Fin r → m`, the `r` measurements on
`X ⊆ Fin n → Bool` (read via `Cslib.BitString.bitVal R`) take at most `(2 * n + 1) ^ r` values. -/
theorem card_image_submatrix_mulVec_bitVal_le {m R : Type*} [CommRing R] [DecidableEq R]
    {r n : ℕ} (M : Matrix m (Fin n) R) (hM : IsUnitTrinary M)
    (sel : Fin r → m) (X : Finset (Fin n → Bool)) :
    #(X.image fun x => (M.submatrix sel id) *ᵥ fun j => Cslib.BitString.bitVal R (x j)) ≤
      (2 * n + 1) ^ r := by
  refine card_image_mulVec_le_two_mul_add_one_pow (M.submatrix sel id) (hM.submatrix sel id) X _ ?_
  intro x _
  refine ⟨fun j => Cslib.BitString.bitVal ℤ (x j), fun j => ?_, fun j => ?_⟩
  · cases h : x j <;> simp [h, Cslib.BitString.bitVal]
  · cases h : x j <;> simp [h, Cslib.BitString.bitVal]

/-- **`(2n + 1)^r` value bound for `r` selected `±1`-sign measurements**: for any `M` with entries
in `{-1, 0, 1}` and `sel : Fin r → m`, the `r` signed measurements on `X ⊆ Fin n → Bool` take at
most `(2 * n + 1) ^ r` values. -/
theorem card_image_submatrix_mulVec_sign_le {m R : Type*} [CommRing R] [DecidableEq R]
    {r n : ℕ} (M : Matrix m (Fin n) R) (hM : IsUnitTrinary M)
    (sel : Fin r → m) (X : Finset (Fin n → Bool)) :
    #(X.image fun x => (M.submatrix sel id) *ᵥ fun j => (-1 : R) ^ (x j).toNat) ≤
      (2 * n + 1) ^ r := by
  refine card_image_mulVec_le_two_mul_add_one_pow (M.submatrix sel id) (hM.submatrix sel id) X _ ?_
  intro x _
  refine ⟨fun j => (-1 : ℤ) ^ (x j).toNat, fun j => ?_, fun j => ?_⟩
  · cases h : x j <;> simp [h]
  · cases h : x j <;> simp [h]

/-- **General rank-compressed `(2n + 1)^{rank M}` bound** over any field `K` (including `K = ℚ`):
if `M : Matrix m (Fin n) K` has entries in `{-1, 0, 1}` and `φ x` (`x ∈ X`) lifts to integer
vectors of `ℓ_∞`-norm at most `1`, then `x ↦ M *ᵥ φ x` takes at most `(2 * n + 1) ^ M.rank`
distinct values on `X`. -/
theorem card_image_mulVec_le_pow_rank {α m K : Type*} [Field K] [Finite m]
    [DecidableEq (m → K)] {n : ℕ} (M : Matrix m (Fin n) K) (hM : IsUnitTrinary M)
    (X : Finset α) (φ : α → Fin n → K)
    (hφ : ∀ x ∈ X, ∃ z : Fin n → ℤ, (∀ j, (z j : K) = φ x j) ∧ ∀ j, |z j| ≤ 1) :
    #(X.image fun x => M *ᵥ φ x) ≤ (2 * n + 1) ^ M.rank := by
  classical
  let B := selectRowBasis M
  let red := fun x : α => (M.submatrix B.rowIdx id) *ᵥ φ x
  have himg : (X.image fun x => M *ᵥ φ x) = (X.image red).image B.reconstruct := by
    ext y
    simp only [mem_image, exists_exists_and_eq_and, red]
    exact ⟨fun ⟨x, hx, hy⟩ => ⟨x, hx, (B.reconstruct_submatrix_mulVec (φ x)).trans hy⟩,
      fun ⟨x, hx, hy⟩ => ⟨x, hx, (B.reconstruct_submatrix_mulVec (φ x)).symm.trans hy⟩⟩
  rw [himg]
  exact card_image_le.trans
    (card_image_mulVec_le_two_mul_add_one_pow (M.submatrix B.rowIdx id)
      (hM.submatrix B.rowIdx id) X φ hφ)

/-- **Rank-compressed `(2n + 1)^{rank M}` bound for `{0, 1}`-bit measurements** over any field `K`
(including `K = ℚ`). -/
theorem card_image_mulVec_bitVal_le_pow_rank {m K : Type*} [Field K] [Finite m]
    [DecidableEq (m → K)] {n : ℕ} (M : Matrix m (Fin n) K) (hM : IsUnitTrinary M)
    (X : Finset (Fin n → Bool)) :
    #(X.image fun x => M *ᵥ fun j => Cslib.BitString.bitVal K (x j)) ≤
      (2 * n + 1) ^ M.rank := by
  refine card_image_mulVec_le_pow_rank M hM X _ fun x _ =>
    ⟨fun j => Cslib.BitString.bitVal ℤ (x j), fun j => ?_, fun j => ?_⟩
  · cases h : x j <;> simp [h, Cslib.BitString.bitVal]
  · cases h : x j <;> simp [h, Cslib.BitString.bitVal]

/-- **Rank-compressed `(2n + 1)^{rank M}` bound for `±1`-sign measurements** over any field `K`
(including `K = ℚ`). -/
theorem card_image_mulVec_sign_le_pow_rank {m K : Type*} [Field K] [Finite m]
    [DecidableEq (m → K)] {n : ℕ} (M : Matrix m (Fin n) K) (hM : IsUnitTrinary M)
    (X : Finset (Fin n → Bool)) :
    #(X.image fun x => M *ᵥ fun j => (-1 : K) ^ (x j).toNat) ≤
      (2 * n + 1) ^ M.rank := by
  refine card_image_mulVec_le_pow_rank M hM X _ fun x _ =>
    ⟨fun j => (-1 : ℤ) ^ (x j).toNat, fun j => ?_, fun j => ?_⟩
  · cases h : x j <;> simp [h]
  · cases h : x j <;> simp [h]

end ValueBound

/-! ### Fibre partition and summation identities for arbitrary linear measurements -/

section FibreIdentities

/-- The finset of measurement vectors attained by `x ↦ M *ᵥ φ x` on `X`. -/
@[expose] def measurementValues {α m col R : Type*} [Semiring R] [Fintype col]
    [DecidableEq (m → R)] (M : Matrix m col R) (φ : α → col → R) (X : Finset α) :
    Finset (m → R) :=
  X.image fun x => M *ᵥ φ x

/-- The fibre `{x ∈ X | M *ᵥ φ x = y}` of inputs in `X` producing measurement vector `y`. -/
@[expose] def measurementFiber {α m col R : Type*} [Semiring R] [Fintype col]
    [DecidableEq (m → R)] (M : Matrix m col R) (φ : α → col → R) (X : Finset α)
    (y : m → R) : Finset α :=
  X.filter fun x => M *ᵥ φ x = y

/-- `measurementFiber`s over `measurementValues` union back to `X`. -/
theorem biUnion_measurementFiber {α m col R : Type*} [DecidableEq α] [Semiring R] [Fintype col]
    [DecidableEq (m → R)] (M : Matrix m col R) (φ : α → col → R) (X : Finset α) :
    (measurementValues M φ X).biUnion (measurementFiber M φ X) = X := by
  ext x
  simp only [mem_biUnion, measurementValues, measurementFiber, mem_image, mem_filter]
  exact ⟨fun ⟨_, _, hx, _⟩ => hx, fun hx => ⟨M *ᵥ φ x, ⟨x, hx, rfl⟩, hx, rfl⟩⟩

/-- Distinct measurement vectors define disjoint measurement fibres. -/
theorem pairwiseDisjoint_measurementFiber {α m col R : Type*} [Semiring R] [Fintype col]
    [DecidableEq (m → R)] (M : Matrix m col R) (φ : α → col → R) (X : Finset α) :
    (measurementValues M φ X : Set (m → R)).PairwiseDisjoint (measurementFiber M φ X) := by
  intro y₁ _ y₂ _ hne
  refine disjoint_left.mpr fun x hx₁ hx₂ => hne ?_
  rw [← (mem_filter.mp hx₁).2, (mem_filter.mp hx₂).2]

/-- General fibrewise summation over `measurementValues` and `measurementFiber`. -/
theorem sum_eq_sum_measurementFiber {α m col R M₀ : Type*} [Semiring R] [Fintype col]
    [DecidableEq (m → R)] [AddCommMonoid M₀] (M : Matrix m col R) (φ : α → col → R)
    (X : Finset α) (w : α → M₀) :
    ∑ x ∈ X, w x = ∑ y ∈ measurementValues M φ X, ∑ x ∈ measurementFiber M φ X y, w x :=
  (sum_fiberwise_of_maps_to (fun _ hx => mem_image_of_mem _ hx) w).symm

/-- Cardinalities of the measurement fibres over `measurementValues` sum to `#X`. -/
theorem sum_card_measurementFiber {α m col R : Type*} [Semiring R] [Fintype col]
    [DecidableEq (m → R)] (M : Matrix m col R) (φ : α → col → R) (X : Finset α) :
    ∑ y ∈ measurementValues M φ X, #(measurementFiber M φ X y) = #X := by
  simpa only [card_eq_sum_ones] using (sum_eq_sum_measurementFiber M φ X fun _ => (1 : ℕ)).symm

/-- **Pigeonhole for `{-1, 0, 1}` linear measurements**: for any nonempty `X ⊆ Fin n → Bool` and
`M : Matrix m (Fin n) K` (`[Field K] [Finite m]`) with entries in `{-1, 0, 1}`, some attained
measurement vector `y` has a fibre in `X` of cardinality `(2 * n + 1) ^ M.rank * #fibre ≥ #X`. -/
theorem exists_le_card_measurementFiber_bitVal {m K : Type*} [Field K] [Finite m]
    [DecidableEq (m → K)] {n : ℕ} (M : Matrix m (Fin n) K) (hM : IsUnitTrinary M)
    {X : Finset (Fin n → Bool)} (hX : X.Nonempty) :
    ∃ y ∈ measurementValues M (fun x j => Cslib.BitString.bitVal K (x j)) X,
      #X ≤ (2 * n + 1) ^ M.rank *
        #(measurementFiber M (fun x j => Cslib.BitString.bitVal K (x j)) X y) := by
  let φ := fun (x : Fin n → Bool) (j : Fin n) => Cslib.BitString.bitVal K (x j)
  let V := measurementValues M φ X
  have hVne : V.Nonempty := hX.image _
  have hcardV : #V ≤ (2 * n + 1) ^ M.rank := card_image_mulVec_bitVal_le_pow_rank M hM X
  obtain ⟨y, hyV, hmax⟩ := exists_max_image V (fun y => #(measurementFiber M φ X y)) hVne
  refine ⟨y, hyV, ?_⟩
  calc #X = ∑ y' ∈ V, #(measurementFiber M φ X y') := (sum_card_measurementFiber M φ X).symm
    _ ≤ #V • #(measurementFiber M φ X y) := sum_le_card_nsmul V _ _ hmax
    _ = #V * #(measurementFiber M φ X y) := smul_eq_mul _ _
    _ ≤ (2 * n + 1) ^ M.rank * #(measurementFiber M φ X y) :=
        Nat.mul_le_mul_right _ hcardV

/-- **Factored linear-measurement fibre-sum identity**: a function `g (M *ᵥ φ x)` depending only on
the linear measurements factors outside each `measurementFiber` sum. -/
theorem sum_mul_comp_mulVec {α m col R S : Type*} [Semiring R] [Fintype col]
    [DecidableEq (m → R)] [CommSemiring S] (M : Matrix m col R) (φ : α → col → R)
    (X : Finset α) (g : (m → R) → S) (w : α → S) :
    ∑ x ∈ X, g (M *ᵥ φ x) * w x =
      ∑ y ∈ measurementValues M φ X, g y * ∑ x ∈ measurementFiber M φ X y, w x := by
  rw [sum_eq_sum_measurementFiber M φ X (fun x => g (M *ᵥ φ x) * w x)]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [(mem_filter.mp hx).2]

/-- **Row-basis compressed fibre-sum identity**: using `B : RowBasisSelection M`, any sum of
`g (M *ᵥ φ x) * w x` over `X` compresses to a sum over the reduced `M.rank`-coordinate measurement
values `y` of `M.submatrix B.rowIdx id`, with `g (B.reconstruct y)` factored outside each fibre. -/
theorem RowBasisSelection.sum_mul_comp_mulVec {α m col K S : Type*} [Field K] [DecidableEq K]
    [Fintype col] [CommSemiring S] {M : Matrix m col K} (B : RowBasisSelection M)
    (φ : α → col → K) (X : Finset α) (g : (m → K) → S) (w : α → S) :
    ∑ x ∈ X, g (M *ᵥ φ x) * w x =
      ∑ y ∈ measurementValues (M.submatrix B.rowIdx id) φ X,
        g (B.reconstruct y) * ∑ x ∈ measurementFiber (M.submatrix B.rowIdx id) φ X y, w x := by
  have hcongr : ∑ x ∈ X, g (M *ᵥ φ x) * w x =
      ∑ x ∈ X, g (B.reconstruct ((M.submatrix B.rowIdx id) *ᵥ φ x)) * w x :=
    sum_congr rfl fun x _ => by rw [B.reconstruct_submatrix_mulVec]
  rw [hcongr]
  exact Matrix.sum_mul_comp_mulVec (M.submatrix B.rowIdx id) φ X (fun y => g (B.reconstruct y)) w

/-- **Kernel-coset translation for full-space linear measurements**: summing `w` over the fibre
`{x : col → R | M *ᵥ x = M *ᵥ x₀}` equals summing `z ↦ w (z + x₀)` over `{z | M *ᵥ z = 0}`. -/
theorem sum_filter_mulVec_eq_sum_ker {m col R M₀ : Type*} [Ring R] [Fintype col]
    [Fintype (col → R)] [DecidableEq (m → R)] [AddCommMonoid M₀]
    (M : Matrix m col R) (x₀ : col → R) (w : (col → R) → M₀) :
    ∑ x ∈ univ.filter (fun x : col → R => M *ᵥ x = M *ᵥ x₀), w x =
      ∑ z ∈ univ.filter (fun z : col → R => M *ᵥ z = 0), w (z + x₀) := by
  refine sum_bij' (fun x _ => x - x₀) (fun z _ => z + x₀) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [mulVec_sub, hx, sub_self]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [mulVec_add, hz, zero_add]
  · intro x _
    exact sub_add_cancel x x₀
  · intro z _
    exact add_sub_cancel_right z x₀
  · intro x _
    rw [sub_add_cancel]

/-- Every nonempty full-space fibre `{x : col → R | M *ᵥ x = M *ᵥ x₀}` has the same cardinality as
the kernel `{z : col → R | M *ᵥ z = 0}`. -/
theorem card_filter_mulVec_eq_card_ker {m col R : Type*} [Ring R] [Fintype col]
    [Fintype (col → R)] [DecidableEq (m → R)] (M : Matrix m col R) (x₀ : col → R) :
    #(univ.filter fun x : col → R => M *ᵥ x = M *ᵥ x₀) =
      #(univ.filter fun z : col → R => M *ᵥ z = 0) := by
  simpa only [card_eq_sum_ones] using sum_filter_mulVec_eq_sum_ker M x₀ (fun _ => (1 : ℕ))

/-- **Fourier fibre-sum identity over `𝔽₂`**: for `M : Matrix α β (ZMod 2)`, `y : α → ZMod 2`, and
`w : (β → ZMod 2) → ℝ`, `2 ^ |α|` times the sum of `w` over the linear-measurement fibre
`{x | M *ᵥ x = y}` equals the sum over frequencies `u : α → ZMod 2` of `(-1)^{u ⬝ᵥ y}` times the
Walsh–Hadamard sum `∑ x, (-1)^{(Mᵀ *ᵥ u) ⬝ᵥ x} * w x`. -/
theorem two_pow_mul_sum_filter_mulVec_zmodTwo {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix α β (ZMod 2)) (y : α → ZMod 2)
    (w : (β → ZMod 2) → ℝ) :
    (2 : ℝ) ^ Fintype.card α * ∑ x ∈ univ.filter (fun x => M *ᵥ x = y), w x =
      ∑ u : α → ZMod 2, (-1 : ℝ) ^ (u ⬝ᵥ y).val *
        ∑ x : β → ZMod 2, (-1 : ℝ) ^ ((Mᵀ *ᵥ u) ⬝ᵥ x).val * w x := by
  have hrhs :
      (∑ u : α → ZMod 2, (-1 : ℝ) ^ (u ⬝ᵥ y).val *
          ∑ x : β → ZMod 2, (-1 : ℝ) ^ ((Mᵀ *ᵥ u) ⬝ᵥ x).val * w x) =
        ∑ x : β → ZMod 2, w x * ∑ u : α → ZMod 2, (-1 : ℝ) ^ (u ⬝ᵥ (M *ᵥ x - y)).val := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    refine sum_congr rfl fun u _ => ?_
    have hdot : (u ⬝ᵥ y) + ((Mᵀ *ᵥ u) ⬝ᵥ x) = u ⬝ᵥ (M *ᵥ x - y) := by
      have hm : (Mᵀ *ᵥ u) ⬝ᵥ x = u ⬝ᵥ (M *ᵥ x) := by
        rw [← vecMul_transpose, transpose_transpose, dotProduct_mulVec]
      rw [hm, dotProduct_sub, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
    have hsign : (-1 : ℝ) ^ (u ⬝ᵥ y).val * (-1 : ℝ) ^ ((Mᵀ *ᵥ u) ⬝ᵥ x).val =
        (-1 : ℝ) ^ (u ⬝ᵥ (M *ᵥ x - y)).val := by
      rw [← ZMod.neg_one_pow_val_add, hdot]
    calc (-1 : ℝ) ^ (u ⬝ᵥ y).val * ((-1 : ℝ) ^ ((Mᵀ *ᵥ u) ⬝ᵥ x).val * w x)
        = ((-1 : ℝ) ^ (u ⬝ᵥ y).val * (-1 : ℝ) ^ ((Mᵀ *ᵥ u) ⬝ᵥ x).val) * w x :=
            (mul_assoc _ _ _).symm
      _ = w x * (-1 : ℝ) ^ (u ⬝ᵥ (M *ᵥ x - y)).val := by rw [hsign, mul_comm]
  rw [hrhs]
  simp_rw [sum_neg_one_pow_val_dotProduct, sub_eq_zero]
  rw [sum_filter, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

end FibreIdentities

end Matrix

/-! ### Character fibre-sum identity for finite abelian group homomorphisms -/

section AbelianCharacterFibre

/-- **Fourier / character fibre-sum identity** for any additive homomorphism `φ : G →+ H` between
finite abelian groups: `|H|` times the sum of `w` over the fibre `{x : G | φ x = y}` equals the
character expansion `∑ ψ : AddChar H ℂ, ψ (-y) * ∑ x : G, ψ (φ x) * w x`. -/
theorem AddChar.card_mul_sum_filter_eq {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (φ : G →+ H) (y : H) (w : G → ℂ) :
    (Fintype.card H : ℂ) * ∑ x ∈ univ.filter (fun x : G => φ x = y), w x =
      ∑ ψ : AddChar H ℂ, ψ (-y) * ∑ x : G, ψ (φ x) * w x := by
  have hrhs : (∑ ψ : AddChar H ℂ, ψ (-y) * ∑ x : G, ψ (φ x) * w x) =
      ∑ x : G, w x * ∑ ψ : AddChar H ℂ, ψ (φ x - y) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    refine sum_congr rfl fun ψ _ => ?_
    have hψ : ψ (-y) * ψ (φ x) = ψ (φ x - y) := by
      rw [sub_eq_add_neg, ψ.map_add_eq_mul, mul_comm]
    calc ψ (-y) * (ψ (φ x) * w x) = (ψ (-y) * ψ (φ x)) * w x := (mul_assoc _ _ _).symm
      _ = w x * ψ (φ x - y) := by rw [hψ, mul_comm]
  rw [hrhs]
  simp_rw [AddChar.sum_apply_eq_ite, sub_eq_zero]
  rw [sum_filter, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

end AbelianCharacterFibre
