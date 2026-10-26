/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/LinearAlgebra/Matrix/Toeplitz.lean)

public import Complexity.Init
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Toeplitz matrices

A *Toeplitz matrix* is constant along each diagonal: its entry in row `i` and column `j` depends
only on `i - j`. An `m × n` Toeplitz matrix is therefore determined by its first row and its first
column, `m + n - 1` entries in all (`Matrix.toeplitz`, `Matrix.exists_toeplitz_eq_iff`,
`Matrix.toeplitz_injective`).

Over a field, for every nonzero `d : Fin n → α`, the Toeplitz matrices `T` reach every vector `T d`
(`Matrix.toeplitz_mulVec_surjective`). Indeed, if `j₀` is the last coordinate with `d j₀ ≠ 0`, then
on Toeplitz matrices supported on the `m` diagonals through column `j₀`, the map `T ↦ T d` is
triangular with diagonal `d j₀`.

## Main definitions

* `Matrix.toeplitz`: the `m × n` Toeplitz matrix with the given `m + n - 1` diagonals.

## Main results

* `Matrix.exists_toeplitz_eq_iff`, `Matrix.toeplitz_injective`: the matrices with at least one
  row and one column whose entries depend only on the difference of their indices are exactly
  the Toeplitz matrices, and each determines its diagonals.
* `Matrix.toeplitz_mulVec_surjective`: over a field, `T ↦ T d` maps Toeplitz matrices onto all
  vectors for every `d ≠ 0`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
-/

@[expose] public section

open Finset
open scoped Matrix

namespace Matrix

variable {α : Type*} {m n : ℕ}

/-- The `m × n` *Toeplitz matrix* with diagonals `a`: its entry in row `i` and column `j` is
`a (i - j + n - 1)`. It is constant along each diagonal: `a 0` is the top right corner, the
first row is `a (n - 1), …, a 0`, the first column is `a (n - 1), …, a (m + n - 2)`, and the
last entry `a (m + n - 2)` is the bottom left corner [Katz and Lindell, Exercise 4.26]
[KatzLindell2020]. -/
def toeplitz (a : Fin (m + n - 1) → α) : Matrix (Fin m) (Fin n) α :=
  of fun i j => a ⟨i + (n - 1 - j), by omega⟩

/-- The entry of `toeplitz a` in row `i` and column `j` is `a (i + (n - 1 - j))`. -/
@[simp]
theorem toeplitz_apply (a : Fin (m + n - 1) → α) (i : Fin m) (j : Fin n) :
    toeplitz a i j = a ⟨i + (n - 1 - j), by omega⟩ :=
  rfl

/-- The entries of a Toeplitz matrix depend only on the difference of their indices. -/
theorem toeplitz_apply_eq_of_add_eq (a : Fin (m + n - 1) → α) {i i' : Fin m} {j j' : Fin n}
    (h : (i : ℕ) + j' = i' + j) : toeplitz a i j = toeplitz a i' j' := by
  simp only [toeplitz_apply]
  congr 2
  omega

/-- A Toeplitz matrix with at least one row and one column determines its diagonals. -/
theorem toeplitz_injective (hm : m ≠ 0) (hn : n ≠ 0) :
    Function.Injective (toeplitz : (Fin (m + n - 1) → α) → Matrix (Fin m) (Fin n) α) := by
  intro a b h
  ext k
  obtain ⟨i, j, hij⟩ : ∃ (i : Fin m) (j : Fin n), (i : ℕ) + (n - 1 - j) = k := by
    by_cases hk : n - 1 ≤ (k : ℕ)
    · exact ⟨⟨(k : ℕ) - (n - 1), by omega⟩, ⟨0, by omega⟩, by simp only; omega⟩
    · exact ⟨⟨0, by omega⟩, ⟨n - 1 - (k : ℕ), by omega⟩, by simp only; omega⟩
  rw [show k = ⟨i + (n - 1 - j), by omega⟩ from Fin.ext hij.symm]
  exact congr_fun₂ h i j

/-- A matrix with at least one row and one column is a Toeplitz matrix exactly when its entries
depend only on the difference of their indices. -/
theorem exists_toeplitz_eq_iff (hm : m ≠ 0) (hn : n ≠ 0) {A : Matrix (Fin m) (Fin n) α} :
    (∃ a, toeplitz a = A) ↔
      ∀ (i i' : Fin m) (j j' : Fin n), (i : ℕ) + j' = i' + j → A i j = A i' j' := by
  constructor
  · rintro ⟨a, rfl⟩ i i' j j' h
    exact toeplitz_apply_eq_of_add_eq a h
  · intro hA
    refine ⟨fun k => if n - 1 ≤ (k : ℕ) then A ⟨(k : ℕ) - (n - 1), by omega⟩ ⟨0, by omega⟩
      else A ⟨0, by omega⟩ ⟨n - 1 - (k : ℕ), by omega⟩, ?_⟩
    ext i j
    simp only [toeplitz_apply]
    split_ifs with h
    · exact hA _ _ _ _ (by simp only; omega)
    · exact hA _ _ _ _ (by simp only; omega)

/-- The Toeplitz matrix with zero diagonals is zero. -/
@[simp]
theorem toeplitz_zero [Zero α] : toeplitz (0 : Fin (m + n - 1) → α) = 0 :=
  ext fun _ _ => rfl

/-- `toeplitz` sends sums of diagonals to sums of matrices. -/
theorem toeplitz_add [Add α] (a b : Fin (m + n - 1) → α) :
    toeplitz (a + b) = toeplitz a + toeplitz b :=
  ext fun _ _ => rfl

/-- `toeplitz` commutes with negation. -/
theorem toeplitz_neg [Neg α] (a : Fin (m + n - 1) → α) : toeplitz (-a) = -toeplitz a :=
  ext fun _ _ => rfl

/-- `toeplitz` sends differences of diagonals to differences of matrices. -/
theorem toeplitz_sub [Sub α] (a b : Fin (m + n - 1) → α) :
    toeplitz (a - b) = toeplitz a - toeplitz b :=
  ext fun _ _ => rfl

/-- `toeplitz` commutes with scalar multiplication. -/
theorem toeplitz_smul {R : Type*} [SMul R α] (c : R) (a : Fin (m + n - 1) → α) :
    toeplitz (c • a) = c • toeplitz a :=
  ext fun _ _ => rfl

/-- Every nonzero vector `v : Fin k → α` has a last nonzero coordinate `j₀`. -/
private theorem exists_last_ne_zero {k : ℕ} [Zero α] {v : Fin k → α} (hv : v ≠ 0) :
    ∃ j₀ : Fin k, v j₀ ≠ 0 ∧ (∀ j, v j ≠ 0 → j ≤ j₀) ∧ ∀ j, j₀ < j → v j = 0 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  obtain ⟨j₀, h₀, hmax⟩ := exists_max_image {j | v j ≠ 0} id ⟨j, by simpa using hj⟩
  have hle (j : Fin k) (hj : v j ≠ 0) : j ≤ j₀ := hmax j (by simpa using hj)
  exact ⟨j₀, by simpa using h₀, hle, fun j hj => by_contra fun h => (hle j h).not_gt hj⟩

/-- `toeplitzBand j₀ w` writes `w` on the `m` diagonals through column `j₀`, starting from row
`0`. -/
private def toeplitzBand [Semiring α] (j₀ : Fin n) : (Fin m → α) →ₗ[α] Fin (m + n - 1) → α :=
  LinearMap.pi fun k =>
    if h : n - 1 - (j₀ : ℕ) ≤ k ∧ (k : ℕ) - (n - 1 - j₀) < m then
      LinearMap.proj (⟨(k : ℕ) - (n - 1 - j₀), h.2⟩ : Fin m)
    else 0

/-- If `d` vanishes beyond `j₀` and `w` vanishes beyond `i`, then the `i`-th coordinate of
`toeplitz (toeplitzBand j₀ w) *ᵥ d` is `w i * d j₀`. -/
private theorem toeplitzBand_mulVec_apply [Semiring α] {d : Fin n → α} {j₀ : Fin n}
    (hmax : ∀ j, d j ≠ 0 → j ≤ j₀) (w : Fin m → α) (i : Fin m)
    (hw : ∀ i', i < i' → w i' = 0) :
    (toeplitz (toeplitzBand j₀ w) *ᵥ d) i = w i * d j₀ := by
  change ∑ j, toeplitz (toeplitzBand j₀ w) i j * d j = w i * d j₀
  rw [sum_eq_single j₀]
  · congr 1
    simp only [toeplitz_apply, toeplitzBand, LinearMap.pi_apply]
    rw [dite_eq_left (by omega)]
    simp only [LinearMap.proj_apply]
    congr 1
    ext
    simp only
    omega
  · intro j _ hj
    by_cases hdj : d j = 0
    · rw [hdj, mul_zero]
    have hlt : (j : ℕ) < j₀ := Fin.lt_def.1 (lt_of_le_of_ne (hmax j hdj) hj)
    simp only [toeplitz_apply, toeplitzBand, LinearMap.pi_apply]
    split_ifs with h
    · rw [LinearMap.proj_apply, hw _ (Fin.lt_def.2 (by simp only; omega)), zero_mul]
    · rw [LinearMap.zero_apply, zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- **Toeplitz matrices reach every vector**: over a field, for every nonzero vector `d`, every
vector is `T d` for some `m × n` Toeplitz matrix `T`. If `j₀` is the last coordinate with
`d j₀ ≠ 0`, then for a Toeplitz matrix `T` supported on the `m` diagonals through column `j₀`,
the `i`-th coordinate of `T d` is `d j₀` times the entry of `T` in row `i` and column `j₀`, plus
entries further down the diagonals; this triangular system can be solved for any `T d`. -/
theorem toeplitz_mulVec_surjective [Field α] {d : Fin n → α} (hd : d ≠ 0) :
    Function.Surjective fun a : Fin (m + n - 1) → α => toeplitz a *ᵥ d := by
  classical
  obtain ⟨j₀, hj₀, hmax, -⟩ := exists_last_ne_zero hd
  let L : (Fin m → α) →ₗ[α] Fin m → α :=
    { toFun w := toeplitz (toeplitzBand j₀ w) *ᵥ d
      map_add' w w' := by
        rw [map_add, toeplitz_add, add_mulVec]
      map_smul' c w := by
        simp only [RingHom.id_apply]
        rw [map_smul, toeplitz_smul, smul_mulVec] }
  -- `L` is injective: if `L w = 0` with `w ≠ 0`, look at the last `i` with `w i ≠ 0`.
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun w hw => ?_
    by_contra hne
    obtain ⟨i, hwi, -, hbeyond⟩ := exists_last_ne_zero hne
    have hLi : L w i = w i * d j₀ := toeplitzBand_mulVec_apply hmax w i hbeyond
    rw [hw, Pi.zero_apply] at hLi
    exact mul_ne_zero hwi hj₀ hLi.symm
  intro c
  obtain ⟨w, rfl⟩ := LinearMap.injective_iff_surjective.1 hinj c
  exact ⟨toeplitzBand j₀ w, rfl⟩

end Matrix
