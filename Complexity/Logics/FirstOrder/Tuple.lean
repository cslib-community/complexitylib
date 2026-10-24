/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Nat.Radix
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Numbering tuples over finite universes

These generic helpers number finite tuples without depending on machine encodings. The index
uses the first coordinate as the least significant digit, as in Mathlib's `finFunctionFinEquiv`.
The public names and numbering convention are unchanged from their original location in
`Complexity.Logics.FirstOrder.Encoding`, which publicly imports this module.

## Main definitions

* `Cslib.Logic.tupleIndex`: the colexicographic index of a tuple of natural-number digits.
* `Cslib.Logic.tupleEquiv`: number tuples along an enumeration of their coordinates.

## Main results

* `Cslib.Logic.tupleIndex_lt_iff`: numerical order agrees with the highest differing coordinate.
* `Cslib.Logic.tupleIndex_lt_pow_iff`: indices below a power have zero higher digits.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32, for the distinct
  lexicographic convention required by ordered first-order queries.
-/

@[expose] public section

namespace Cslib.Logic

/-! ### Tuples -/

/-- The index of a tuple of `Fin n` in the truth table of a relation of arity `k`: the number
`∑ i, x i * n ^ i` below `n ^ k`, the order of `finFunctionFinEquiv`. -/
def tupleIndex {n k : ℕ} (x : Fin k → Fin n) : ℕ :=
  finFunctionFinEquiv x

/-- `tupleIndex x` is the base-`n` sum `∑ i, x i * n ^ i`. -/
theorem tupleIndex_apply {n k : ℕ} (x : Fin k → Fin n) :
    tupleIndex x = ∑ i : Fin k, (x i : ℕ) * n ^ (i : ℕ) :=
  finFunctionFinEquiv_apply x

/-- Every `k`-tuple over `Fin n` has `tupleIndex` strictly less than `n ^ k`. -/
theorem tupleIndex_lt {n k : ℕ} (x : Fin k → Fin n) : tupleIndex x < n ^ k :=
  (finFunctionFinEquiv x).2

/-- `tupleIndex` is injective. -/
theorem tupleIndex_injective {n k : ℕ} : Function.Injective (tupleIndex (n := n) (k := k)) :=
  fun _ _ h => finFunctionFinEquiv.injective (Fin.ext h)

/-- Number tuples whose coordinates are enumerated by `e`, using the same colexicographic
indexing as `tupleIndex`. -/
def tupleEquiv {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d) : (ι → Fin n) ≃ Fin (n ^ d) :=
  (e.arrowCongr (Equiv.refl (Fin n))).trans finFunctionFinEquiv

/-- The numerical value of `tupleEquiv e x` is `tupleIndex (x ∘ e.symm)`. -/
@[simp]
theorem tupleEquiv_apply_val {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d) (x : ι → Fin n) :
    (tupleEquiv e x).val = tupleIndex (x ∘ e.symm) := rfl

/-- `(tupleEquiv e).symm u` at coordinate `i` is `finFunctionFinEquiv.symm u (e i)`. -/
@[simp]
theorem tupleEquiv_symm_apply {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d) (u : Fin (n ^ d))
    (i : ι) : (tupleEquiv e).symm u i = finFunctionFinEquiv.symm u (e i) := rfl

/-- The `i`-th coordinate of `(tupleEquiv e).symm u` is the `(e i)`-th base-`n` digit of `u`. -/
theorem tupleEquiv_symm_apply_val {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d)
    (u : Fin (n ^ d)) (i : ι) :
    ((tupleEquiv e).symm u i : ℕ) = u / n ^ (e i : ℕ) % n := by
  rw [tupleEquiv_symm_apply, finFunctionFinEquiv_symm_apply_val]

/-- The tuple with a given index. -/
theorem tupleIndex_symm {n k : ℕ} (i : Fin (n ^ k)) :
    tupleIndex (finFunctionFinEquiv.symm i) = i := by
  simp [tupleIndex]

/-- Precomposing a tuple with `Fin.cast` leaves its `tupleIndex` unchanged. -/
theorem tupleIndex_comp_cast {n k l : ℕ} (h : k = l) (x : Fin l → Fin n) :
    tupleIndex (x ∘ Fin.cast h) = tupleIndex x := by
  subst h
  rfl

/-- Separate the highest-weight digit `(x (Fin.last k) : ℕ) * n ^ k` of `tupleIndex x`. -/
theorem tupleIndex_snoc {n k : ℕ} (x : Fin (k + 1) → Fin n) :
    tupleIndex x = tupleIndex (x ∘ Fin.castSucc) + (x (Fin.last k) : ℕ) * n ^ k :=
  finFunctionFinEquiv_snoc x

/-- When all coordinates of `x : Fin k → Fin n` at indices `≥ a` are zero, `tupleIndex x` equals
the index of its prefix of length `a`. -/
theorem tupleIndex_eq_of_high_zero {n a : ℕ} :
    ∀ {k : ℕ} (ha : a ≤ k) {x : Fin k → Fin n}
      (_ : ∀ i : Fin k, a ≤ (i : ℕ) → (x i : ℕ) = 0),
      tupleIndex x = tupleIndex (fun j : Fin a => x (Fin.castLE ha j)) :=
  finFunctionFinEquiv_eq_of_high_zero

/-- For `a ≤ k`, a `k`-tuple has index `< n ^ a` iff all coordinates at indices `≥ a` are zero. -/
theorem tupleIndex_lt_pow_iff {n a : ℕ} :
    ∀ {k : ℕ} (_ : a ≤ k) (x : Fin k → Fin n),
      tupleIndex x < n ^ a ↔ ∀ i : Fin k, a ≤ (i : ℕ) → (x i : ℕ) = 0 :=
  finFunctionFinEquiv_lt_pow_iff

/-- The numerical order on `tupleIndex` is the colexicographic order on `Fin k → Fin n`
(comparing at the most significant coordinate where the tuples differ). -/
theorem tupleIndex_lt_iff {n : ℕ} :
    ∀ {k : ℕ} (x y : Fin k → Fin n),
      tupleIndex x < tupleIndex y ↔
        ∃ i : Fin k, x i < y i ∧ ∀ j : Fin k, i < j → x j = y j :=
  finFunctionFinEquiv_lt_iff

end Cslib.Logic
