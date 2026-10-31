/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
import Complexity.Foundations.Data.BitString.WordCount

/-!
# Counting accepted strings

`Cslib.Complexity.acceptCount V a n` is the number of strings `w` of length `n` with
`V (a, w) = true`, for any Boolean predicate `V : α × List Bool → Bool`. No efficiency of `V` is
assumed. It counts the certificates of a verifier in the counting classes
(`Cslib.Complexity.SharpP`), the random strings accepted by a bounded-error or majority verifier,
and the choice strings accepted by a fair-coin machine (`Turing.MultiTapePTM.acceptCount`).

## Main definitions

* `Cslib.Complexity.acceptCount`: the number of accepted strings of a given length.

## Main results

* `Cslib.Complexity.acceptCount_le_two_pow`, `Cslib.Complexity.acceptCount_pos_iff`: the range
  and support of the count.
* `Cslib.Complexity.acceptCount_add`: counting accepted strings by their prefixes.
* `Cslib.Complexity.acceptCount_zero`, `Cslib.Complexity.acceptCount_add_acceptCount_not`,
  `Cslib.Complexity.acceptCount_not`: counts of trivial and negated verifiers.
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type}

/-- The number of strings `w` of length `n` with `V (a, w) = true`. -/
def acceptCount (V : α × List Bool → Bool) (a : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = true).card

section acceptCount

variable {V : α × List Bool → Bool} {a : α} {n : ℕ}

/-- At most all `2 ^ n` strings are accepted. -/
theorem acceptCount_le_two_pow : acceptCount V a n ≤ 2 ^ n :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- Some string of length `n` is accepted exactly when the count is positive. -/
theorem acceptCount_pos_iff :
    0 < acceptCount V a n ↔ ∃ w : List Bool, w.length = n ∧ V (a, w) = true := by
  rw [acceptCount, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨w, -, hw⟩
    exact ⟨List.ofFn w, List.length_ofFn, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨fun i => w[i.val], Finset.mem_univ _, by rwa [List.ofFn_getElem]⟩

/-- The strings that `V` accepts together with `a` and those it rejects are all the strings. -/
theorem acceptCount_add_card_filter_eq_false :
    acceptCount V a n +
      (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = false).card = 2 ^ n := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    fun w : Fin n → Bool => V (a, List.ofFn w) = true
  simpa only [acceptCount, Bool.not_eq_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using this

/-- **Counting strings by their prefixes**: the strings of length `m + n` accepted by `V` are the
strings `u ++ w`, with `u` of length `m` and `w` of length `n` accepted with the prefix `u`. -/
theorem acceptCount_add (V : α × List Bool → Bool) (a : α) (m n : ℕ) :
    acceptCount V a (m + n) =
      ∑ u : Fin m → Bool, acceptCount (fun x => V (x.1, List.ofFn u ++ x.2)) a n := by
  have h := BitString.card_filter_ofFn_add m n fun u w => V (a, u ++ w) = true
  simp only [List.take_append_drop] at h
  exact h

/-- Verifiers that agree on an instance accept the same strings with it. -/
theorem acceptCount_congr {W : α × List Bool → Bool} (h : ∀ w, V (a, w) = W (a, w)) (n : ℕ) :
    acceptCount V a n = acceptCount W a n := by
  simp only [acceptCount, h]

/-- With no bits there is one string, the empty one. -/
theorem acceptCount_zero (V : α × List Bool → Bool) (a : α) :
    acceptCount V a 0 = if V (a, []) = true then 1 else 0 := by
  unfold acceptCount
  rw [Finset.univ_unique, Finset.filter_singleton]
  split_ifs with h₁ h₂ h₂ <;> simp_all

/-- The verifier accepting everything accepts all `2 ^ n` strings of length `n`. -/
@[simp]
theorem acceptCount_true (a : α) (n : ℕ) : acceptCount (fun _ => true) a n = 2 ^ n := by
  simp [acceptCount]

/-- The verifier rejecting everything accepts no string. -/
@[simp]
theorem acceptCount_false (a : α) (n : ℕ) : acceptCount (fun _ => false) a n = 0 := by
  simp [acceptCount]

/-- A verifier and its negation together accept every string once. -/
theorem acceptCount_add_acceptCount_not (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount V a n + acceptCount (fun x => !V x) a n = 2 ^ n := by
  simpa only [acceptCount, Bool.not_eq_true'] using
    acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := n)

/-- The negation of a verifier accepts the strings that it rejects. -/
theorem acceptCount_not (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (fun x => !V x) a n = 2 ^ n - acceptCount V a n := by
  have := acceptCount_add_acceptCount_not V a n
  omega

end acceptCount

end Cslib.Complexity
