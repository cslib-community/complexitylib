/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

/-!
# Inner products of bit strings as parities

Over the two-element Boolean ring, the inner product `x ⬝ᵥ w = Σᵢ xᵢ wᵢ` of two bit strings is the
parity of `x` on the support of `w` (`Cslib.BitString.dotProduct_eq_parityOn`). Parities on nonempty
sets are balanced (`Cslib.card_filter_parityOn_eq`), so the inner product with a fixed nonzero
string takes each value on half of the strings (`Cslib.BitString.card_dotProduct_eq_false`).
Consequently a nonzero string lies in the kernel of exactly `2 ^ ((d - 1) c)` of the `2 ^ (d c)`
matrices with `c` rows (`Cslib.BitString.card_kernel`). Since `v`, `w` and `v + w` are all nonzero
for distinct nonzero `v` and `w`, inclusion–exclusion shows that a quarter of the strings are
orthogonal to both (`Cslib.BitString.card_dotProduct_eq_false_and_eq_false`), so both lie in the
kernel of a `4 ^ c`-th of the matrices (`Cslib.BitString.card_kernel_pair`).

## Main results

* `Cslib.BitString.dotProduct_eq_parityOn`: the inner product with `w` is the parity on the support
  of `w`.
* `Cslib.BitString.card_dotProduct_eq_false`: half of the strings are orthogonal to a nonzero `w`.
* `Cslib.BitString.card_kernel`: the matrices whose kernel contains a nonzero `w`.
* `Cslib.BitString.card_dotProduct_eq_false_and_eq_false`, `Cslib.BitString.card_kernel_pair`: the
  same for two distinct nonzero strings.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι]

/-- The inner product with `w` is the parity on the support of `w`. -/
theorem dotProduct_eq_parityOn (x w : ι → Bool) : x ⬝ᵥ w = parityOn {i | w i = true} x := by
  rw [parityOn_eq_sum, dotProduct, sum_filter]
  exact sum_congr rfl fun i _ => by cases w i <;> cases x i <;> rfl

section Kernel

variable {c d : ℕ}

/-- The rows orthogonal to a nonzero `w`: `2 ^ (d - 1)` of the `2 ^ d`. -/
theorem card_dotProduct_eq_false {w : Fin d → Bool} (hw : w ≠ 0) :
    #{x : Fin d → Bool | x ⬝ᵥ w = false} = 2 ^ (d - 1) := by
  obtain ⟨j, hj⟩ : ∃ j, w j = true := by
    by_contra h
    simp only [not_exists, Bool.not_eq_true] at h
    exact hw (funext h)
  simp only [dotProduct_eq_parityOn]
  rw [card_filter_parityOn_eq ⟨j, by simpa using hj⟩, Fintype.card_fin]

/-- Matrices with `c` rows whose kernel contains a nonzero `w`: `2 ^ ((d - 1) c)`. -/
theorem card_kernel {w : Fin d → Bool} (hw : w ≠ 0) :
    #{A : Fin c → Fin d → Bool | ∀ i, A i ⬝ᵥ w = false} = (2 ^ (d - 1)) ^ c := by
  rw [← card_dotProduct_eq_false hw, ← Fintype.card_piFinset_const]
  congr 1
  ext A
  simp [Fintype.mem_piFinset]

/-- The rows orthogonal to two distinct nonzero strings `v` and `w`: a quarter of the `2 ^ d`. -/
theorem card_dotProduct_eq_false_and_eq_false {v w : Fin d → Bool} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : v ≠ w) :
    #{x : Fin d → Bool | x ⬝ᵥ v = false ∧ x ⬝ᵥ w = false} * 4 = 2 ^ d := by
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact absurd (funext fun i => i.elim0) hv
    · exact hd
  have hvw' : v + w ≠ 0 := fun h => hvw <| funext fun i => by
    have hi := congrFun h i
    revert hi
    simp only [Pi.add_apply, Pi.zero_apply]
    cases v i <;> cases w i <;> decide
  have hpt : ∀ x : Fin d → Bool,
      ((if x ⬝ᵥ v = false then 1 else 0) + (if x ⬝ᵥ w = false then 1 else 0) +
        (if x ⬝ᵥ (v + w) = false then 1 else 0) : ℕ) =
        1 + 2 * (if x ⬝ᵥ v = false ∧ x ⬝ᵥ w = false then 1 else 0) := by
    intro x
    rw [dotProduct_add]
    cases x ⬝ᵥ v <;> cases x ⬝ᵥ w <;> rfl
  have hsum := sum_congr rfl fun x (_ : x ∈ (univ : Finset (Fin d → Bool))) => hpt x
  simp only [sum_add_distrib, ← mul_sum, ← card_filter, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  rw [card_dotProduct_eq_false hv, card_dotProduct_eq_false hw, card_dotProduct_eq_false hvw']
    at hsum
  have h2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  omega

/-- Matrices with `c` rows whose kernel contains two distinct nonzero strings `v` and `w`: a
`4 ^ c`-th of the `2 ^ (d c)`. -/
theorem card_kernel_pair {v w : Fin d → Bool} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    #{A : Fin c → Fin d → Bool | ∀ i, A i ⬝ᵥ v = false ∧ A i ⬝ᵥ w = false} * 4 ^ c =
      2 ^ (d * c) := by
  have h : #{A : Fin c → Fin d → Bool | ∀ i, A i ⬝ᵥ v = false ∧ A i ⬝ᵥ w = false} =
      #{x : Fin d → Bool | x ⬝ᵥ v = false ∧ x ⬝ᵥ w = false} ^ c := by
    rw [← Fintype.card_piFinset_const]
    congr 1
    ext A
    simp [Fintype.mem_piFinset]
  rw [h, ← mul_pow, card_dotProduct_eq_false_and_eq_false hv hw hvw, pow_mul]

end Kernel

end Cslib.BitString
