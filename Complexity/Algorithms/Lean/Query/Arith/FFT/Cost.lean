/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.Arith.FFT.Defs
public import Complexity.Algorithms.Lean.Query.Arith.Lemmas
public import Cslib.Algorithms.Lean.Query.Bounds
public import Mathlib.Data.Nat.Log
import Complexity.Algorithms.Lean.Query.FreeM.MOfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Cost of the fast Fourier transform and FFT multiplication

The programs of `Complexity.Algorithms.Lean.Query.Arith.FFT.Defs` make the same queries under
every oracle, so their costs are exact closed forms. With multiplications weighted `c_mul` and
additions and subtractions weighted `c_add`:

* the radix-2 transform of length `n = 2 ^ k` costs exactly
  `c_mul * ((n / 2) * log₂ n) + c_add * (n * log₂ n)` (`Cslib.Query.cost_fft`), the classical
  `(n / 2) log₂ n` multiplications and `n log₂ n` additive operations ([CooleyTukey1965];
  [CLRS2009], Section 30.2);
* FFT multiplication of length `N = 2 ^ (k + 1)`, including the computation of the twiddle table,
  makes `(3 / 2) N log₂ N + (5 / 2) N - 1` multiplications and `3 N log₂ N` additive operations
  (`Cslib.Query.cost_fftMul`), at most `7 N log₂ N` queries in total
  (`Cslib.Query.countQueries_fftMul_le`, `Cslib.Query.fftMul_upperBound`).

## Main results

* `Cslib.Query.cost_fft`, `Cslib.Query.cost_fft_two_pow`: exact cost of the transform.
* `Cslib.Query.cost_ifft`, `Cslib.Query.cost_cyclicMul`: exact costs of the inverse transform
  and of cyclic convolution with a supplied twiddle table.
* `Cslib.Query.cost_fftMul`: exact cost of FFT multiplication.
* `Cslib.Query.countQueries_fftMul`, `Cslib.Query.countQueries_fftMul_le`: its exact query count
  and the bound `7 N log₂ N`.
* `Cslib.Query.fftMul_upperBound`: the bound as a cslib `UpperBound`.

## References

* [Cooley and Tukey, *An Algorithm for the Machine Calculation of Complex Fourier
  Series*][CooleyTukey1965].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 30.2.
-/

public section

namespace Cslib.Query

open ArithQuery FFT

variable {α : Type}

namespace FFT

/-- A butterfly costs one multiplication and two additive operations. -/
theorem cost_butterfly (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (w e o : α) :
    (butterfly w e o).cost oracle (weight c_add c_mul) = c_mul + 2 * c_add := by
  simp only [butterfly, doMul, doAdd, doSub, FreeM.cost_liftBind, FreeM.cost_pure, weight]
  omega

/-- `powersFrom ω (r + 1) c` costs `r` multiplications. -/
theorem cost_powersFrom (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (ω : α)
    (r : ℕ) (c : α) :
    (powersFrom ω (r + 1) c).cost oracle (weight c_add c_mul) = c_mul * r := by
  induction r generalizing c with
  | zero => rfl
  | succ r ih =>
    simp only [powersFrom, FreeM.cost_bind, doMul, FreeM.cost_lift, weight, ih, FreeM.cost_pure]
    ring

end FFT

/-- **Cost of the FFT.** Under every oracle, the radix-2 transform of length `2 ^ k` makes
`(2 ^ k / 2) * k` multiplications and `2 ^ k * k` additions and subtractions. -/
theorem cost_fft (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (k : ℕ)
    (w : ℕ → α) (a : Fin (2 ^ k) → α) :
    (fft k w a).cost oracle (weight c_add c_mul) =
      c_mul * (2 ^ k / 2 * k) + c_add * (2 ^ k * k) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    simp only [fft, FreeM.cost_bind, FreeM.cost_pure, ih, FreeM.cost_mOfFn, cost_butterfly,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, add_zero]
    rcases k with _ | k
    · simp only [pow_zero]
      omega
    · rw [pow_succ 2 (k + 1), Nat.mul_div_cancel _ two_pos, pow_succ 2 k,
        Nat.mul_div_cancel _ two_pos]
      ring

/-- **Cost of the FFT** in terms of the length `n = 2 ^ k`: `(n / 2) log₂ n` multiplications and
`n log₂ n` additive operations. -/
theorem cost_fft_two_pow (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (k : ℕ)
    (w : ℕ → α) (a : Fin (2 ^ k) → α) :
    (fft k w a).cost oracle (weight c_add c_mul) =
      c_mul * (2 ^ k / 2 * Nat.log 2 (2 ^ k)) + c_add * (2 ^ k * Nat.log 2 (2 ^ k)) := by
  rw [Nat.log_pow one_lt_two, cost_fft]

/-- The inverse FFT costs one transform plus `2 ^ k` scaling multiplications. -/
theorem cost_ifft (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (k : ℕ)
    (w : ℕ → α) (nInv : α) (a : Fin (2 ^ k) → α) :
    (ifft k w nInv a).cost oracle (weight c_add c_mul) =
      c_mul * (2 ^ k / 2 * k + 2 ^ k) + c_add * (2 ^ k * k) := by
  simp only [ifft, FreeM.cost_bind, FreeM.cost_pure, cost_fft, FreeM.cost_mOfFn, doMul,
    FreeM.cost_lift, weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    add_zero]
  ring

/-- Cyclic convolution with a supplied twiddle table costs three transforms and `2 * 2 ^ k`
multiplications (pointwise product and scaling). -/
theorem cost_cyclicMul (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (k : ℕ)
    (w : ℕ → α) (nInv : α) (a b : Fin (2 ^ k) → α) :
    (cyclicMul k w nInv a b).cost oracle (weight c_add c_mul) =
      c_mul * (3 * (2 ^ k / 2 * k) + 2 * 2 ^ k) + c_add * (3 * (2 ^ k * k)) := by
  simp only [cyclicMul, FreeM.cost_bind, cost_fft, cost_ifft, FreeM.cost_mOfFn, doMul,
    FreeM.cost_lift, weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- **Cost of FFT multiplication** of length `2 ^ (k + 1)`, including the `2 ^ k - 1`
multiplications that build the twiddle table. -/
theorem cost_fftMul [One α] (oracle : {ι : Type} → ArithQuery α ι → ι) (c_add c_mul : ℕ) (k : ℕ)
    (ω nInv : α) (a b : Fin (2 ^ (k + 1)) → α) :
    (fftMul k ω nInv a b).cost oracle (weight c_add c_mul) =
      c_mul * (3 * (2 ^ k * (k + 1)) + 4 * 2 ^ k + (2 ^ k - 1)) +
        c_add * (3 * (2 ^ (k + 1) * (k + 1))) := by
  have h1 : 2 ^ k = 2 ^ k - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  simp only [fftMul, FreeM.cost_bind, cost_cyclicMul]
  rw [h1, cost_powersFrom, ← h1, pow_succ 2 k, Nat.mul_div_cancel _ two_pos]
  ring

/-- The exact number of queries of FFT multiplication of length `2 ^ (k + 1)`. -/
theorem countQueries_fftMul [One α] (oracle : {ι : Type} → ArithQuery α ι → ι) (k : ℕ)
    (ω nInv : α) (a b : Fin (2 ^ (k + 1)) → α) :
    (fftMul k ω nInv a b).countQueries oracle =
      3 * (2 ^ k * (k + 1)) + 4 * 2 ^ k + (2 ^ k - 1) + 3 * (2 ^ (k + 1) * (k + 1)) := by
  rw [ArithQuery.countQueries_eq_cost_weight_one, cost_fftMul, one_mul, one_mul]

/-- **FFT multiplication makes `O(N log N)` queries**: for `N = 2 ^ (k + 1)`, at most
`7 N log₂ N`. -/
theorem countQueries_fftMul_le [One α] (oracle : {ι : Type} → ArithQuery α ι → ι) (k : ℕ)
    (ω nInv : α) (a b : Fin (2 ^ (k + 1)) → α) :
    (fftMul k ω nInv a b).countQueries oracle ≤
      7 * 2 ^ (k + 1) * Nat.log 2 (2 ^ (k + 1)) := by
  rw [countQueries_fftMul, Nat.log_pow one_lt_two,
    show 2 ^ (k + 1) * (k + 1) = 2 * (2 ^ k * (k + 1)) by ring,
    show 7 * 2 ^ (k + 1) * (k + 1) = 14 * (2 ^ k * (k + 1)) by ring]
  have hle : 2 ^ k ≤ 2 ^ k * (k + 1) := Nat.le_mul_of_pos_right _ k.succ_pos
  generalize 2 ^ k * (k + 1) = B at hle ⊢
  omega

/-- **FFT multiplication makes `O(N log N)` queries**, as a cslib `UpperBound`: on inputs of
length `N = 2 ^ (k + 1)` it makes at most `7 N log₂ N` queries under every oracle. -/
theorem fftMul_upperBound [One α] (k : ℕ) (ω nInv : α) :
    UpperBound (fun ab : (Fin (2 ^ (k + 1)) → α) × (Fin (2 ^ (k + 1)) → α) =>
        fftMul k ω nInv ab.1 ab.2)
      (fun _ => 2 ^ (k + 1)) (fun n => 7 * n * Nat.log 2 n) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.mul_le_mul (Nat.mul_le_mul_left _ h) (Nat.log_mono_right h))
    fun oracle ab => countQueries_fftMul_le oracle k ω nInv ab.1 ab.2

end Cslib.Query
