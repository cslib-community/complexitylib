/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Arith.Karatsuba.Defs
public import CslibFrontier.Algorithms.Lean.Query.Arith.Lemmas
public import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence
public import CslibFrontier.Foundations.Data.Nat.LogTwoRpow
public import Cslib.Algorithms.Lean.Query.Bounds

/-!
# Cost of Karatsuba multiplication

Under every oracle, `Cslib.Query.karatsuba p q` on lists of length at most `N` makes exactly
`mulCount N` multiplications and `addCount N` additions and subtractions, where
`N = max(|p|, |q|)` (`Cslib.Query.cost_karatsuba`, `Cslib.Query.countQueries_karatsuba`).
These counts satisfy

* `mulCount (2 ^ k) = 3 ^ k` and `2 addCount (2 ^ k) + 16 · 2 ^ k = 13 · 3 ^ k + 3`;
* `mulCount n ≤ 3 ^ ⌈log₂ n⌉` and `addCount n + 8 · 2 ^ ⌈log₂ n⌉ ≤ 8 · 3 ^ ⌈log₂ n⌉`, so the total
  is at most `9 · 3 ^ ⌈log₂ n⌉ ≤ 27 n ^ log₂ 3`;
* `3 ^ ⌊log₂ n⌋ ≤ mulCount n` for `n ≠ 0`, so `n ^ log₂ 3 ≤ 3 mulCount n`: the multiplication
  count is `Θ(n ^ log₂ 3)`;
* `mulCount n < n ^ 2` for `n ≥ 2`: fewer multiplications than the `n ^ 2` coefficient products
  of the schoolbook method.

The upper bounds come from the halving recurrence `Nat.add_mul_two_pow_clog_le_of_halving`.
The query bounds are packaged as `Cslib.Query.karatsuba_upperBound` and, since every input of
length `n` attains the exact count, `Cslib.Query.karatsuba_lowerBound`.

## Main results

* `Cslib.Query.cost_karatsuba`: the exact weighted cost under every oracle.
* `Cslib.Query.countQueries_karatsuba`: the exact query count under every oracle.
* `Cslib.Query.cost_karatsuba_le`: weighted cost at most `(c_mul + 8 c_add) 3 ^ ⌈log₂ N⌉`.
* `Cslib.Query.karatsuba_upperBound`: `UpperBound` with bound `9 · 3 ^ ⌈log₂ n⌉`.
* `Cslib.Query.karatsuba_lowerBound`: `LowerBound` with the exact count
  `mulCount n + addCount n`.
* `Cslib.Query.Karatsuba.mulCount_two_pow`, `Cslib.Query.Karatsuba.addCount_two_pow`: closed
  forms at powers of two.
* `Cslib.Query.Karatsuba.mulCount_le_rpow`, `Cslib.Query.Karatsuba.rpow_le_three_mul_mulCount`,
  `Cslib.Query.Karatsuba.mulCount_add_addCount_le_rpow`: real-exponent bounds.
* `Cslib.Query.Karatsuba.mulCount_lt_sq`: fewer than `n ^ 2` multiplications for `n ≥ 2`.

## References

* [Karatsuba and Ofman, *Multiplication of Many-Digital Numbers by Automatic
  Computers*][KaratsubaOfman1962].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Problem 30-1.
-/

public section

namespace Cslib.Query

open ArithQuery

variable {α : Type}

namespace Karatsuba

/-! ### The counting recurrences -/

@[simp] theorem mulCount_zero : mulCount 0 = 0 := by rw [mulCount]

@[simp] theorem mulCount_one : mulCount 1 = 1 := by rw [mulCount]

@[simp] theorem addCount_zero : addCount 0 = 0 := by rw [addCount]

@[simp] theorem addCount_one : addCount 1 = 0 := by rw [addCount]

/-- `M(n) = M(⌊n/2⌋) + 2 M(n - ⌊n/2⌋)` for `n ≥ 2`. -/
theorem mulCount_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    mulCount n = mulCount (n / 2) + 2 * mulCount (n - n / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [mulCount]

/-- `A(n) = A(⌊n/2⌋) + 2 A(n - ⌊n/2⌋) + 4 n - 3` for `n ≥ 2`. -/
theorem addCount_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    addCount n = addCount (n / 2) + 2 * addCount (n - n / 2) + (4 * n - 3) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [addCount]
  omega

/-! ### Exact costs -/

variable (o : {ι : Type} → ArithQuery α ι → ι) (ca cm : ℕ)

/-- `addList p q` makes one addition for each position where both lists have a coefficient. -/
theorem cost_addList (p q : List α) :
    (addList p q).cost o (weight ca cm) = ca * min p.length q.length := by
  induction p generalizing q with
  | nil => simp [addList]
  | cons a p ih =>
    cases q with
    | nil => simp [addList]
    | cons b q =>
      simp only [addList, doAdd, FreeM.cost_bind, FreeM.cost_lift, FreeM.cost_pure, weight, ih,
        List.length_cons]
      rw [Nat.succ_min_succ, Nat.mul_succ]
      omega

/-- `subList p q` makes one subtraction for each coefficient of `q`. -/
theorem cost_subList [Zero α] (p q : List α) :
    (subList p q).cost o (weight ca cm) = ca * q.length := by
  induction q generalizing p with
  | nil => simp [subList]
  | cons b q ih =>
    simp only [subList, doSub, FreeM.cost_bind, FreeM.cost_lift, FreeM.cost_pure, weight, ih,
      List.length_cons]
    ring

/-- `mulFit n` makes exactly `mulCount n` multiplications and `addCount n` additions and
subtractions under every oracle. -/
theorem cost_mulFit [Zero α] (n : ℕ) (p q : List α) :
    (mulFit n p q).cost o (weight ca cm) = cm * mulCount n + ca * addCount n := by
  induction n using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
    match n with
    | 0 => simp [mulFit]
    | 1 => simp [mulFit, doMul, weight]
    | n + 2 =>
      rw [mulFit, mulCount, addCount]
      simp only [addAt, FreeM.cost_bind, FreeM.cost_pure, cost_addList, cost_subList,
        length_eval_mulFit, length_eval_subList, List.takeD_length, List.length_drop,
        List.length_append, List.length_cons]
      rw [ih _ (by omega), ih _ (by omega), ih _ (by omega)]
      obtain ⟨m, hm⟩ : ∃ m, (n + 2) / 2 = m + 1 := ⟨(n + 2) / 2 - 1, by omega⟩
      obtain ⟨k, hk⟩ : ∃ k, n + 2 - (m + 1) = k + 1 := ⟨n + 2 - (m + 1) - 1, by omega⟩
      have hkm : m ≤ k := by omega
      have hn : n = m + k := by omega
      rw [hm, hk]
      subst hn
      simp (disch := omega) only [Nat.min_eq_left, Nat.min_eq_right, Nat.max_eq_left,
        show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      ring

/-! ### Closed forms at powers of two -/

private theorem two_pow_succ_facts (k : ℕ) :
    2 ≤ 2 ^ (k + 1) ∧ 2 ^ (k + 1) / 2 = 2 ^ k ∧ 2 ^ (k + 1) - 2 ^ (k + 1) / 2 = 2 ^ k := by
  have := Nat.one_le_two_pow (n := k)
  rw [pow_succ]
  omega

/-- Karatsuba multiplies `2 ^ k` coefficients with `3 ^ k` multiplications. -/
theorem mulCount_two_pow (k : ℕ) : mulCount (2 ^ k) = 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h2, h1, h3⟩ := two_pow_succ_facts k
    rw [mulCount_of_two_le h2, h3, h1, ih, pow_succ]
    ring

/-- Karatsuba multiplies `2 ^ k` coefficients with `(13 · 3 ^ k - 16 · 2 ^ k + 3) / 2` additions
and subtractions. -/
theorem addCount_two_pow (k : ℕ) : 2 * addCount (2 ^ k) + 16 * 2 ^ k = 13 * 3 ^ k + 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h2, h1, h3⟩ := two_pow_succ_facts k
    rw [addCount_of_two_le h2, h3, h1, pow_succ, pow_succ]
    have := Nat.one_le_two_pow (n := k)
    generalize 2 ^ k = N at *
    generalize 3 ^ k = T at *
    omega

/-! ### Upper bounds -/

/-- At most `3 ^ ⌈log₂ n⌉` multiplications. -/
theorem mulCount_le_pow_clog (n : ℕ) : mulCount n ≤ 3 ^ Nat.clog 2 n := by
  have := Nat.add_mul_two_pow_clog_le_of_halving (T := mulCount) (a := 3) (c := 0) (α := 1)
    (β := 0) (by norm_num) (by norm_num) ?base ?step n
  · simpa using this
  · intro n hn
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp
  · intro n hn S hS
    rw [mulCount_of_two_le hn]
    have := hS (n / 2) (by omega)
    have := hS (n - n / 2) (by omega)
    omega

/-- `addCount n + 8 · 2 ^ ⌈log₂ n⌉ ≤ 8 · 3 ^ ⌈log₂ n⌉`. -/
theorem addCount_add_le_pow_clog (n : ℕ) :
    addCount n + 8 * 2 ^ Nat.clog 2 n ≤ 8 * 3 ^ Nat.clog 2 n := by
  refine Nat.add_mul_two_pow_clog_le_of_halving (T := addCount) (a := 3) (c := 4) (α := 8)
    (β := 8) (by norm_num) (by norm_num) ?_ ?_ n
  · intro n hn
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp
  · intro n hn S hS
    rw [addCount_of_two_le hn]
    have := hS (n / 2) (by omega)
    have := hS (n - n / 2) (by omega)
    omega

/-- At most `8 · 3 ^ ⌈log₂ n⌉` additions and subtractions. -/
theorem addCount_le_pow_clog (n : ℕ) : addCount n ≤ 8 * 3 ^ Nat.clog 2 n :=
  (Nat.le_add_right _ _).trans (addCount_add_le_pow_clog n)

/-- At most `9 · 3 ^ ⌈log₂ n⌉` arithmetic operations in total. -/
theorem mulCount_add_addCount_le (n : ℕ) :
    mulCount n + addCount n ≤ 9 * 3 ^ Nat.clog 2 n := by
  have := mulCount_le_pow_clog n
  have := addCount_add_le_pow_clog n
  omega

/-! ### Lower bound and comparison with the schoolbook method -/

/-- At least `3 ^ ⌊log₂ n⌋` multiplications for `n ≠ 0`. -/
theorem pow_log_le_mulCount {n : ℕ} (hn : n ≠ 0) : 3 ^ Nat.log 2 n ≤ mulCount n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp
    · rw [mulCount_of_two_le h]
      have h1 := ih (n / 2) (by omega) (by omega)
      have h2 := ih (n - n / 2) (by omega) (by omega)
      have hlog : Nat.log 2 n = Nat.log 2 (n / 2) + 1 := by
        have := Nat.log_pos (b := 2) (by norm_num) h
        rw [Nat.log_div_base]
        omega
      have hmono : 3 ^ Nat.log 2 (n / 2) ≤ 3 ^ Nat.log 2 (n - n / 2) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.log_mono_right (by omega))
      rw [hlog, pow_succ]
      omega

/-- At most `n ^ 2` multiplications. -/
theorem mulCount_le_sq (n : ℕ) : mulCount n ≤ n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp
    · rw [mulCount_of_two_le h]
      have h1 := ih (n / 2) (by omega)
      have h2 := ih (n - n / 2) (by omega)
      obtain ⟨m, hm⟩ : ∃ m, n / 2 = m := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k, n - n / 2 = k := ⟨_, rfl⟩
      rw [hk] at h2 ⊢
      rw [hm] at h1 ⊢
      have hn : n = m + k := by omega
      have hkm : k ≤ m + 1 := by omega
      subst hn
      nlinarith

/-- Fewer than the `n ^ 2` coefficient products of the schoolbook method, for `n ≥ 2`. -/
theorem mulCount_lt_sq {n : ℕ} (hn : 2 ≤ n) : mulCount n < n ^ 2 := by
  rw [mulCount_of_two_le hn]
  have h1 := mulCount_le_sq (n / 2)
  have h2 := mulCount_le_sq (n - n / 2)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, n - n / 2 = k := ⟨_, rfl⟩
  rw [hk] at h2 ⊢
  rw [hm] at h1 ⊢
  have hn' : n = m + k := by omega
  have hkm : k ≤ m + 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hkm' : m ≤ k := by omega
  subst hn'
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    have h22 : mulCount 2 = 3 := by simpa using mulCount_two_pow 1
    rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · simp
    · simp [h22]
  · nlinarith

/-! ### Real-exponent bounds -/

/-- At most `3 n ^ log₂ 3` multiplications. -/
theorem mulCount_le_rpow (n : ℕ) : (mulCount n : ℝ) ≤ 3 * (n : ℝ) ^ Real.logb 2 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mulCount_zero, Nat.cast_zero]
    positivity
  · have h := Nat.pow_clog_two_le_mul_rpow_logb (a := 3) (by norm_num) hn.ne'
    have h' : (mulCount n : ℝ) ≤ ((3 ^ Nat.clog 2 n : ℕ) : ℝ) := by
      exact_mod_cast mulCount_le_pow_clog n
    push_cast at h h' ⊢
    linarith

/-- At most `27 n ^ log₂ 3` arithmetic operations in total. -/
theorem mulCount_add_addCount_le_rpow (n : ℕ) :
    ((mulCount n + addCount n : ℕ) : ℝ) ≤ 27 * (n : ℝ) ^ Real.logb 2 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mulCount_zero, addCount_zero, Nat.add_zero, Nat.cast_zero]
    positivity
  · have h := Nat.pow_clog_two_le_mul_rpow_logb (a := 3) (by norm_num) hn.ne'
    have h' : ((mulCount n + addCount n : ℕ) : ℝ) ≤ ((9 * 3 ^ Nat.clog 2 n : ℕ) : ℝ) := by
      exact_mod_cast mulCount_add_addCount_le n
    push_cast at h h' ⊢
    linarith

/-- At least `n ^ log₂ 3 / 3` multiplications. -/
theorem rpow_le_three_mul_mulCount (n : ℕ) :
    (n : ℝ) ^ Real.logb 2 3 ≤ 3 * mulCount n := by
  have h := Nat.rpow_logb_le_mul_pow_log_two (a := 3) (by norm_num) n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (Real.logb_pos one_lt_two (by norm_num)).ne']
    positivity
  · have hle : ((3 ^ Nat.log 2 n : ℕ) : ℝ) ≤ mulCount n := by
      exact_mod_cast pow_log_le_mulCount hn.ne'
    push_cast at h hle
    linarith

end Karatsuba

/-! ### Karatsuba on coefficient lists -/

/-- **Exact cost of Karatsuba multiplication.** Under every oracle, `karatsuba p q` makes
`mulCount N` multiplications and `addCount N` additions and subtractions, `N = max(|p|, |q|)`. -/
theorem cost_karatsuba [Zero α] (o : {ι : Type} → ArithQuery α ι → ι) (ca cm : ℕ)
    (p q : List α) :
    (karatsuba p q).cost o (weight ca cm) =
      cm * Karatsuba.mulCount (max p.length q.length) +
        ca * Karatsuba.addCount (max p.length q.length) :=
  Karatsuba.cost_mulFit o ca cm _ p q

/-- Under every oracle, `karatsuba p q` makes `mulCount N + addCount N` queries,
`N = max(|p|, |q|)`. -/
theorem countQueries_karatsuba [Zero α] (o : {ι : Type} → ArithQuery α ι → ι) (p q : List α) :
    (karatsuba p q).countQueries o =
      Karatsuba.mulCount (max p.length q.length) + Karatsuba.addCount (max p.length q.length) := by
  rw [ArithQuery.countQueries_eq_cost_weight_one, cost_karatsuba]
  ring

/-- **Karatsuba multiplication in `O(N ^ log₂ 3)` weighted operations**: at most
`(c_mul + 8 c_add) 3 ^ ⌈log₂ N⌉`, `N = max(|p|, |q|)`, under every oracle. -/
theorem cost_karatsuba_le [Zero α] (o : {ι : Type} → ArithQuery α ι → ι) (ca cm : ℕ)
    (p q : List α) :
    (karatsuba p q).cost o (weight ca cm) ≤
      (cm + 8 * ca) * 3 ^ Nat.clog 2 (max p.length q.length) := by
  rw [cost_karatsuba]
  have h1 := Nat.mul_le_mul_left cm (Karatsuba.mulCount_le_pow_clog (max p.length q.length))
  have h2 := Nat.mul_le_mul_left ca (Karatsuba.addCount_le_pow_clog (max p.length q.length))
  nlinarith

/-- Karatsuba multiplication makes at most `9 · 3 ^ ⌈log₂ n⌉` queries on operands of length at
most `n`, under every oracle. -/
theorem karatsuba_upperBound [Zero α] :
    UpperBound (fun pq : List α × List α => karatsuba pq.1 pq.2)
      (fun pq => max pq.1.length pq.2.length) (fun n => 9 * 3 ^ Nat.clog 2 n) := by
  refine UpperBound.of_pointwise ?_ ?_
  · intro a b hab
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 hab))
  · intro o pq
    rw [countQueries_karatsuba]
    exact Karatsuba.mulCount_add_addCount_le _

/-- The exact count is attained: for every `n`, operands of length `n` make
`mulCount n + addCount n` queries (under any oracle; the witness answers each query with its
first operand). With `karatsuba_upperBound` and `Karatsuba.rpow_le_three_mul_mulCount`, the query
complexity of Karatsuba multiplication is `Θ(n ^ log₂ 3)`. -/
theorem karatsuba_lowerBound [Zero α] :
    LowerBound (fun pq : List α × List α => karatsuba pq.1 pq.2)
      (fun pq => max pq.1.length pq.2.length)
      (fun n => Karatsuba.mulCount n + Karatsuba.addCount n) := by
  intro n
  refine ⟨(List.replicate n 0, List.replicate n 0), by simp, fun {ι} q => ?_, ?_⟩
  · cases q with
    | add a _ => exact a
    | sub a _ => exact a
    | mul a _ => exact a
  · rw [countQueries_karatsuba]
    simp

end Cslib.Query
