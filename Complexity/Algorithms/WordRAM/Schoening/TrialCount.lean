/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Schoening.Counter
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The trial count of Schöning's algorithm

Schöning's algorithm with confidence `c` runs
`schoeningTrials k n c = ⌈(3 n + 1) (2 (k - 1) / k) ^ n (k / (k - 1)) ^ (k - 3)⌉ c` trials on
`n` variables and clauses of at most `k` literals [Schöning][Schoening1999]. For `k = 3` this is
`⌈(3 n + 1) (4 / 3) ^ n⌉ c`, a number of about `0.415 n` bits.

The amplified algorithm computes this number on the word RAM with the multiword counter of
`Cslib.Algorithms.WordRAM.Schoening.mulAdd` and `Cslib.Algorithms.WordRAM.Schoening.divFloor`:
it forms the numerator `(3 n + 1) (2 (k - 1)) ^ n k ^ (k - 3)` by multiplications, divides it by
`k` `n` times and by `k - 1` `k - 3` times, rounding up each time, and multiplies by `c`.
`Cslib.Algorithms.WordRAM.Schoening.counterDigits` is the resulting digit list, and
`Cslib.Algorithms.WordRAM.Schoening.ofDigits_counterDigits` proves that its value is
`schoeningTrials k n c`: rounding up in stages is rounding up once, and the real expression is
this quotient of natural numbers.

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.schoeningTrials`: the trial count for confidence `c`.
* `Cslib.Algorithms.WordRAM.Schoening.mulStep`, `Cslib.Algorithms.WordRAM.Schoening.ceilStep`:
  multiplication and division rounding up on digit lists.
* `Cslib.Algorithms.WordRAM.Schoening.counterDigits`: the digits of the trial count, as computed.
* `Cslib.Algorithms.WordRAM.Schoening.counterLen`: a bound on their number.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.ofDigits_counterDigits`: the digits have the value
  `schoeningTrials k n c`.
* `Cslib.Algorithms.WordRAM.Schoening.length_counterDigits_le`: there are at most
  `counterLen k n c = O((n + k) log (n + k) + log c)` of them.
* `Cslib.Algorithms.WordRAM.Schoening.schoeningTrials_le`: the trial count is at most
  `(9 n + 4) (2 (k - 1) / k) ^ n c`.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

/-- The number of trials for confidence `c`:
`⌈(3 n + 1) (2 (k - 1) / k) ^ n (k / (k - 1)) ^ (k - 3)⌉ c`, the inverse of Schöning's bound
for one trial, rounded up, times `c`. For `k = 3` it is `⌈(3 n + 1) (4 / 3) ^ n⌉ c`. -/
noncomputable def schoeningTrials (k n c : ℕ) : ℕ :=
  ⌈(3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n * ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3)⌉₊ * c

/-- Rounding up a quotient of natural numbers. -/
theorem natCeil_natCast_div {m d : ℕ} (hd : 0 < d) :
    ⌈(m : ℝ) / d⌉₊ = (m + d - 1) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hd']
    have h := Nat.div_add_mod' (m + d - 1) d
    have hr := Nat.mod_lt (m + d - 1) hd
    have : m ≤ (m + d - 1) / d * d := by omega
    exact_mod_cast this
  · have hq := Nat.le_ceil ((m : ℝ) / d)
    rw [div_le_iff₀ hd'] at hq
    have hq' : m ≤ ⌈(m : ℝ) / d⌉₊ * d := by exact_mod_cast hq
    rw [Nat.div_le_iff_le_mul_add_pred hd, Nat.mul_comm]
    omega

/-- Rounding up in two stages is rounding up once. -/
theorem add_pred_div_add_pred_div {v a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((v + a - 1) / a + b - 1) / b = (v + a * b - 1) / (a * b) := by
  have h : v + a - 1 + a * (b - 1) = v + a * b - 1 := by
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]
    omega
  calc ((v + a - 1) / a + b - 1) / b = (v + a - 1 + a * (b - 1)) / a / b := by
        rw [Nat.add_mul_div_left _ _ ha, Nat.add_sub_assoc hb]
    _ = (v + a * b - 1) / (a * b) := by rw [Nat.div_div_eq_div_mul, h]

/-! ### The digits of the trial count -/

/-- Multiplication by `a` on digit lists. -/
def mulStep (a : ℕ) (ds : List ℕ) : List ℕ := mulAddDigits a 0 ds

/-- Division by `d`, rounding up, on digit lists: add `d - 1`, then divide. -/
def ceilStep (d : ℕ) (ds : List ℕ) : List ℕ := (divDigits d 0 (mulAddDigits 1 (d - 1) ds)).1

/-- The digits of `(3 n + 1) (2 (k - 1)) ^ n k ^ (k - 3)`, the numerator of the trial count. -/
def numeratorDigits (k n : ℕ) : List ℕ :=
  (mulStep k)^[k - 3] ((mulStep (2 * (k - 1)))^[n] (mulAddDigits 0 (3 * n + 1) []))

/-- **The digits of the trial count**, as the amplified algorithm computes them: the numerator,
divided by `k` `n` times and by `k - 1` `k - 3` times, rounding up, then multiplied by `c`. -/
def counterDigits (k n c : ℕ) : List ℕ :=
  mulAddDigits c 0 ((ceilStep (k - 1))^[k - 3] ((ceilStep k)^[n] (numeratorDigits k n)))

/-- A bound on the number of digits of the trial count. -/
def counterLen (k n c : ℕ) : ℕ :=
  (2 * n + 2 * k) * (Nat.digits 2 (3 * n + 2 * k)).length + (Nat.digits 2 c).length

theorem ofDigits_mulStep (a : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (mulStep a ds) = Nat.ofDigits 2 ds * a := by
  simp [mulStep, ofDigits_mulAddDigits]

theorem ofDigits_ceilStep {d : ℕ} (hd : 0 < d) (ds : List ℕ) :
    Nat.ofDigits 2 (ceilStep d ds) = (Nat.ofDigits 2 ds + d - 1) / d := by
  rw [ceilStep, ofDigits_divDigits_zero hd, ofDigits_mulAddDigits, Nat.mul_one,
    Nat.add_sub_assoc (by omega)]

theorem ofDigits_mulStep_iterate (a m : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 ((mulStep a)^[m] ds) = Nat.ofDigits 2 ds * a ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ofDigits_mulStep, ih, pow_succ, Nat.mul_assoc]

theorem ofDigits_ceilStep_iterate {d : ℕ} (hd : 0 < d) (m : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 ((ceilStep d)^[m] ds) = (Nat.ofDigits 2 ds + d ^ m - 1) / d ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ofDigits_ceilStep hd, ih,
      add_pred_div_add_pred_div (by positivity) hd, pow_succ]

/-- The trial count as a quotient of natural numbers, rounded up. -/
theorem schoeningTrials_eq {k : ℕ} (hk : 3 ≤ k) (n c : ℕ) :
    schoeningTrials k n c =
      ((3 * n + 1) * (2 * (k - 1)) ^ n * k ^ (k - 3) + k ^ n * (k - 1) ^ (k - 3) - 1) /
        (k ^ n * (k - 1) ^ (k - 3)) * c := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have hden : 0 < k ^ n * (k - 1) ^ (k - 3) :=
    Nat.mul_pos (by positivity) (pow_pos (by omega : 0 < k - 1) _)
  rw [schoeningTrials, ← natCeil_natCast_div hden]
  congr 2
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  push_cast [hcast]
  simp only [div_pow]
  have hp0 : (k : ℝ) ^ n ≠ 0 := pow_ne_zero _ hk0
  have hp1 : ((k : ℝ) - 1) ^ (k - 3) ≠ 0 := pow_ne_zero _ hk1
  field_simp

/-- **The value of the counter digits** is the trial count. -/
theorem ofDigits_counterDigits {k : ℕ} (hk : 3 ≤ k) (n c : ℕ) :
    Nat.ofDigits 2 (counterDigits k n c) = schoeningTrials k n c := by
  rw [schoeningTrials_eq hk, counterDigits, ofDigits_mulAddDigits, Nat.add_zero,
    ofDigits_ceilStep_iterate (by omega), ofDigits_ceilStep_iterate (by omega), numeratorDigits,
    ofDigits_mulStep_iterate, ofDigits_mulStep_iterate, ofDigits_mulAddDigits,
    add_pred_div_add_pred_div (by positivity) (pow_pos (by omega : 0 < k - 1) _)]
  simp

/-! ### The number of digits -/

theorem mulStep_digit_le (a : ℕ) (ds : List ℕ) : ∀ d ∈ mulStep a ds, d ≤ 1 :=
  mulAddDigits_digit_le a 0 ds

theorem ceilStep_digit_le {d : ℕ} (hd : 0 < d) (ds : List ℕ) : ∀ e ∈ ceilStep d ds, e ≤ 1 :=
  divDigits_digit_le hd hd (mulAddDigits_digit_le 1 (d - 1) ds)

theorem length_le_length_mulStep (a : ℕ) (ds : List ℕ) : ds.length ≤ (mulStep a ds).length :=
  length_le_length_mulAddDigits a 0 ds

theorem length_le_length_ceilStep (d : ℕ) (ds : List ℕ) : ds.length ≤ (ceilStep d ds).length := by
  rw [ceilStep, length_divDigits]
  exact length_le_length_mulAddDigits 1 (d - 1) ds

theorem length_mulStep_le {a B : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (ha : a ≤ B) :
    (mulStep a ds).length ≤ ds.length + (Nat.digits 2 B).length :=
  length_mulAddDigits_le hds ha (Nat.zero_le B)

theorem length_ceilStep_le {d B : ℕ} {ds : List ℕ} (hds : ∀ e ∈ ds, e ≤ 1) (hd : 0 < d)
    (hdB : d ≤ B) : (ceilStep d ds).length ≤ ds.length + (Nat.digits 2 B).length := by
  rw [ceilStep, length_divDigits]
  exact length_mulAddDigits_le hds (by omega) (by omega)

/-- Iterating a step that keeps digits binary and adds at most `D` digits. -/
theorem length_iterate_le {F : List ℕ → List ℕ} {D : ℕ}
    (hbin : ∀ ds, (∀ d ∈ ds, d ≤ 1) → ∀ d ∈ F ds, d ≤ 1)
    (hlen : ∀ ds, (∀ d ∈ ds, d ≤ 1) → (F ds).length ≤ ds.length + D) (m : ℕ) {ds : List ℕ}
    (hds : ∀ d ∈ ds, d ≤ 1) :
    (F^[m] ds).length ≤ ds.length + m * D ∧ ∀ d ∈ F^[m] ds, d ≤ 1 := by
  induction m with
  | zero => simpa using hds
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨?_, hbin _ ih.2⟩
    have := hlen _ ih.2
    rw [Nat.succ_mul]
    omega

/-- Iterating a step that does not shorten the list. -/
theorem length_iterate_mono {F : List ℕ → List ℕ} (hF : ∀ ds, ds.length ≤ (F ds).length)
    {i j : ℕ} (hij : i ≤ j) (ds : List ℕ) : (F^[i] ds).length ≤ (F^[j] ds).length := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · rw [Function.iterate_succ_apply']
      exact (ih (by omega)).trans (hF _)
    · rw [Nat.le_antisymm hij h]

/-- The digits of the numerator are binary, and there are at most
`(1 + n + (k - 3)) D` of them, with `D` the number of digits of `3 n + 2 k`. -/
theorem numeratorDigits_bound {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (numeratorDigits k n).length ≤ (1 + n + (k - 3)) * (Nat.digits 2 (3 * n + 2 * k)).length ∧
      ∀ d ∈ numeratorDigits k n, d ≤ 1 := by
  set D := (Nat.digits 2 (3 * n + 2 * k)).length
  have h0 : (mulAddDigits 0 (3 * n + 1) []).length ≤ D := by
    have := length_mulAddDigits_le (a := 0) (cy := 3 * n + 1) (ds := []) (B := 3 * n + 2 * k)
      (by simp) (by omega)
      (show 3 * n + 1 ≤ 3 * n + 2 * k by omega)
    simpa using this
  have h1 := length_iterate_le (F := mulStep (2 * (k - 1))) (D := D)
    (fun ds _ => mulStep_digit_le _ ds)
    (fun ds hds => length_mulStep_le (B := 3 * n + 2 * k) hds (by omega)) n
    (mulAddDigits_digit_le 0 (3 * n + 1) [])
  have h2 := length_iterate_le (F := mulStep k) (D := D)
    (fun ds _ => mulStep_digit_le _ ds)
    (fun ds hds => length_mulStep_le (B := 3 * n + 2 * k) hds (by omega)) (k - 3)
    h1.2
  refine ⟨?_, h2.2⟩
  rw [numeratorDigits]
  have := h1.1
  have := h2.1
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

/-- **The number of digits** of the trial count is at most `counterLen k n c`. -/
theorem length_counterDigits_le {k : ℕ} (hk : 3 ≤ k) (n c : ℕ) :
    (counterDigits k n c).length ≤ counterLen k n c := by
  rw [counterDigits, counterLen]
  obtain ⟨hn, hnb⟩ := numeratorDigits_bound hk n
  set D := (Nat.digits 2 (3 * n + 2 * k)).length
  have h3 := length_iterate_le (F := ceilStep k) (D := D)
    (fun ds _ => ceilStep_digit_le (by omega) ds)
    (fun ds hds => length_ceilStep_le (B := 3 * n + 2 * k) hds (by omega) (by omega)) n hnb
  have h4 := length_iterate_le (F := ceilStep (k - 1)) (D := D)
    (fun ds _ => ceilStep_digit_le (by omega) ds)
    (fun ds hds => length_ceilStep_le (B := 3 * n + 2 * k) hds (by omega) (by omega)) (k - 3) h3.2
  have h5 := length_mulAddDigits_le h4.2 (le_refl c) (Nat.zero_le c)
  have := h3.1
  have := h4.1
  have : (1 + n + (k - 3)) * D + n * D + (k - 3) * D ≤ (2 * n + 2 * k) * D := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- The digits of the trial count are binary. -/
theorem counterDigits_digit_le (k n c : ℕ) :
    ∀ d ∈ counterDigits k n c, d ≤ 1 :=
  mulAddDigits_digit_le c 0 _

/-- Every intermediate digit list of the computation of the trial count is at most as long as the
final one: the multiplications by `2 (k - 1)`, by `k`, and the divisions by `k` and by
`k - 1`. -/
theorem length_stages_le (k n c : ℕ) :
    (∀ i ≤ n, ((mulStep (2 * (k - 1)))^[i] (mulAddDigits 0 (3 * n + 1) [])).length ≤
        (counterDigits k n c).length) ∧
      (∀ i ≤ k - 3, ((mulStep k)^[i] ((mulStep (2 * (k - 1)))^[n]
        (mulAddDigits 0 (3 * n + 1) []))).length ≤ (counterDigits k n c).length) ∧
      (∀ i ≤ n, ((ceilStep k)^[i] (numeratorDigits k n)).length ≤
        (counterDigits k n c).length) ∧
      (∀ i ≤ k - 3, ((ceilStep (k - 1))^[i] ((ceilStep k)^[n] (numeratorDigits k n))).length ≤
        (counterDigits k n c).length) := by
  have hm (a : ℕ) := length_le_length_mulStep a
  have hc (d : ℕ) := length_le_length_ceilStep d
  have h4 : ∀ i ≤ k - 3, ((ceilStep (k - 1))^[i] ((ceilStep k)^[n]
      (numeratorDigits k n))).length ≤ (counterDigits k n c).length := fun i hi =>
    (length_iterate_mono (hc _) hi _).trans (length_le_length_mulAddDigits c 0 _)
  have h3 : ∀ i ≤ n, ((ceilStep k)^[i] (numeratorDigits k n)).length ≤
      (counterDigits k n c).length := fun i hi =>
    (length_iterate_mono (hc _) hi _).trans (h4 0 (Nat.zero_le _))
  have h2 : ∀ i ≤ k - 3, ((mulStep k)^[i] ((mulStep (2 * (k - 1)))^[n]
      (mulAddDigits 0 (3 * n + 1) []))).length ≤ (counterDigits k n c).length := fun i hi =>
    (length_iterate_mono (hm _) hi _).trans (h3 0 (Nat.zero_le _))
  exact ⟨fun i hi => (length_iterate_mono (hm _) hi _).trans (h2 0 (Nat.zero_le _)), h2, h3, h4⟩

/-! ### Size bounds -/

/-- `(k / (k - 1)) ^ (k - 3) ≤ 3` for `k ≥ 3`: the constant factor of the trial count. -/
theorem div_sub_one_pow_le_three {k : ℕ} (hk : 3 ≤ k) :
    ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) ≤ 3 := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have h1 : (k : ℝ) / ((k : ℝ) - 1) = 1 / ((k : ℝ) - 1) + 1 := by field_simp; ring
  have hcast : ((k - 3 : ℕ) : ℝ) = (k : ℝ) - 3 := by rw [Nat.cast_sub hk]; norm_num
  calc ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) ≤ Real.exp (1 / ((k : ℝ) - 1)) ^ (k - 3) := by
        rw [h1]
        exact pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
    _ = Real.exp ((k - 3 : ℕ) * (1 / ((k : ℝ) - 1))) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp 1 := by
        rw [Real.exp_le_exp, hcast, ← mul_div_assoc, mul_one, div_le_one hk1]
        linarith
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- **The size of the trial count**: at most `(9 n + 4) (2 (k - 1) / k) ^ n c`. -/
theorem schoeningTrials_le {k : ℕ} (hk : 3 ≤ k) (n c : ℕ) :
    (schoeningTrials k n c : ℝ) ≤ (9 * n + 4) * (2 * ((k : ℝ) - 1) / k) ^ n * c := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 1 ≤ 2 * ((k : ℝ) - 1) / k := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hrn : 1 ≤ (2 * ((k : ℝ) - 1) / k) ^ n := one_le_pow₀ hr
  have hq := div_sub_one_pow_le_three hk
  have hq0 : 0 ≤ ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) := by
    apply pow_nonneg; apply div_nonneg <;> linarith
  set A := (3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n * ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3)
  have hA0 : 0 ≤ A := by positivity
  have hA : A ≤ 3 * (3 * n + 1) * (2 * ((k : ℝ) - 1) / k) ^ n := by
    have : (3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n * ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) ≤
        (3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n * 3 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    linarith
  have hceil : (⌈A⌉₊ : ℝ) ≤ (9 * n + 4) * (2 * ((k : ℝ) - 1) / k) ^ n := by
    have := Nat.ceil_lt_add_one hA0
    nlinarith
  rw [schoeningTrials]
  push_cast
  exact mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg c)

/-- The number of counter digits is at most `6 (n + k) ^ 2 + c`. -/
theorem counterLen_le (k n c : ℕ) : counterLen k n c ≤ 6 * (n + k) ^ 2 + c := by
  have h1 : (Nat.digits 2 (3 * n + 2 * k)).length ≤ 3 * n + 2 * k :=
    (Nat.digits_length_le_iff (by decide) _).mpr Nat.lt_two_pow_self
  have h2 : (Nat.digits 2 c).length ≤ c := (Nat.digits_length_le_iff (by decide) _).mpr
    Nat.lt_two_pow_self
  have h3 := Nat.mul_le_mul_left (2 * n + 2 * k) h1
  rw [counterLen]
  nlinarith

end Cslib.Algorithms.WordRAM.Schoening

end
