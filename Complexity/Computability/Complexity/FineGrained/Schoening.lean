/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Flip
public import Complexity.Logics.Propositional.CNF
public import Mathlib.InformationTheory.Hamming
public import Complexity.Probability.PMF
import Complexity.Foundations.Data.BitString.Hamming
import Complexity.Probability.PMF.Event
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Schöning's random walk for k-SAT

Schöning's algorithm searches for a satisfying assignment of a CNF formula by local search with
restarts. One *trial* draws a uniformly random assignment and then performs `3 n` steps, where `n`
is the number of variables. Each step stops if the formula is satisfied. Otherwise it takes the
first unsatisfied clause, chooses one of its literal occurrences uniformly, and flips that
variable (`Cslib.Complexity.Schoening.walk`, `Cslib.Complexity.Schoening.trial`)
[Schöning][Schoening1999].

For `k ≥ 3` and a satisfiable formula whose clauses have at most `k` literals, a trial succeeds
with probability at least `((k - 1)/k)^{k - 3} (k / (2(k - 1)))^n / (3 n + 1)`
(`Cslib.Complexity.Schoening.trial_success_of_length_le`); for `k = 3` this is
`(3 / 4) ^ n / (3 n + 1)` (`Cslib.Complexity.Schoening.trial_success`). So about
`(2 - 2/k)^n` independent trials find a satisfying assignment with high probability, exponentially
faster than the `2 ^ n` assignments of brute force. Schöning states the bound up to a polynomial
factor; the factors `((k - 1)/k)^{k - 3}` and `1 / (3 n + 1)` are this file's explicit constants.

The proof compares the walk with a biased random walk on distances. Fix a satisfying assignment
`σ⋆`. A step changes the Hamming distance to `σ⋆` by one. Since `σ⋆` satisfies the chosen clause
and the current assignment does not, at least one of its at most `k` literals moves toward `σ⋆`.
Let `hit k t d` be the probability that a walk on `ℕ`, stepping down with probability `1 / k` and
up with probability `(k - 1) / k`, reaches `0` from `d` within `t` steps
(`Cslib.Complexity.Schoening.hit`). It is antitone in `d` (`hit_succ_le`), so by induction on `t`
the trial walk succeeds with probability at least `hit k t (dist σ σ⋆)` (`hit_le_succeedProb`).
No coupling is needed.

Write `d = (k - 2) i + e` with `e < k - 2`. A path of `i + d` down-steps and `i` up-steps reaches
`0` from `d` within `ki + e ≤ 3d` steps (`choose_mul_le_hit`). The middle weight
`C(ki, i) (k - 1)^{ki - i}` is the largest of the `ki + 1` terms of `((k - 1) + 1)^{ki}`
(`pow_le_choose_mul`), which gives `hit k (3 d) d ≥ ((k - 1)/k)^{k - 3} (k - 1)^{-d} / (3 d + 1)`
(`inv_le_hit`). Averaging `(k - 1)^{-dist}` over a uniform start gives `(k / (2(k - 1)))^n`, a
product over the coordinates (`sum_pow_hammingDist`).

## Main definitions

* `Cslib.Complexity.Schoening.walk`: `t` steps of the local search from an assignment.
* `Cslib.Complexity.Schoening.trial`: a uniform start followed by `3 n` steps.
* `Cslib.Complexity.Schoening.hit`: hitting probabilities of the biased walk.

## Main results

* `Cslib.Complexity.Schoening.hit_le_succeedProb`: the local search dominates the biased walk.
* `Cslib.Complexity.Schoening.choose_mul_le_hit`: path counting for the biased walk.
* `Cslib.Complexity.Schoening.pow_le_choose_mul`: `k^{ki} ≤ C(ki, i) (k - 1)^{ki - i} (ki + 1)`.
* `Cslib.Complexity.Schoening.inv_le_hit`: the hitting bound from distance `d` within `3 d` steps.
* `Cslib.Complexity.Schoening.trial_success_of_length_le`: Schöning's bound for k-SAT.
* `Cslib.Complexity.Schoening.trial_success`: a trial for 3-SAT succeeds with probability at
  least `(3 / 4) ^ n / (3 n + 1)`.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Complexity.Schoening

open Cslib.BitString Cslib.Logic.PL Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The algorithm -/

/-- The first clause of `φ` that `σ` falsifies, if any. -/
def firstUnsat (φ : CNF V) (σ : V → Bool) : Option (Clause V) :=
  φ.find? fun c => !c.eval σ

/-- Flip the variable of a uniformly chosen literal occurrence of `c`. The empty clause, which no
assignment satisfies, leaves the assignment unchanged. -/
noncomputable def flipStep (c : Clause V) (σ : V → Bool) : PMF (V → Bool) :=
  if h : c.length = 0 then PMF.pure σ else
    haveI : NeZero c.length := ⟨h⟩
    (Probability.PMF.uniformOfFintype (Fin c.length)).map fun i => flipOn {(c.get i).1} σ

/-- **Schöning's local search**: `t` steps from `σ`. Each step stops if `φ` is satisfied, and
otherwise flips a uniformly chosen variable of the first unsatisfied clause. -/
noncomputable def walk (φ : CNF V) : ℕ → (V → Bool) → PMF (V → Bool)
  | 0, σ => PMF.pure σ
  | t + 1, σ =>
    match firstUnsat φ σ with
    | none => PMF.pure σ
    | some c => (flipStep c σ).bind (walk φ t)

/-- **One trial of Schöning's algorithm**: a uniformly random assignment followed by `3 n` steps of
local search, where `n` is the number of variables. -/
noncomputable def trial (φ : CNF V) : PMF (V → Bool) :=
  (Probability.PMF.uniformOfFintype (V → Bool)).bind (walk φ (3 * Fintype.card V))

/-- The probability that `μ` produces an assignment satisfying `φ`. -/
noncomputable def succeedProb (φ : CNF V) (μ : PMF (V → Bool)) : ℝ :=
  (μ.toOuterMeasure {σ | φ.eval σ = true}).toReal

/-! ### The biased walk -/

/-- The probability that a walk on `ℕ` that steps down with probability `1 / k` and up with
probability `(k - 1) / k` reaches `0` from `d` within `t` steps. -/
noncomputable def hit (k : ℕ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | t + 1, d + 1 => (hit k t d + ((k : ℝ) - 1) * hit k t (d + 2)) / k

variable {k : ℕ}

@[simp] theorem hit_zero_right (k t : ℕ) : hit k t 0 = 1 := by cases t <;> rfl

@[simp] theorem hit_zero_succ (k d : ℕ) : hit k 0 (d + 1) = 0 := rfl

theorem hit_succ_succ (k t d : ℕ) :
    hit k (t + 1) (d + 1) = (hit k t d + ((k : ℝ) - 1) * hit k t (d + 2)) / k :=
  rfl

theorem hit_nonneg (hk : 1 ≤ k) (t d : ℕ) : 0 ≤ hit k t d := by
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  induction t generalizing d with
  | zero => cases d <;> simp
  | succ t ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [hit_succ_succ]
      have := ih d
      have := ih (d + 2)
      positivity

theorem hit_le_one (hk : 1 ≤ k) (t d : ℕ) : hit k t d ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction t generalizing d with
  | zero => cases d <;> simp
  | succ t ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [hit_succ_succ, div_le_one (by linarith)]
      nlinarith [ih d, ih (d + 2), hit_nonneg hk t (d + 2)]

/-- Hitting `0` is less likely from farther away. -/
theorem hit_succ_le (hk : 1 ≤ k) (t d : ℕ) : hit k t (d + 1) ≤ hit k t d := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction t generalizing d with
  | zero => simpa using hit_nonneg hk 0 d
  | succ t ih =>
    cases d with
    | zero => simpa using hit_le_one hk (t + 1) 1
    | succ d =>
      rw [hit_succ_succ, hit_succ_succ]
      gcongr ?_ / _
      nlinarith [ih d, ih (d + 2)]

theorem hit_antitone (hk : 1 ≤ k) (t : ℕ) : Antitone (hit k t) :=
  antitone_nat_of_succ_le (hit_succ_le hk t)

/-- Hitting `0` is more likely with more time. -/
theorem hit_le_hit_succ (hk : 1 ≤ k) (t d : ℕ) : hit k t d ≤ hit k (t + 1) d := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction t generalizing d with
  | zero => cases d <;> simp [hit_nonneg hk]
  | succ t ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [hit_succ_succ, hit_succ_succ (t := t + 1)]
      gcongr ?_ / _
      nlinarith [ih d, ih (d + 2)]

theorem hit_monotone (hk : 1 ≤ k) (d : ℕ) : Monotone fun t => hit k t d :=
  monotone_nat_of_le_succ fun t => hit_le_hit_succ hk t d

/-- A single binomial weight is at most one. -/
private theorem choose_mul_pow_le_one (hk : 1 ≤ k) (m a b : ℕ) (h : a + b = m) :
    (m.choose a : ℝ) * (1 / k) ^ b * (((k : ℝ) - 1) / k) ^ a ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsum := add_pow (((k : ℝ) - 1) / k) (1 / k) m
  rw [show ((k : ℝ) - 1) / k + 1 / k = 1 by field_simp; ring, one_pow] at hsum
  have ha : a ∈ range (m + 1) := mem_range.mpr (by omega)
  have hle := single_le_sum
    (f := fun i => (((k : ℝ) - 1) / k) ^ i * (1 / k) ^ (m - i) * (m.choose i))
    (fun i _ => by have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
                   positivity) ha
  rw [← hsum, show m - a = b by omega] at hle
  linarith

/-- **Path counting.** Any sequence of `b` down-steps and `a` up-steps with `d + a ≤ b` reaches `0`
from `d`, so the biased walk reaches `0` from `d` within `a + b` steps with probability at least
`C(a + b, a) (1/k)^b ((k - 1)/k)^a`. -/
theorem choose_mul_le_hit (hk : 1 ≤ k) (a b d : ℕ) (h : d + a ≤ b) :
    ((a + b).choose a : ℝ) * (1 / k) ^ b * (((k : ℝ) - 1) / k) ^ a ≤ hit k (a + b) d := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  induction hm : a + b generalizing a b d with
  | zero =>
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    obtain rfl : d = 0 := by omega
    simp
  | succ m ih =>
    cases d with
    | zero => simpa using choose_mul_pow_le_one hk (m + 1) a b hm
    | succ d =>
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [hit_succ_succ]
      have h₁ := ih a b d (by omega) (by omega)
      have hB := hit_nonneg hk m (d + 2)
      cases a with
      | zero =>
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one] at h₁ ⊢
        rw [pow_succ, le_div_iff₀ hk0]
        have : (1 / (k : ℝ)) ^ b * (1 / k) * k = (1 / k) ^ b := by field_simp
        nlinarith [mul_nonneg hkm hB]
      | succ a =>
        have h₂ := ih a (b + 1) (d + 2) (by omega) (by omega)
        rw [Nat.choose_succ_succ, Nat.cast_add]
        calc
          ((m.choose a : ℝ) + m.choose (a + 1)) * (1 / k) ^ (b + 1) *
              (((k : ℝ) - 1) / k) ^ (a + 1) =
              ((m.choose (a + 1) : ℝ) * (1 / k) ^ b * (((k : ℝ) - 1) / k) ^ (a + 1) +
                ((k : ℝ) - 1) * ((m.choose a : ℝ) * (1 / k) ^ (b + 1) *
                  (((k : ℝ) - 1) / k) ^ a)) / k := by
            rw [eq_div_iff hkne]
            have hkk : (k : ℝ) * (k : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hkne
            linear_combination ((m.choose a : ℝ) + m.choose (a + 1)) * ((k : ℝ)⁻¹) ^ b *
              (((k : ℝ) - 1) * (k : ℝ)⁻¹) ^ (a + 1) * hkk
          _ ≤ (hit k m d + ((k : ℝ) - 1) * hit k m (d + 2)) / k := by gcongr

/-! ### The middle binomial weight -/

/-- The weights `C(ki, a) (k - 1)^{ki - a}` of `((k - 1) + 1)^{ki}` increase up to `a = i`. -/
private theorem weight_le_succ {k i a : ℕ} (hk : 1 ≤ k) (ha : a < i) :
    (k * i).choose a * (k - 1) ^ (k * i - a) ≤
      (k * i).choose (a + 1) * (k - 1) ^ (k * i - (a + 1)) := by
  have hrec := Nat.choose_succ_right_eq (k * i) a
  have hai : a + 1 ≤ k * i := le_trans ha (Nat.le_mul_of_pos_left i hk)
  have hpow : (k - 1) ^ (k * i - a) = (k - 1) * (k - 1) ^ (k * i - (a + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcoef : (k - 1) * (a + 1) ≤ k * i - a := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (k' + 1) * (a + 1) ≤ (k' + 1) * i := Nat.mul_le_mul_left _ ha
    have : k' * (a + 1) + (a + 1) = (k' + 1) * (a + 1) := by ring
    omega
  rw [hpow]
  have key : (k * i).choose a * ((k - 1) * (k - 1) ^ (k * i - (a + 1))) * (a + 1) ≤
      (k * i).choose (a + 1) * (k - 1) ^ (k * i - (a + 1)) * (a + 1) := by
    calc
      (k * i).choose a * ((k - 1) * (k - 1) ^ (k * i - (a + 1))) * (a + 1) =
          (k * i).choose a * ((k - 1) * (a + 1)) * (k - 1) ^ (k * i - (a + 1)) := by ring
      _ ≤ (k * i).choose a * (k * i - a) * (k - 1) ^ (k * i - (a + 1)) := by gcongr
      _ = (k * i).choose (a + 1) * (k - 1) ^ (k * i - (a + 1)) * (a + 1) := by
        rw [← hrec]
        ring
  exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos a)

/-- The weights `C(ki, a) (k - 1)^{ki - a}` of `((k - 1) + 1)^{ki}` decrease from `a = i`. -/
private theorem weight_succ_le {k i a : ℕ} (hk : 1 ≤ k) (ha : i ≤ a) :
    (k * i).choose (a + 1) * (k - 1) ^ (k * i - (a + 1)) ≤
      (k * i).choose a * (k - 1) ^ (k * i - a) := by
  rcases lt_or_ge a (k * i) with hlt | hge
  · have hrec := Nat.choose_succ_right_eq (k * i) a
    have hpow : (k - 1) ^ (k * i - a) = (k - 1) * (k - 1) ^ (k * i - (a + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have hcoef : k * i - a ≤ (k - 1) * (a + 1) := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : (k' + 1) * i ≤ (k' + 1) * a := Nat.mul_le_mul_left _ ha
      have : k' * (a + 1) + (a + 1) = (k' + 1) * a + (k' + 1) := by ring
      omega
    rw [hpow]
    have key : (k * i).choose (a + 1) * (k - 1) ^ (k * i - (a + 1)) * (a + 1) ≤
        (k * i).choose a * ((k - 1) * (k - 1) ^ (k * i - (a + 1))) * (a + 1) := by
      calc
        (k * i).choose (a + 1) * (k - 1) ^ (k * i - (a + 1)) * (a + 1) =
            (k * i).choose a * (k * i - a) * (k - 1) ^ (k * i - (a + 1)) := by
          rw [← hrec]
          ring
        _ ≤ (k * i).choose a * ((k - 1) * (a + 1)) * (k - 1) ^ (k * i - (a + 1)) := by gcongr
        _ = (k * i).choose a * ((k - 1) * (k - 1) ^ (k * i - (a + 1))) * (a + 1) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos a)
  · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    exact Nat.zero_le _

/-- The middle weight `C(ki, i) (k - 1)^{ki - i}` is the largest weight of `((k - 1) + 1)^{ki}`. -/
private theorem weight_le_middle {k : ℕ} (hk : 1 ≤ k) (i a : ℕ) :
    (k * i).choose a * (k - 1) ^ (k * i - a) ≤ (k * i).choose i * (k - 1) ^ (k * i - i) := by
  rcases le_total a i with hai | hai
  · have key : ∀ m a, a + m = i →
        (k * i).choose a * (k - 1) ^ (k * i - a) ≤ (k * i).choose i * (k - 1) ^ (k * i - i) := by
      intro m
      induction m with
      | zero => intro a ha; subst ha; rfl
      | succ m ih =>
        intro a ha
        exact (weight_le_succ hk (by omega)).trans (ih (a + 1) (by omega))
    exact key (i - a) a (by omega)
  · have key : ∀ m, (k * i).choose (i + m) * (k - 1) ^ (k * i - (i + m)) ≤
        (k * i).choose i * (k - 1) ^ (k * i - i) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => exact (weight_succ_le (a := i + m) hk (by omega)).trans ih
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hai
    exact key m

/-- **The middle binomial weight**: `k^{ki} ≤ C(ki, i) (k - 1)^{ki - i} (ki + 1)`, since the middle
weight is the largest of the `ki + 1` weights of `((k - 1) + 1)^{ki}`. -/
theorem pow_le_choose_mul (hk : 1 ≤ k) (i : ℕ) :
    k ^ (k * i) ≤ (k * i).choose i * (k - 1) ^ (k * i - i) * (k * i + 1) := by
  have hsum : k ^ (k * i) = ∑ a ∈ range (k * i + 1), (k * i).choose a * (k - 1) ^ (k * i - a) := by
    have h := add_pow (1 : ℕ) (k - 1) (k * i)
    rw [show 1 + (k - 1) = k by omega] at h
    rw [h]
    exact sum_congr rfl fun a _ => by rw [one_pow, one_mul, mul_comm, Nat.cast_id]
  rw [hsum]
  calc
    ∑ a ∈ range (k * i + 1), (k * i).choose a * (k - 1) ^ (k * i - a) ≤
        ∑ _a ∈ range (k * i + 1), (k * i).choose i * (k - 1) ^ (k * i - i) :=
      sum_le_sum fun a _ => weight_le_middle hk i a
    _ = (k * i).choose i * (k - 1) ^ (k * i - i) * (k * i + 1) := by
      rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-- From distance `d`, the biased walk reaches `0` within `3 d` steps with probability at least
`((k - 1)/k)^{k - 3} (k - 1)^{-d} / (3 d + 1)`, for `k ≥ 3`. Write `d = (k - 2) i + e` with
`e < k - 2`; the paths with `i` up-steps and `i + d` down-steps have length `ki + e ≤ 3d`. -/
theorem inv_le_hit (hk : 3 ≤ k) (d : ℕ) :
    (((k : ℝ) - 1) / k) ^ (k - 3) * (1 / ((k : ℝ) - 1)) ^ d / (3 * d + 1) ≤ hit k (3 * d) d := by
  set i := d / (k - 2)
  set e := d % (k - 2)
  have hdie : (k - 2) * i + e = d := Nat.div_add_mod d (k - 2)
  have he : e ≤ k - 3 := by
    have := Nat.mod_lt d (show 0 < k - 2 by omega)
    omega
  have hlen : i + (i + d) = k * i + e := by
    rw [← hdie]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hid : i ≤ d := Nat.div_le_self d (k - 2)
  have hki : k * i ≤ 3 * d := by omega
  have hpath := choose_mul_le_hit (by omega : 1 ≤ k) i (i + d) d (by omega)
  have hmono : hit k (i + (i + d)) d ≤ hit k (3 * d) d :=
    hit_monotone (by omega) d (by omega)
  refine le_trans ?_ (hpath.trans hmono)
  -- The natural-number inequality behind the bound.
  have hmode := pow_le_choose_mul (by omega : 1 ≤ k) i
  have hnat : (k - 1) ^ (k - 3) * k ^ (i + (i + d)) ≤
      (i + (i + d)).choose i * (k - 1) ^ (i + d) * k ^ (k - 3) * (3 * d + 1) := by
    obtain ⟨f, hf⟩ : ∃ f, k - 3 = e + f := ⟨k - 3 - e, by omega⟩
    have hid' : i + d = (k * i - i) + e := by omega
    rw [hlen, hf, hid', pow_add, pow_add, pow_add, pow_add]
    calc
      (k - 1) ^ e * (k - 1) ^ f * (k ^ (k * i) * k ^ e) ≤
          (k - 1) ^ e * (k - 1) ^ f *
            ((k * i).choose i * (k - 1) ^ (k * i - i) * (k * i + 1) * k ^ e) := by gcongr
      _ ≤ (k - 1) ^ e * k ^ f *
            ((k * i).choose i * (k - 1) ^ (k * i - i) * (k * i + 1) * k ^ e) := by
        gcongr
        omega
      _ = (k * i).choose i * ((k - 1) ^ (k * i - i) * (k - 1) ^ e) * (k ^ e * k ^ f) *
            (k * i + 1) := by ring
      _ ≤ (k * i + e).choose i * ((k - 1) ^ (k * i - i) * (k - 1) ^ e) * (k ^ e * k ^ f) *
            (3 * d + 1) := by
        gcongr
        omega
  -- Transfer to the reals.
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hreal : ((k : ℝ) - 1) ^ (k - 3) * (k : ℝ) ^ (i + (i + d)) ≤
      ((i + (i + d)).choose i : ℝ) * ((k : ℝ) - 1) ^ (i + d) * (k : ℝ) ^ (k - 3) *
        (3 * d + 1) := by
    rw [← hcast]
    exact_mod_cast hnat
  have hpos1 : (0 : ℝ) < ((k : ℝ) - 1) := by linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_pow, div_pow, div_pow, one_pow, one_pow]
  rw [show ((k : ℝ) - 1) ^ (k - 3) / (k : ℝ) ^ (k - 3) * (1 / ((k : ℝ) - 1) ^ d) =
      ((k : ℝ) - 1) ^ (k - 3) / ((k : ℝ) ^ (k - 3) * ((k : ℝ) - 1) ^ d) by
    field_simp]
  rw [div_le_iff₀ (by positivity)]
  have hsplit : (k : ℝ) ^ (i + (i + d)) = (k : ℝ) ^ (i + d) * (k : ℝ) ^ i := by
    rw [← pow_add]
    congr 1
    ring
  calc
    ((k : ℝ) - 1) ^ (k - 3) =
        ((k : ℝ) - 1) ^ (k - 3) * (k : ℝ) ^ (i + (i + d)) / (k : ℝ) ^ (i + (i + d)) := by
      field_simp
    _ ≤ ((i + (i + d)).choose i : ℝ) * ((k : ℝ) - 1) ^ (i + d) * (k : ℝ) ^ (k - 3) *
          (3 * d + 1) / (k : ℝ) ^ (i + (i + d)) := by gcongr
    _ = ((i + (i + d)).choose i : ℝ) * (1 / (k : ℝ) ^ (i + d)) *
          (((k : ℝ) - 1) / (k : ℝ)) ^ i * (3 * d + 1) *
          ((k : ℝ) ^ (k - 3) * ((k : ℝ) - 1) ^ d) := by
      rw [hsplit, div_pow]
      have hdd : ((k : ℝ) - 1) ^ (i + d) = ((k : ℝ) - 1) ^ i * ((k : ℝ) - 1) ^ d := pow_add _ _ _
      rw [hdd]
      field_simp

/-! ### The local search dominates the biased walk -/

omit [Fintype V] [DecidableEq V] in
theorem succeedProb_pure (φ : CNF V) (σ : V → Bool) :
    succeedProb φ (PMF.pure σ) = if φ.eval σ = true then 1 else 0 := by
  rw [succeedProb, PMF.toOuterMeasure_pure_apply]
  split_ifs <;> simp_all

omit [Fintype V] [DecidableEq V] in
theorem succeedProb_nonneg (φ : CNF V) (μ : PMF (V → Bool)) : 0 ≤ succeedProb φ μ :=
  ENNReal.toReal_nonneg

omit [Fintype V] in
/-- The success probability of one step followed by `t` more is the average over the literal
occurrences of the chosen clause. -/
private theorem succeedProb_flipStep_bind (φ : CNF V) {c : Clause V} (hc : c.length ≠ 0)
    (σ : V → Bool) (μ : (V → Bool) → PMF (V → Bool)) :
    haveI : NeZero c.length := ⟨hc⟩
    succeedProb φ ((flipStep c σ).bind μ) =
      ∑ i : Fin c.length, (c.length : ℝ)⁻¹ * succeedProb φ (μ (flipOn {(c.get i).1} σ)) := by
  have : NeZero c.length := ⟨hc⟩
  simp only [flipStep, hc, ↓reduceDIte]
  rw [PMF.bind_map, succeedProb, Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Function.comp_apply, succeedProb]

/-- **The local search dominates the biased walk.** If `σ⋆` satisfies `φ` and every clause of `φ`
has at most `k ≥ 1` literals, then `t` steps from `σ` reach a satisfying assignment with probability
at least `hit k t (dist σ σ⋆)`. -/
theorem hit_le_succeedProb (hk : 1 ≤ k) {φ : CNF V} {σs : V → Bool} (hs : φ.eval σs = true)
    (h3 : ∀ c ∈ φ, c.length ≤ k) (t : ℕ) (σ : V → Bool) :
    hit k t (hammingDist σ σs) ≤ succeedProb φ (walk φ t σ) := by
  induction t generalizing σ with
  | zero =>
    rw [walk, succeedProb_pure]
    rcases Nat.eq_zero_or_pos (hammingDist σ σs) with h0 | hpos
    · rw [hammingDist_eq_zero.mp h0]
      simp [hs]
    · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hd, hit_zero_succ]
      split_ifs <;> norm_num
  | succ t ih =>
    rw [walk]
    cases hfu : firstUnsat φ σ with
    | none =>
      have hsat : φ.eval σ = true := by
        rw [CNF.eval_eq_true_iff]
        intro c hc
        have := List.find?_eq_none.mp hfu c hc
        simpa using this
      simp only [succeedProb_pure, hsat, ite_true]
      exact hit_le_one hk _ _
    | some c =>
      have hc : c ∈ φ := List.mem_of_find?_eq_some hfu
      have hcσ : ∀ l ∈ c, σ l.1 ≠ l.2 := by
        have := List.find?_some hfu
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
        intro l hl hl'
        have hsat : c.eval σ = true := (Clause.eval_eq_true_iff σ c).mpr ⟨l, hl, hl'⟩
        rw [hsat] at this
        exact absurd this (by decide)
      obtain ⟨l, hl, hls⟩ :=
        (Clause.eval_eq_true_iff σs c).mp ((CNF.eval_eq_true_iff σs φ).mp hs c hc)
      have hne : σ l.1 ≠ σs l.1 := by rw [hls]; exact hcσ l hl
      have hdpos : hammingDist σ σs ≠ 0 := fun h => hne (congrFun (hammingDist_eq_zero.mp h) _)
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hdpos
      have hlen : c.length ≠ 0 := (List.length_pos_of_mem hl).ne'
      have : NeZero c.length := ⟨hlen⟩
      rw [hd, hit_succ_succ, succeedProb_flipStep_bind φ hlen]
      set f : Fin c.length → ℝ := fun i => succeedProb φ (walk φ t (flipOn {(c.get i).1} σ))
      obtain ⟨i₀, hi₀⟩ := List.get_of_mem hl
      have hterm : ∀ i, hit k t (d + 2) ≤ f i := by
        intro i
        refine le_trans (hit_antitone hk t ?_) (ih _)
        rw [hammingDist_flip, hd]
        split_ifs <;> omega
      have hterm₀ : hit k t d ≤ f i₀ := by
        refine le_trans (le_of_eq ?_) (ih _)
        rw [hi₀, hammingDist_flip, hd]
        simp [hne]
      have hsum : hit k t d + ((c.length : ℝ) - 1) * hit k t (d + 2) ≤ ∑ i, f i := by
        rw [← add_sum_erase _ _ (mem_univ i₀)]
        have hcard : ((c.length : ℝ) - 1) * hit k t (d + 2) =
            ∑ _i ∈ univ.erase i₀, hit k t (d + 2) := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hlen), Nat.cast_one]
        rw [hcard]
        exact add_le_add hterm₀ (sum_le_sum fun i _ => hterm i)
      rw [← mul_sum]
      have hm3 : (c.length : ℝ) ≤ k := by exact_mod_cast h3 c hc
      have hm1 : (1 : ℝ) ≤ c.length := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hlen
      have hAB : hit k t (d + 2) ≤ hit k t d := hit_antitone hk t (by omega)
      have hB := hit_nonneg hk t (d + 2)
      calc
        (hit k t d + ((k : ℝ) - 1) * hit k t (d + 2)) / k ≤
            (c.length : ℝ)⁻¹ * (hit k t d + ((c.length : ℝ) - 1) * hit k t (d + 2)) := by
          rw [inv_mul_eq_div, div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hm3)]
        _ ≤ (c.length : ℝ)⁻¹ * ∑ i, f i := by gcongr

/-! ### Schöning's bound -/

omit [DecidableEq V] in
/-- Averaging `q^{dist(σ, τ)}` over all assignments `σ` gives `(1 + q)^n`, a product over the
coordinates. -/
theorem sum_pow_hammingDist [DecidableEq V] (q : ℝ) (τ : V → Bool) :
    ∑ σ : V → Bool, q ^ hammingDist σ τ = (1 + q) ^ Fintype.card V := by
  have hprod (σ : V → Bool) : q ^ hammingDist σ τ = ∏ i, if σ i = τ i then 1 else q := by
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    rfl
  simp only [hprod]
  rw [← Fintype.prod_sum (fun i b => if b = τ i then (1 : ℝ) else q)]
  have hb (i : V) : ∑ b : Bool, (if b = τ i then (1 : ℝ) else q) = 1 + q := by
    rw [Fintype.sum_bool]
    cases τ i <;> simp [add_comm]
  simp only [hb, prod_const, card_univ]

/-- **Schöning's theorem for k-SAT, one trial.** For `k ≥ 3` and a satisfiable CNF formula on `n`
variables whose clauses have at most `k` literals, one trial of Schöning's algorithm finds a
satisfying assignment with probability at least
`((k - 1)/k)^{k - 3} (k / (2 (k - 1)))^n / (3 n + 1)`. -/
theorem trial_success_of_length_le (hk : 3 ≤ k) {φ : CNF V} (hφ : φ.Satisfiable)
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (((k : ℝ) - 1) / k) ^ (k - 3) * ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ Fintype.card V /
        (3 * Fintype.card V + 1) ≤ succeedProb φ (trial φ) := by
  obtain ⟨σs, hs⟩ := hφ
  set n := Fintype.card V
  have hk1 : (1 : ℝ) < (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set c := (((k : ℝ) - 1) / k) ^ (k - 3)
  have hc : 0 ≤ c := by positivity
  have hlow (σ : V → Bool) : c * (1 / ((k : ℝ) - 1)) ^ hammingDist σ σs / (3 * n + 1) ≤
      succeedProb φ (walk φ (3 * n) σ) := by
    have hd : hammingDist σ σs ≤ n := hammingDist_le_card_fintype
    calc
      c * (1 / ((k : ℝ) - 1)) ^ hammingDist σ σs / (3 * n + 1) ≤
          c * (1 / ((k : ℝ) - 1)) ^ hammingDist σ σs / (3 * hammingDist σ σs + 1) := by
        gcongr
      _ ≤ hit k (3 * hammingDist σ σs) (hammingDist σ σs) := inv_le_hit hk _
      _ ≤ hit k (3 * n) (hammingDist σ σs) := hit_monotone (by omega) _ (by omega)
      _ ≤ _ := hit_le_succeedProb (by omega) hs hlen _ σ
  rw [trial, succeedProb, Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  calc
    c * ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ n / (3 * n + 1) =
        ∑ σ : V → Bool, ((2 : ℝ) ^ n)⁻¹ *
          (c * (1 / ((k : ℝ) - 1)) ^ hammingDist σ σs / (3 * n + 1)) := by
      rw [← mul_sum, ← sum_div, ← mul_sum, sum_pow_hammingDist]
      have : (1 + 1 / ((k : ℝ) - 1)) = (k : ℝ) / ((k : ℝ) - 1) := by
        field_simp
        ring
      rw [this, div_pow, div_pow, mul_pow, show Fintype.card V = n from rfl]
      field_simp
    _ ≤ ∑ σ : V → Bool, ((2 : ℝ) ^ n)⁻¹ * succeedProb φ (walk φ (3 * n) σ) := by
      gcongr with σ
      exact hlow σ

/-- **Schöning's theorem for 3-SAT, one trial.** For a satisfiable CNF formula on `n` variables
whose clauses have at most three literals, one trial of Schöning's algorithm finds a satisfying
assignment with probability at least `(3 / 4) ^ n / (3 n + 1)`. -/
theorem trial_success {φ : CNF V} (hφ : φ.Satisfiable) (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (3 / 4 : ℝ) ^ Fintype.card V / (3 * Fintype.card V + 1) ≤ succeedProb φ (trial φ) := by
  have h := trial_success_of_length_le (le_refl 3) hφ h3
  norm_num at h ⊢
  exact h

end Cslib.Complexity.Schoening
