/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Sparsification
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Reductions of linear size

Exponential time bounds in a parameter of the instance transfer along polynomial-time reductions
that increase the parameter at most linearly. If `f` reduces `A` to `B` in polynomial time and
`μB (f a) ≤ c μA a + c`, then a decider for `B` within time `2 ^ (δ μB b)` times a polynomial in
the length of the encoded instance gives a decider for `A` within time `2 ^ (c δ μA a)` times a
polynomial (`Cslib.Complexity.DecidableInExpTime.of_reduction`): run the reduction, then the
decider. The polynomial absorbs the running time of the reduction and the length of its output.
Hence subexponential time in `μB` gives subexponential time in `μA`
(`Cslib.Complexity.DecidableInSubexpTime.of_reduction`).

Under the exponential time hypothesis, 3SAT is not decidable in subexponential time in the number
of clauses (`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`, by the sparsification
lemma). So a polynomial-time reduction from 3SAT whose output measure is linear in the number of
clauses shows that the target problem is not decidable in subexponential time in that measure
(`Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`)
[ImpagliazzoPaturiZane2001] [CyganEtAl2015, Chapter 14]. Lower bounds for larger measures are
stronger: a lower bound for a measure gives one for every measure at most linear in it
(`Cslib.Complexity.DecidableInSubexpTime.mono_measure`).

## Main results

* `Cslib.Complexity.DecidableInExpTime.mono_measure`,
  `Cslib.Complexity.DecidableInSubexpTime.mono_measure`: changing the measure.
* `Cslib.Complexity.DecidableInExpTime.of_reduction`,
  `Cslib.Complexity.DecidableInSubexpTime.of_reduction`: transfer along reductions of linear
  size.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`: lower bounds from the exponential
  time hypothesis through reductions of linear size from 3SAT.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Changing the measure -/

section Measure

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α} {μ μ' : α → ℕ}

/-- A decider within time `2 ^ (δ μ a)` times a polynomial, for a measure `μ ≤ c μ' + c`, decides
within time `2 ^ (c δ μ' a)` times a polynomial. -/
theorem DecidableInExpTime.mono_measure {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : DecidableInExpTime A enc μ δ) : DecidableInExpTime A enc μ' (c * δ) := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, h.mono ⌈(2 : ℝ) ^ (δ * c)⌉₊ (fun a => ?_) fun a => by positivity⟩
  have hK : (2 : ℝ) ^ (δ * c) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ := Nat.le_ceil _
  have h₁ : (2 : ℝ) ^ (δ * μ a) ≤ 2 ^ (δ * c) * 2 ^ (c * δ * μ' a) := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (μ a : ℝ) ≤ c * μ' a + c := by exact_mod_cast hμ a
    nlinarith
  have h₂ : (2 : ℝ) ^ (δ * μ a) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ * 2 ^ (c * δ * μ' a) :=
    h₁.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  have h₃ := mul_le_mul_of_nonneg_right h₂ (by positivity :
    (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
  have h₄ : (0 : ℝ) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ := Nat.cast_nonneg _
  nlinarith

/-- Subexponential time in a measure `μ ≤ c μ' + c` gives subexponential time in `μ'`. So a lower
bound for `μ'` gives the lower bound for `μ`. -/
theorem DecidableInSubexpTime.mono_measure {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : DecidableInSubexpTime A enc μ) : DecidableInSubexpTime A enc μ' := by
  intro δ hδ
  refine ((h (δ / (c + 1)) (by positivity)).mono_measure hμ (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end Measure

/-! ### Reductions -/

section Reduction

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
  {μA : α → ℕ} {μB : β → ℕ}

/-- **Transfer along reductions of linear size.** If `f` reduces `A` to `B` in polynomial time
with `μB (f a) ≤ c μA a + c`, then a decider for `B` within time `2 ^ (δ μB b)` times a polynomial
in the length of the encoded instance gives a decider for `A` within time `2 ^ (c δ μA a)` times a
polynomial. -/
theorem DecidableInExpTime.of_reduction {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ c * μA a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime B encB μB δ) : DecidableInExpTime A encA μA (c * δ) := by
  have hf := hf.tidy
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  have hg := hg.tidy
  obtain ⟨d, _, hf⟩ := hf.exists_degree
  have hfO := hf.inO
  obtain ⟨l, hl⟩ := hfO.length_le_time
  set K : ℝ := 1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k
  refine Complexity.DecidableInExpTime.of_computableInO (.of_tidy (hg.comp hfO))
    (fun a => (hfA a).trans (hgB (f a)))
    ⌈K⌉₊ (d * e + d) fun a => ?_
  show _ ≤ _
  set P : ℝ := ((encA a).length + 1) ^ d
  set X : ℝ := 2 ^ (c * δ * μA a)
  have hP : 1 ≤ P := one_le_pow₀ (by linarith [(Nat.cast_nonneg (encA a).length : (0 : ℝ) ≤ _)])
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  -- the output of the reduction has length at most `2 l P`
  have hlen : ((encB (f a)).length : ℝ) + 1 ≤ (2 * l + 1) * P := by
    have : ((encB (f a)).length : ℝ) ≤ l * (P + 1) := by
      have := hl a
      simp only [P]
      exact_mod_cast this
    nlinarith
  -- the exponential factor
  have hexp : (2 : ℝ) ^ (δ * μB (f a)) ≤ 2 ^ (δ * c) * X := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (μB (f a) : ℝ) ≤ c * μA a + c := by exact_mod_cast hμ a
    nlinarith
  -- the decider on the reduced instance
  have hpow : (((encB (f a)).length : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlen e
  have ht' : (t (f a) : ℝ) ≤ k * (2 ^ (δ * c) * (2 * l + 1) ^ e) * (X * P ^ e) + k := by
    refine (ht (f a)).trans ?_
    have := mul_le_mul hexp hpow (by positivity) (by positivity)
    nlinarith
  have hPe : P ^ e ≤ P ^ (e + 1) := pow_le_pow_right₀ hP (Nat.le_succ e)
  have hP1 : P ≤ P ^ (e + 1) := le_self_pow₀ hP (Nat.succ_ne_zero e)
  have hXP : 1 ≤ X * P ^ (e + 1) := one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP)
  have hgoal : P + (t (f a) : ℝ) ≤ K * (X * P ^ (e + 1)) := by
    have h₁ : P ≤ X * P ^ (e + 1) := hP1.trans (le_mul_of_one_le_left (by positivity) hX)
    have h₂ : X * P ^ e ≤ X * P ^ (e + 1) := mul_le_mul_of_nonneg_left hPe (by positivity)
    have h₃ := mul_le_mul_of_nonneg_left h₂
      (by positivity : (0 : ℝ) ≤ k * (2 ^ (δ * c) * (2 * l + 1) ^ e))
    have h₄ := mul_le_mul_of_nonneg_left hXP hk
    simp only [K]
    nlinarith
  have hPow : X * P ^ (e + 1) = X * (((encA a).length : ℝ) + 1) ^ (d * e + d) := by
    simp only [P, ← pow_mul]
    ring_nf
  have hK : K ≤ ⌈K⌉₊ := Nat.le_ceil K
  push_cast
  calc P + (t (f a) : ℝ) ≤ K * (X * P ^ (e + 1)) := hgoal
    _ ≤ ⌈K⌉₊ * (X * P ^ (e + 1)) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = ⌈K⌉₊ * (X * (((encA a).length : ℝ) + 1) ^ (d * e + d)) := by rw [hPow]

/-- **Transfer along reductions of linear size.** If `f` reduces `A` to `B` in polynomial time
with `μB (f a) ≤ c μA a + c`, and `B` is decidable in subexponential time in `μB`, then `A` is
decidable in subexponential time in `μA`. -/
theorem DecidableInSubexpTime.of_reduction {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ c * μA a + c) (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro δ hδ
  refine ((h (δ / (c + 1)) (by positivity)).of_reduction hf hfA hμ (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- **Lower bounds from the exponential time hypothesis** [ImpagliazzoPaturiZane2001]
[CyganEtAl2015, Chapter 14]. Under `ETH`, if `f` is computable in polynomial time and, on formulas
`φ` in conjunctive normal form with `m` clauses of at most three literals, maps `φ` to an instance
of `B` exactly when `φ` is satisfiable, with `μB (f φ) ≤ k m + k`, then `B` is not decidable in
subexponential time in `μB`: for some `δ > 0`, no decider runs within time `2 ^ (δ μB b)` times a
polynomial in the length of the encoded instance. -/
theorem ETH.not_decidableInSubexpTime_of_reduction (hETH : ETH) {f : CNF ℕ → β}
    (hf : ComputableInPolyTime f encCNF encB)
    (hfB : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → (f φ ∈ B ↔ φ ∈ SAT)) {k : ℕ}
    (hμ : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → μB (f φ) ≤ k * φ.length + k) :
    ¬DecidableInSubexpTime B encB μB := by
  intro h
  -- formulas with a clause of more than three literals go to the image of the empty clause
  refine ETH_iff_not_decidableInSubexpTime_length.mp hETH
    (h.of_reduction (f := fun φ => if φ.all (fun c => decide (c.length ≤ 3)) then f φ
      else f [[]]) (ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
        hf (ComputableInPolyTime.const _)) (fun φ => ?_) (c := 2 * k) fun φ => ?_)
  · by_cases hφ : ∀ c ∈ φ, c.length ≤ 3
    · have hw : (φ.all fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
      simp only [hw, ite_true, hfB φ hφ]
      exact ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩
    · have hw : (φ.all fun c => decide (c.length ≤ 3)) = false := by simpa using hφ
      simp only [hw, Bool.false_eq_true, ite_false, hfB [[]] (by simp)]
      exact ⟨fun h => (hφ h.1).elim, fun ⟨σ, hσ⟩ => by simp at hσ⟩
  · split_ifs with hw
    · have := hμ φ (by simpa using hw)
      nlinarith
    · have := hμ [[]] (by simp)
      simp only [List.length_singleton, mul_one] at this
      nlinarith

end Reduction

end Cslib.Complexity
