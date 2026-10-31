/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Sparsification
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

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

More generally, subexponential time transfers along **$2^{O(m(a))}$-time reductions**
(`Cslib.Complexity.DecidableInSubexpTime.of_expReduction`), where the target measure is bounded
linearly in $m(a) \log_2 m(a)$ and the $2^{O(m(a))}$ runtime is absorbed into
$2^{(\varepsilon / 2) m(a) \log_2 m(a)}$.

Under the exponential time hypothesis, 3SAT is not decidable in subexponential time in the number
of clauses (`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`, by the sparsification
lemma). So a polynomial-time reduction from 3SAT whose output measure is linear in the number of
clauses shows that the target problem is not decidable in subexponential time in that measure
(`Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`)
[ImpagliazzoPaturiZane2001] [CyganEtAl2015, Chapter 14]. Lower bounds for larger measures are
stronger: a lower bound for a measure gives one for every measure at most linear in it
(`Cslib.Complexity.DecidableInSubexpTime.mono_measure`).

`Cslib.Complexity.CountingNativeEndpoint.not_ETH` proves that `ETH` is false, so lower bounds
obtained this way hold vacuously. The transfer theorems are unconditional.

## Main results

* `Cslib.Complexity.DecidableInExpTime.mono_measure`,
  `Cslib.Complexity.DecidableInSubexpTime.mono_measure`: changing the measure.
* `Cslib.Complexity.DecidableInExpTime.of_reduction`,
  `Cslib.Complexity.DecidableInSubexpTime.of_reduction`: transfer along reductions of linear
  size.
* `Cslib.Complexity.DecidableInSubexpTime.of_expReduction`: subexponential-time transfer along
  $2^{O(m)}$-time reductions into parameter $m \log_2 m$.
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
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨d, _, hf⟩ := hf.exists_degree
  have hfO := hf.inO
  obtain ⟨l, hl⟩ := hfO.length_le_time
  set K : ℝ := 1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k
  refine Complexity.DecidableInExpTime.of_computableInO (hg.comp hfO)
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

/-! ### Exponential-time reductions into $m \log_2 m$ -/

/-- For any constant $C \ge 0$ and $\varepsilon > 0$, $(C : \mathbb{R}) \cdot n$ is bounded by an
$\varepsilon$-dependent constant plus $(\varepsilon / 2) \cdot n \log_2 n$. -/
private theorem mul_le_pow_add_mul_log (C : ℕ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (C : ℝ) * n ≤ C * ((2 ^ (⌈(2 * C : ℝ) / ε⌉₊ + 1) : ℕ) : ℝ) +
      (ε / 2) * (n * Nat.log 2 n : ℝ) := by
  set M : ℕ := ⌈(2 * C : ℝ) / ε⌉₊ + 1
  have hnonneg : 0 ≤ (ε / 2) * (n * Nat.log 2 n : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (C : ℝ) * ((2 ^ M : ℕ) : ℝ) := by positivity
  by_cases hn : n < 2 ^ M
  · have hn_le : (n : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast hn.le
    have h1 : (C : ℝ) * n ≤ C * ((2 ^ M : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hn_le (Nat.cast_nonneg C)
    linarith
  · have hn' : 2 ^ M ≤ n := not_lt.mp hn
    have hlog : M ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two hn'
    have hM_ge : (2 * C : ℝ) / ε ≤ M :=
      (Nat.le_ceil ((2 * C : ℝ) / ε)).trans (by simp [M])
    have hlog_ge : (2 * C : ℝ) / ε ≤ (Nat.log 2 n : ℝ) :=
      hM_ge.trans (by exact_mod_cast hlog)
    have hC_le : (C : ℝ) ≤ (ε / 2) * (Nat.log 2 n : ℝ) := by
      rw [div_le_iff₀ hε] at hlog_ge
      linarith
    have hmul := mul_le_mul_of_nonneg_right hC_le (Nat.cast_nonneg n)
    linarith [show (ε / 2) * (Nat.log 2 n : ℝ) * n = (ε / 2) * (n * Nat.log 2 n : ℝ) by ring]

/-- **Subexponential-time transfer along $2^{O(m(a))}$-time reductions.** If $f : \alpha \to \beta$
is computable in time $O(2^{C m(a)} \cdot (|a| + 1)^D)$, reduces $A$ to $B$, and maps every
instance $a$ to one with parameter $\mu_B(f(a)) \le c \cdot m(a) \log_2 m(a) + c$, then a
$2^{o(\mu_B)}$-time decider for $B$ yields a $2^{o(m \log m)}$-time decider for $A$. -/
theorem DecidableInSubexpTime.of_expReduction {f : α → β} {m : α → ℕ}
    (hf : ∃ C D : ℕ, ComputableInO f encA encB
      (fun a => 2 ^ (C * m a) * ((encA a).length + 1) ^ D)
      (fun a => 2 ^ (C * m a) * ((encA a).length + 1) ^ D))
    (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ c * (m a * Nat.log 2 (m a)) + c)
    (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA (fun a => m a * Nat.log 2 (m a)) := by
  intro ε hε
  obtain ⟨C, D, hfO⟩ := hf
  obtain ⟨l, hl⟩ := hfO.length_le_time
  set δ : ℝ := ε / (2 * (c + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨e, hdec⟩ := h δ hδ
  obtain ⟨g, t, k, hg, hgB, ht⟩ := hdec.exists_computableInO
  set C' : ℕ := C * (e + 1)
  set E : ℕ := D * (e + 1)
  set M : ℕ := ⌈(2 * C' : ℝ) / ε⌉₊ + 1
  set K₀ : ℝ := 2 ^ ((C' : ℝ) * ((2 ^ M : ℕ) : ℝ))
  set K₁ : ℝ := 1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k
  set K : ℝ := K₁ * K₀
  refine DecidableInExpTime.of_computableInO (hg.comp hfO)
    (fun a => (hfA a).trans (hgB (f a)))
    ⌈K⌉₊ E fun a => ?_
  show _ ≤ _
  set L : ℕ := (encA a).length
  set P_exp : ℝ := 2 ^ ((C : ℝ) * m a)
  set P_poly : ℝ := ((L : ℝ) + 1) ^ D
  set P : ℝ := P_exp * P_poly
  set X₁ : ℝ := 2 ^ ((ε / 2) * (m a * Nat.log 2 (m a) : ℕ))
  set X : ℝ := 2 ^ (ε * (m a * Nat.log 2 (m a) : ℕ))
  have hP_exp1 : 1 ≤ P_exp := Real.one_le_rpow (by norm_num) (by positivity)
  have hP_poly1 : 1 ≤ P_poly :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hP_exp1 hP_poly1
  have hX₁ : 1 ≤ X₁ := Real.one_le_rpow (by norm_num) (by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hP_nat : ((2 ^ (C * m a) * (L + 1) ^ D : ℕ) : ℝ) = P := by
    simp only [P, P_exp, P_poly]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    push_cast
    rfl
  have hlen : ((encB (f a)).length : ℝ) + 1 ≤ (2 * l + 1) * P := by
    have h1 : ((encB (f a)).length : ℝ) ≤ l * (P + 1) := by
      have := hl a
      rw [← hP_nat]
      exact_mod_cast this
    nlinarith
  have hcδ : (c : ℝ) * δ ≤ ε / 2 := by
    simp only [δ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hexp : (2 : ℝ) ^ (δ * μB (f a)) ≤ 2 ^ (δ * c) * X₁ := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hμ' : (μB (f a) : ℝ) ≤ c * (m a * Nat.log 2 (m a) : ℕ) + c := by
      exact_mod_cast hμ a
    have hmul := mul_le_mul_of_nonneg_right hcδ (Nat.cast_nonneg (m a * Nat.log 2 (m a)))
    nlinarith
  have hpow : (((encB (f a)).length : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlen e
  have ht' : (t (f a) : ℝ) ≤
      k * (2 ^ (δ * c) * (2 * l + 1) ^ e) * (X₁ * P ^ e) + k := by
    refine (ht (f a)).trans ?_
    have := mul_le_mul hexp hpow (by positivity) (by positivity)
    nlinarith
  have hPe : P ^ e ≤ P ^ (e + 1) := pow_le_pow_right₀ hP (Nat.le_succ e)
  have hP1 : P ≤ P ^ (e + 1) := le_self_pow₀ hP (Nat.succ_ne_zero e)
  have hX₁P : 1 ≤ X₁ * P ^ (e + 1) := one_le_mul_of_one_le_of_one_le hX₁ (one_le_pow₀ hP)
  have hstep1 : P + (t (f a) : ℝ) ≤ K₁ * (X₁ * P ^ (e + 1)) := by
    have h₁ : P ≤ X₁ * P ^ (e + 1) := hP1.trans (le_mul_of_one_le_left (by positivity) hX₁)
    have h₂ : X₁ * P ^ e ≤ X₁ * P ^ (e + 1) := mul_le_mul_of_nonneg_left hPe (by positivity)
    have h₃ := mul_le_mul_of_nonneg_left h₂
      (by positivity : (0 : ℝ) ≤ k * (2 ^ (δ * c) * (2 * l + 1) ^ e))
    have h₄ := mul_le_mul_of_nonneg_left hX₁P hk
    simp only [K₁]
    nlinarith
  have hP_exp_pow : P_exp ^ (e + 1) ≤ K₀ * X₁ := by
    have hrpow : P_exp ^ (e + 1) = 2 ^ ((C' : ℝ) * m a) := by
      simp only [P_exp, C', ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hrpow]
    have hK₀X₁ : K₀ * X₁ =
        2 ^ ((C' : ℝ) * ((2 ^ M : ℕ) : ℝ) + (ε / 2) * (m a * Nat.log 2 (m a) : ℕ)) := by
      simp only [K₀, X₁]
      rw [← Real.rpow_add (by norm_num)]
    rw [hK₀X₁]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    simpa only [Nat.cast_mul] using mul_le_pow_add_mul_log C' hε (m a)
  have hP_poly_pow : P_poly ^ (e + 1) = ((L : ℝ) + 1) ^ E := by
    simp only [P_poly, E, ← pow_mul]
  have hX₁_sq : X₁ * X₁ = X := by
    simp only [X₁, X]
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hstep2 : X₁ * P ^ (e + 1) ≤ K₀ * (X * ((L : ℝ) + 1) ^ E) := by
    have hsplit : X₁ * P ^ (e + 1) = X₁ * P_exp ^ (e + 1) * P_poly ^ (e + 1) := by
      simp only [P, mul_pow]
      ring
    rw [hsplit, hP_poly_pow]
    have hmul1 := mul_le_mul_of_nonneg_left hP_exp_pow (by positivity : (0 : ℝ) ≤ X₁)
    have hmul2 := mul_le_mul_of_nonneg_right hmul1 (by positivity : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ E)
    calc X₁ * P_exp ^ (e + 1) * ((L : ℝ) + 1) ^ E
        ≤ X₁ * (K₀ * X₁) * ((L : ℝ) + 1) ^ E := hmul2
      _ = K₀ * ((X₁ * X₁) * ((L : ℝ) + 1) ^ E) := by ring
      _ = K₀ * (X * ((L : ℝ) + 1) ^ E) := by rw [hX₁_sq]
  have hK_ceil : K ≤ ⌈K⌉₊ := Nat.le_ceil K
  have hLHS : (((2 ^ (C * m a) * (L + 1) ^ D + t (f a) : ℕ) : ℝ)) =
      P + (t (f a) : ℝ) := by
    rw [Nat.cast_add, hP_nat]
  calc (((2 ^ (C * m a) * (L + 1) ^ D + t (f a) : ℕ) : ℝ))
      = P + (t (f a) : ℝ) := hLHS
    _ ≤ K₁ * (X₁ * P ^ (e + 1)) := hstep1
    _ ≤ K₁ * (K₀ * (X * ((L : ℝ) + 1) ^ E)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = K * (X * ((L : ℝ) + 1) ^ E) := by simp only [K, mul_assoc]
    _ ≤ ⌈K⌉₊ * (X * ((L : ℝ) + 1) ^ E) :=
        mul_le_mul_of_nonneg_right hK_ceil (by positivity)

end Reduction

end Cslib.Complexity
