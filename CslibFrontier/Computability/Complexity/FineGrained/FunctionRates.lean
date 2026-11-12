/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FunctionTime
public import CslibFrontier.Computability.Complexity.FineGrained
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Foundations.Data.Nat.Power

/-!
# Parameterized time bounds for functions

`Cslib.Complexity.DecidableInTimeO`, `DecidableInExpTime` and `DecidableInSubexpTime` measure the
running time of decision problems in a structural parameter `μ : α → ℕ` of the instance rather than
in the bit length `L = (encIn a).length` alone. This module develops the same three notions for
functions: `f` is computable within time `O(T a)`, within time `2 ^ (δ * μ a)` times a polynomial in
`L`, and within that time for every `δ > 0`. It bridges them to `Cslib.Complexity.FTIME` and to
decision, and transfers them along polynomial-time reductions that change the parameter linearly.

## Main definitions

* `Cslib.Complexity.ComputableInTimeO`, `Cslib.Complexity.ComputableInExpTime`,
  `Cslib.Complexity.ComputableInSubexpTime`: parameterized time bounds for functions.

## Main results

* `Cslib.Complexity.mem_FTIME_iff_computableInTimeO`: agreement with `FTIME` on length bounds.
* `Cslib.Complexity.decidableInTimeO_iff_exists_computableInTimeO`: decision as computation of a
  Boolean indicator.
* `Cslib.Complexity.DecidableInExpTime.of_computableInExpTime_polyBounded`: a polynomial-time test
  on a function value with polynomially bounded output length is decided at the function's rate.
* `Cslib.Complexity.ComputableInExpTime.of_reduction`,
  `Cslib.Complexity.ComputableInSubexpTime.of_reduction`: transfer along linear-parameter
  polynomial-time reductions.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-! ### Parameterized function time bounds -/

section FunctionBounds

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {f : α → β} {T T' : α → ℝ}

/-- `f` is computable within time `O(T a)` on the instance `a`: within time `c * T a + c`, for a
constant `c`, by a native multi-tape machine reading `encIn a` and writing `encOut (f a)` with some
workspace bound. -/
@[expose] def ComputableInTimeO (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ, (∀ a, (t a : ℝ) ≤ c * T a + c) ∧
    ComputableInTimeAndSpace f encIn encOut t s

/-- Weakening the bound of `ComputableInTimeO` up to constants. -/
theorem ComputableInTimeO.mono (h : ComputableInTimeO f encIn encOut T) (c : ℕ)
    (hT : ∀ a, T a ≤ c * T' a + c) (hT' : ∀ a, 0 ≤ T' a) :
    ComputableInTimeO f encIn encOut T' := by
  obtain ⟨c₀, t, s, ht, hf⟩ := h
  refine ⟨c₀ * c + c₀, t, s, fun a => (ht a).trans ?_, hf⟩
  have h₁ := mul_le_mul_of_nonneg_left (hT a) (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀)
  have h₂ := mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀) (hT' a)
  push_cast
  nlinarith

/-- `f` is computable within time `2 ^ (δ * μ a)` times a polynomial in the encoded input length:
within time `O(2 ^ (δ * μ a) * (L + 1) ^ e)` for some `e`. -/
@[expose] def ComputableInExpTime (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, ComputableInTimeO f encIn encOut fun a => 2 ^ (δ * μ a) * ((encIn a).length + 1) ^ e

/-- `f` is computable in subexponential time in `μ`: within time `2 ^ (δ * μ a)` times a polynomial
in the encoded input length for every `δ > 0` (the machine and polynomial degree may depend on
`δ`). -/
@[expose] def ComputableInSubexpTime (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (μ : α → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ComputableInExpTime f encIn encOut μ δ

/-- Larger exponents allow more functions. -/
theorem ComputableInExpTime.mono {μ : α → ℕ} {δ δ' : ℝ}
    (h : ComputableInExpTime f encIn encOut μ δ) (hδ : δ ≤ δ') :
    ComputableInExpTime f encIn encOut μ δ' := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, h.mono 1 (fun a => ?_) fun a => by positivity⟩
  have h₁ : (2 : ℝ) ^ (δ * μ a) ≤ 2 ^ (δ' * μ a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _))
  have h₂ := mul_le_mul_of_nonneg_right h₁ (by positivity : (0 : ℝ) ≤ ((encIn a).length + 1) ^ e)
  push_cast
  linarith

/-- Rescaling the parameter linearly rescales the exponential rate. -/
theorem ComputableInExpTime.mono_measure {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : ComputableInExpTime f encIn encOut μ δ) :
    ComputableInExpTime f encIn encOut μ' (c * δ) := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, h.mono ⌈(2 : ℝ) ^ (δ * c)⌉₊ (fun a => ?_) fun a => by positivity⟩
  have h₂ := two_rpow_le_natCeil_mul_of_le_mul_add hδ (hμ a)
  have h₃ := mul_le_mul_of_nonneg_right h₂
    (by positivity : (0 : ℝ) ≤ ((encIn a).length + 1) ^ e)
  have h₄ : (0 : ℝ) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ := Nat.cast_nonneg _
  nlinarith

/-- Subexponential computability transfers to any parameter at least linear in `μ`. -/
theorem ComputableInSubexpTime.mono_measure {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : ComputableInSubexpTime f encIn encOut μ) :
    ComputableInSubexpTime f encIn encOut μ' := by
  intro δ hδ
  refine ((h (δ / (c + 1)) (by positivity)).mono_measure hμ (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end FunctionBounds

section FunctionMachines

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {f : α → β} {T : α → ℝ}

/-- **`FTIME` in terms of `ComputableInTimeO`.** For a bound depending only on the encoded input
length, `ComputableInTimeO` agrees with membership in `FTIME`. -/
theorem mem_FTIME_iff_computableInTimeO {t : ℕ → ℕ} :
    f ∈ FTIME encIn encMid t ↔ ComputableInTimeO f encIn encMid fun a => t (encIn a).length := by
  constructor
  · rintro ⟨c₁, c₂, s, hf⟩
    refine ⟨c₁ + c₂, _, _, fun a => ?_, hf⟩
    push_cast
    nlinarith [(Nat.cast_nonneg (t (encIn a).length) : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg c₂ : (0 : ℝ) ≤ _), (Nat.cast_nonneg c₁ : (0 : ℝ) ≤ _)]
  · rintro ⟨c, t', s, ht', hf⟩
    have ht : ∀ a, t' a ≤ c * t (encIn a).length + c := fun a => by
      have := ht' a
      simp only at this
      exact_mod_cast this
    obtain ⟨k, hf'⟩ := ComputableInTimeAndSpace.exists_space_linear hf
    exact ⟨c, c, fun n => k * (c * t n + c) + k,
      ComputableInTimeAndSpace.mono hf' ht fun a => by
        have := Nat.mul_le_mul_left k (ht a)
        simp only
        omega⟩

/-- A function computable within time `O(T)` has a `ComputableInO` certificate within time and
charged workspace `O(t)`, for a natural clock `t` within `O(T)`. -/
theorem ComputableInTimeO.exists_computableInO (h : ComputableInTimeO f encIn encMid T) :
    ∃ (t : α → ℕ) (c : ℕ), ComputableInO f encIn encMid t t ∧
      ∀ a, (t a : ℝ) ≤ c * T a + c := by
  obtain ⟨c, t, s, ht, hf⟩ := h
  have hl : ∀ a, (encMid (f a)).length ≤ t a := hf.length_le
  obtain ⟨k, hf'⟩ := ComputableInTimeAndSpace.exists_space_linear hf
  refine ⟨t, c, ComputableInO.of_bounds hf' (k + 1)
    (fun a => by nlinarith) (fun a => by nlinarith) (fun a => by nlinarith [hl a]), ht⟩

/-- A `ComputableInO` certificate within time `t ≤ T` gives `ComputableInTimeO` within `T`. -/
theorem ComputableInTimeO.of_computableInO {t S : α → ℕ}
    (hf : ComputableInO f encIn encMid t S) (hT : ∀ a, (t a : ℝ) ≤ T a) :
    ComputableInTimeO f encIn encMid T := by
  obtain ⟨c, hf', -⟩ := hf
  refine ⟨c, _, _, fun a => ?_, hf'⟩
  push_cast
  nlinarith [hT a, (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]

/-- `DecidableInTimeO` is `ComputableInTimeO` of a Boolean indicator function. -/
theorem decidableInTimeO_iff_exists_computableInTimeO {A : Set α} :
    DecidableInTimeO A encIn T ↔
      ∃ g : α → Bool, (∀ a, a ∈ A ↔ g a = true) ∧ ComputableInTimeO g encIn encBool T := by
  constructor
  · rintro ⟨c, t, s, ht, h⟩
    obtain ⟨g, hg, hA⟩ := decidableInTimeAndSpace_iff.mp h
    exact ⟨g, hA, c, t, s, ht, hg⟩
  · rintro ⟨g, hA, c, t, s, ht, hg⟩
    exact ⟨c, t, s, ht, decidableInTimeAndSpace_iff.mpr ⟨g, hg, hA⟩⟩

/-- A `ComputableInO` certificate within `c * (2 ^ (δ * μ a) * (L + 1) ^ e)` gives
`ComputableInExpTime`. -/
theorem ComputableInExpTime.of_computableInO {μ : α → ℕ} {δ : ℝ} {t S : α → ℕ}
    (hf : ComputableInO f encIn encMid t S) (c e : ℕ)
    (ht : ∀ a, (t a : ℝ) ≤ c * (2 ^ (δ * μ a) * ((encIn a).length + 1) ^ e)) :
    ComputableInExpTime f encIn encMid μ δ :=
  ⟨e, (ComputableInTimeO.of_computableInO hf ht).mono c
    (fun _ => le_add_of_nonneg_right (Nat.cast_nonneg c)) fun _ => by positivity⟩

/-- Every polynomial-time computable function has exponential rate `0` in any parameter `μ`. -/
theorem ComputableInExpTime.of_computableInPolyTime {μ : α → ℕ}
    (hf : ComputableInPolyTime f encIn encMid) :
    ComputableInExpTime f encIn encMid μ 0 := by
  obtain ⟨d, _, hf'⟩ := hf.exists_degree
  refine ComputableInExpTime.of_computableInO hf'.inO 1 d fun a => ?_
  simp

/-- Guarding an exponential-time function by a polynomial-time test and fallback preserves rate
`δ ≥ 0`. -/
theorem ComputableInExpTime.ite_polyTime {μ : α → ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {p : α → Bool}
    {g : α → β} (hp : ComputableInPolyTime p encIn encBool)
    (hf : ComputableInExpTime f encIn encMid μ δ)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInExpTime (fun a => if p a then f a else g a) encIn encMid μ δ := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨t, c, hfO, ht⟩ := hf.exists_computableInO
  obtain ⟨dp, _, hp'⟩ := hp.exists_degree
  obtain ⟨dg, _, hg'⟩ := hg.exists_degree
  have hcomb := hp'.inO.ite hfO hg'.inO
  refine ComputableInExpTime.of_computableInO hcomb (2 * c + 3) (dp + dg + e) fun a => ?_
  set L : ℝ := ((encIn a).length : ℝ)
  have hL1 : (1 : ℝ) ≤ L + 1 := by
    dsimp only [L]
    linarith [(Nat.cast_nonneg (encIn a).length : (0 : ℝ) ≤ _)]
  have hX1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
  have hdp : (L + 1) ^ dp ≤ (L + 1) ^ (dp + dg + e) := pow_le_pow_right₀ hL1 (by omega)
  have hdg : (L + 1) ^ dg ≤ (L + 1) ^ (dp + dg + e) := pow_le_pow_right₀ hL1 (by omega)
  have he : (L + 1) ^ e ≤ (L + 1) ^ (dp + dg + e) := pow_le_pow_right₀ hL1 (by omega)
  have hbase : (L + 1) ^ (dp + dg + e) ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) :=
    le_mul_of_one_le_left (by positivity) hX1
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hpos : (0 : ℝ) ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) := by positivity
  have ht_le : (t a : ℝ) ≤ (2 * c + 1) * (2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e)) := by
    have hta := ht a
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 ^ (δ * μ a))
    have hmulc := mul_le_mul_of_nonneg_left hmul hc0
    have hc1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) :=
      one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hL1)
    have hcc := mul_le_mul_of_nonneg_left hc1 hc0
    dsimp only [L] at *
    nlinarith
  change ((((encIn a).length + 1) ^ dp +
    if p a then t a else ((encIn a).length + 1) ^ dg : ℕ) : ℝ) ≤ _
  split_ifs
  · push_cast
    dsimp only [L] at *
    nlinarith [hdp.trans hbase]
  · push_cast
    dsimp only [L] at *
    nlinarith [hdp.trans hbase, hdg.trans hbase]

/-- **Exact-rate decision from function computation.** If `f` is computable in time
`2 ^ (δ * μ a) · poly(|a|)` (`δ ≥ 0`) and its encoded output length is polynomially bounded in
`|a|`, then any polynomial-time test on `f a` decides `{a | test (f a) = true}` at the same
exponential rate `δ`. -/
theorem DecidableInExpTime.of_computableInExpTime_polyBounded {μ : α → ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ComputableInExpTime f encIn encMid μ δ)
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (encMid (f a)).length))
    {test : β → Bool} (htest : ComputableInPolyTime test encMid encBool) :
    DecidableInExpTime {a | test (f a) = true} encIn μ δ := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨t, c, hfO, ht⟩ := hf.exists_computableInO
  obtain ⟨d, _, htest'⟩ := htest.exists_degree
  obtain ⟨p, q, hp⟩ := hlen.exists_le
  have hcomp := htest'.inO.comp hfO
  refine DecidableInExpTime.of_computableInO hcomp (fun _ => Iff.rfl)
    (2 * c + 1 + (p + 1) ^ d) (e + q * d) fun a => ?_
  set L : ℕ := (encIn a).length
  have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast hL1
  have hX1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
  have hout_pow : ((encMid (f a)).length + 1) ^ d ≤ (p + 1) ^ d * (L + 1) ^ (q * d) :=
    Nat.add_one_pow_le_of_le_mul_pow hL1 (hp a) d
  have hqd : (((L : ℝ) + 1)) ^ (q * d) ≤ ((L : ℝ) + 1) ^ (e + q * d) :=
    pow_le_pow_right₀ hLR1 (Nat.le_add_left _ _)
  have he : (((L : ℝ) + 1)) ^ e ≤ ((L : ℝ) + 1) ^ (e + q * d) :=
    pow_le_pow_right₀ hLR1 (Nat.le_add_right _ _)
  have houtR : (((encMid (f a)).length : ℝ) + 1) ^ d ≤
      ((p + 1) ^ d : ℕ) * (2 ^ (δ * μ a) * ((L : ℝ) + 1) ^ (e + q * d)) := by
    have h1 : (((encMid (f a)).length : ℝ) + 1) ^ d ≤
        ((p + 1) ^ d : ℕ) * ((L : ℝ) + 1) ^ (q * d) := by exact_mod_cast hout_pow
    have h2 : ((L : ℝ) + 1) ^ (q * d) ≤ 2 ^ (δ * μ a) * ((L : ℝ) + 1) ^ (e + q * d) :=
      hqd.trans (le_mul_of_one_le_left (by positivity) hX1)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  have htR : (t a : ℝ) ≤ (2 * c + 1 : ℕ) * (2 ^ (δ * μ a) * ((L : ℝ) + 1) ^ (e + q * d)) := by
    have hta := ht a
    have h1 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 ^ (δ * μ a))
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
    have h3 : (1 : ℝ) ≤ 2 ^ (δ * μ a) * ((L : ℝ) + 1) ^ (e + q * d) :=
      one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hLR1)
    have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg c)
    push_cast
    dsimp only [L] at *
    linarith
  change ((t a + ((encMid (f a)).length + 1) ^ d : ℕ) : ℝ) ≤ _
  push_cast
  dsimp only [L] at *
  push_cast at htR houtR
  linarith

/-- Subexponential function computation with polynomially bounded output length transfers to
subexponential decision for any polynomial-time output predicate. -/
theorem DecidableInSubexpTime.of_computableInSubexpTime_polyBounded {μ : α → ℕ}
    (hf : ComputableInSubexpTime f encIn encMid μ)
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (encMid (f a)).length))
    {test : β → Bool} (htest : ComputableInPolyTime test encMid encBool) :
    DecidableInSubexpTime {a | test (f a) = true} encIn μ :=
  fun δ hδ => .of_computableInExpTime_polyBounded hδ.le (hf δ hδ) hlen htest

/-- **Transfer along linear-parameter parsimonious reductions.** If `r : α → β` is computable in
polynomial time with `μB (r a) ≤ c * μA a + c`, and `g : β → γ` is computable in time
`2 ^ (δ * μB b) · poly(|b|)` (`δ ≥ 0`), then `g ∘ r` is computable in time
`2 ^ (c * δ * μA a) · poly(|a|)`. -/
theorem ComputableInExpTime.of_reduction {μA : α → ℕ} {μB : β → ℕ} {r : α → β} {g : β → γ}
    (hr : ComputableInPolyTime r encIn encMid) {c : ℕ}
    (hμ : ∀ a, μB (r a) ≤ c * μA a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ComputableInExpTime g encMid encOut μB δ) :
    ComputableInExpTime (g ∘ r) encIn encOut μA (c * δ) := by
  obtain ⟨e, hg⟩ := hg
  obtain ⟨t, k, hgO, ht⟩ := hg.exists_computableInO
  obtain ⟨d, _, hr'⟩ := hr.exists_degree
  obtain ⟨l, hl⟩ := hr'.inO.length_le_time
  refine ComputableInExpTime.of_computableInO (hgO.comp hr'.inO)
    ⌈(1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k : ℝ)⌉₊ (d * (e + 1)) fun a => ?_
  set P : ℝ := ((encIn a).length + 1 : ℝ) ^ d
  set X : ℝ := 2 ^ (c * δ * μA a)
  have hP : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hn : ((encMid (r a)).length : ℝ) ≤ l * (P + 1) := by
    dsimp only [P]
    exact_mod_cast hl a
  have hexp : (2 : ℝ) ^ (δ * μB (r a)) ≤ 2 ^ (δ * c) * X := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (μB (r a) : ℝ) ≤ c * μA a + c := by exact_mod_cast hμ a
    nlinarith
  have hsum := reduction_add_time_le (C := (2 : ℝ) ^ (δ * c))
    hP hX (by positivity) hn hexp (ht (r a))
  change ((((encIn a).length + 1) ^ d + t (r a) : ℕ) : ℝ) ≤ _
  push_cast
  rw [pow_mul]
  exact hsum.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))

/-- Subexponential function computation transfers along linear-parameter polynomial-time
reductions. -/
theorem ComputableInSubexpTime.of_reduction {μA : α → ℕ} {μB : β → ℕ} {r : α → β} {g : β → γ}
    (hr : ComputableInPolyTime r encIn encMid) {c : ℕ}
    (hμ : ∀ a, μB (r a) ≤ c * μA a + c)
    (hg : ComputableInSubexpTime g encMid encOut μB) :
    ComputableInSubexpTime (g ∘ r) encIn encOut μA := by
  intro δ hδ
  refine ((hg (δ / (c + 1)) (by positivity)).of_reduction hr hμ (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end FunctionMachines

end Cslib.Complexity
