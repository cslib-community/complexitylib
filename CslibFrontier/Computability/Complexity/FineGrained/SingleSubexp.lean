/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
public import Mathlib.Analysis.Asymptotics.Defs
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Single-machine subexponential time (`2 ^ o(μ)`) versus machine families (`∀ δ > 0, ∃ M`)

Fine-grained complexity distinguishes two formulations of subexponential runtime in a parameter
`μ : α → ℕ` [ImpagliazzoPaturi2001; ImpagliazzoPaturiZane2001]:

1. **Family subexponential time** (`Cslib.Complexity.DecidableInSubexpTime`,
   `Cslib.Complexity.ComputableInSubexpTime`): for every `δ > 0` there exist a machine `M_δ` and
   polynomial degree `e_δ` solving the problem within time `O(2 ^ (δ * μ a) * (L + 1) ^ e_δ)`.
   For instance, fixed-threshold sparsification [ImpagliazzoPaturiZane2001] chooses its branching
   fan-out threshold from the target accuracy `ε > 0`, producing a family indexed by `δ`.
2. **Single-machine subexponential time** (`Cslib.Complexity.DecidableInSingleSubexpTime`,
   `Cslib.Complexity.ComputableInSingleSubexpTime`): a *single* machine and fixed polynomial degree
   `e` solve the problem within time `O(2 ^ s (μ a) * (L + 1) ^ e)` for a nonnegative scale
   `s =o[atTop] id`.

This module formalizes single-machine subexponential decision and function computation and proves
their exact relationship to the family notions:

* **Quantifier-order characterization**
  (`decidableInSingleSubexpTime_iff_exists_machine`,
  `computableInSingleSubexpTime_iff_exists_machine`): single-machine `2 ^ o(μ)` time holds if and
  only if a single machine and polynomial degree `e` achieve the `2 ^ (δ * μ a) * (L + 1) ^ e`
  bound for every `δ > 0` (with only the leading constant `c` depending on `δ`).
* **Hierarchy** (`DecidableInSingleSubexpTime.decidableInSubexpTime`,
  `ComputableInSingleSubexpTime.computableInSubexpTime`): single-machine subexponential time
  implies family subexponential time, hence `ETH → SingleETH` and `SharpETH → SingleSharpETH`.
* **Monotone envelope and transfers** (`exists_monotone_isLittleO_ge`,
  `DecidableInSingleSubexpTime.of_reduction`, `ComputableInSingleSubexpTime.of_reduction`):
  replacing `s` by its running maximum `(Finset.range (n + 1)).sup' _ s` preserves `s =o[atTop] id`
  while making `s` monotone, so single-machine subexponential time transfers unconditionally along
  linear-parameter polynomial-time and parsimonious reductions.
* **Unconditional native single-machine algorithms**
  (`computableInSingleSubexpTime_SharpDeclaredKSAT`, `computableInSingleSubexpTime_SharpKSAT`,
  `decidableInSingleSubexpTime_KSAT`, `not_SingleETH`, `not_SingleSharpETH`): because
  `CountingNativeEndpoint.exists_declaredCounter` adapts its branching divisor dynamically with the
  declared variable count (`interpolationScale =o[atTop] id`), a *single* native multi-tape machine
  solves `#k-SAT` and `k`-SAT in time `2 ^ o(n) · poly(L)` for each fixed `k`.

## Main definitions

* `Cslib.Complexity.DecidableInSingleSubexpTime`,
  `Cslib.Complexity.ComputableInSingleSubexpTime`: single-machine `2 ^ o(μ) · poly(L)` time.
* `Cslib.Complexity.SingleETH`, `Cslib.Complexity.SingleSharpETH`: single-machine `ETH` and `#ETH`.
* `Cslib.Complexity.DeclaredFormula`, `Cslib.Complexity.encDeclaredFormula`,
  `Cslib.Complexity.SharpDeclaredKSAT`: structured declared-variable counting instances.

## Main results

* `Cslib.Complexity.exists_two_pow_le_of_isLittleO`,
  `Cslib.Complexity.exists_monotone_isLittleO_ge`: asymptotic comparison and monotone envelopes for
  `o(n)` scales.
* `Cslib.Complexity.decidableInSingleSubexpTime_iff_exists_machine`,
  `Cslib.Complexity.computableInSingleSubexpTime_iff_exists_machine`: equivalence with exchanging
  `∃ (M, e)` and `∀ δ > 0`.
* `Cslib.Complexity.DecidableInSingleSubexpTime.of_reduction`,
  `Cslib.Complexity.ComputableInSingleSubexpTime.of_reduction`,
  `Cslib.Complexity.DecidableInSingleSubexpTime.of_computableInSingleSubexpTime_polyBounded`:
  unconditional single-machine reduction and decision-from-counting transfers.
* `Cslib.Complexity.computableInSingleSubexpTime_SharpDeclaredKSAT`,
  `Cslib.Complexity.computableInSingleSubexpTime_SharpKSAT`,
  `Cslib.Complexity.decidableInSingleSubexpTime_KSAT`,
  `Cslib.Complexity.not_SingleETH`, `Cslib.Complexity.not_SingleSharpETH`: single-machine native
  subexponential counting and decision for every fixed width `k`.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing Turing.MultiTapeTM Filter Asymptotics Topology

/-! ### Asymptotic envelopes for `o(n)` exponents -/

/-- Any sublinear exponent `s =o[atTop] id` satisfies `2 ^ s n ≤ K * 2 ^ (δ * n)` globally for
every `δ > 0`. -/
theorem exists_two_pow_le_of_isLittleO {s : ℕ → ℝ}
    (hs : s =o[atTop] fun n : ℕ => (n : ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (2 : ℝ) ^ s n ≤ K * (2 : ℝ) ^ (δ * n) := by
  have hev : ∀ᶠ n : ℕ in atTop, s n ≤ δ * n := by
    filter_upwards [hs.bound hδ] with n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg n)] at hn
    exact (Real.le_norm_self (s n)).trans hn
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  let K : ℝ := 1 + ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ s m
  have hsum : 0 ≤ ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ s m :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hK1 : 1 ≤ K := by dsimp only [K]; linarith
  refine ⟨K, hK1, fun n => ?_⟩
  have h2δ : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : n < N₀
  · have hle_sum : (2 : ℝ) ^ s n ≤ ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ s m :=
      Finset.single_le_sum (f := fun m => (2 : ℝ) ^ s m)
        (fun _ _ => by positivity) (Finset.mem_range.mpr hn)
    have hle_K : (2 : ℝ) ^ s n ≤ K := by dsimp only [K]; linarith
    exact hle_K.trans (le_mul_of_one_le_right (by positivity) h2δ)
  · have hrpow : (2 : ℝ) ^ s n ≤ (2 : ℝ) ^ (δ * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hN₀ n (not_lt.mp hn))
    exact hrpow.trans (le_mul_of_one_le_left (by positivity) hK1)

/-- Every nonnegative `o(n)` scale is bounded above by a *monotone* nonnegative `o(n)` scale
(its running maximum). -/
theorem exists_monotone_isLittleO_ge {s : ℕ → ℝ} (hnn : ∀ n, 0 ≤ s n)
    (hs : s =o[atTop] fun n : ℕ => (n : ℝ)) :
    ∃ sBar : ℕ → ℝ, Monotone sBar ∧ (∀ n, 0 ≤ sBar n) ∧ (∀ n, s n ≤ sBar n) ∧
      (sBar =o[atTop] fun n : ℕ => (n : ℝ)) := by
  let sBar (N : ℕ) : ℝ := (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one s
  have hle : ∀ N, s N ≤ sBar N := fun N =>
    Finset.le_sup' s (Finset.mem_range.mpr (Nat.lt_succ_self N))
  have hnnBar : ∀ N, 0 ≤ sBar N := fun N => (hnn N).trans (hle N)
  have hmono : Monotone sBar := fun M N hMN =>
    Finset.sup'_mono s (Finset.range_mono (Nat.add_le_add_right hMN 1))
      Finset.nonempty_range_add_one
  refine ⟨sBar, hmono, hnnBar, hle, isLittleO_iff.mpr fun ε hε => ?_⟩
  have hev : ∀ᶠ m : ℕ in atTop, s m ≤ (ε / 2) * m := by
    filter_upwards [hs.bound (half_pos hε)] with m hm
    rw [Real.norm_of_nonneg (Nat.cast_nonneg m)] at hm
    exact (Real.le_norm_self (s m)).trans hm
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  let B : ℝ := ∑ m ∈ Finset.range N₀, s m
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun m _ => hnn m
  have hsBar_le : ∀ N : ℕ, sBar N ≤ B + (ε / 2) * N := fun N => by
    refine Finset.sup'_le Finset.nonempty_range_add_one s fun m hm => ?_
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    by_cases hm0 : m < N₀
    · have h1 : s m ≤ B :=
        Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_range.mpr hm0)
      have h2 : (0 : ℝ) ≤ (ε / 2) * N := by positivity
      linarith
    · have h1 : s m ≤ (ε / 2) * m := hN₀ m (not_lt.mp hm0)
      have h2 : (ε / 2) * m ≤ (ε / 2) * N := mul_le_mul_of_nonneg_left hmN (by positivity)
      linarith
  refine eventually_atTop.mpr ⟨⌈2 * B / ε⌉₊, fun N hN => ?_⟩
  have hBN : B ≤ (ε / 2) * N := by
    have hceil : 2 * B / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ hε] at hceil
    linarith
  rw [Real.norm_of_nonneg (hnnBar N), Real.norm_of_nonneg (Nat.cast_nonneg N)]
  linarith [hsBar_le N]

private theorem isLittleO_comp_linear_of_nonneg {s : ℕ → ℝ} (hnn : ∀ n, 0 ≤ s n)
    (hs : s =o[atTop] fun n : ℕ => (n : ℝ)) (c d : ℕ) :
    (fun n : ℕ => s (c * n + d)) =o[atTop] fun n : ℕ => (n : ℝ) := by
  refine isLittleO_iff.mpr fun ε hε => ?_
  by_cases hc : c = 0
  · subst hc
    refine eventually_atTop.mpr ⟨⌈s d / ε⌉₊ + 1, fun n hn => ?_⟩
    have hn_ge : s d / ε ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_of_succ_le hn))
    rw [div_le_iff₀ hε] at hn_ge
    simp only [zero_mul, zero_add]
    rw [Real.norm_of_nonneg (hnn d), Real.norm_of_nonneg (Nat.cast_nonneg n)]
    linarith
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc
    set ε' : ℝ := ε / (2 * c + 1)
    have hε' : 0 < ε' := by dsimp only [ε']; positivity
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hs.bound hε')
    refine eventually_atTop.mpr ⟨max M₀ d + 1, fun n hn => ?_⟩
    have hn_M : M₀ ≤ c * n + d := by
      have h1 : M₀ ≤ n := (le_max_left M₀ d).trans (Nat.le_of_succ_le hn)
      have h2 : n ≤ c * n := Nat.le_mul_of_pos_left n hc_pos
      omega
    have hd_n : d ≤ n := (le_max_right M₀ d).trans (Nat.le_of_succ_le hn)
    have hbound := hM₀ (c * n + d) hn_M
    rw [Real.norm_of_nonneg (hnn _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hbound
    have hlin : ((c * n + d : ℕ) : ℝ) ≤ (2 * c + 1 : ℝ) * n := by
      have hdnR : (d : ℝ) ≤ n := by exact_mod_cast hd_n
      have hcn : (0 : ℝ) ≤ (c : ℝ) * n := by positivity
      push_cast
      linarith
    have hmul : ε' * ((c * n + d : ℕ) : ℝ) ≤ ε * n := by
      have h1 := mul_le_mul_of_nonneg_left hlin hε'.le
      dsimp only [ε'] at h1
      have hne : (2 * (c : ℝ) + 1) ≠ 0 := by positivity
      calc (ε / (2 * c + 1)) * ((c * n + d : ℕ) : ℝ)
          ≤ (ε / (2 * c + 1)) * ((2 * c + 1) * n) := h1
        _ = ε * n := by field_simp [hne]
    rw [Real.norm_of_nonneg (hnn _), Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact hbound.trans hmul

/-! ### Single-machine subexponential decision and function computation -/

section SingleBounds

variable {α β γ : Type*}

/-- `A` is decidable in *single-machine* subexponential time in `μ`: a single machine and fixed
polynomial degree `e` decide `A` within time `O(2 ^ s (μ a) * (L + 1) ^ e)` for a nonnegative
scale `s =o[atTop] id`. -/
@[expose] def DecidableInSingleSubexpTime (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) : Prop :=
  ∃ (s : ℕ → ℝ) (e : ℕ), (∀ n, 0 ≤ s n) ∧ (s =o[atTop] fun n : ℕ => (n : ℝ)) ∧
    DecidableInTimeO A enc fun a => 2 ^ s (μ a) * ((enc a).length + 1) ^ e

/-- `f` is computable in *single-machine* subexponential time in `μ`: a single machine and fixed
polynomial degree `e` compute `f` within time `O(2 ^ s (μ a) * (L + 1) ^ e)` for a nonnegative
scale `s =o[atTop] id`. -/
@[expose] def ComputableInSingleSubexpTime (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (μ : α → ℕ) : Prop :=
  ∃ (s : ℕ → ℝ) (e : ℕ), (∀ n, 0 ≤ s n) ∧ (s =o[atTop] fun n : ℕ => (n : ℝ)) ∧
    ComputableInTimeO f encIn encOut fun a => 2 ^ s (μ a) * ((encIn a).length + 1) ^ e

/-- **Single-machine implies family subexponential decision.** -/
theorem DecidableInSingleSubexpTime.decidableInSubexpTime {A : Set α} {enc : α ↪ List Bool}
    {μ : α → ℕ} (h : DecidableInSingleSubexpTime A enc μ) :
    DecidableInSubexpTime A enc μ := by
  obtain ⟨s, e, _, hs_o, hO⟩ := h
  intro δ hδ
  obtain ⟨K, _, hK⟩ := exists_two_pow_le_of_isLittleO hs_o hδ
  refine ⟨e, hO.mono ⌈K⌉₊ (fun a => ?_) fun _ => by positivity⟩
  have h1 : (2 : ℝ) ^ s (μ a) ≤ ⌈K⌉₊ * (2 : ℝ) ^ (δ * μ a) :=
    (hK (μ a)).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))
  have h2 := mul_le_mul_of_nonneg_right h1
    (by positivity : (0 : ℝ) ≤ (((enc a).length : ℝ) + 1) ^ e)
  have h3 : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
  nlinarith

/-- **Single-machine implies family subexponential function computation.** -/
theorem ComputableInSingleSubexpTime.computableInSubexpTime {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {μ : α → ℕ}
    (h : ComputableInSingleSubexpTime f encIn encOut μ) :
    ComputableInSubexpTime f encIn encOut μ := by
  obtain ⟨s, e, _, hs_o, hO⟩ := h
  intro δ hδ
  obtain ⟨K, _, hK⟩ := exists_two_pow_le_of_isLittleO hs_o hδ
  refine ⟨e, hO.mono ⌈K⌉₊ (fun a => ?_) fun _ => by positivity⟩
  have h1 : (2 : ℝ) ^ s (μ a) ≤ ⌈K⌉₊ * (2 : ℝ) ^ (δ * μ a) :=
    (hK (μ a)).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))
  have h2 := mul_le_mul_of_nonneg_right h1
    (by positivity : (0 : ℝ) ≤ (((encIn a).length : ℝ) + 1) ^ e)
  have h3 : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
  nlinarith

/-! ### Quantifier-order characterization (`∃ (M, e), ∀ δ > 0, ∃ c`) -/

private theorem exists_isLittleO_of_forall_exp_bound {t : α → ℕ} {enc : α ↪ List Bool}
    {μ : α → ℕ} {e : ℕ}
    (h : ∀ δ : ℝ, 0 < δ → ∃ c : ℕ,
      ∀ a, (t a : ℝ) ≤ c * (2 ^ (δ * μ a) * ((enc a).length + 1) ^ e) + c) :
    ∃ s : ℕ → ℝ, (∀ n, 0 ≤ s n) ∧ (s =o[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ a, (t a : ℝ) ≤ 2 ^ s (μ a) * ((enc a).length + 1) ^ e := by
  let fiber (n : ℕ) : Set ℝ :=
    (fun a : α => (t a : ℝ) / (((enc a).length : ℝ) + 1) ^ e) '' {a : α | μ a = n}
  have hbdd_of_delta : ∀ {δ : ℝ}, 0 < δ → ∃ K : ℝ, 1 ≤ K ∧
      ∀ n : ℕ, ∀ y ∈ fiber n, y ≤ K * 2 ^ (δ * n) := by
    intro δ hδ
    obtain ⟨c, hc⟩ := h δ hδ
    refine ⟨2 * c + 1, by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)], ?_⟩
    rintro n _ ⟨a, ha, rfl⟩
    subst ha
    set P : ℝ := (((enc a).length : ℝ) + 1) ^ e
    have hP1 : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
    have hPpos : 0 < P := zero_lt_one.trans_le hP1
    have hX1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
    have hca := hc a
    rw [div_le_iff₀ hPpos]
    have hcP : (c : ℝ) ≤ c * (2 ^ (δ * μ a) * P) :=
      le_mul_of_one_le_right (Nat.cast_nonneg c) (one_le_mul_of_one_le_of_one_le hX1 hP1)
    have hpos : (0 : ℝ) ≤ 2 ^ (δ * μ a) * P := by positivity
    dsimp only [P] at *
    nlinarith
  have hbdd : ∀ n, BddAbove (fiber n) := fun n => by
    obtain ⟨K, _, hK⟩ := hbdd_of_delta one_pos
    exact ⟨K * 2 ^ ((1 : ℝ) * n), fun y hy => hK n y hy⟩
  let R (n : ℕ) : ℝ := max 1 (sSup (fiber n))
  let s (n : ℕ) : ℝ := Real.logb 2 (R n)
  have hR1 : ∀ n, 1 ≤ R n := fun n => le_max_left 1 _
  have hRpos : ∀ n, 0 < R n := fun n => zero_lt_one.trans_le (hR1 n)
  have hnn : ∀ n, 0 ≤ s n := fun n => Real.logb_nonneg one_lt_two (hR1 n)
  have hrpow : ∀ n, (2 : ℝ) ^ s n = R n := fun n =>
    Real.rpow_logb two_pos (by norm_num) (hRpos n)
  have hbound : ∀ a, (t a : ℝ) ≤ 2 ^ s (μ a) * ((enc a).length + 1) ^ e := fun a => by
    set P : ℝ := (((enc a).length : ℝ) + 1) ^ e
    have hPpos : 0 < P := by positivity
    have hmem : (t a : ℝ) / P ∈ fiber (μ a) := ⟨a, rfl, rfl⟩
    have hle_sup : (t a : ℝ) / P ≤ sSup (fiber (μ a)) := le_csSup (hbdd (μ a)) hmem
    have hle_R : (t a : ℝ) / P ≤ R (μ a) := hle_sup.trans (le_max_right 1 _)
    rw [hrpow (μ a)]
    exact (div_le_iff₀ hPpos).mp hle_R
  refine ⟨s, hnn, isLittleO_iff.mpr fun ε hε => ?_, hbound⟩
  obtain ⟨K, hK1, hK⟩ := hbdd_of_delta (half_pos hε)
  have hKpos : 0 < K := zero_lt_one.trans_le hK1
  have hR_le : ∀ n : ℕ, R n ≤ K * 2 ^ ((ε / 2) * n) := fun n => by
    have hX1 : (1 : ℝ) ≤ 2 ^ ((ε / 2) * n) := Real.one_le_rpow (by norm_num) (by positivity)
    have h1_le : (1 : ℝ) ≤ K * 2 ^ ((ε / 2) * n) := one_le_mul_of_one_le_of_one_le hK1 hX1
    refine max_le h1_le ?_
    rcases (fiber n).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, Real.sSup_empty]
      positivity
    · exact csSup_le hne fun y hy => hK n y hy
  let L : ℝ := Real.logb 2 K
  have hL_nn : 0 ≤ L := Real.logb_nonneg one_lt_two hK1
  have hs_le : ∀ n : ℕ, s n ≤ L + (ε / 2) * n := fun n => by
    have hpos : 0 < K * (2 : ℝ) ^ ((ε / 2) * n) := by positivity
    have hlog := Real.logb_le_logb_of_le one_lt_two (hRpos n) (hR_le n)
    have hpow_ne : (2 : ℝ) ^ ((ε / 2) * n) ≠ 0 := by positivity
    rw [Real.logb_mul hKpos.ne' hpow_ne,
      Real.logb_rpow two_pos (by norm_num : (2 : ℝ) ≠ 1)] at hlog
    exact hlog
  refine eventually_atTop.mpr ⟨⌈2 * L / ε⌉₊, fun n hn => ?_⟩
  have hLn : L ≤ (ε / 2) * n := by
    have hceil : 2 * L / ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hε] at hceil
    linarith
  rw [Real.norm_of_nonneg (hnn n), Real.norm_of_nonneg (Nat.cast_nonneg n)]
  linarith [hs_le n]

/-- **Machine-quantifier characterization of `DecidableInSingleSubexpTime`.** Single-machine
`2 ^ o(μ)` decision is equivalent to having *one* machine (`DecidableInTimeAndSpace A enc t sp`)
and *one* polynomial degree `e` that satisfy the `2 ^ (δ * μ a) * (L + 1) ^ e` runtime bound for
every `δ > 0` (with only the constant `c` depending on `δ`). -/
theorem decidableInSingleSubexpTime_iff_exists_machine {A : Set α} {enc : α ↪ List Bool}
    {μ : α → ℕ} :
    DecidableInSingleSubexpTime A enc μ ↔
      ∃ (t sp : α → ℕ) (e : ℕ), DecidableInTimeAndSpace A enc t sp ∧
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ,
          ∀ a, (t a : ℝ) ≤ c * (2 ^ (δ * μ a) * ((enc a).length + 1) ^ e) + c := by
  constructor
  · rintro ⟨s, e, _, hs_o, c₀, t, sp, ht, hdec⟩
    refine ⟨t, sp, e, hdec, fun δ hδ => ?_⟩
    obtain ⟨K, _, hK⟩ := exists_two_pow_le_of_isLittleO hs_o hδ
    refine ⟨c₀ * ⌈K⌉₊ + c₀, fun a => (ht a).trans ?_⟩
    have h1 : (2 : ℝ) ^ s (μ a) ≤ ⌈K⌉₊ * (2 : ℝ) ^ (δ * μ a) :=
      (hK (μ a)).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))
    have h2 := mul_le_mul_of_nonneg_right h1
      (by positivity : (0 : ℝ) ≤ (((enc a).length : ℝ) + 1) ^ e)
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c₀)
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * μ a) * (((enc a).length : ℝ) + 1) ^ e := by positivity
    have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
    push_cast
    nlinarith
  · rintro ⟨t, sp, e, hdec, h⟩
    obtain ⟨s, hnn, hs_o, hbound⟩ := exists_isLittleO_of_forall_exp_bound h
    refine ⟨s, e, hnn, hs_o, 1, t, sp, fun a => ?_, hdec⟩
    push_cast
    linarith [hbound a]

/-- **Machine-quantifier characterization of `ComputableInSingleSubexpTime`.** Single-machine
`2 ^ o(μ)` function computation is equivalent to having *one* machine
(`ComputableInTimeAndSpace f encIn encOut t sp`) and *one* polynomial degree `e` that satisfy the
`2 ^ (δ * μ a) * (L + 1) ^ e` runtime bound for every `δ > 0`. -/
theorem computableInSingleSubexpTime_iff_exists_machine {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {μ : α → ℕ} :
    ComputableInSingleSubexpTime f encIn encOut μ ↔
      ∃ (t sp : α → ℕ) (e : ℕ), ComputableInTimeAndSpace f encIn encOut t sp ∧
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ,
          ∀ a, (t a : ℝ) ≤ c * (2 ^ (δ * μ a) * ((encIn a).length + 1) ^ e) + c := by
  constructor
  · rintro ⟨s, e, _, hs_o, c₀, t, sp, ht, hcomp⟩
    refine ⟨t, sp, e, hcomp, fun δ hδ => ?_⟩
    obtain ⟨K, _, hK⟩ := exists_two_pow_le_of_isLittleO hs_o hδ
    refine ⟨c₀ * ⌈K⌉₊ + c₀, fun a => (ht a).trans ?_⟩
    have h1 : (2 : ℝ) ^ s (μ a) ≤ ⌈K⌉₊ * (2 : ℝ) ^ (δ * μ a) :=
      (hK (μ a)).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))
    have h2 := mul_le_mul_of_nonneg_right h1
      (by positivity : (0 : ℝ) ≤ (((encIn a).length : ℝ) + 1) ^ e)
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c₀)
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * μ a) * (((encIn a).length : ℝ) + 1) ^ e := by positivity
    have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
    push_cast
    nlinarith
  · rintro ⟨t, sp, e, hcomp, h⟩
    obtain ⟨s, hnn, hs_o, hbound⟩ := exists_isLittleO_of_forall_exp_bound h
    refine ⟨s, e, hnn, hs_o, 1, t, sp, fun a => ?_, hcomp⟩
    push_cast
    linarith [hbound a]

/-! ### Measure rescaling and reduction transfers -/

/-- Single-machine subexponential decision transfers to any parameter at least linear in `μ`. -/
theorem DecidableInSingleSubexpTime.mono_measure {A : Set α} {enc : α ↪ List Bool}
    {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : DecidableInSingleSubexpTime A enc μ) :
    DecidableInSingleSubexpTime A enc μ' := by
  obtain ⟨s, e, hnn, hs_o, hO⟩ := h
  obtain ⟨sBar, hmono, hnnBar, hle, hsBar_o⟩ := exists_monotone_isLittleO_ge hnn hs_o
  refine ⟨fun n => sBar (c * n + c), e, fun n => hnnBar _,
    isLittleO_comp_linear_of_nonneg hnnBar hsBar_o c c,
    hO.mono 1 (fun a => ?_) fun _ => by positivity⟩
  have h1 : s (μ a) ≤ sBar (c * μ' a + c) := (hle (μ a)).trans (hmono (hμ a))
  have h2 : (2 : ℝ) ^ s (μ a) ≤ 2 ^ sBar (c * μ' a + c) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have h3 := mul_le_mul_of_nonneg_right h2
    (by positivity : (0 : ℝ) ≤ (((enc a).length : ℝ) + 1) ^ e)
  push_cast
  linarith

/-- Single-machine subexponential function computation transfers to any parameter at least linear
in `μ`. -/
theorem ComputableInSingleSubexpTime.mono_measure {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : ComputableInSingleSubexpTime f encIn encOut μ) :
    ComputableInSingleSubexpTime f encIn encOut μ' := by
  obtain ⟨s, e, hnn, hs_o, hO⟩ := h
  obtain ⟨sBar, hmono, hnnBar, hle, hsBar_o⟩ := exists_monotone_isLittleO_ge hnn hs_o
  refine ⟨fun n => sBar (c * n + c), e, fun n => hnnBar _,
    isLittleO_comp_linear_of_nonneg hnnBar hsBar_o c c,
    hO.mono 1 (fun a => ?_) fun _ => by positivity⟩
  have h1 : s (μ a) ≤ sBar (c * μ' a + c) := (hle (μ a)).trans (hmono (hμ a))
  have h2 : (2 : ℝ) ^ s (μ a) ≤ 2 ^ sBar (c * μ' a + c) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have h3 := mul_le_mul_of_nonneg_right h2
    (by positivity : (0 : ℝ) ≤ (((encIn a).length : ℝ) + 1) ^ e)
  push_cast
  linarith

end SingleBounds

section SingleMachines

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Polynomial-time decidable sets are decidable in single-machine subexponential time. -/
theorem DecidableInSingleSubexpTime.of_computableInPolyTime {A : Set α} {μ : α → ℕ}
    {g : α → Bool} (hg : ComputableInPolyTime g encIn encBool) (hA : ∀ a, a ∈ A ↔ g a = true) :
    DecidableInSingleSubexpTime A encIn μ := by
  obtain ⟨e, hO⟩ := DecidableInExpTime.of_computableInPolyTime (μ := μ) hg hA
  refine ⟨fun _ => 0, e, fun _ => le_rfl, by simp, ?_⟩
  simpa only [zero_mul] using hO

/-- Polynomial-time computable functions are computable in single-machine subexponential time. -/
theorem ComputableInSingleSubexpTime.of_computableInPolyTime {f : α → β} {μ : α → ℕ}
    (hf : ComputableInPolyTime f encIn encMid) :
    ComputableInSingleSubexpTime f encIn encMid μ := by
  obtain ⟨e, hO⟩ := ComputableInExpTime.of_computableInPolyTime (μ := μ) hf
  refine ⟨fun _ => 0, e, fun _ => le_rfl, by simp, ?_⟩
  simpa only [zero_mul] using hO

/-- Guarding a single-machine subexponential function by a polynomial-time test and fallback
preserves single-machine subexponential time. -/
theorem ComputableInSingleSubexpTime.ite_polyTime {f g : α → β} {p : α → Bool} {μ : α → ℕ}
    (hp : ComputableInPolyTime p encIn encBool)
    (hf : ComputableInSingleSubexpTime f encIn encMid μ)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInSingleSubexpTime (fun a => if p a then f a else g a) encIn encMid μ := by
  obtain ⟨t, sp, e, hcomp, hbound⟩ := computableInSingleSubexpTime_iff_exists_machine.mp hf
  have hl : ∀ a, (encMid (f a)).length ≤ t a := hcomp.length_le
  obtain ⟨k, hf'⟩ := ComputableInTimeAndSpace.exists_space_linear hcomp
  have hfO : ComputableInO f encIn encMid t t := ComputableInO.of_bounds hf' (k + 1)
    (fun a => by nlinarith) (fun a => by nlinarith) (fun a => by nlinarith [hl a])
  obtain ⟨dp, _, hp'⟩ := hp.exists_degree
  obtain ⟨dg, _, hg'⟩ := hg.exists_degree
  obtain ⟨c_comb, hcomb_ts, -⟩ := hp'.inO.ite hfO hg'.inO
  refine computableInSingleSubexpTime_iff_exists_machine.mpr
    ⟨_, _, dp + dg + e, hcomb_ts, fun δ hδ => ?_⟩
  obtain ⟨c, hc⟩ := hbound δ hδ
  refine ⟨c_comb * (2 * c + 4), fun a => ?_⟩
  set L : ℝ := ((encIn a).length : ℝ)
  have hL1 : (1 : ℝ) ≤ L + 1 := by
    dsimp only [L]
    linarith [(Nat.cast_nonneg (encIn a).length : (0 : ℝ) ≤ _)]
  have hX1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
  have hdp : (L + 1) ^ dp ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) :=
    (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
  have hdg : (L + 1) ^ dg ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) :=
    (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
  have he : (L + 1) ^ e ≤ (L + 1) ^ (dp + dg + e) := pow_le_pow_right₀ hL1 (by omega)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hcc0 : (0 : ℝ) ≤ c_comb := Nat.cast_nonneg c_comb
  have hpos : (0 : ℝ) ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) := by positivity
  have ht_le : (t a : ℝ) ≤ (2 * c + 1) * (2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e)) := by
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 ^ (δ * μ a))
    have hmulc := mul_le_mul_of_nonneg_left hmul hc0
    have hc1 : (c : ℝ) ≤ c * (2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e)) :=
      le_mul_of_one_le_right hc0 (one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hL1))
    dsimp only [L] at *
    nlinarith [hc a]
  have h1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) * (L + 1) ^ (dp + dg + e) :=
    one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hL1)
  change ((c_comb * ((((encIn a).length + 1) ^ dp +
    if p a then t a else ((encIn a).length + 1) ^ dg) + 1) : ℕ) : ℝ) ≤ _
  split_ifs
  · push_cast
    dsimp only [L] at *
    nlinarith
  · push_cast
    dsimp only [L] at *
    nlinarith

/-- **Single-machine decision from function computation.** Composing a single-machine
subexponential function of polynomially bounded output length with a polynomial-time test yields a
single-machine subexponential decision procedure. -/
theorem DecidableInSingleSubexpTime.of_computableInSingleSubexpTime_polyBounded
    {f : α → β} {μ : α → ℕ}
    (hf : ComputableInSingleSubexpTime f encIn encMid μ)
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (encMid (f a)).length))
    {test : β → Bool} (htest : ComputableInPolyTime test encMid encBool) :
    DecidableInSingleSubexpTime {a | test (f a) = true} encIn μ := by
  obtain ⟨s, e, hnn, hs_o, hfO_time⟩ := hf
  obtain ⟨t, c, hfO, ht⟩ := hfO_time.exists_computableInO
  obtain ⟨d, _, htest'⟩ := htest.exists_degree
  obtain ⟨p, q, hp⟩ := hlen.exists_le
  obtain ⟨c_comp, hcomp_ts, -⟩ := htest'.inO.comp hfO
  refine ⟨s, e + q * d, hnn, hs_o, c_comp * (2 * c + 2 + (p + 1) ^ d), _, _, fun a => ?_,
    decidableInTimeAndSpace_iff.mpr ⟨test ∘ f, hcomp_ts, fun _ => Iff.rfl⟩⟩
  set L : ℕ := (encIn a).length
  have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast hL1
  have hX1 : (1 : ℝ) ≤ 2 ^ s (μ a) := Real.one_le_rpow (by norm_num) (hnn (μ a))
  have hout_pow : ((encMid (f a)).length + 1) ^ d ≤ (p + 1) ^ d * (L + 1) ^ (q * d) :=
    Nat.add_one_pow_le_of_le_mul_pow hL1 (hp a) d
  have hqd : ((L : ℝ) + 1) ^ (q * d) ≤ ((L : ℝ) + 1) ^ (e + q * d) :=
    pow_le_pow_right₀ hLR1 (Nat.le_add_left _ _)
  have he : ((L : ℝ) + 1) ^ e ≤ ((L : ℝ) + 1) ^ (e + q * d) :=
    pow_le_pow_right₀ hLR1 (Nat.le_add_right _ _)
  have houtR : (((encMid (f a)).length : ℝ) + 1) ^ d ≤
      ((p + 1) ^ d : ℕ) * (2 ^ s (μ a) * ((L : ℝ) + 1) ^ (e + q * d)) := by
    have h1 : (((encMid (f a)).length : ℝ) + 1) ^ d ≤
        ((p + 1) ^ d : ℕ) * ((L : ℝ) + 1) ^ (q * d) := by exact_mod_cast hout_pow
    have h2 : ((L : ℝ) + 1) ^ (q * d) ≤ 2 ^ s (μ a) * ((L : ℝ) + 1) ^ (e + q * d) :=
      hqd.trans (le_mul_of_one_le_left (by positivity) hX1)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  have htR : (t a : ℝ) ≤ (2 * c + 1 : ℕ) * (2 ^ s (μ a) * ((L : ℝ) + 1) ^ (e + q * d)) := by
    have h1 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 ^ s (μ a))
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
    have h3 : (1 : ℝ) ≤ 2 ^ s (μ a) * ((L : ℝ) + 1) ^ (e + q * d) :=
      one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hLR1)
    have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg c)
    push_cast
    dsimp only [L] at *
    linarith [ht a]
  have h1 : (1 : ℝ) ≤ 2 ^ s (μ a) * ((L : ℝ) + 1) ^ (e + q * d) :=
    one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hLR1)
  have hsum : (t a : ℝ) + (((encMid (f a)).length : ℝ) + 1) ^ d + 1 ≤
      (2 * c + 2 + (p + 1) ^ d : ℕ) * (2 ^ s (μ a) * ((L : ℝ) + 1) ^ (e + q * d)) := by
    push_cast at htR houtR ⊢
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg c_comp)
  have hnonneg : (0 : ℝ) ≤ (c_comp * (2 * c + 2 + (p + 1) ^ d) : ℕ) := Nat.cast_nonneg _
  change ((c_comp * ((t a + ((encMid (f a)).length + 1) ^ d) + 1) : ℕ) : ℝ) ≤ _
  push_cast at hmul hnonneg ⊢
  dsimp only [L] at *
  linarith

/-- **Transfer along linear-parameter parsimonious reductions (`SingleSubexp`).** -/
theorem ComputableInSingleSubexpTime.of_reduction {μA : α → ℕ} {μB : β → ℕ}
    {r : α → β} {g : β → γ}
    (hr : ComputableInPolyTime r encIn encMid) {c : ℕ}
    (hμ : ∀ a, μB (r a) ≤ c * μA a + c)
    (hg : ComputableInSingleSubexpTime g encMid encOut μB) :
    ComputableInSingleSubexpTime (g ∘ r) encIn encOut μA := by
  obtain ⟨s, e, hnn, hs_o, hg_time⟩ := hg
  obtain ⟨sBar, hmono, hnnBar, hle, hsBar_o⟩ := exists_monotone_isLittleO_ge hnn hs_o
  obtain ⟨t, k, hgO, ht⟩ := hg_time.exists_computableInO
  obtain ⟨d, _, hr'⟩ := hr.exists_degree
  obtain ⟨l, hl⟩ := hr'.inO.length_le_time
  let s' (n : ℕ) : ℝ := sBar (c * n + c)
  refine ⟨s', d * (e + 1), fun n => hnnBar _,
    isLittleO_comp_linear_of_nonneg hnnBar hsBar_o c c,
    (ComputableInTimeO.of_computableInO (hgO.comp hr'.inO) fun _ => le_rfl).mono
      (1 + k * (2 * l + 1) ^ e + k) (fun a => ?_) fun _ => by positivity⟩
  set P : ℝ := (((encIn a).length : ℝ) + 1) ^ d
  set X : ℝ := (2 : ℝ) ^ s' (μA a)
  have hP : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (hnnBar _)
  have hn : ((encMid (r a)).length : ℝ) ≤ l * (P + 1) := by
    dsimp only [P]
    exact_mod_cast hl a
  have hexp : (2 : ℝ) ^ s (μB (r a)) ≤ X := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact (hle _).trans (hmono (hμ a))
  have hpow : (((encMid (r a)).length : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) e
  have hT' := mul_le_mul_of_nonneg_left (mul_le_mul hexp hpow (by positivity) (by positivity))
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have h₁ : P ≤ X * P ^ (e + 1) :=
    (le_self_pow₀ hP (Nat.succ_ne_zero e)).trans (le_mul_of_one_le_left (by positivity) hX)
  have h₂ : X * P ^ e ≤ X * P ^ (e + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (Nat.le_add_right e 1)) (by positivity)
  have h₂' := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ k * (2 * l + 1) ^ e)
  have h₃ : (k : ℝ) ≤ k * (X * P ^ (e + 1)) :=
    le_mul_of_one_le_right (Nat.cast_nonneg k)
      (one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP))
  have hsum : P + t (r a) ≤ (1 + k * (2 * l + 1) ^ e + k) * (X * P ^ (e + 1)) := by
    linarith [ht (r a)]
  change ((((encIn a).length + 1) ^ d + t (r a) : ℕ) : ℝ) ≤ _
  have hc_nn : (0 : ℝ) ≤ (1 + k * (2 * l + 1) ^ e + k : ℕ) := Nat.cast_nonneg _
  push_cast at hc_nn ⊢
  rw [pow_mul]
  dsimp only [P, X] at hsum ⊢
  linarith

/-- **Transfer along linear-parameter polynomial-time reductions (`SingleSubexp` decision).** -/
theorem DecidableInSingleSubexpTime.of_reduction {A : Set α} {B : Set β}
    {μA : α → ℕ} {μB : β → ℕ} {r : α → β}
    (hr : ComputableInPolyTime r encIn encMid) (hAB : ∀ a, a ∈ A ↔ r a ∈ B)
    {c : ℕ} (hμ : ∀ a, μB (r a) ≤ c * μA a + c)
    (hB : DecidableInSingleSubexpTime B encMid μB) :
    DecidableInSingleSubexpTime A encIn μA := by
  obtain ⟨s, e, hnn, hs_o, hB_time⟩ := hB
  obtain ⟨g, hgB, hg_time⟩ := decidableInTimeO_iff_exists_computableInTimeO.mp hB_time
  have hg_single : ComputableInSingleSubexpTime g encMid encBool μB :=
    ⟨s, e, hnn, hs_o, hg_time⟩
  obtain ⟨s', e', hnn', hs'_o, hgr_time⟩ := hg_single.of_reduction hr hμ
  exact ⟨s', e', hnn', hs'_o,
    decidableInTimeO_iff_exists_computableInTimeO.mpr ⟨g ∘ r, fun a => (hAB a).trans (hgB (r a)),
      hgr_time⟩⟩

end SingleMachines

/-! ### `SingleETH`, `SingleSharpETH`, and native single-machine algorithms -/

/-- **Single-machine `ETH`:** `3`-SAT is not decidable by a single machine in time
`2 ^ o(n) · poly(L)` (`n = φ.numVars`). -/
@[expose] def SingleETH : Prop :=
  ¬DecidableInSingleSubexpTime (KSAT 3) encCNF CNF.numVars

/-- **Single-machine `#ETH`:** `#3-SAT` is not computable by a single machine in time
`2 ^ o(n) · poly(L)` (`n = φ.numVars`). -/
@[expose] def SingleSharpETH : Prop :=
  ¬ComputableInSingleSubexpTime SharpThreeSAT encCNF encNat CNF.numVars

/-- Family `ETH` implies single-machine `SingleETH` (the contrapositive
`DecidableInSingleSubexpTime.decidableInSubexpTime` is unconditional). -/
theorem ETH.singleETH (h : ETH) : SingleETH := fun hsingle =>
  (ETH_iff_not_decidableInSubexpTime.mp h) hsingle.decidableInSubexpTime

/-- Family `SharpETH` implies single-machine `SingleSharpETH`. -/
theorem SharpETH.singleSharpETH (h : SharpETH) : SingleSharpETH := fun hsingle =>
  (SharpETH_iff_not_computableInSubexpTime.mp h) hsingle.computableInSubexpTime

/-- Single-machine `#k-SAT` counting gives single-machine `k`-SAT decision. -/
theorem DecidableInSingleSubexpTime.KSAT_of_SharpKSAT {k : ℕ}
    (h : ComputableInSingleSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars) :
    DecidableInSingleSubexpTime (KSAT k) encCNF CNF.numVars := by
  have hdec := DecidableInSingleSubexpTime.of_computableInSingleSubexpTime_polyBounded h
    (polyBounded_length_encNat_SharpKSAT k) computableInPolyTime_pos_nat
  have heq : {φ : CNF ℕ | decide (0 < SharpKSAT k φ) = true} = KSAT k := by
    ext φ
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq, mem_KSAT_iff_pos_SharpKSAT]
  rwa [heq] at hdec

/-- Single-machine decision hardness implies single-machine counting hardness
(`SingleETH → SingleSharpETH`). -/
theorem SingleETH.singleSharpETH (h : SingleETH) : SingleSharpETH := fun hcount =>
  h (DecidableInSingleSubexpTime.KSAT_of_SharpKSAT hcount)

/-- Single-machine `#k-SAT` counting in `numVars` gives single-machine `#k-SAT` counting in
clause count `List.length`. -/
theorem ComputableInSingleSubexpTime.SharpKSAT_length_of_numVars {k : ℕ}
    (h : ComputableInSingleSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars) :
    ComputableInSingleSubexpTime (SharpKSAT k) encCNF encNat List.length := by
  obtain ⟨s, e, hnn, hs_o, htime⟩ := h
  obtain ⟨sBar, hmono, hnnBar, hle, hsBar_o⟩ := exists_monotone_isLittleO_ge hnn hs_o
  obtain ⟨t, c, hO, ht⟩ := htime.exists_computableInO
  obtain ⟨dw, _, hw⟩ := (computableInPolyTime_all_length_le k).exists_degree
  obtain ⟨dc, _, hc0⟩ := (ComputableInPolyTime.const (encIn := encCNF) (0 : ℕ)).exists_degree
  have hite := (hw.inO.ite hO hc0.inO).of_enc_eq (g := SharpKSAT k) fun φ => congrArg encNat <| by
    split_ifs with hφ
    · simp only [SharpKSAT, hφ, ↓reduceIte]
    · simp only [SharpKSAT, hφ, Bool.false_eq_true, ↓reduceIte]
  let s' (m : ℕ) : ℝ := sBar (k * m + 0)
  refine ⟨s', dw + dc + e, fun m => hnnBar _,
    isLittleO_comp_linear_of_nonneg hnnBar hsBar_o k 0,
    (ComputableInTimeO.of_computableInO hite fun _ => le_rfl).mono (2 * c + 3)
      (fun φ => ?_) fun _ => by positivity⟩
  set L : ℝ := ((encCNF φ).length : ℝ)
  have hL1 : (1 : ℝ) ≤ L + 1 := by
    dsimp only [L]
    linarith [(Nat.cast_nonneg (encCNF φ).length : (0 : ℝ) ≤ _)]
  have hX1 : (1 : ℝ) ≤ 2 ^ s' φ.length := Real.one_le_rpow (by norm_num) (hnnBar _)
  have hdw : (L + 1) ^ dw ≤ 2 ^ s' φ.length * (L + 1) ^ (dw + dc + e) :=
    (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
  have hdc : (L + 1) ^ dc ≤ 2 ^ s' φ.length * (L + 1) ^ (dw + dc + e) :=
    (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
  have he : (L + 1) ^ e ≤ (L + 1) ^ (dw + dc + e) := pow_le_pow_right₀ hL1 (by omega)
  have hc_nn : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hpos : (0 : ℝ) ≤ 2 ^ s' φ.length * (L + 1) ^ (dw + dc + e) := by positivity
  change ((((encCNF φ).length + 1) ^ dw +
    if φ.all (fun cl => decide (cl.length ≤ k)) then t φ
    else ((encCNF φ).length + 1) ^ dc : ℕ) : ℝ) ≤ _
  split_ifs with hφ
  · simp only [List.all_eq_true, decide_eq_true_eq] at hφ
    have hexp : (2 : ℝ) ^ s φ.numVars ≤ 2 ^ s' φ.length := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      exact (hle _).trans (hmono (by simpa only [Nat.add_zero] using CNF.numVars_le_mul_length hφ))
    have hmul := mul_le_mul hexp he (by positivity) (by positivity)
    have hmulc := mul_le_mul_of_nonneg_left hmul hc_nn
    have hc1 : (c : ℝ) ≤ c * (2 ^ s' φ.length * (L + 1) ^ (dw + dc + e)) :=
      le_mul_of_one_le_right hc_nn (one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hL1))
    push_cast
    dsimp only [L] at *
    nlinarith [ht φ]
  · push_cast
    dsimp only [L] at *
    nlinarith

/-- Input to declared-variable model counting: a unary declared variable bound `numDeclared` and a
CNF formula `formula`. -/
structure DeclaredFormula where
  /-- Declared variable bound `N`, representing the domain `Finset.range N`. -/
  numDeclared : ℕ
  /-- Input CNF formula over natural variable indices. -/
  formula : CNF ℕ
  deriving Inhabited

/-- Framed encoding of `DeclaredFormula` (`numDeclared` in unary, `formula` via `encCNF`). -/
enc_structure encDeclaredFormula : DeclaredFormula where
  numDeclared : encUnary, formula : encCNF

/-- Guarded model count of `x.formula` on `Finset.range x.numDeclared` when `x.formula` has clause
width `≤ k` and all variables `< x.numDeclared`, and `0` otherwise. -/
@[expose] def SharpDeclaredKSAT (k : ℕ) (x : DeclaredFormula) : ℕ :=
  if CNF.validDeclaredInput k x.numDeclared x.formula then
    x.formula.modelCountOn (Finset.range x.numDeclared)
  else 0

/-- On valid declared inputs, `SharpDeclaredKSAT k x` scales `x.formula.modelCount` by the
`2 ^ (x.numDeclared - x.formula.numVars)` assignments to unused declared variables. -/
theorem SharpDeclaredKSAT_of_valid {k : ℕ} {x : DeclaredFormula}
    (hw : ∀ c ∈ x.formula, c.length ≤ k) (hv : ∀ v ∈ x.formula.vars, v < x.numDeclared) :
    SharpDeclaredKSAT k x = x.formula.modelCount * 2 ^ (x.numDeclared - x.formula.numVars) := by
  have hsub : x.formula.vars.toFinset ⊆ Finset.range x.numDeclared := fun v hmem =>
    Finset.mem_range.mpr (hv v (List.mem_toFinset.mp hmem))
  have hval : CNF.validDeclaredInput k x.numDeclared x.formula = true :=
    CNF.validDeclaredInput_eq_true_iff.mpr ⟨hw, hsub⟩
  simp only [SharpDeclaredKSAT, hval, ↓reduceIte,
    CNF.modelCountOn_eq_mul_modelCount x.formula _ hsub, Finset.card_range, Nat.mul_comm]

/-- On invalid declared inputs (`CNF.validDeclaredInput = false`), `SharpDeclaredKSAT k x = 0`. -/
theorem SharpDeclaredKSAT_of_not_valid {k : ℕ} {x : DeclaredFormula}
    (h : CNF.validDeclaredInput k x.numDeclared x.formula = false) :
    SharpDeclaredKSAT k x = 0 := by
  simp only [SharpDeclaredKSAT, h, Bool.false_eq_true, ↓reduceIte]

/-- **Unconditional single-machine declared model counting.** For each fixed width `k`, one native
multi-tape machine computes `SharpDeclaredKSAT k` in time `2 ^ o(numDeclared) · poly(L)`. -/
theorem computableInSingleSubexpTime_SharpDeclaredKSAT (k : ℕ) :
    ComputableInSingleSubexpTime (SharpDeclaredKSAT k) encDeclaredFormula encNat
      DeclaredFormula.numDeclared := by
  open SubexponentialSAT in
  obtain ⟨count, T, S, A, c, e, _, _, hcountO, hspec, hT, -⟩ :=
    CountingNativeEndpoint.exists_declaredCounter k
  have htoPair : ComputableInPolyTime (fun x : DeclaredFormula => (x.numDeclared, x.formula))
      encDeclaredFormula (encPair encUnary encCNF) := by fun_prop
  obtain ⟨dg, _, hdg⟩ := htoPair.exists_degree
  obtain ⟨p, q, hp⟩ := htoPair.polyBounded_length.exists_le
  have hcompO := (hcountO.comp hdg.inO).of_enc_eq (g := SharpDeclaredKSAT k) fun x =>
    congrArg encNat (hspec (x.numDeclared, x.formula)).symm
  let s (N : ℕ) : ℝ := (A : ℝ) * interpolationScale N
  have hs_nn : ∀ N, 0 ≤ s N := fun N =>
    mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg N)
  have hs_o : s =o[atTop] fun N : ℕ => (N : ℝ) :=
    isLittleO_interpolationScale.const_mul_left (A : ℝ)
  refine ⟨s, dg + q * e, hs_nn, hs_o,
    (ComputableInTimeO.of_computableInO hcompO fun _ => le_rfl).mono
      (1 + c * (p + 1) ^ e + c) (fun x => ?_) fun _ => by positivity⟩
  set L : ℕ := (encDeclaredFormula x).length
  have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast hL1
  have hX1 : (1 : ℝ) ≤ 2 ^ s x.numDeclared := Real.one_le_rpow (by norm_num) (hs_nn _)
  have hpow : ((encPair encUnary encCNF (x.numDeclared, x.formula)).length + 1) ^ e ≤
      (p + 1) ^ e * (L + 1) ^ (q * e) :=
    Nat.add_one_pow_le_of_le_mul_pow hL1 (hp x) e
  have hqe : ((L : ℝ) + 1) ^ (q * e) ≤ ((L : ℝ) + 1) ^ (dg + q * e) :=
    pow_le_pow_right₀ hLR1 (Nat.le_add_left _ _)
  have hdg_le : ((L : ℝ) + 1) ^ dg ≤ 2 ^ s x.numDeclared * ((L : ℝ) + 1) ^ (dg + q * e) :=
    (pow_le_pow_right₀ hLR1 (Nat.le_add_right _ _)).trans
      (le_mul_of_one_le_left (by positivity) hX1)
  have hpowR : (((encPair encUnary encCNF (x.numDeclared, x.formula)).length : ℝ) + 1) ^ e ≤
      ((p + 1) ^ e : ℕ) * ((L : ℝ) + 1) ^ (dg + q * e) := by
    have h1 : (((encPair encUnary encCNF (x.numDeclared, x.formula)).length : ℝ) + 1) ^ e ≤
        ((p + 1) ^ e : ℕ) * ((L : ℝ) + 1) ^ (q * e) := by exact_mod_cast hpow
    exact h1.trans (mul_le_mul_of_nonneg_left hqe (Nat.cast_nonneg _))
  have hTR : (T (x.numDeclared, x.formula) : ℝ) ≤
      ((c * (p + 1) ^ e : ℕ) : ℝ) * (2 ^ s x.numDeclared * ((L : ℝ) + 1) ^ (dg + q * e)) + c := by
    have h0 := hT (x.numDeclared, x.formula)
    have hmul : (2 : ℝ) ^ s x.numDeclared *
        (((encPair encUnary encCNF (x.numDeclared, x.formula)).length : ℝ) + 1) ^ e ≤
        ((p + 1) ^ e : ℕ) * (2 ^ s x.numDeclared * ((L : ℝ) + 1) ^ (dg + q * e)) := by
      have hm := mul_le_mul_of_nonneg_left hpowR (by positivity : (0 : ℝ) ≤ 2 ^ s x.numDeclared)
      linarith [show (2 : ℝ) ^ s x.numDeclared * (((p + 1) ^ e : ℕ) * ((L : ℝ) + 1) ^ (dg + q * e))
        = ((p + 1) ^ e : ℕ) * (2 ^ s x.numDeclared * ((L : ℝ) + 1) ^ (dg + q * e)) by ring]
    have hmulc := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg c)
    push_cast at hmulc ⊢
    dsimp only [s] at *
    linarith
  have hc1 : (c : ℝ) ≤ c * (2 ^ s x.numDeclared * ((L : ℝ) + 1) ^ (dg + q * e)) :=
    le_mul_of_one_le_right (Nat.cast_nonneg c)
      (one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hLR1))
  have hconst_nn : (0 : ℝ) ≤ (1 + c * (p + 1) ^ e + c : ℕ) := Nat.cast_nonneg _
  change ((((encDeclaredFormula x).length + 1) ^ dg +
    T (x.numDeclared, x.formula) : ℕ) : ℝ) ≤ _
  push_cast at hTR hconst_nn ⊢
  dsimp only [L] at *
  linarith

/-- **Unconditional single-machine `#k-SAT` model counting.** For each fixed width `k`, a *single*
native multi-tape machine computes `SharpKSAT k` in time `2 ^ o(n) · poly(L)` (`n = φ.numVars`). -/
theorem computableInSingleSubexpTime_SharpKSAT (k : ℕ) :
    ComputableInSingleSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars := by
  open SubexponentialSAT in
  obtain ⟨count, A, e, _, hspec, hcountO⟩ := CountingNativeEndpoint.exists_modelCounter k
  let s (n : ℕ) : ℝ := (A : ℝ) * interpolationScale n
  have hs_nn : ∀ n, 0 ≤ s n := fun n =>
    mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg n)
  have hs_o : s =o[atTop] fun n : ℕ => (n : ℝ) :=
    isLittleO_interpolationScale.const_mul_left (A : ℝ)
  have hraw : ComputableInSingleSubexpTime count encCNF encNat CNF.numVars := by
    refine ⟨s, e, hs_nn, hs_o,
      (ComputableInTimeO.of_computableInO hcountO fun _ => le_rfl).mono 2
        (fun φ => ?_) fun _ => by positivity⟩
    set X : ℝ := (2 : ℝ) ^ s φ.numVars
    have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (hs_nn _)
    have hceil : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
      have hlt := (Nat.ceil_lt_add_one (by positivity : 0 ≤ X)).le
      linarith
    have hmul := mul_le_mul_of_nonneg_right hceil
      (by positivity : (0 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ e)
    push_cast
    dsimp only [X, s] at hmul ⊢
    linarith
  have hguarded := hraw.ite_polyTime (computableInPolyTime_all_length_le k)
    (ComputableInPolyTime.const 0)
  have heq : (fun φ : CNF ℕ => if φ.all (fun c => decide (c.length ≤ k)) then count φ else 0) =
      SharpKSAT k := by
    funext φ
    unfold SharpKSAT SharpSAT
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      exact hspec φ hw
    · rfl
  rwa [heq] at hguarded

/-- **Unconditional single-machine `k`-SAT decision.** For each fixed width `k`, a *single* native
multi-tape machine decides `KSAT k` in time `2 ^ o(n) · poly(L)` (`n = φ.numVars`). -/
theorem decidableInSingleSubexpTime_KSAT (k : ℕ) :
    DecidableInSingleSubexpTime (KSAT k) encCNF CNF.numVars :=
  DecidableInSingleSubexpTime.KSAT_of_SharpKSAT (computableInSingleSubexpTime_SharpKSAT k)

/-- The single-machine native `3`-SAT solver refutes `SingleETH`. -/
theorem not_SingleETH : ¬SingleETH := fun h => h (decidableInSingleSubexpTime_KSAT 3)

/-- The single-machine native `#3-SAT` counter refutes `SingleSharpETH`. -/
theorem not_SingleSharpETH : ¬SingleSharpETH := fun h =>
  h (computableInSingleSubexpTime_SharpKSAT 3)

end Cslib.Complexity
