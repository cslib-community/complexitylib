/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
public import Mathlib.Analysis.Asymptotics.Defs
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Foundations.Analysis.SublinearEnvelope
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
* **Monotone envelope and transfers** (`Cslib.exists_monotone_isLittleO_ge`,
  `DecidableInSingleSubexpTime.of_reduction`, `ComputableInSingleSubexpTime.of_reduction`):
  replacing `s` by its running maximum `(Finset.range (n + 1)).sup' _ s` preserves `s =o[atTop] id`
  while making `s` monotone, so single-machine subexponential time transfers unconditionally along
  linear-parameter polynomial-time and parsimonious reductions.
* **Effective-uniformity converse** (`PrecisionInput`,
  `DecidableInSingleSubexpTime.of_uniformFamily`, `ComputableInSingleSubexpTime.of_uniformFamily`):
  an effectively uniform rate family solving `(m, a)` at rate `1 / (m + 1)` with polynomial overhead
  in `m` yields a single machine running in time `2 ^ o(μ a) · poly(L)` by diagonally scheduling `m`
  in polynomial time.

## Main definitions

* `Cslib.Complexity.DecidableInSingleSubexpTime`,
  `Cslib.Complexity.ComputableInSingleSubexpTime`: single-machine `2 ^ o(μ) · poly(L)` time.
* `Cslib.Complexity.PrecisionInput`, `Cslib.Complexity.PrecisionInput.encoding`: unary-precision
  input pairs for uniform rate families.
* `Cslib.Complexity.SingleETH`, `Cslib.Complexity.SingleSharpETH`: single-machine `ETH` and `#ETH`.

## Main results

* `Cslib.Complexity.decidableInSingleSubexpTime_iff_exists_computableInSingleSubexpTime`: decision
  as single-machine computation of a Boolean indicator. The `Decidable…` transfers are derived from
  their `Computable…` counterparts through it.
* `Cslib.Complexity.decidableInSingleSubexpTime_iff_exists_machine`,
  `Cslib.Complexity.computableInSingleSubexpTime_iff_exists_machine`: equivalence with exchanging
  `∃ (M, e)` and `∀ δ > 0`.
* `Cslib.Complexity.DecidableInSingleSubexpTime.of_uniformFamily`,
  `Cslib.Complexity.ComputableInSingleSubexpTime.of_uniformFamily`: conversion from effectively
  uniform rate families back to a single `2 ^ o(μ)` machine.
* `Cslib.Complexity.DecidableInSingleSubexpTime.of_reduction`,
  `Cslib.Complexity.ComputableInSingleSubexpTime.of_reduction`,
  `Cslib.Complexity.DecidableInSingleSubexpTime.of_computableInSingleSubexpTime_polyBounded`:
  unconditional single-machine reduction and decision-from-counting transfers.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing Turing.MultiTapeTM Filter Asymptotics Topology

/-! ### Asymptotic rescaling for `o(n)` exponents -/

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

/-- `DecidableInSingleSubexpTime` is `ComputableInSingleSubexpTime` of a Boolean indicator
function. -/
theorem decidableInSingleSubexpTime_iff_exists_computableInSingleSubexpTime {A : Set α}
    {enc : α ↪ List Bool} {μ : α → ℕ} :
    DecidableInSingleSubexpTime A enc μ ↔
      ∃ g : α → Bool, (∀ a, a ∈ A ↔ g a = true) ∧
        ComputableInSingleSubexpTime g enc encBool μ := by
  constructor
  · rintro ⟨s, e, hnn, hs_o, h⟩
    obtain ⟨g, hA, hg⟩ := decidableInTimeO_iff_exists_computableInTimeO.mp h
    exact ⟨g, hA, s, e, hnn, hs_o, hg⟩
  · rintro ⟨g, hA, s, e, hnn, hs_o, hg⟩
    exact ⟨s, e, hnn, hs_o, decidableInTimeO_iff_exists_computableInTimeO.mpr ⟨g, hA, hg⟩⟩

/-- **Single-machine implies family subexponential decision.** -/
theorem DecidableInSingleSubexpTime.decidableInSubexpTime {A : Set α} {enc : α ↪ List Bool}
    {μ : α → ℕ} (h : DecidableInSingleSubexpTime A enc μ) :
    DecidableInSubexpTime A enc μ := by
  obtain ⟨s, e, _, hs_o, hO⟩ := h
  intro δ hδ
  obtain ⟨K, _, hK⟩ := exists_two_pow_le_of_isLittleO hs_o hδ
  exact ⟨e, hO.mono _ (fun a => two_rpow_mul_pow_le_natCeil_mul_add_of_le (hK (μ a)))
    fun _ => by positivity⟩

/-- **Single-machine implies family subexponential function computation.** -/
theorem ComputableInSingleSubexpTime.computableInSubexpTime {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {μ : α → ℕ}
    (h : ComputableInSingleSubexpTime f encIn encOut μ) :
    ComputableInSubexpTime f encIn encOut μ := by
  obtain ⟨s, e, _, hs_o, hO⟩ := h
  intro δ hδ
  obtain ⟨K, _, hK⟩ := exists_two_pow_le_of_isLittleO hs_o hδ
  exact ⟨e, hO.mono _ (fun a => two_rpow_mul_pow_le_natCeil_mul_add_of_le (hK (μ a)))
    fun _ => by positivity⟩

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
    have h := mul_le_mul_of_nonneg_left (two_rpow_mul_pow_le_natCeil_mul_add_of_le
      (L := (encIn a).length) (e := e) (hK (μ a))) (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀)
    have hpos := mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀)
      (by positivity : (0 : ℝ) ≤ 2 ^ (δ * μ a) * (((encIn a).length : ℝ) + 1) ^ e)
    push_cast
    linarith
  · rintro ⟨t, sp, e, hcomp, h⟩
    obtain ⟨s, hnn, hs_o, hbound⟩ := exists_isLittleO_of_forall_exp_bound h
    refine ⟨s, e, hnn, hs_o, 1, t, sp, fun a => ?_, hcomp⟩
    push_cast
    linarith [hbound a]

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
  rw [decidableInSingleSubexpTime_iff_exists_computableInSingleSubexpTime]
  constructor
  · rintro ⟨g, hA, hg⟩
    obtain ⟨t, sp, e, hcomp, h⟩ := computableInSingleSubexpTime_iff_exists_machine.mp hg
    exact ⟨t, sp, e, decidableInTimeAndSpace_iff.mpr ⟨g, hcomp, hA⟩, h⟩
  · rintro ⟨t, sp, e, hdec, h⟩
    obtain ⟨g, hcomp, hA⟩ := decidableInTimeAndSpace_iff.mp hdec
    exact ⟨g, hA, computableInSingleSubexpTime_iff_exists_machine.mpr ⟨t, sp, e, hcomp, h⟩⟩

/-! ### Measure rescaling and reduction transfers -/

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
  have h := two_rpow_mul_pow_le_two_rpow_mul_pow (L := (encIn a).length) (d := e) (e := e)
    ((hle (μ a)).trans (hmono (hμ a))) le_rfl
  push_cast
  linarith

/-- Single-machine subexponential decision transfers to any parameter at least linear in `μ`. -/
theorem DecidableInSingleSubexpTime.mono_measure {A : Set α} {enc : α ↪ List Bool}
    {μ μ' : α → ℕ} {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : DecidableInSingleSubexpTime A enc μ) :
    DecidableInSingleSubexpTime A enc μ' := by
  rw [decidableInSingleSubexpTime_iff_exists_computableInSingleSubexpTime] at h ⊢
  exact h.imp fun g ⟨hA, hg⟩ => ⟨hA, hg.mono_measure hμ⟩

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
  obtain ⟨s, e, hnn, hs_o, hf⟩ := hf
  obtain ⟨e', h⟩ := hf.ite_polyTime_of_le hp hg (fun a => hnn (μ a)) fun _ _ => le_rfl
  exact ⟨s, e', hnn, hs_o, h⟩

/-- **Single-machine decision from function computation.** Composing a single-machine
subexponential function of polynomially bounded output length with a polynomial-time test yields a
single-machine subexponential decision procedure. -/
theorem DecidableInSingleSubexpTime.of_computableInSingleSubexpTime_polyBounded
    {f : α → β} {μ : α → ℕ}
    (hf : ComputableInSingleSubexpTime f encIn encMid μ)
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (encMid (f a)).length))
    {test : β → Bool} (htest : ComputableInPolyTime test encMid encBool) :
    DecidableInSingleSubexpTime {a | test (f a) = true} encIn μ := by
  obtain ⟨s, e, hnn, hs_o, hf⟩ := hf
  obtain ⟨e', h⟩ :=
    DecidableInTimeO.of_computableInTimeO_polyBounded (fun a => hnn (μ a)) hf hlen htest
  exact ⟨s, e', hnn, hs_o, h⟩

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
  have hsum := reduction_add_time_le (C := 1) (Y := (2 : ℝ) ^ s (μB (r a)))
    hP hX (by norm_num) hn (by simpa only [one_mul] using hexp) (ht (r a))
  simp only [mul_one] at hsum
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
  rw [decidableInSingleSubexpTime_iff_exists_computableInSingleSubexpTime] at hB ⊢
  obtain ⟨g, hgB, hg⟩ := hB
  exact ⟨g ∘ r, fun a => (hAB a).trans (hgB (r a)), hg.of_reduction hr hμ⟩

end SingleMachines

/-- Problem instance `input` paired with a unary precision index `precision` (representing target
rate `1 / (precision + 1)` in an effectively uniform algorithm family). -/
structure PrecisionInput (α : Type) where
  /-- Unary precision index `m`. -/
  precision : ℕ
  /-- Underlying problem instance. -/
  input : α

/-- Framed encoding of `PrecisionInput α` (`encUnary` precision and `enc` instance). -/
@[expose] def PrecisionInput.encoding {α : Type} (enc : α ↪ List Bool) :
    PrecisionInput α ↪ List Bool :=
  Function.Embedding.trans
    ⟨fun x => (x.precision, x.input), fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl⟩
    (encPair encUnary enc)

section UniformFamily

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **Converse from an effectively uniform rate family (`ComputableInSingleSubexpTime`).**
While an arbitrary non-uniform `∀ δ > 0, ∃ M_δ` family need not collapse to one machine, a single
uniform machine `evalAt : PrecisionInput α → β` running in time
`≤ c * ((m + 1) ^ d * 2 ^ (μ a / (m + 1)) * (|enc a| + 1) ^ e) + c` together with a
polynomial-time precision schedule `sched : α → ℕ` tending to `∞` with `μ a` yields a single
`2 ^ o(μ a) · poly(L)` machine. -/
theorem ComputableInSingleSubexpTime.of_uniformFamily {f : α → β} {μ : α → ℕ}
    {evalAt : PrecisionInput α → β} {T S : PrecisionInput α → ℕ}
    (heval : ComputableInO evalAt (PrecisionInput.encoding encIn) encOut T S)
    (hcorrect : ∀ m a, evalAt { precision := m, input := a } = f a)
    {c d e : ℕ}
    (htime : ∀ m a,
      (T { precision := m, input := a } : ℝ) ≤
        c * ((m + 1 : ℝ) ^ d * (2 ^ ((μ a : ℝ) / (m + 1)) * ((encIn a).length + 1) ^ e)) + c)
    {sched : α → ℕ} (hsched : ComputableInPolyTime sched encIn encUnary)
    (htend : ∀ M : ℕ, ∃ N : ℕ, ∀ a, N ≤ μ a → M ≤ sched a) :
    ComputableInSingleSubexpTime f encIn encOut μ := by
  have hmk : ComputableInPolyTime (fun a : α => PrecisionInput.mk (sched a) a) encIn
      (PrecisionInput.encoding encIn) :=
    .of_enc_eq (hsched.prod .id') fun _ => rfl
  obtain ⟨dp, _, hmk_deg⟩ := hmk.exists_degree
  obtain ⟨cs, ds, hs_len⟩ := hsched.polyBounded_length.exists_le
  have hcomp_eq : (evalAt ∘ fun a : α => PrecisionInput.mk (sched a) a) = f :=
    funext fun a => hcorrect (sched a) a
  have hfO : ComputableInO f encIn encOut
      (fun a => ((encIn a).length + 1) ^ dp + T { precision := sched a, input := a })
      (fun a => ((encIn a).length + 1) ^ dp + S { precision := sched a, input := a }) := by
    rw [← hcomp_eq]
    exact heval.comp hmk_deg.inO
  have hforall : ∀ δ : ℝ, 0 < δ → ∃ C : ℕ, ∀ a : α,
      ((((encIn a).length + 1) ^ dp + T { precision := sched a, input := a } : ℕ) : ℝ) ≤
        C * (2 ^ (δ * μ a) * ((encIn a).length + 1) ^ (dp + ds * d + e)) + C := by
    intro δ hδ
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
    have hM_rate : 1 / ((M : ℝ) + 1) ≤ δ := by
      have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hpos]
      have h1 := (div_lt_iff₀ hδ).mp hM
      linarith
    obtain ⟨N, hN⟩ := htend M
    let C_sched : ℕ := (cs + 1) ^ d
    let C_total : ℕ := 1 + c * C_sched * 2 ^ N + c
    refine ⟨C_total, fun a => ?_⟩
    set L1 : ℝ := ((encIn a).length : ℝ) + 1
    have hL1 : 1 ≤ L1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hsched_bound : ((sched a : ℝ) + 1) ^ d ≤ (C_sched : ℝ) * L1 ^ (ds * d) := by
      have hsl := hs_len a
      rw [encUnary_apply, List.length_replicate] at hsl
      have hslR : (sched a : ℝ) + 1 ≤ (cs + 1 : ℝ) * L1 ^ ds := by
        have hpow1 : (1 : ℝ) ≤ L1 ^ ds := one_le_pow₀ hL1
        have hcast : (sched a : ℝ) ≤ cs * L1 ^ ds := by
          dsimp only [L1]
          exact_mod_cast hsl
        linarith
      calc ((sched a : ℝ) + 1) ^ d
          ≤ ((cs + 1 : ℝ) * L1 ^ ds) ^ d := pow_le_pow_left₀ (by positivity) hslR d
        _ = (C_sched : ℝ) * L1 ^ (ds * d) := by
          dsimp only [C_sched]
          rw [mul_pow, ← pow_mul]
          push_cast
          rfl
    have hexp_bound : (2 : ℝ) ^ ((μ a : ℝ) / (sched a + 1)) ≤
        (2 ^ N : ℝ) * 2 ^ (δ * μ a) := by
      by_cases hμN : N ≤ μ a
      · have hMs : M ≤ sched a := hN a hμN
        have hdiv_le : (μ a : ℝ) / (sched a + 1) ≤ δ * μ a := by
          have h1 : (μ a : ℝ) / (sched a + 1) ≤ (μ a : ℝ) / (M + 1) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
              (by exact_mod_cast Nat.add_le_add_right hMs 1)
          have h2 : (μ a : ℝ) / (M + 1) ≤ δ * μ a := by
            rw [show (μ a : ℝ) / (M + 1) = (1 / ((M : ℝ) + 1)) * μ a by ring]
            exact mul_le_mul_of_nonneg_right hM_rate (Nat.cast_nonneg _)
          exact h1.trans h2
        have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv_le).trans
          (le_mul_of_one_le_left (by positivity) hpow1)
      · simp only [not_le] at hμN
        have hdiv_le : (μ a : ℝ) / (sched a + 1) ≤ N := by
          have hden : (1 : ℝ) ≤ (sched a : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
          exact (div_le_self (Nat.cast_nonneg _) hden).trans (by exact_mod_cast hμN.le)
        have h1 : (2 : ℝ) ^ ((μ a : ℝ) / (sched a + 1)) ≤ (2 : ℝ) ^ N := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv_le
        have hX1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
        exact h1.trans (le_mul_of_one_le_right (by positivity) hX1)
    have hT_le := htime (sched a) a
    have hprod : ((sched a : ℝ) + 1) ^ d * (2 ^ ((μ a : ℝ) / (sched a + 1)) * L1 ^ e) ≤
        (C_sched * 2 ^ N : ℝ) * (2 ^ (δ * μ a) * L1 ^ (dp + ds * d + e)) := by
      have hL_grow : L1 ^ (ds * d) * L1 ^ e ≤ L1 ^ (dp + ds * d + e) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hL1 (by omega)
      calc ((sched a : ℝ) + 1) ^ d * (2 ^ ((μ a : ℝ) / (sched a + 1)) * L1 ^ e)
          ≤ ((C_sched : ℝ) * L1 ^ (ds * d)) * (((2 ^ N : ℝ) * 2 ^ (δ * μ a)) * L1 ^ e) :=
            mul_le_mul hsched_bound
              (mul_le_mul_of_nonneg_right hexp_bound (by positivity))
              (by positivity) (by positivity)
        _ = (C_sched * 2 ^ N : ℝ) * (2 ^ (δ * μ a) * (L1 ^ (ds * d) * L1 ^ e)) := by ring
        _ ≤ (C_sched * 2 ^ N : ℝ) * (2 ^ (δ * μ a) * L1 ^ (dp + ds * d + e)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hL_grow (by positivity)) (by positivity)
    have hc_prod := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    have hX1 : (1 : ℝ) ≤ 2 ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
    have hdp_le : L1 ^ dp ≤ 2 ^ (δ * μ a) * L1 ^ (dp + ds * d + e) :=
      (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
    have hc_one : (0 : ℝ) ≤ (c : ℝ) * (2 ^ (δ * μ a) * L1 ^ (dp + ds * d + e)) := by positivity
    set X : ℝ := 2 ^ (δ * μ a) * L1 ^ (dp + ds * d + e)
    have hring : (1 + (c : ℝ) * C_sched * 2 ^ N + c) * X =
        X + (c : ℝ) * ((C_sched * 2 ^ N : ℝ) * X) + (c : ℝ) * X := by ring
    have hnn_extra : (0 : ℝ) ≤ 1 + (c : ℝ) * C_sched * 2 ^ N := by positivity
    dsimp only [C_total, L1, X] at hT_le hc_prod hdp_le hc_one hring hnn_extra ⊢
    push_cast at hc_prod ⊢
    linarith
  obtain ⟨s, hnn, hs_o, hbound⟩ := exists_isLittleO_of_forall_exp_bound hforall
  exact ⟨s, dp + ds * d + e, hnn, hs_o, ComputableInTimeO.of_computableInO hfO hbound⟩

/-- **Converse from an effectively uniform rate family (`DecidableInSingleSubexpTime`).** -/
theorem DecidableInSingleSubexpTime.of_uniformFamily {A : Set α} {μ : α → ℕ}
    {decideAt : PrecisionInput α → Bool} {T S : PrecisionInput α → ℕ}
    (hdec : ComputableInO decideAt (PrecisionInput.encoding encIn) encBool T S)
    (hcorrect : ∀ m a, a ∈ A ↔ decideAt { precision := m, input := a } = true)
    {c d e : ℕ}
    (htime : ∀ m a,
      (T { precision := m, input := a } : ℝ) ≤
        c * ((m + 1 : ℝ) ^ d * (2 ^ ((μ a : ℝ) / (m + 1)) * ((encIn a).length + 1) ^ e)) + c)
    {sched : α → ℕ} (hsched : ComputableInPolyTime sched encIn encUnary)
    (htend : ∀ M : ℕ, ∃ N : ℕ, ∀ a, N ≤ μ a → M ≤ sched a) :
    DecidableInSingleSubexpTime A encIn μ := by
  let g (a : α) : Bool := decideAt { precision := 0, input := a }
  exact decidableInSingleSubexpTime_iff_exists_computableInSingleSubexpTime.mpr ⟨g,
    fun a => hcorrect 0 a, .of_uniformFamily hdec
      (fun m a => Bool.eq_iff_iff.mpr ((hcorrect m a).symm.trans (hcorrect 0 a)))
      htime hsched htend⟩

end UniformFamily

/-! ### `SingleETH`, `SingleSharpETH`, and single-machine rate transfers -/

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
  have hpos : ComputableInPolyTime (fun n : ℕ => decide (0 < n)) encNat encBool :=
    ComputableInPolyTime.binary_lt.comp
      ((ComputableInPolyTime.const 0).prod ComputableInPolyTime.id')
  have hdec := DecidableInSingleSubexpTime.of_computableInSingleSubexpTime_polyBounded h
    (polyBounded_length_encNat_SharpKSAT k) hpos
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
  obtain ⟨e', hite⟩ := htime.ite_polyTime_of_le (computableInPolyTime_all_length_le k)
    (ComputableInPolyTime.const 0) (y := fun φ => sBar (k * φ.length + 0)) (fun _ => hnnBar _)
    fun φ hφ => (hle _).trans (hmono (Nat.le_add_right_of_le (CNF.numVars_le_mul_length
      (by simpa only [List.all_eq_true, decide_eq_true_eq] using hφ))))
  refine ⟨fun m => sBar (k * m + 0), e', fun _ => hnnBar _,
    isLittleO_comp_linear_of_nonneg hnnBar hsBar_o k 0, ?_⟩
  simpa only [ite_all_length_le_SharpKSAT le_rfl] using hite

end Cslib.Complexity
