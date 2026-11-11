/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Magnification
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Foundations.Analysis.SpecificLimits.PolyLtPow
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Gap-MCSP magnification near linear size

Oliveira, Pich and Santhanam's Theorem 1.4 [OliveiraPichSanthanam2019, Theorem 1.4; ECCC TR18-158
Theorem 4] states: if there is `ε > 0` such that for every small enough `β > 0`,
`Gap-MCSP[2^{βn}/10n, 2^{βn}]` has no circuits of size `N^{1+ε}`, where `N = 2^n`, then
`NP ⊄ P/poly`. Here this is `Cslib.MCSP.not_NP_subset_PPoly_of_gapMCSP_hard`, with the source's
constant `c = 10`, and `Cslib.MCSP.P_ne_NP_of_gapMCSP_hard` adds `P ≠ NP`.

**Proof route.** The statement is OPS's; the proof is not. OPS derive Theorem 1.4 from their
efficient anti-checker (Lemma 4.1), which is not formalized. Here it follows from the
McKay–Murray–Williams merge tree in `Cslib.MCSP.exists_complexity_yesSet_le_of_NP_subset_PPoly`:
under `NP ⊆ P/poly`, the `2 ^ n`-bit slice of `MCSP[s]` has circuits of size
`2^n·c·(n + s + 1)^c` for every `s`, and a circuit for `MCSP[s₂]` separates
`Gap-MCSP[s₁, s₂]` whenever `s₁ ≤ s₂` (`Cslib.MCSP.exists_gapMCSP_separator_of_NP_subset_PPoly`).
At `s₂ = ⌊2^{βn}⌋₊` that size is at most `N^{1+cβ}` up to a polynomial factor in `n`, which is
below `N^{1+ε}` for large `n` once `cβ < ε`. The proof never uses the factor `10n` between the two
thresholds, only `s₁ ≤ s₂`.

**Statement conventions.**
* Circuits are the library's fan-in-two De Morgan circuits, and size counts every gate
  (`Cslib.Circuits.Boolean.complexity` with `interpretation`), as in
  `CslibFrontier/Computability/MCSP/Magnification.lean`.
  OPS fix fan-in-two circuits and remark that gate types do not matter for their results. Sizes
  over another basis differ by a constant factor, so this Gap-MCSP is not literally the same
  promise problem as one over that basis, and no translation is claimed.
* The thresholds are `⌊2^{βn}/(10n)⌋₊` and `⌊2^{βn}⌋₊`. Circuit sizes are integers, so rounding
  down changes neither "size `≤ s₁`" nor "size `> s₂`".
* "`Gap-MCSP ∉ Circuit[N^{1+ε}]`" is read as: for infinitely many `n`, no Boolean function on
  `2 ^ n`-bit truth tables that accepts every yes-instance and rejects every no-instance has
  complexity at most `N^{1+ε}`. "For every small enough `β > 0`" is `∀ᶠ β in 𝓝[>] 0`.
* `NP ⊆ Circuit[poly]` is `NP encBits ⊆ PPolyOn encBits`, as in
  `CslibFrontier/Computability/MCSP/Magnification.lean`.

## Main results

* `Cslib.MCSP.slice_yesSet_separates`: the slice of `MCSP[s₂]` separates `Gap-MCSP[s₁, s₂]`.
* `Cslib.MCSP.exists_gapMCSP_separator_of_NP_subset_PPoly`: under `NP ⊆ P/poly`, `Gap-MCSP[s₁, s₂]`
  has separators of size `2^n·c·(n + s₂ n + 1)^c`.
* `Cslib.MCSP.not_NP_subset_PPoly_of_gapMCSP_hard`: OPS Theorem 1.4, through the MMW merge tree.
* `Cslib.MCSP.P_ne_NP_of_gapMCSP_hard`: the same hypothesis gives `P ≠ NP`.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness Magnification near State-Of-The-Art Lower
  Bounds*][OliveiraPichSanthanam2019]
* [D. McKay, C. D. Murray, R. R. Williams, *Weak Lower Bounds on Resource-Bounded Compression
  Imply Strong Separations of Complexity Classes*][McKayMurrayWilliams2019]
-/

public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity Filter Topology

/-! ### Separators from the exact problem -/

/-- **The slice of `MCSP[s₂]` separates `Gap-MCSP[s₁, s₂]`** at a length `n` with
`s₁ n ≤ s₂ n`: it accepts every yes-instance and rejects every no-instance. -/
theorem slice_yesSet_separates {s₁ s₂ : ℕ → ℕ} {n : ℕ} (hs : s₁ n ≤ s₂ n) :
    (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        (GapMCSP.yesSet s₂).slice (2 ^ n) T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        (GapMCSP.yesSet s₂).slice (2 ^ n) T = false) := by
  refine ⟨fun T hT => GapMCSP.slice_yesSet_eq_true_iff.2
      ((GapMCSP.ofFn_mem_yesSet_iff.1 hT).trans hs), fun T hT => ?_⟩
  rw [Bool.eq_false_iff]
  intro hyes
  exact (GapMCSP.ofFn_mem_noSet_iff.1 hT).not_ge (GapMCSP.slice_yesSet_eq_true_iff.1 hyes)

/-- **Gap-MCSP separators under `NP ⊆ P/poly`**, from the McKay–Murray–Williams circuits for
`MCSP[s₂]` (`exists_complexity_yesSet_le_of_NP_subset_PPoly`): there is `c > 0` such that at every
length `n` with `s₁ n ≤ s₂ n`, some Boolean function on `2 ^ n`-bit truth tables of complexity at
most `2^n·c·(n + s₂ n + 1)^c` accepts the yes-instances and rejects the no-instances of
`Gap-MCSP[s₁, s₂]`. -/
theorem exists_gapMCSP_separator_of_NP_subset_PPoly (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ c > 0, ∀ (s₁ s₂ : ℕ → ℕ) (n : ℕ), s₁ n ≤ s₂ n →
      ∃ F : BooleanFunction (2 ^ n),
        complexity interpretation (single F) ≤ 2 ^ n * c * (n + s₂ n + 1) ^ c ∧
        (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ → F T = true) ∧
        (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ → F T = false) := by
  obtain ⟨c, hc, hub⟩ := exists_complexity_yesSet_le_of_NP_subset_PPoly hNP
  exact ⟨c, hc, fun s₁ s₂ n hs => ⟨_, hub s₂ n, slice_yesSet_separates hs⟩⟩

/-! ### Arithmetic -/

/-- For `0 < β` and `c β < ε`, the McKay–Murray–Williams size `2^n·c·(n + ⌊2^{βn}⌋₊ + 1)^c` is
eventually below `N^{1+ε}`, where `N = 2^n`. -/
private theorem eventually_bound_lt_rpow (c : ℕ) {β ε : ℝ} (hβ : 0 < β)
    (hcβ : (c : ℝ) * β < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((2 ^ n * c * (n + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c : ℕ) : ℝ) <
        ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) := by
  set a : ℝ := (2 : ℝ) ^ β with ha_def
  set r : ℝ := (2 : ℝ) ^ (ε - c * β) with hr_def
  have ha : 1 ≤ a := Real.one_le_rpow (by norm_num) hβ.le
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  have ha0 : 0 < a := by linarith
  filter_upwards [eventually_mul_add_one_pow_lt_pow ((c : ℝ) * 2 ^ c) c hr] with n hn
  have hpow : ∀ x : ℝ, (2 : ℝ) ^ (x * n) = ((2 : ℝ) ^ x) ^ n := fun x => by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hfloor : (⌊(2 : ℝ) ^ (β * n)⌋₊ : ℝ) ≤ a ^ n := by
    rw [hpow, ← ha_def]
    exact Nat.floor_le (by positivity)
  have han : 1 ≤ a ^ n := one_le_pow₀ ha
  have hsum : (n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1 ≤ 2 * ((n + 1) * a ^ n) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hsum0 : (0 : ℝ) ≤ (n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1 := by positivity
  have hac : (a ^ n) ^ c * r ^ n = ((2 : ℝ) ^ ε) ^ n := by
    rw [← pow_mul, mul_comm n c, pow_mul, ← mul_pow]
    congr 1
    rw [ha_def, hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    ring_nf
  have hRHS : ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) = (2 : ℝ) ^ n * ((2 : ℝ) ^ ε) ^ n := by
    have h2 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ (n : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    rw [h2, ← Real.rpow_mul (by norm_num), ← hpow, ← Real.rpow_natCast (2 : ℝ) n,
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((2 ^ n * c * (n + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c : ℕ) : ℝ) =
      (2 : ℝ) ^ n * c * ((n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c := by
    push_cast
    ring
  have hmain : (2 : ℝ) ^ n * c * ((n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c ≤
      (2 : ℝ) ^ n * ((c * 2 ^ c * ((n : ℝ) + 1) ^ c) * (a ^ n) ^ c) := by
    have hle : ((n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c ≤ (2 * ((n + 1) * a ^ n)) ^ c :=
      pow_le_pow_left₀ hsum0 hsum c
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc (2 : ℝ) ^ n * c * ((n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c
        ≤ (2 : ℝ) ^ n * c * (2 * ((n + 1) * a ^ n)) ^ c := by gcongr
      _ = (2 : ℝ) ^ n * ((c * 2 ^ c * ((n : ℝ) + 1) ^ c) * (a ^ n) ^ c) := by
        rw [mul_pow, mul_pow]
        ring
  have hanc : 0 < (a ^ n) ^ c := by positivity
  rw [hcast, hRHS, ← hac]
  calc (2 : ℝ) ^ n * c * ((n : ℝ) + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c
      ≤ (2 : ℝ) ^ n * ((c * 2 ^ c * ((n : ℝ) + 1) ^ c) * (a ^ n) ^ c) := hmain
    _ < (2 : ℝ) ^ n * ((a ^ n) ^ c * r ^ n) := by
      rw [mul_comm (_ * _ * _) ((a ^ n) ^ c)]
      gcongr

/-- `⌊x / (10 n)⌋₊ ≤ ⌊x⌋₊`: the yes-threshold of OPS Theorem 1.4 is at most its no-threshold. -/
private theorem floor_div_ten_mul_le (x : ℝ) (n : ℕ) : ⌊x / (10 * n)⌋₊ ≤ ⌊x⌋₊ := by
  rw [show (10 * (n : ℝ)) = ((10 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_div_natCast]
  exact Nat.div_le_self _ _

/-! ### OPS Theorem 1.4 -/

/-- **Oliveira–Pich–Santhanam Theorem 1.4** [OliveiraPichSanthanam2019, Theorem 1.4; ECCC
TR18-158 Theorem 4], with the source's constant `c = 10`: if for some `ε > 0` and every small
enough `β > 0`, `Gap-MCSP[⌊2^{βn}/10n⌋₊, ⌊2^{βn}⌋₊]` has, for infinitely many `n`, no separating
Boolean function of complexity at most `N^{1+ε}` (`N = 2 ^ n`), then `NP ⊄ P/poly`.

The statement is OPS's; the proof goes through the McKay–Murray–Williams merge tree
(`exists_gapMCSP_separator_of_NP_subset_PPoly`), not OPS's anti-checker (Lemma 4.1, which is not
formalized). Circuits are De Morgan circuits counting all gates; see the module docstring. -/
theorem not_NP_subset_PPoly_of_gapMCSP_hard {ε : ℝ} (hε : 0 < ε)
    (h : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), ∀ N₀ : ℕ, ∃ n ≥ N₀, ∀ F : BooleanFunction (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.yesSet (fun m => ⌊(2 : ℝ) ^ (β * m) / (10 * m)⌋₊) → F T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.noSet (fun m => ⌊(2 : ℝ) ^ (β * m)⌋₊) → F T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < complexity interpretation (single F)) :
    ¬ (NP encBits ⊆ PPolyOn encBits) := by
  intro hNP
  obtain ⟨c, -, hsep⟩ := exists_gapMCSP_separator_of_NP_subset_PPoly hNP
  have hsmall : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), 0 < β ∧ (c : ℝ) * β < ε := by
    have hb : 0 < ε / (c + 1) := div_pos hε (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hb] with β ⟨hβ0, hβ⟩
    refine ⟨hβ0, ?_⟩
    rw [lt_div_iff₀ (by positivity)] at hβ
    nlinarith
  obtain ⟨β, hhard, hβ, hcβ⟩ := (h.and hsmall).exists
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_bound_lt_rpow c hβ hcβ)
  obtain ⟨n, hn, hhardn⟩ := hhard N₀
  obtain ⟨F, hF, hyes, hno⟩ := hsep (fun m => ⌊(2 : ℝ) ^ (β * m) / (10 * m)⌋₊)
    (fun m => ⌊(2 : ℝ) ^ (β * m)⌋₊) n (floor_div_ten_mul_le _ n)
  have hFr : (complexity interpretation (single F) : ℝ) ≤
      ((2 ^ n * c * (n + ⌊(2 : ℝ) ^ (β * n)⌋₊ + 1) ^ c : ℕ) : ℝ) := by
    exact_mod_cast hF
  exact (hhardn F hyes hno).not_ge (hFr.trans (hN₀ n hn).le)

/-- **OPS Theorem 1.4 gives `P ≠ NP`**: the hypothesis of `not_NP_subset_PPoly_of_gapMCSP_hard`
implies `P ≠ NP`, through `P ⊆ P/poly` (`P_subset_PPolyOn`). -/
theorem P_ne_NP_of_gapMCSP_hard {ε : ℝ} (hε : 0 < ε)
    (h : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), ∀ N₀ : ℕ, ∃ n ≥ N₀, ∀ F : BooleanFunction (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.yesSet (fun m => ⌊(2 : ℝ) ^ (β * m) / (10 * m)⌋₊) → F T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.noSet (fun m => ⌊(2 : ℝ) ^ (β * m)⌋₊) → F T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < complexity interpretation (single F)) :
    P encBits ≠ NP encBits := by
  intro hEq
  refine not_NP_subset_PPoly_of_gapMCSP_hard hε h ?_
  rw [← hEq]
  exact P_subset_PPolyOn

end Cslib.MCSP
