/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Williams
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Foundations.Data.Nat.AffineBound
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Foundations.Data.Nat.LogRpow
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Time–space separation corollaries from Williams's simulation

Combining Williams's square-root-space simulation of deterministic time
(`Cslib.Complexity.DTIME_subset_DSPACE_sqrt`, Theorem 1.1 of [Williams2025]) with the
deterministic space hierarchy theorem (`Cslib.Complexity.DSPACE_ssubset_DSPACE`, [Stearns,
Hartmanis and Lewis][StearnsHartmanisLewis1965]) separates deterministic space from smaller
deterministic time classes on bit words.

Specifically, whenever `s` is space-constructible (`Cslib.Complexity.SpaceConstructible`) with
`⌊log₂ n⌋ ≤ s n` eventually, any time bound `t` satisfying
`√(max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)) = o(s n)` satisfies
`DTIME encBits t ⊂ DSPACE encBits s` and `¬ DSPACE encBits s ⊆ DTIME encBits t`
(`Cslib.Complexity.DTIME_ssubset_DSPACE_of_sqrt`, with squared and little-o sufficient conditions).
In particular, when `s n ≥ n` eventually:

* for every real `ε > 0`, `DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits s`
  (`Cslib.Complexity.DTIME_rpow_sub_ssubset_DSPACE`), and in particular for linear space `s n = n`,
  `¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊)`
  (`Cslib.Complexity.DSPACE_id_not_subset_DTIME_rpow_sub`);
* for `a, b : ℕ` with `1 ≤ b` and `a < 2 * b`,
  `DTIME encBits (· ^ a) ⊂ DSPACE encBits (· ^ b)`
  (`Cslib.Complexity.DTIME_pow_ssubset_DSPACE_pow`);
* with the sharper polylogarithmic gap `n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2`,
  `DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) ⊂ DSPACE encBits s`
  (`Cslib.Complexity.DTIME_sq_div_log2_sq_ssubset_DSPACE`), and likewise for linear space.

The separating problem can be taken to be the explicit budgeted diagonal language
`{x | spaceDiagonal (fun n => 4 * s n) x = true}` when `⌊log₂ n⌋ ≤ s n` holds pointwise
(`Cslib.Complexity.setOf_spaceDiagonal_id_mem_DSPACE`,
`Cslib.Complexity.setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub`).

Note on sources: `[Williams2025]` Theorem 1.1 is established by
`Cslib.Complexity.DTIME_subset_DSPACE_sqrt`
(`CslibFrontier/Computability/Complexity/Classes/TimeSpace/Williams.lean`). The separation
corollaries below are proved directly from it and `Cslib.Complexity.DSPACE_ssubset_DSPACE`;
only Theorem 1.1's verified statement in the repository (not a separate PDF inspection of later
numbered corollaries) is relied upon.

## Main results

* `Cslib.Complexity.DTIME_subset_DSPACE_sqrt_max`,
  `Cslib.Complexity.DTIME_subset_DSPACE_sqrt_of_eventually_le`: square-root-space simulation
  without a pointwise `n ≤ t n` hypothesis.
* `Cslib.Complexity.DTIME_ssubset_DSPACE_of_sqrt`,
  `Cslib.Complexity.DTIME_ssubset_DSPACE_of_mul_log2_le_sq`,
  `Cslib.Complexity.DTIME_ssubset_DSPACE_of_isLittleO`: general time–space separations and their
  negated-containment forms.
* `Cslib.Complexity.DTIME_rpow_sub_ssubset_DSPACE`,
  `Cslib.Complexity.DTIME_rpow_lt_two_ssubset_DSPACE`,
  `Cslib.Complexity.DSPACE_not_subset_DTIME_rpow_sub`: `DTIME (⌊s(n) ^ (2 - ε)⌋) ⊂ DSPACE (s)`
  and `DSPACE (s) ⊄ DTIME (⌊s(n) ^ (2 - ε)⌋)` for every `ε > 0`.
* `Cslib.Complexity.DTIME_pow_ssubset_DSPACE_pow`,
  `Cslib.Complexity.DTIME_sq_div_log2_sq_ssubset_DSPACE`,
  `Cslib.Complexity.DTIME_id_ssubset_DSPACE_id`: polynomial-exponent,
  `s(n) ^ 2 / (⌊log₂ (s n)⌋ + 1) ^ 2`, and linear-space (`s n = n`) separations.
* `Cslib.Complexity.setOf_spaceDiagonal_notMem_DTIME`,
  `Cslib.Complexity.setOf_spaceDiagonal_id_mem_DSPACE`,
  `Cslib.Complexity.setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub`,
  `Cslib.Complexity.setOf_spaceDiagonal_id_notMem_DTIME_sq_div_log2_sq`: explicit diagonal
  separating witnesses.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.8][AroraBarak09]
* [R. E. Stearns, J. Hartmanis, P. M. Lewis II, *Hierarchies of memory limited
  computations*][StearnsHartmanisLewis1965]
* [R. Williams, *Simulating Time With Square-Root Space*, Theorem 1.1][Williams2025]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter Asymptotics

/-! ### Extensions of the square-root-space inclusion -/

/-- **Williams's square-root-space simulation for arbitrary time bounds**: replacing `t n` by
`max n (t n)` removes the pointwise `n ≤ t n` condition from `DTIME_subset_DSPACE_sqrt`. -/
theorem DTIME_subset_DSPACE_sqrt_max {α : Type*} (enc : α ↪ List Bool) (t : ℕ → ℕ) :
    DTIME enc t ⊆ DSPACE enc (fun n => Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1))) :=
  (DTIME_mono fun n => le_max_right n (t n)).trans
    (DTIME_subset_DSPACE_sqrt enc (fun n => max n (t n)) fun n => le_max_left n (t n))

/-- **Williams's square-root-space simulation for eventually linear-or-larger time bounds**:
if `n ≤ t n` for all sufficiently large `n`, `DTIME enc t` lies in
`DSPACE enc (fun n => Nat.sqrt (t n * (Nat.log2 (t n) + 1)))`. -/
theorem DTIME_subset_DSPACE_sqrt_of_eventually_le {α : Type*} (enc : α ↪ List Bool) {t : ℕ → ℕ}
    (ht : ∀ᶠ n in atTop, n ≤ t n) :
    DTIME enc t ⊆ DSPACE enc (fun n => Nat.sqrt (t n * (Nat.log2 (t n) + 1))) := by
  refine (DTIME_subset_DSPACE_sqrt_max enc t).trans (DSPACE_mono_of_eventually_le ?_)
  filter_upwards [ht] with n hn
  simp only [max_eq_right hn, le_rfl]

/-! ### Arithmetic and shift helpers -/

/-- Eventual domination in `g ^ 2` implies eventual domination of `Nat.sqrt f` in `g`. -/
private theorem eventually_mul_sqrt_add_le_of_mul_add_le_sq {f g : ℕ → ℕ}
    (h : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ g n ^ 2) :
    ∀ c, ∀ᶠ n in atTop, c * Nat.sqrt (f n) + c ≤ g n := by
  intro c
  filter_upwards [h (2 * c ^ 2)] with n hn
  refine (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp ?_
  have hsqrt : Nat.sqrt (f n) ^ 2 ≤ f n := by simpa only [sq] using Nat.sqrt_le (f n)
  have hsq : (c * Nat.sqrt (f n) + c) ^ 2 ≤ 2 * (c * Nat.sqrt (f n)) ^ 2 + 2 * c ^ 2 := by
    rcases le_total (c * Nat.sqrt (f n)) c with hle | hle <;> nlinarith
  have hsq' : 2 * (c * Nat.sqrt (f n)) ^ 2 + 2 * c ^ 2 =
      2 * c ^ 2 * Nat.sqrt (f n) ^ 2 + 2 * c ^ 2 := by ring
  have hmul : 2 * c ^ 2 * Nat.sqrt (f n) ^ 2 ≤ 2 * c ^ 2 * f n :=
    Nat.mul_le_mul_left _ hsqrt
  nlinarith

/-- If `Nat.log2 n ≤ s n` holds eventually, adding `Nat.log2 N` preserves `SpaceConstructible`,
preserves `DSPACE`, and ensures the logarithmic lower bound holds pointwise. -/
private theorem exists_shift_of_eventually_log2_le {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n) :
    ∃ c₀ : ℕ, SpaceConstructible (fun n => s n + c₀) ∧
      (∀ n, Nat.log2 n ≤ s n + c₀) ∧
      DSPACE encBits (fun n => s n + c₀) = DSPACE encBits s := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlog
  refine ⟨Nat.log2 N, hs.add (spaceConstructible_const (Nat.log2 N)), fun n => ?_, ?_⟩
  · rcases le_or_gt N n with hn | hn
    · exact (hN n hn).trans (Nat.le_add_right _ _)
    · rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact (Nat.log_mono_right hn.le).trans (Nat.le_add_left _ _)
  · exact Set.Subset.antisymm
      (DSPACE_mono_of_le_mul_add (C := 1 + Nat.log2 N) fun n => by
        have h1 := Nat.le_mul_of_pos_left (s n) (Nat.succ_pos (Nat.log2 N))
        rw [Nat.succ_eq_add_one, add_comm] at h1
        omega)
      (DSPACE_mono fun n => Nat.le_add_right _ _)

private theorem eventually_log2_le_of_eventually_le {s : ℕ → ℕ} (hn : ∀ᶠ n in atTop, n ≤ s n) :
    ∀ᶠ n in atTop, Nat.log2 n ≤ s n :=
  hn.mono fun _ h => (Nat.log2_le_self _).trans h

private theorem log2_le_two_mul_log2_add_one {m k : ℕ} (hk : 1 ≤ k) (hm : m ≤ k ^ 2) :
    Nat.log2 m ≤ 2 * Nat.log2 k + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hpow := Nat.log_mono_right (b := 2) hm
  have hlt : k ^ 2 < 2 ^ (2 * Nat.log 2 k + 2) := by
    have hk_lt : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self one_lt_two k
    calc k ^ 2 < (2 ^ (Nat.log 2 k + 1)) ^ 2 := Nat.pow_lt_pow_left hk_lt (by norm_num)
      _ = 2 ^ (2 * Nat.log 2 k + 2) := by rw [← pow_mul]; ring_nf
  exact hpow.trans (Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (pow_ne_zero 2 (by omega)) hlt))

private theorem tendsto_of_eventually_log2_le {s : ℕ → ℕ} (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n) :
    Tendsto s atTop atTop :=
  tendsto_atTop_atTop.mpr fun k => by
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((Nat.eventually_le_log k one_lt_two).and hlog)
    refine ⟨M, fun n hn => ?_⟩
    have h₁ := (hM n hn).1
    rw [← Nat.log2_eq_log_two] at h₁
    exact h₁.trans (hM n hn).2

/-! ### General time–space separation theorems -/

/-- **General Williams + space-hierarchy separation.** When `s` is space-constructible with
`⌊log₂ n⌋ ≤ s n` eventually and `√(max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)) = o(s n)`,
`DTIME encBits t` is strictly contained in `DSPACE encBits s`. -/
theorem DTIME_ssubset_DSPACE_of_sqrt {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hdom : ∀ c, ∀ᶠ n in atTop,
      c * Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n) :
    DTIME encBits t ⊂ DSPACE encBits s := by
  obtain ⟨c₀, hs', hlog', hEq⟩ := exists_shift_of_eventually_log2_le hs hlog
  have hsub := DSPACE_ssubset_DSPACE hs' hlog' fun c =>
    (hdom c).mono fun _ h => h.trans (Nat.le_add_right _ _)
  rw [hEq] at hsub
  exact (DTIME_subset_DSPACE_sqrt_max encBits t).trans_ssubset hsub

/-- **Containment failure form of the general separation**: `DSPACE encBits s` is not contained in
`DTIME encBits t`. -/
theorem DSPACE_not_subset_DTIME_of_sqrt {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hdom : ∀ c, ∀ᶠ n in atTop,
      c * Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n) :
    ¬ DSPACE encBits s ⊆ DTIME encBits t :=
  fun h => (DTIME_ssubset_DSPACE_of_sqrt hs hlog hdom).not_superset h

/-- **Explicit separating diagonal witness**: when `⌊log₂ n⌋ ≤ s n` holds pointwise and
`√(max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)) = o(s n)`, the diagonal problem
`{x | spaceDiagonal (fun n => 4 * s n) x = true}` is outside `DTIME encBits t`. -/
theorem setOf_spaceDiagonal_notMem_DTIME {t s : ℕ → ℕ} (hlog : ∀ n, Nat.log2 n ≤ s n)
    (hdom : ∀ c, ∀ᶠ n in atTop,
      c * Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n) :
    {x | spaceDiagonal (fun n => 4 * s n) x = true} ∉ DTIME encBits t := by
  intro hmem
  have hnot := setOf_spaceDiagonal_notMem_DSPACE
    (f := fun n => Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)))
    (G := fun n => 4 * s n) (fun n => Nat.mul_le_mul_left 4 (hlog n)) fun c =>
      (hdom c).mono fun _ h => by omega
  exact hnot (DTIME_subset_DSPACE_sqrt_max encBits t hmem)

/-- **Explicit separating witness membership**: for space-constructible `s` with
`⌊log₂ n⌋ ≤ s n` pointwise, `{x | spaceDiagonal (fun n => 4 * s n) x = true}` lies in
`DSPACE encBits s`. -/
theorem setOf_spaceDiagonal_four_mul_mem_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ n, Nat.log2 n ≤ s n) :
    {x | spaceDiagonal (fun n => 4 * s n) x = true} ∈ DSPACE encBits s :=
  DSPACE_mono_of_le_mul_add (C := 4) (fun _ => Nat.le_add_right _ _)
    (setOf_spaceDiagonal_mem_DSPACE (hs.const_mul 4) fun n =>
      (hlog n).trans (Nat.le_mul_of_pos_left _ (by norm_num)))

/-- **Squared-domination form of Williams's separation**: if every affine multiple of
`max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)` is eventually at most `s n ^ 2`, then
`DTIME encBits t ⊂ DSPACE encBits s`. -/
theorem DTIME_ssubset_DSPACE_of_mul_log2_le_sq {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hsq : ∀ c, ∀ᶠ n in atTop, c * (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n ^ 2) :
    DTIME encBits t ⊂ DSPACE encBits s :=
  DTIME_ssubset_DSPACE_of_sqrt hs hlog (eventually_mul_sqrt_add_le_of_mul_add_le_sq hsq)

/-- **Squared-domination containment failure**: `¬ DSPACE encBits s ⊆ DTIME encBits t`. -/
theorem DSPACE_not_subset_DTIME_of_mul_log2_le_sq {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hsq : ∀ c, ∀ᶠ n in atTop, c * (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n ^ 2) :
    ¬ DSPACE encBits s ⊆ DTIME encBits t :=
  fun h => (DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs hlog hsq).not_superset h

/-- **Little-o form of Williams's separation**: if
`max n (t n) · (⌊log₂ (max n (t n))⌋ + 1) = o(s n ^ 2)`, then
`DTIME encBits t ⊂ DSPACE encBits s`. -/
theorem DTIME_ssubset_DSPACE_of_isLittleO {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (ho : (fun n => ((max n (t n) * (Nat.log2 (max n (t n)) + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n => ((s n ^ 2 : ℕ) : ℝ))) :
    DTIME encBits t ⊂ DSPACE encBits s := by
  refine DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs hlog fun c => ?_
  have hten : Tendsto s atTop atTop := tendsto_of_eventually_log2_le hlog
  have ho_nat := Asymptotics.isLittleO_iff_nat_mul_le.mp ho (2 * c)
  filter_upwards [ho_nat, hten.eventually_ge_atTop (2 * c + 1)] with n hn hsc
  simp only [Real.norm_natCast] at hn
  set m := max n (t n) * (Nat.log2 (max n (t n)) + 1)
  have h1 : 2 * c * m ≤ s n ^ 2 := by exact_mod_cast hn
  have h2 : 2 * c ≤ s n ^ 2 := by nlinarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]; omega
  · have h3 : c * m + c ≤ 2 * c * m := by nlinarith
    omega

/-- **Little-o containment failure**: `¬ DSPACE encBits s ⊆ DTIME encBits t`. -/
theorem DSPACE_not_subset_DTIME_of_isLittleO {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (ho : (fun n => ((max n (t n) * (Nat.log2 (max n (t n)) + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n => ((s n ^ 2 : ℕ) : ℝ))) :
    ¬ DSPACE encBits s ⊆ DTIME encBits t :=
  fun h => (DTIME_ssubset_DSPACE_of_isLittleO hs hlog ho).not_superset h

/-! ### Subquadratic-exponent and polylogarithmic separations -/

/-- Shared domination proof for `t n = ⌊(s n : ℝ) ^ (2 - ε)⌋₊` when `n ≤ s n` eventually and
`0 < ε`. -/
private theorem eventually_rpow_sub_mul_log2_le_sq {s : ℕ → ℕ} (hn : ∀ᶠ n in atTop, n ≤ s n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ c, ∀ᶠ n in atTop,
      c * (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ * (Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) + 1)) + c ≤
        s n ^ 2 := by
  let α : ℝ := max 1 (2 - ε)
  have hα1 : 1 ≤ α := le_max_left 1 (2 - ε)
  have hα2 : α < 2 := max_lt (by norm_num) (by linarith)
  have hδ : 0 < 2 - α := sub_pos.mpr hα2
  have hten : Tendsto s atTop atTop :=
    tendsto_atTop_mono' atTop hn tendsto_id
  intro c
  let K : ℝ := (4 * c + 2 : ℕ)
  have hK : 0 < K := by positivity
  have hlog_rpowK := hten.eventually
    (Nat.eventually_mul_log_add_pow_le_rpow (b := 2) one_lt_two 0 2 1 hK hδ)
  filter_upwards [eventually_ge_atTop 1, hn, hten.eventually_ge_atTop 2, hlog_rpowK]
    with n hn1 hns hs2 hKbd
  have hKbd' : K * ((Nat.log 2 (s n) : ℝ) + 2) ≤ (s n : ℝ) ^ (2 - α) := by
    simpa only [add_zero, pow_one, Nat.cast_ofNat] using hKbd
  have hsR1 : (1 : ℝ) ≤ s n := by exact_mod_cast (by omega : 1 ≤ s n)
  have hsR0 : (0 : ℝ) < s n := by positivity
  have hn_le_rpow : (n : ℝ) ≤ (s n : ℝ) ^ α :=
    (show (n : ℝ) ≤ (s n : ℝ) by exact_mod_cast hns).trans <| by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hsR1 hα1
  have hfl_le_rpow : (⌊(s n : ℝ) ^ (2 - ε)⌋₊ : ℝ) ≤ (s n : ℝ) ^ α :=
    (Nat.floor_le (Real.rpow_nonneg hsR0.le _)).trans
      (Real.rpow_le_rpow_of_exponent_le hsR1 (le_max_right 1 (2 - ε)))
  have hm_le_rpow : ((max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ : ℕ) : ℝ) ≤ (s n : ℝ) ^ α := by
    push_cast
    exact max_le hn_le_rpow hfl_le_rpow
  have hm_le_sq : max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ ≤ s n ^ 2 := by
    have h1 : ((max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ : ℕ) : ℝ) ≤ ((s n ^ 2 : ℕ) : ℝ) := by
      refine hm_le_rpow.trans ?_
      rw [Nat.cast_pow, ← Real.rpow_natCast (s n : ℝ) 2]
      exact Real.rpow_le_rpow_of_exponent_le hsR1 hα2.le
    exact_mod_cast h1
  have hlog_sq : Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) ≤ 2 * Nat.log2 (s n) + 1 :=
    log2_le_two_mul_log2_add_one (by omega) hm_le_sq
  have hlogR : ((Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) : ℝ) + 1) ≤
      2 * ((Nat.log 2 (s n) : ℝ) + 2) := by
    have hnat : Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) + 1 ≤ 2 * (Nat.log 2 (s n) + 2) := by
      simp only [Nat.log2_eq_log_two] at hlog_sq ⊢
      omega
    exact_mod_cast hnat
  have hreal_bd :
      ((2 * c * (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ *
          (Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) + 1)) : ℕ) : ℝ) ≤
        ((s n ^ 2 : ℕ) : ℝ) := by
    set m := max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊
    have hprod :
        ((2 * c * (m * (Nat.log2 m + 1)) : ℕ) : ℝ) ≤
          (s n : ℝ) ^ α * (K * ((Nat.log 2 (s n) : ℝ) + 2)) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      have hK_le : (2 : ℝ) * (2 * (c : ℝ)) ≤ K := by dsimp only [K]; push_cast; linarith
      calc (2 : ℝ) * c * ((m : ℝ) * ((Nat.log2 m : ℝ) + 1))
          ≤ 2 * c * ((s n : ℝ) ^ α * (2 * ((Nat.log 2 (s n) : ℝ) + 2))) := by gcongr
        _ = (s n : ℝ) ^ α * ((2 * (2 * (c : ℝ))) * ((Nat.log 2 (s n) : ℝ) + 2)) := by ring
        _ ≤ (s n : ℝ) ^ α * (K * ((Nat.log 2 (s n) : ℝ) + 2)) := by gcongr
    refine hprod.trans ?_
    calc (s n : ℝ) ^ α * (K * ((Nat.log 2 (s n) : ℝ) + 2))
        ≤ (s n : ℝ) ^ α * (s n : ℝ) ^ (2 - α) := by gcongr
      _ = (s n : ℝ) ^ (α + (2 - α)) := (Real.rpow_add hsR0 _ _).symm
      _ = ((s n ^ 2 : ℕ) : ℝ) := by
          rw [show α + (2 - α) = (2 : ℝ) by ring, Real.rpow_two, Nat.cast_pow]
  have hnat_bd :
      2 * c * (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ * (Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) + 1)) ≤
        s n ^ 2 := by
    exact_mod_cast hreal_bd
  have hone : 1 ≤ max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ * (Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) + 1) :=
    Nat.mul_pos (lt_of_lt_of_le hn1 (le_max_left _ _)) (Nat.succ_pos _)
  nlinarith

/-- **Subquadratic-time vs. constructible-space separation** ([Williams2025], Theorem 1.1
consequence): for any space-constructible `s` satisfying `n ≤ s n` eventually and any real
`ε > 0`, `DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊)` is strictly contained in
`DSPACE encBits s`. -/
theorem DTIME_rpow_sub_ssubset_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) {ε : ℝ} (hε : 0 < ε) :
    DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits s :=
  DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs (eventually_log2_le_of_eventually_le hn)
    (eventually_rpow_sub_mul_log2_le_sq hn hε)

/-- **Exponent-below-two form** of the constructible-space separation: for any real `α < 2`,
`DTIME encBits (fun n => ⌊(s n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits s`. -/
theorem DTIME_rpow_lt_two_ssubset_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) {α : ℝ} (hα : α < 2) :
    DTIME encBits (fun n => ⌊(s n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits s := by
  simpa only [sub_sub_cancel] using DTIME_rpow_sub_ssubset_DSPACE hs hn (sub_pos.mpr hα)

/-- **Williams's separation in containment-failure form**: for any space-constructible `s` with
`n ≤ s n` eventually and any `ε > 0`, `DSPACE encBits s` is not contained in
`DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊)`. -/
theorem DSPACE_not_subset_DTIME_rpow_sub {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) {ε : ℝ} (hε : 0 < ε) :
    ¬ DSPACE encBits s ⊆ DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊) :=
  fun h => (DTIME_rpow_sub_ssubset_DSPACE hs hn hε).not_superset h

/-- Shared domination proof for `t n = s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2` when `n ≤ s n`
eventually. -/
private theorem eventually_sq_div_log2_sq_mul_log2_le_sq {s : ℕ → ℕ}
    (hn : ∀ᶠ n in atTop, n ≤ s n) :
    ∀ c, ∀ᶠ n in atTop,
      c * (max n (s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) *
          (Nat.log2 (max n (s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2)) + 1)) + c ≤ s n ^ 2 := by
  have hten : Tendsto s atTop atTop := tendsto_atTop_mono' atTop hn tendsto_id
  have hlog2 : ∀ k : ℕ, ∀ᶠ n in atTop, k ≤ Nat.log2 (s n) := fun k => by
    have h := hten.eventually (Nat.eventually_le_log k one_lt_two)
    refine h.mono fun n hn' => ?_
    simpa only [Nat.log2_eq_log_two] using hn'
  have hsq_vs_log : ∀ᶠ n in atTop, (Nat.log2 (s n) + 1) ^ 2 ≤ s n := by
    have hr := hten.eventually
      (Nat.eventually_mul_log_add_pow_le_rpow (b := 2) one_lt_two 0 1 2 one_pos one_pos)
    filter_upwards [hr] with n h'
    rw [Nat.log2_eq_log_two]
    have hR : ((Nat.log 2 (s n) + 1 : ℕ) : ℝ) ^ 2 ≤ (s n : ℝ) := by
      simpa only [add_zero, one_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        Real.rpow_one] using h'
    exact_mod_cast hR
  intro c
  filter_upwards [hn, hlog2 (8 * c + 8), hsq_vs_log, hten.eventually_ge_atTop (4 * c + 4)]
    with n hns hL hL2 hsmin
  set L := Nat.log2 (s n) + 1
  set t := s n ^ 2 / L ^ 2
  have hLpos : 0 < L := Nat.succ_pos _
  have hL_ge : 8 * c + 9 ≤ L := by omega
  have hns_le_t : s n ≤ t := (Nat.le_div_iff_mul_le (pow_pos hLpos 2)).mpr (by
    calc s n * L ^ 2 ≤ s n * s n := Nat.mul_le_mul_left _ hL2
      _ = s n ^ 2 := (sq (s n)).symm)
  have hmax : max n t = t := max_eq_right (hns.trans hns_le_t)
  have ht_le_sq : t ≤ s n ^ 2 := Nat.div_le_self _ _
  have hlogt : Nat.log2 t + 1 ≤ 2 * L := by
    have hpow := log2_le_two_mul_log2_add_one (by omega) ht_le_sq
    dsimp only [L]
    omega
  have ht_mul_L : t * L ≤ s n ^ 2 / L := by
    have : t * L = (s n ^ 2 / L) / L * L := by
      dsimp only [t]
      rw [sq L, Nat.div_div_eq_div_mul]
    rw [this]
    exact Nat.div_mul_le_self _ L
  have ht_log : t * (Nat.log2 t + 1) ≤ 2 * (s n ^ 2 / L) := by
    calc t * (Nat.log2 t + 1) ≤ t * (2 * L) := Nat.mul_le_mul_left _ hlogt
      _ = 2 * (t * L) := by ring
      _ ≤ 2 * (s n ^ 2 / L) := Nat.mul_le_mul_left 2 ht_mul_L
  have hc_mul : (c + 1) * (2 * (s n ^ 2 / L)) ≤ s n ^ 2 := by
    have hdiv : 2 * (c + 1) * (s n ^ 2 / L) ≤ L * (s n ^ 2 / L) :=
      Nat.mul_le_mul_right _ (by omega)
    calc (c + 1) * (2 * (s n ^ 2 / L)) = 2 * (c + 1) * (s n ^ 2 / L) := by ring
      _ ≤ L * (s n ^ 2 / L) := hdiv
      _ ≤ s n ^ 2 := Nat.mul_div_le _ L
  have hlast : c * (t * (Nat.log2 t + 1)) + c ≤ s n ^ 2 := by
    have hc1 : c * (t * (Nat.log2 t + 1)) ≤ c * (2 * (s n ^ 2 / L)) :=
      Nat.mul_le_mul_left c ht_log
    have hone : c ≤ 2 * (s n ^ 2 / L) := by
      have hsdiv : c ≤ s n ^ 2 / L := (Nat.le_div_iff_mul_le hLpos).mpr (by
        calc c * L ≤ L * L := Nat.mul_le_mul_right _ (by omega)
          _ = L ^ 2 := (sq L).symm
          _ ≤ s n := hL2
          _ ≤ s n ^ 2 := Nat.le_self_pow (by decide) _)
      omega
    nlinarith
  simpa only [hmax] using hlast

/-- **Logarithmic-factor sharpening for constructible space**: for any space-constructible `s`
with `n ≤ s n` eventually, `DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2)` is
strictly contained in `DSPACE encBits s`. -/
theorem DTIME_sq_div_log2_sq_ssubset_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) :
    DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) ⊂ DSPACE encBits s :=
  DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs (eventually_log2_le_of_eventually_le hn)
    (eventually_sq_div_log2_sq_mul_log2_le_sq hn)

/-- **Containment failure for the `s(n) ^ 2 / (⌊log₂ (s n)⌋ + 1) ^ 2` time bound**. -/
theorem DSPACE_not_subset_DTIME_sq_div_log2_sq {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) :
    ¬ DSPACE encBits s ⊆ DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) :=
  fun h => (DTIME_sq_div_log2_sq_ssubset_DSPACE hs hn).not_superset h

/-- **Polynomial time–space separation**: for `1 ≤ b` and `a < 2 * b`, deterministic time
`n ^ a` is strictly contained in deterministic space `n ^ b`. In particular, linear time
(`a = 1`, `b = 1`) is strictly contained in linear space. -/
theorem DTIME_pow_ssubset_DSPACE_pow {a b : ℕ} (hb : 1 ≤ b) (hab : a < 2 * b) :
    DTIME encBits (· ^ a) ⊂ DSPACE encBits (· ^ b) := by
  have hsub1 : DSPACE encBits (fun n => (n + 1) ^ b) ⊆ DSPACE encBits (· ^ b) :=
    DSPACE_mono_of_le_mul_add (Nat.add_one_pow_le_two_pow_mul_add b)
  have hsub2 : DSPACE encBits (· ^ b) ⊆ DSPACE encBits (fun n => (n + 1) ^ b) :=
    DSPACE_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) b
  have hEq : DSPACE encBits (fun n => (n + 1) ^ b) = DSPACE encBits (· ^ b) :=
    Set.Subset.antisymm hsub1 hsub2
  have hε : (0 : ℝ) < 1 / (b : ℝ) := by positivity
  have hsep := DTIME_rpow_sub_ssubset_DSPACE (spaceConstructible_succ_pow b)
    (Eventually.of_forall fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)) hε
  rw [hEq] at hsep
  refine (DTIME_mono_of_eventually_le ?_).trans_ssubset hsep
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hexp : (a : ℝ) ≤ (b : ℝ) * (2 - 1 / (b : ℝ)) := by
    have : (b : ℝ) * (2 - 1 / (b : ℝ)) = 2 * b - 1 := by field_simp [hb0]
    have ha1 : (a : ℝ) + 1 ≤ 2 * (b : ℝ) := by exact_mod_cast hab
    linarith
  have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hreal : ((n ^ a : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ ((b : ℝ) * (2 - 1 / (b : ℝ))) := by
    calc ((n ^ a : ℕ) : ℝ) = (n : ℝ) ^ (a : ℝ) := by rw [Nat.cast_pow, ← Real.rpow_natCast]
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (a : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_succ n)
              (Nat.cast_nonneg a)
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ ((b : ℝ) * (2 - 1 / (b : ℝ))) :=
            Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hreal' : ((n ^ a : ℕ) : ℝ) ≤ (((n + 1) ^ b : ℕ) : ℝ) ^ (2 - 1 / (b : ℝ)) := by
    refine hreal.trans_eq ?_
    push_cast
    rw [← Real.rpow_natCast ((n : ℝ) + 1) b, ← Real.rpow_mul (by positivity)]
  exact Nat.le_floor hreal'

/-- **Polynomial containment failure**: deterministic space `n ^ b` (`b ≥ 1`) is not contained in
deterministic time `n ^ a` when `a < 2 * b`. -/
theorem DSPACE_pow_not_subset_DTIME_pow {a b : ℕ} (hb : 1 ≤ b) (hab : a < 2 * b) :
    ¬ DSPACE encBits (· ^ b) ⊆ DTIME encBits (· ^ a) :=
  fun h => (DTIME_pow_ssubset_DSPACE_pow hb hab).not_superset h

/-! ### Linear-space separations -/

/-- **Linear space vs. subquadratic time**: for every real `ε > 0`,
`DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_rpow_sub_ssubset_DSPACE_id {ε : ℝ} (hε : 0 < ε) :
    DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_rpow_sub_ssubset_DSPACE spaceConstructible_id (Eventually.of_forall fun _ => le_rfl) hε

/-- **Exponent-below-two form for linear space**: for every real `α < 2`,
`DTIME encBits (fun n => ⌊(n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_rpow_lt_two_ssubset_DSPACE_id {α : ℝ} (hα : α < 2) :
    DTIME encBits (fun n => ⌊(n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_rpow_lt_two_ssubset_DSPACE spaceConstructible_id (Eventually.of_forall fun _ => le_rfl) hα

/-- **Linear time is strictly contained in linear space**:
`DTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_id_ssubset_DSPACE_id :
    DTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) := by
  simpa only [pow_one] using DTIME_pow_ssubset_DSPACE_pow (a := 1) (b := 1) le_rfl (by decide)

/-- **Linear space is not contained in subquadratic deterministic time**: for every real `ε > 0`,
`¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊)`. -/
theorem DSPACE_id_not_subset_DTIME_rpow_sub {ε : ℝ} (hε : 0 < ε) :
    ¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) :=
  fun h => (DTIME_rpow_sub_ssubset_DSPACE_id hε).not_superset h

/-- **Sharper linear-space separation**:
`DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_sq_div_log2_sq_ssubset_DSPACE_id :
    DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_sq_div_log2_sq_ssubset_DSPACE spaceConstructible_id (Eventually.of_forall fun _ => le_rfl)

/-- **Linear space is not contained in `DTIME (n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2)`**. -/
theorem DSPACE_id_not_subset_DTIME_sq_div_log2_sq :
    ¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) :=
  fun h => DTIME_sq_div_log2_sq_ssubset_DSPACE_id.not_superset h

/-- The explicit linear-space diagonal problem `{x | spaceDiagonal (fun n => 4 * n) x = true}`
belongs to `DSPACE encBits (fun n => n)`. -/
theorem setOf_spaceDiagonal_id_mem_DSPACE :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∈ DSPACE encBits (fun n => n) :=
  setOf_spaceDiagonal_four_mul_mem_DSPACE spaceConstructible_id Nat.log2_le_self

/-- The explicit linear-space diagonal problem `{x | spaceDiagonal (fun n => 4 * n) x = true}`
is outside `DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊)` for every `ε > 0`. -/
theorem setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub {ε : ℝ} (hε : 0 < ε) :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∉
      DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) :=
  setOf_spaceDiagonal_notMem_DTIME Nat.log2_le_self
    (eventually_mul_sqrt_add_le_of_mul_add_le_sq
      (eventually_rpow_sub_mul_log2_le_sq (Eventually.of_forall fun _ => le_rfl) hε))

/-- The explicit linear-space diagonal problem `{x | spaceDiagonal (fun n => 4 * n) x = true}`
is outside `DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2)`. -/
theorem setOf_spaceDiagonal_id_notMem_DTIME_sq_div_log2_sq :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∉
      DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) :=
  setOf_spaceDiagonal_notMem_DTIME Nat.log2_le_self
    (eventually_mul_sqrt_add_le_of_mul_add_le_sq
      (eventually_sq_div_log2_sq_mul_log2_le_sq (Eventually.of_forall fun _ => le_rfl)))

end Cslib.Complexity
