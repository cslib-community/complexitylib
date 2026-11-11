/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.PartialHardness.Knowledge
import CslibFrontier.Computability.Circuit.Boolean.CountingBound
import CslibFrontier.Foundations.Combinatorics.WeightedTail
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# No soundness of the CMMSA table

For a No instance `I` of `GapCMMSA Δ g 1`, the partial MCSP table
`FromCMMSA.toInstance I Δ k λ P f` is a No instance for at least two thirds of the choices of the
functions `f`, once `λ ≥ λ₀ (N + 1) ²` for a bound `N` on the number of formulas, the number of
variables and the weights (issue #4362, route B, milestone H4). The table comes from
`CslibFrontier.Computability.MCSP.PartialHardness.Construction`, and its Yes completeness is
`CslibFrontier.Computability.MCSP.PartialHardness.Completeness`. The analysis is the library's
own; [Hirahara2022] fixes only the problem shape.

**The count.** A circuit `h` of size at most `s` that agrees with the table for `f` makes the
variables `v` with `f v ∈ cand h v` weigh more than `g θ` (`FromCMMSA.lt_weight_cand`). The set
`cand h v` does not depend on `f`. With `γ = log 2 - H(δ₀)` and `B = log (4 Δ⁴) + A log 2` for the
input length `A`, the list-size bound `FromCMMSA.card_cand_le` and `2 ^ ℓ v ≥ w v λ` give
`#cand h v ≤ e^(-c w v) 2 ^ 2 ^ ℓ v` with `c = γ λ - B`. Independence of the `f v` and the
weighted tail bound `Cslib.card_filter_le_sum_weight_le` leave at most a `2 ^ n e^(-c g θ)` fraction
of the `f` for each `h`. A union bound over any family `F` of at most `2 ^ M` functions that covers
the `f` in question bounds their fraction by `2 ^ (M + n) e^(-c g θ)`
(`FromCMMSA.three_mul_card_le_of_log_le`). For partial MCSP, `F` is the functions of complexity at
most `s` (`Cslib.Circuits.Boolean.card_computableFunctions_le_two_pow`).

**The parameters.** The threshold is `s = ⌊(P + 2) 2 ^ L / (P L)⌋` with `2 ^ L ≤ 4 θ λ`, so
`M ≤ (s + 1) (2 L + 3) ≈ 8 (1 + 2 / P) θ λ`, while `c g θ ≈ g γ θ λ`. Since `A = O(log λ)` and
`n ≤ N ≤ λ / λ₀`, the fraction is below `1 / 3` for large `λ` once
`g (log 2 - H(δ₀)) > 8 (1 + 2 / P) log 2`, that is `g > 8 (1 + 2 / P) / (1 - H₂(δ₀))` for the
binary entropy `H₂ = H / log 2` in bits. The design review of #4362 asked for the constant `4`;
`8` comes from the crude count `card_computableFunctions_le_two_pow`, and `4` would need a
Stirling-level count of circuits. The gap `g` is free in the NP-hardness of `GapCMMSA`, so the
larger constant does not affect the reduction.

**Other families.** When `F` has at most `2 ^ (κ θ λ + C (N + 1))` members, the same analysis
needs only `g (log 2 - H(δ₀)) > κ log 2` and `λ ≥ λ₀ (N + 1)`
(`FromCMMSA.exists_three_mul_card_le_of_card_le_two_pow`). This serves targets whose small objects
are counted directly, such as truth tables of small time-bounded Kolmogorov complexity (MINKT\*,
issue #4447).

## Main results

* `Cslib.PartialMCSP.FromCMMSA.three_mul_card_toInstance_mem_PartialMCSP_le`: No soundness of the
  table, as a count over the functions `f`.
* `Cslib.PartialMCSP.FromCMMSA.three_mul_card_le_of_log_le`: the count for fixed parameters, for
  any family `F` covering the functions `f` counted.
* `Cslib.PartialMCSP.FromCMMSA.exists_three_mul_card_le_of_card_le_two_pow`: No soundness for any
  family of size `2 ^ (κ θ λ + C (N + 1))`.
* `Cslib.PartialMCSP.FromCMMSA.inputLength_le_clog`: the input length is `O(log λ)`.
* `Cslib.PartialMCSP.FromCMMSA.agreesWith_toInstance_iff`: agreement with the table is agreement
  with `entry f`.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Circuits.Boolean Finset Filter

/-! ### Analysis helpers -/

/-- A linear function of `L` is eventually below any positive multiple of `2 ^ L`. -/
private theorem eventually_mul_add_le_mul_two_pow (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℕ in atTop, a * L + b ≤ c * 2 ^ L := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := (2 : ℝ)) one_lt_two
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (r := (2 : ℝ)) one_lt_two
  have h : Tendsto (fun L : ℕ => a * ((L : ℝ) ^ 1 / 2 ^ L) + b * ((L : ℝ) ^ 0 / 2 ^ L)) atTop
      (nhds 0) := by
    simpa using (h1.const_mul a).add (h0.const_mul b)
  filter_upwards [h.eventually (ge_mem_nhds hc)] with L hL
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  have he : a * ((L : ℝ) ^ 1 / 2 ^ L) + b * ((L : ℝ) ^ 0 / 2 ^ L) = (a * L + b) / 2 ^ L := by
    field_simp
  rw [he, div_le_iff₀ h2] at hL
  linarith

/-- A gap `a < g (log 2 - H(δ₀))` above some `a ≥ 0` forces `g > 0`, and, with
`(1 - 2 δ₀) ^ k ≤ 1 / (2 Δ ²)` and `δ₀ ≤ 1 / 2`, also `Δ > 0`: at `Δ = 0` the bound forces
`δ₀ = 1 / 2`, where `log 2 - H(δ₀) = 0`. -/
private theorem pos_of_gap {Δ k : ℕ} {δ₀ g a : ℝ} (hδ₀' : δ₀ ≤ 1 / 2)
    (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2)) (ha : 0 ≤ a)
    (hg : a < g * (Real.log 2 - Real.binEntropy δ₀)) : 0 < g ∧ 0 < Δ := by
  have hγ0 : 0 ≤ Real.log 2 - Real.binEntropy δ₀ := sub_nonneg.2 Real.binEntropy_le_log_two
  have hgγ : 0 < g * (Real.log 2 - Real.binEntropy δ₀) := ha.trans_lt hg
  refine ⟨?_, ?_⟩
  · by_contra hneg
    push Not at hneg
    nlinarith
  · rcases Nat.eq_zero_or_pos Δ with rfl | h
    · exfalso
      have h0 : (1 - 2 * δ₀) ^ k ≤ 0 := by simpa using hkδ
      have hd : δ₀ = 1 / 2 := by
        by_contra hne
        have : 0 < 1 - 2 * δ₀ := by
          rcases lt_or_eq_of_le hδ₀' with h | h
          · linarith
          · exact absurd h hne
        exact absurd h0 (not_le.2 (pow_pos this k))
      rw [hd, one_div, Real.binEntropy_two_inv, sub_self, mul_zero] at hgγ
      exact lt_irrefl _ hgγ
    · exact h

/-- **The input length is logarithmic in `λ`.** When the numbers of formulas and the weights are
at most `λ`, the input length is at most `(1 + 2 k Δ²) ⌈log₂ λ⌉ + Δ²`. -/
theorem inputLength_le_clog {I : CMMSAInstance} {Δ k lam : ℕ} (hm : I.formulas.length ≤ lam)
    (hw : ∀ w ∈ I.weights, w ≤ lam) :
    inputLength I Δ k lam ≤ Nat.clog 2 lam + Δ ^ 2 * (2 * k * Nat.clog 2 lam + 1) := by
  have hlamL : lam ≤ 2 ^ Nat.clog 2 lam := Nat.le_pow_clog Nat.one_lt_two _
  have hidx : indexWidth I ≤ Nat.clog 2 lam := Nat.clog_le_of_le_pow (hm.trans hlamL)
  have hvar (v : ℕ) (hv : v < I.weights.length) : varLength I lam v ≤ 2 * Nat.clog 2 lam := by
    refine Nat.clog_le_of_le_pow ?_
    calc I.weights.getD v 0 * lam ≤ lam * lam := Nat.mul_le_mul_right _ (hw _ (getD_weights_mem hv))
      _ ≤ 2 ^ Nat.clog 2 lam * 2 ^ Nat.clog 2 lam := Nat.mul_le_mul hlamL hlamL
      _ = 2 ^ (2 * Nat.clog 2 lam) := by rw [← pow_add, two_mul]
  have hW : seedWidth I lam ≤ 2 * Nat.clog 2 lam :=
    Finset.sup_le fun v hv => hvar v (Finset.mem_range.1 hv)
  have h1 : slotWidth I k lam ≤ 2 * k * Nat.clog 2 lam + 1 :=
    calc k * seedWidth I lam + 1 ≤ k * (2 * Nat.clog 2 lam) + 1 := by gcongr
      _ = 2 * k * Nat.clog 2 lam + 1 := by ring
  have h2 : Δ * Δ * slotWidth I k lam ≤ Δ ^ 2 * (2 * k * Nat.clog 2 lam + 1) := by
    rw [sq]
    exact Nat.mul_le_mul_left _ h1
  exact Nat.add_le_add hidx h2

/-- **Absorbing the input length.** For `C ≥ 0` and `ε > 0`, eventually in `λ`, every instance
whose numbers of formulas and weights are at most `λ` has
`C (log (4 Δ⁴) + A log 2) ≤ ε λ` for its input length `A`. -/
private theorem eventually_log_inputLength_le (Δ k : ℕ) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ lam : ℕ in atTop, ∀ I : CMMSAInstance, I.formulas.length ≤ lam →
      (∀ w ∈ I.weights, w ≤ lam) →
        C * (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) ≤ ε * lam := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog4 : 0 ≤ Real.log (4 * Δ ^ 4) := by
    rcases Nat.eq_zero_or_pos Δ with rfl | h
    · simp
    · have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast h
      exact Real.log_nonneg (by nlinarith [pow_le_pow_left₀ zero_le_one hΔ' 4])
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (eventually_mul_add_le_mul_two_pow
    (2 * C * (1 + 2 * k * Δ ^ 2) * Real.log 2)
    (2 * C * (Real.log (4 * Δ ^ 4) + Δ ^ 2 * Real.log 2)) hε)
  filter_upwards [eventually_ge_atTop (2 ^ L₀)] with lam hlam I hm hw
  have hlam1 : 1 ≤ lam := le_trans Nat.one_le_two_pow hlam
  have hL' : L₀ ≤ Nat.clog 2 lam := by
    rw [← Nat.clog_pow 2 L₀ Nat.one_lt_two]
    exact Nat.clog_mono_right 2 hlam
  have hpow : ((2 ^ Nat.clog 2 lam : ℕ) : ℝ) ≤ 2 * lam := by
    exact_mod_cast Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
  have hA : (inputLength I Δ k lam : ℝ) ≤
      (1 + 2 * k * Δ ^ 2) * (Nat.clog 2 lam : ℕ) + Δ ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).2 (inputLength_le_clog (Δ := Δ) (k := k) hm hw)
    push_cast at this ⊢
    linarith
  have hE := hL₀ _ hL'
  push_cast at hpow hE
  have a1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hl2.le) hC
  have a2 := mul_le_mul_of_nonneg_left hpow hε.le
  nlinarith

/-! ### The count for fixed parameters -/

section Fixed

variable {I : CMMSAInstance} {Δ k lam : ℕ}

/-- The per-variable bound: with `c = γ λ - B`, a candidate set holds at most an `e^(-c w v)`
fraction of the functions of variable `v`. -/
private theorem card_cand_le_exp_mul (hwf : I.WellFormed Δ) (hk : Odd k) (hΔ : 0 < Δ)
    {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (h : BooleanFunction (inputLength I Δ k lam)) (v : Fin I.weights.length) :
    (#(cand h v) : ℝ) ≤
      Real.exp (-((lam * (Real.log 2 - Real.binEntropy δ₀) -
          (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2)) *
        I.weights.getD v 0)) * Fintype.card (BooleanFunction (varLength I lam v)) := by
  obtain ⟨A, hA⟩ : ∃ A, A = inputLength I Δ k lam := ⟨_, rfl⟩
  set ℓ := varLength I lam v
  set γ := Real.log 2 - Real.binEntropy δ₀ with hγ
  set w : ℕ := I.weights.getD v 0
  set B := Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2 with hB
  have hγ0 : 0 ≤ γ := sub_nonneg.2 Real.binEntropy_le_log_two
  have hw1 : 1 ≤ w := hwf.weight_pos _ (getD_weights_mem v.isLt)
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hB0 : 0 ≤ B := by
    have : (1 : ℝ) ≤ 4 * Δ ^ 4 := by nlinarith [pow_le_pow_left₀ zero_le_one hΔ' 4]
    have := Real.log_nonneg this
    have := Real.log_nonneg (one_le_two (α := ℝ))
    positivity
  have hℓ : ((w * lam : ℕ) : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast Nat.le_pow_clog Nat.one_lt_two _
  have hcard : (Fintype.card (BooleanFunction ℓ) : ℝ) = Real.exp (2 ^ ℓ * Real.log 2) := by
    have : Fintype.card (BooleanFunction ℓ) = 2 ^ 2 ^ ℓ := by simp [BooleanFunction, BitString]
    rw [this, show (2 : ℝ) ^ ℓ = ((2 ^ ℓ : ℕ) : ℝ) by push_cast; rfl, Real.exp_nat_mul,
      Real.exp_log two_pos]
    push_cast
    rfl
  have hpre : (4 * Δ ^ 4 * 2 ^ A : ℝ) = Real.exp B := by
    rw [hB, hA, Real.exp_add, Real.exp_log (by positivity), ← Real.log_pow,
      Real.exp_log (by positivity)]
  calc (#(cand h v) : ℝ) ≤ 4 * Δ ^ 4 * 2 ^ A * Real.exp (2 ^ ℓ * Real.binEntropy δ₀) :=
        hA ▸ card_cand_le hk hΔ hδ₀ hδ₀' hkδ h v
    _ = Real.exp (B + 2 ^ ℓ * Real.binEntropy δ₀) := by rw [hpre, ← Real.exp_add]
    _ ≤ Real.exp (-((lam * γ - B) * w) + 2 ^ ℓ * Real.log 2) := by
        refine Real.exp_le_exp.2 ?_
        have hw1' : (1 : ℝ) ≤ w := by exact_mod_cast hw1
        push_cast at hℓ
        have h1 : B ≤ B * w := le_mul_of_one_le_right hB0 hw1'
        have h2 : (w * lam : ℝ) * γ ≤ 2 ^ ℓ * γ := mul_le_mul_of_nonneg_right hℓ hγ0
        nlinarith
    _ = Real.exp (-((lam * γ - B) * w)) * Fintype.card (BooleanFunction ℓ) := by
        rw [Real.exp_add, hcard]

/-- **Agreement through the entries.** A total function agrees with the table
`toInstance I Δ k λ P f` exactly when it extends `entry f`; the threshold `P` plays no role. -/
theorem agreesWith_toInstance_iff {P : ℕ} {f : VarFunctions I lam}
    {h : BooleanFunction (inputLength I Δ k lam)} :
    (toInstance I Δ k lam P f).AgreesWith h ↔ ∀ x b, entry f x = some b → h x = b := by
  simp [Instance.AgreesWith, toInstance]

/-- **The count for fixed parameters, for any family of functions.** Let `F` hold at most `2 ^ M`
functions on the input length `A`, and let every `f` with `Good f` have its entries extended by
some member of `F`. If `log 3 + (M + n) log 2 ≤ c g θ` for `c = γ λ - B ≥ 0`, then `Good` holds
for at most a third of the functions `f`. For partial MCSP, `F` is the functions of circuit
complexity at most the threshold; for MINKT\*, the functions whose truth tables have small `K^t`. -/
theorem three_mul_card_le_of_log_le {g : ℝ} (hI : I ∈ (GapCMMSA Δ g 1).no) (hk : Odd k)
    (hΔ : 0 < Δ) {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2)
    (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (F : Finset (BooleanFunction (inputLength I Δ k lam))) {M : ℕ} (hF : #F ≤ 2 ^ M)
    (Good : VarFunctions I lam → Prop) [DecidablePred Good]
    (hGood : ∀ f, Good f → ∃ h ∈ F, ∀ x b, entry f x = some b → h x = b)
    (hc : 0 ≤ lam * (Real.log 2 - Real.binEntropy δ₀) -
      (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2))
    (hlog : Real.log 3 + (M + I.weights.length) * Real.log 2 ≤
      (lam * (Real.log 2 - Real.binEntropy δ₀) -
        (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2)) * (g * I.threshold)) :
    3 * #{f : VarFunctions I lam | Good f} ≤ Fintype.card (VarFunctions I lam) := by
  classical
  obtain ⟨hwf, -, -⟩ := mem_no_GapCMMSA_one.1 hI
  set c := lam * (Real.log 2 - Real.binEntropy δ₀) -
    (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) with hc_def
  set T := c * (g * I.threshold) with hT
  let Bad : BooleanFunction (inputLength I Δ k lam) → Finset (VarFunctions I lam) := fun h =>
    {f | T ≤ ∑ v with f v ∈ cand h v, c * (I.weights.getD v 0 : ℝ)}
  have hsub : ({f : VarFunctions I lam | Good f} : Finset _) ⊆ F.biUnion Bad := by
    intro f hf
    obtain ⟨h, hmem, hh⟩ := hGood f (mem_filter.1 hf).2
    refine mem_biUnion.2 ⟨h, hmem, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have hlt := lt_weight_cand hI 0 f h (agreesWith_toInstance_iff.2 hh)
    have hw : (I.weight ((univ.filter fun v => f v ∈ cand h v).map Fin.valEmbedding) : ℝ) =
        ∑ v with f v ∈ cand h v, (I.weights.getD v 0 : ℝ) := by
      simp [CMMSAInstance.weight]
    rw [← mul_sum, ← hw]
    exact mul_le_mul_of_nonneg_left hlt.le hc
  have hbad (h : BooleanFunction (inputLength I Δ k lam)) : (#(Bad h) : ℝ) ≤
      2 ^ I.weights.length * Real.exp (-T) * Fintype.card (VarFunctions I lam) := by
    have := card_filter_le_sum_weight_le (fun v : Fin I.weights.length => cand h v)
      (fun v => c * (I.weights.getD v 0 : ℝ))
      (fun v => card_cand_le_exp_mul hwf hk hΔ hδ₀ hδ₀' hkδ h v) T
    rwa [Fintype.card_fin] at this
  have hF' : (#F : ℝ) ≤ 2 ^ M := by exact_mod_cast hF
  have h2 (m : ℕ) : (2 : ℝ) ^ m = Real.exp (m * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hfin : 3 * 2 ^ M * (2 ^ I.weights.length * Real.exp (-T)) ≤ (1 : ℝ) := by
    rw [h2, h2, ← Real.exp_log (show (0 : ℝ) < 3 by norm_num)]
    simp only [← Real.exp_add]
    refine Real.exp_le_one_iff.2 ?_
    linarith
  have hVF : (0 : ℝ) ≤ Fintype.card (VarFunctions I lam) := Nat.cast_nonneg _
  have key : (3 * #{f : VarFunctions I lam | Good f} : ℝ) ≤ Fintype.card (VarFunctions I lam) :=
    calc (3 * #{f : VarFunctions I lam | Good f} : ℝ)
        ≤ 3 * #(F.biUnion Bad) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub) (by norm_num)
      _ ≤ 3 * ∑ h ∈ F, (#(Bad h) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast card_biUnion_le) (by norm_num)
      _ ≤ 3 * ∑ h ∈ F,
            2 ^ I.weights.length * Real.exp (-T) * Fintype.card (VarFunctions I lam) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun h _ => hbad h) (by norm_num)
      _ = 3 * #F * (2 ^ I.weights.length * Real.exp (-T)) *
            Fintype.card (VarFunctions I lam) := by
          rw [sum_const, nsmul_eq_mul]
          ring
      _ ≤ 3 * 2 ^ M * (2 ^ I.weights.length * Real.exp (-T)) *
            Fintype.card (VarFunctions I lam) := by
          gcongr
      _ ≤ 1 * Fintype.card (VarFunctions I lam) := mul_le_mul_of_nonneg_right hfin hVF
      _ = Fintype.card (VarFunctions I lam) := one_mul _
  exact_mod_cast key

end Fixed

/-! ### No soundness -/

/-- The final real inequality: the circuit count and the variables fit in the exponent. -/
private theorem log_le_of_parts {l2 l3 Q η g γ X lam θ s L M n Bt : ℝ} (hl2 : 0 ≤ l2)
    (hη : η = g * γ - 8 * Q * l2) (hX : X = θ * lam) (hM : M ≤ (s + 1) * (2 * L + 3))
    (hsL : 2 * s * L * l2 ≤ 8 * Q * l2 * X) (h3s : 3 * s * l2 ≤ η * X / 4)
    (hL : (2 * L + 3) * l2 + l3 ≤ η * X / 4) (hn : n * l2 ≤ η * X / 4)
    (hB : g * Bt * θ ≤ η * X / 4) :
    l3 + (M + n) * l2 ≤ (lam * γ - Bt) * (g * θ) := by
  have h1 := mul_le_mul_of_nonneg_right hM hl2
  have h2 : (lam * γ - Bt) * (g * θ) = (η + 8 * Q * l2) * X - g * Bt * θ := by
    rw [hη, hX]
    ring
  rw [h2]
  linarith

open scoped Classical in
/-- **No soundness of the CMMSA table.** Let `k` be odd, `0 ≤ δ₀ ≤ 1 / 2` with
`(1 - 2 δ₀) ^ k ≤ 1 / (2 Δ ²)`, and `g (log 2 - H(δ₀)) > 8 (1 + 2 / P) log 2`, that is
`g > 8 (1 + 2 / P) / (1 - H₂(δ₀))` with the binary entropy `H₂` in bits. There is a constant `λ₀`
such that for every No instance `I` of `GapCMMSA Δ g 1` whose numbers of formulas and variables
and whose weights are at most `N`, and every `λ ≥ λ₀ (N + 1) ²`, at most a third of the choices of
the functions `f` put the table `toInstance I Δ k λ P f` in partial MCSP.

`λ₀` is existential and not computed: it comes from eventual bounds on `L / 2 ^ L`. The constant
`8` comes from the crude circuit count `card_computableFunctions_le_two_pow`; the design review of
#4362 has `4`, which needs a Stirling-level count. -/
theorem three_mul_card_toInstance_mem_PartialMCSP_le (Δ k P : ℕ) (hP : 0 < P) (hk : Odd k)
    {δ₀ g : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (hg : 8 * (1 + 2 / P) * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) :
    ∃ lam₀ : ℕ, ∀ I ∈ (GapCMMSA Δ g 1).no, ∀ N : ℕ, I.formulas.length ≤ N →
      I.weights.length ≤ N → (∀ w ∈ I.weights, w ≤ N) →
      ∀ lam, lam₀ * (N + 1) ^ 2 ≤ lam →
        3 * #{f : VarFunctions I lam | toInstance I Δ k lam P f ∈ PartialMCSP} ≤
          Fintype.card (VarFunctions I lam) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ : 0 < 1 + 2 / (P : ℝ) := by positivity
  have hQl : 0 < 8 * (1 + 2 / (P : ℝ)) * Real.log 2 := mul_pos (by positivity) hl2
  obtain ⟨hg0, hΔ⟩ := pos_of_gap hδ₀' hkδ hQl.le hg
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = Real.log 2 - Real.binEntropy δ₀ := ⟨_, rfl⟩
  rw [← hγ] at hg
  obtain ⟨η, hη⟩ : ∃ η, η = g * γ - 8 * (1 + 2 / P) * Real.log 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  have hηlt : η < g * γ := by rw [hη]; linarith
  -- The eventual bounds, all in a binary length `L`.
  have e1 : ∀ᶠ L : ℕ in atTop, 48 * (1 + 2 / P) * Real.log 2 ≤ η * L :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hη0).eventually_ge_atTop _
  have e2 : ∀ᶠ L : ℕ in atTop, 2 * (P + 2) ≤ P * L :=
    (tendsto_id.const_mul_atTop' hP).eventually_ge_atTop _
  have e3 := eventually_mul_add_le_mul_two_pow (32 * Real.log 2)
    (16 * (3 * Real.log 2 + Real.log 3)) hη0
  have e4 := eventually_mul_add_le_mul_two_pow (4 * (1 + 2 * k * Δ ^ 2 : ℝ))
    (4 * (Δ ^ 2 + 1 : ℝ)) one_pos
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (((e1.and e2).and e3).and e4)
  -- The input length is absorbed: `g B ≤ η λ / 4`.
  obtain ⟨Λ, hΛ⟩ := eventually_atTop.1
    (eventually_log_inputLength_le Δ k hg0.le (div_pos hη0 four_pos))
  refine ⟨max (max (2 ^ L₀) Λ) ⌈4 * Real.log 2 / η⌉₊, fun I hI N hm hn hwN lam hlam => ?_⟩
  obtain ⟨hwf, -, -⟩ := mem_no_GapCMMSA_one.1 hI
  set lam₀ := max (max (2 ^ L₀) Λ) ⌈4 * Real.log 2 / η⌉₊ with hlam₀_def
  have hlam₀ : 1 ≤ lam₀ := le_trans Nat.one_le_two_pow ((le_max_left _ _).trans (le_max_left _ _))
  have hN1 : lam₀ * (N + 1) ≤ lam :=
    le_trans (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _)) hlam
  have hNl : N * lam₀ ≤ lam :=
    calc N * lam₀ = lam₀ * N := mul_comm _ _
      _ ≤ lam₀ * (N + 1) := Nat.mul_le_mul_left _ (Nat.le_succ N)
      _ ≤ lam := hN1
  have hNlam : N < lam :=
    calc N < N + 1 := Nat.lt_succ_self _
      _ ≤ lam₀ * (N + 1) := Nat.le_mul_of_pos_left _ hlam₀
      _ ≤ lam := hN1
  have hlam₀lam : lam₀ ≤ lam :=
    calc lam₀ ≤ lam₀ * (N + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ lam := hlam
  have hL₀lam : 2 ^ L₀ ≤ lam := ((le_max_left _ _).trans (le_max_left _ _)).trans hlam₀lam
  have hΛlam : Λ ≤ lam := ((le_max_right _ _).trans (le_max_left _ _)).trans hlam₀lam
  -- `L' = ⌈log₂ λ⌉`.
  set L' := Nat.clog 2 lam with hL'
  have hL'₀ : L₀ ≤ L' := by
    rw [hL', ← Nat.clog_pow 2 L₀ Nat.one_lt_two]
    exact Nat.clog_mono_right 2 hL₀lam
  -- `L = ⌈log₂ (2 θ λ)⌉`.
  have hθ1 : 1 ≤ I.threshold := hwf.threshold_pos
  set L := tableLength I lam with hL
  have hL'L : L' ≤ L := Nat.clog_mono_right 2 (Nat.le_mul_of_pos_left lam (by omega))
  have hLθ : 2 ^ L ≤ 4 * I.threshold * lam :=
    calc 2 ^ L = 2 ^ Nat.clog 2 (2 * I.threshold * lam) := rfl
      _ ≤ 2 * (2 * I.threshold * lam) :=
          Nat.pow_clog_le_mul Nat.one_lt_two (Nat.mul_pos (Nat.mul_pos two_pos hθ1) (by omega)).ne'
      _ = 4 * I.threshold * lam := by ring
  obtain ⟨⟨⟨hL1, hL2⟩, hL3⟩, -⟩ := hL₀ L (hL'₀.trans hL'L)
  obtain ⟨⟨⟨-, -⟩, -⟩, hE4⟩ := hL₀ L' hL'₀
  -- The input length `A = O(L')`.
  have hmlam : I.formulas.length ≤ lam := by omega
  have hwlam : ∀ w ∈ I.weights, w ≤ lam := fun w hw => (hwN w hw).trans hNlam.le
  have hA : inputLength I Δ k lam ≤ L' + Δ ^ 2 * (2 * k * L' + 1) :=
    inputLength_le_clog hmlam hwlam
  have hAr : (inputLength I Δ k lam : ℝ) ≤ (1 + 2 * k * Δ ^ 2) * L' + Δ ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).2 hA
    push_cast at this
    linarith
  -- The threshold `s ≤ (P + 2) 2 ^ L / (P L)` and the circuit count `M ≤ (s + 1) (2 L + 3)`.
  have hLpos : 0 < L := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hL2; omega
  set s := sizeThreshold I lam P with hs
  have hsPL : s * (P * L) ≤ (P + 2) * 2 ^ L := Nat.div_mul_le_self _ _
  have h2s : 2 * s ≤ 2 ^ L := by
    have : 2 * s * (P * L) ≤ 2 ^ L * (P * L) := by
      calc 2 * s * (P * L) = 2 * (s * (P * L)) := by ring
        _ ≤ 2 * ((P + 2) * 2 ^ L) := Nat.mul_le_mul_left _ hsPL
        _ = 2 ^ L * (2 * (P + 2)) := by ring
        _ ≤ 2 ^ L * (P * L) := Nat.mul_le_mul_left _ hL2
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have h2A : 2 * (inputLength I Δ k lam + 1) ≤ 2 ^ L' := by
    have h0 : (0 : ℝ) ≤ (1 + 2 * k * Δ ^ 2) * L' := by positivity
    have h0' : (0 : ℝ) ≤ Δ ^ 2 := by positivity
    have : (2 * (inputLength I Δ k lam + 1) : ℝ) ≤ 2 ^ L' := by linarith
    exact_mod_cast this
  have hpowL : 2 ^ L' ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL'L
  have hM : computableFunctionsLogBound (inputLength I Δ k lam) s ≤ (s + 1) * (2 * L + 3) := by
    have : Nat.clog 2 (inputLength I Δ k lam + s + 1) ≤ L := Nat.clog_le_of_le_pow (by omega)
    unfold computableFunctionsLogBound
    gcongr
  -- The real inequality.
  have hθr : (1 : ℝ) ≤ I.threshold := by exact_mod_cast hθ1
  have hLθr : (2 : ℝ) ^ L ≤ 4 * I.threshold * lam := by exact_mod_cast hLθ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hl2' : (0 : ℝ) ≤ 2 * Real.log 2 := by linarith
  have hsLr : (s : ℝ) * L ≤ 4 * (1 + 2 / P) * (I.threshold * lam) := by
    have h := (Nat.cast_le (α := ℝ)).2 hsPL
    push_cast at h
    have h' : (s : ℝ) * L * P ≤ (P + 2) * (4 * I.threshold * lam) := by
      have := mul_le_mul_of_nonneg_left hLθr (by positivity : (0 : ℝ) ≤ P + 2)
      linarith
    have hPne : (P : ℝ) ≠ 0 := hP'.ne'
    have hPP : 2 / (P : ℝ) * P = 2 := by field_simp
    have e : 4 * (1 + 2 / (P : ℝ)) * (I.threshold * lam) * P =
        (P + 2) * (4 * I.threshold * lam) := by
      linear_combination (4 * ((I.threshold : ℝ) * lam)) * hPP
    exact le_of_mul_le_mul_right (h'.trans e.symm.le) hP'
  have hM1 : 2 * (s : ℝ) * L * Real.log 2 ≤
      8 * (1 + 2 / P) * Real.log 2 * (I.threshold * lam) := by
    have := mul_le_mul_of_nonneg_left hsLr hl2'
    linarith
  have hM2 : 3 * (s : ℝ) * Real.log 2 ≤ η * (I.threshold * lam) / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hsLr (by linarith : (0 : ℝ) ≤ 3 * Real.log 2)
    have h2 := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ I.threshold * lam / 4)
    have h3 : 3 * (s : ℝ) * Real.log 2 * L ≤ η * (I.threshold * lam) / 4 * L := by linarith
    exact le_of_mul_le_mul_right h3 hLr
  have hM3 : (2 * L + 3 : ℝ) * Real.log 2 + Real.log 3 ≤ η * (I.threshold * lam) / 4 := by
    have := mul_le_mul_of_nonneg_left hLθr hη0.le
    linarith
  have hn' : (I.weights.length : ℝ) * Real.log 2 ≤ η * (I.threshold * lam) / 4 := by
    have hceil : 4 * Real.log 2 / η ≤ lam₀ :=
      (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))
    have h4 : 4 * Real.log 2 ≤ η * lam₀ := by
      have := (div_le_iff₀ hη0).1 hceil
      linarith
    have hNr : (N : ℝ) * lam₀ ≤ lam := by exact_mod_cast hNl
    have hnN : (I.weights.length : ℝ) ≤ N := by exact_mod_cast hn
    have a1 := mul_le_mul_of_nonneg_right hnN hl2.le
    have a2 := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg (α := ℝ) N)
    have a3 := mul_le_mul_of_nonneg_left hNr hη0.le
    have a4 : η * (lam : ℝ) ≤ η * (I.threshold * lam) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Nat.cast_nonneg _) hθr) hη0.le
    linarith
  have hB : g * (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) ≤ η * lam / 4 := by
    have := hΛ lam hΛlam I hmlam hwlam
    linarith
  have hBθ : g * (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) * I.threshold ≤
      η * (I.threshold * lam) / 4 := by
    have := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg (α := ℝ) I.threshold)
    linarith
  have hc0 : 0 ≤ lam * γ - (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) := by
    have hlam0 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    have a1 := mul_le_mul_of_nonneg_right hηlt.le hlam0
    have a2 : 0 ≤ η * (lam : ℝ) := mul_nonneg hη0.le hlam0
    have a3 : g * (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) ≤
        g * (lam * γ) := by linarith
    linarith [le_of_mul_le_mul_left a3 hg0]
  have hMr : (computableFunctionsLogBound (inputLength I Δ k lam) s : ℝ) ≤
      ((s : ℝ) + 1) * (2 * L + 3) := by exact_mod_cast hM
  have hlog := log_le_of_parts hl2.le hη rfl hMr hM1 hM2 hM3 hn' hBθ
  rw [hγ] at hc0 hlog
  exact three_mul_card_le_of_log_le hI hk hΔ hδ₀ hδ₀' hkδ
    (computableFunctions (inputLength I Δ k lam) (sizeThreshold I lam P))
    (card_computableFunctions_le_two_pow _ _) (fun f => toInstance I Δ k lam P f ∈ PartialMCSP)
    (fun f hf => by
      obtain ⟨h, hmem, hh⟩ := mem_iff_exists_mem_computableFunctions.1 hf
      exact ⟨h, hmem, agreesWith_toInstance_iff.1 hh⟩) hc0 hlog

/-- **No soundness for any small family of functions.** Let `k` be odd, `0 ≤ δ₀ ≤ 1 / 2` with
`(1 - 2 δ₀) ^ k ≤ 1 / (2 Δ ²)`, and `g (log 2 - H(δ₀)) > κ log 2`. There is a constant `λ₀ ≥ 1`
such that for every No instance `I` of `GapCMMSA Δ g 1` whose numbers of formulas and variables
and whose weights are at most `N`, and every `λ ≥ λ₀ (N + 1)`, the following holds. Let `F` be at
most `2 ^ (κ θ λ + C (N + 1))` functions on the input length, and let every `f` with `Good f` have
its entries extended by some member of `F`. Then `Good` holds for at most a third of the choices of
the functions `f`.

This is the union bound of `three_mul_card_toInstance_mem_PartialMCSP_le` with the family left
abstract and its size linear in `θ λ`; it serves a target problem whose small objects number at
most `2 ^ (κ θ λ + C (N + 1))`, such as the truth tables of small time-bounded Kolmogorov
complexity. `λ₀` is existential and not computed. -/
theorem exists_three_mul_card_le_of_card_le_two_pow (Δ k : ℕ) (hk : Odd k) {δ₀ g : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2)) (κ C : ℕ)
    (hg : κ * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) :
    ∃ lam₀ : ℕ, 1 ≤ lam₀ ∧ ∀ I ∈ (GapCMMSA Δ g 1).no, ∀ N : ℕ, I.formulas.length ≤ N →
      I.weights.length ≤ N → (∀ w ∈ I.weights, w ≤ N) →
      ∀ lam, lam₀ * (N + 1) ≤ lam →
      ∀ F : Finset (BooleanFunction (inputLength I Δ k lam)),
        #F ≤ 2 ^ (κ * I.threshold * lam + C * (N + 1)) →
      ∀ (Good : VarFunctions I lam → Prop) [DecidablePred Good],
        (∀ f, Good f → ∃ h ∈ F, ∀ x b, entry f x = some b → h x = b) →
        3 * #{f : VarFunctions I lam | Good f} ≤ Fintype.card (VarFunctions I lam) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hκ : (0 : ℝ) ≤ κ * Real.log 2 := by positivity
  obtain ⟨hg0, hΔ⟩ := pos_of_gap hδ₀' hkδ hκ hg
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = Real.log 2 - Real.binEntropy δ₀ := ⟨_, rfl⟩
  rw [← hγ] at hg
  obtain ⟨η, hη⟩ : ∃ η, η = g * γ - κ * Real.log 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  -- The input length is absorbed: `g B ≤ η λ / 2`.
  obtain ⟨Λ, hΛ⟩ := eventually_atTop.1
    (eventually_log_inputLength_le Δ k hg0.le (div_pos hη0 two_pos))
  refine ⟨max (max Λ 1) ⌈2 * (Real.log 3 + (C + 1) * Real.log 2) / η⌉₊,
    le_max_of_le_left (le_max_right _ _), ?_⟩
  intro I hI N hm hn hwN lam hlam F hF Good _ hGood
  obtain ⟨hwf, -, -⟩ := mem_no_GapCMMSA_one.1 hI
  set lam₀ := max (max Λ 1) ⌈2 * (Real.log 3 + (C + 1) * Real.log 2) / η⌉₊ with hlam₀_def
  have hlam₀lam : lam₀ ≤ lam := (Nat.le_mul_of_pos_right _ (Nat.succ_pos N)).trans hlam
  have hΛlam : Λ ≤ lam := ((le_max_left _ _).trans (le_max_left _ _)).trans hlam₀lam
  have hlam₀1 : 1 ≤ lam₀ := (le_max_right Λ 1).trans (le_max_left _ _)
  have hNlam : N + 1 ≤ lam := (Nat.le_mul_of_pos_left _ hlam₀1).trans hlam
  have hmlam : I.formulas.length ≤ lam := by omega
  have hwlam : ∀ w ∈ I.weights, w ≤ lam := fun w hw => by have := hwN w hw; omega
  have hB := hΛ lam hΛlam I hmlam hwlam
  have hθ1 : (1 : ℝ) ≤ I.threshold := by exact_mod_cast hwf.threshold_pos
  have hlamr : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  -- `c = γ λ - B ≥ 0`.
  have hc : 0 ≤ lam * γ - (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) := by
    have a1 : g * (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2) ≤
        g * (lam * γ) := by
      have := mul_le_mul_of_nonneg_right (show η / 2 ≤ g * γ by rw [hη]; linarith) hlamr
      linarith
    linarith [le_of_mul_le_mul_left a1 hg0]
  -- The constant terms fit in `η λ / 2`.
  have hceil : 2 * (Real.log 3 + (C + 1) * Real.log 2) / η ≤ lam₀ :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))
  have h4 : 2 * (Real.log 3 + (C + 1) * Real.log 2) ≤ η * lam₀ := by
    have := (div_le_iff₀ hη0).1 hceil
    linarith
  have hNr : (lam₀ : ℝ) * (N + 1) ≤ lam := by exact_mod_cast hlam
  have hD : (Real.log 3 + (C + 1) * Real.log 2) * (N + 1) ≤ η / 2 * lam := by
    have a1 := mul_le_mul_of_nonneg_left hNr (by positivity : (0 : ℝ) ≤ η / 2)
    have a2 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ N + 1)
    linarith
  -- `log 3 + (M + n) log 2 ≤ c g θ`.
  have hlog : Real.log 3 + (((κ * I.threshold * lam + C * (N + 1) : ℕ) : ℝ) + I.weights.length) *
      Real.log 2 ≤
      (lam * γ - (Real.log (4 * Δ ^ 4) + inputLength I Δ k lam * Real.log 2)) *
        (g * I.threshold) := by
    push_cast
    have hn' : (I.weights.length : ℝ) ≤ N := by exact_mod_cast hn
    have b1 := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ I.threshold)
    have b3 := mul_le_mul_of_nonneg_right hn' hl2.le
    have b4 : η / 2 * lam ≤ η / 2 * (lam * I.threshold) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hlamr hθ1) (by positivity)
    have b5 : 0 ≤ Real.log 3 * N :=
      mul_nonneg (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _)
    have e : η * (lam * I.threshold) =
        g * γ * (lam * I.threshold) - κ * Real.log 2 * (lam * I.threshold) := by
      rw [hη]
      ring
    linarith
  rw [hγ] at hc hlog
  exact three_mul_card_le_of_log_le hI hk hΔ hδ₀ hδ₀' hkδ F hF Good hGood hc hlog

end Cslib.PartialMCSP.FromCMMSA
