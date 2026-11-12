/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
import CslibFrontier.Computability.Complexity.FineGrained.SingleSubexp
import CslibFrontier.Computability.Complexity.FineGrained.Randomized
import CslibFrontier.Computability.Complexity.FineGrained.GapETH
import CslibFrontier.Computability.Complexity.FineGrained.RatesNativeEndpoint
import CslibFrontier.Foundations.Analysis.SublinearEnvelope
import CslibFrontier.Probability.MajorityVote

/-!
# Fine-grained rates, exponents, and exponential-time hypotheses

Kernel-checked strict-`module` tests (using plain `import` and zero `native_decide`) exercising:

1. **Counting rates and `#k-SAT` (`CountingExponents`):** concrete `BruteForceCount.count`
   evaluations on empty, contradictory, satisfiable 3-CNF, and width-`4` formulas; `SharpKSAT`
   width guarding; `0 ≤ satExponent k ≤ sharpSatExponent k ≤ 1`; `SharpETH` / `SharpSETH`
   characterizations; clause-vs-variable counting sparsification transfers; and unconditional
   `sharpSatExponent_eq_zero`, `not_SharpETH`, `not_SharpSETH`.
2. **Single-machine `2 ^ o(μ)` vs. `∀ δ > 0` families (`SingleSubexp`):** `DeclaredCNF` and
   `SharpDeclaredKSAT` with unused declared variables and out-of-range variable guards; single
   machine quantifier characterizations; `ETH → SingleETH → SingleSharpETH` and
   `SharpETH → SingleSharpETH`; and unconditional `computableInSingleSubexpTime_SharpDeclaredKSAT`,
   `computableInSingleSubexpTime_SharpKSAT`, `decidableInSingleSubexpTime_KSAT`, `not_SingleETH`,
   `not_SingleSharpETH`.
3. **Randomized rates and error amplification (`Randomized`):** `ErrorModel` order and symmetry;
   concrete majority-vote moment bound `card_filter_card_filter_le_of_err_lt_half`; `PromiseBPP` /
   `PromiseRP` / `PromiseCoRP` bridges; rate-preserving threshold invariance across `(0, 1 / 2)`
   and `(0, 1)`; `0 ≤ rSatExponent k ≤ rpSatExponent k ≤ satExponent k`; `rETH` / `rSETH`; and
   unconditional `rpSatExponent_eq_zero`, `rSatExponent_eq_zero`, `not_rETH`, `not_rSETH`.
4. **Gap `k`-SAT and Gap-ETH (`GapETH`):** `MaxSATThresholdSearch.leafAccepts` concrete checks;
   imperfect-completeness `GapKSAT` yes/no witnesses and width-`0` `PromiseP` membership;
   `0 ≤ rGapSatExponent P ≤ gapSatExponent P ≤ 1` for arbitrary `(k, c, s)`; full conditional
   implication diamond `rGapETH → GapETH → ETH → SingleETH → SingleSharpETH` and
   `rGapETH → rETH → ETH → SharpETH → SingleSharpETH`; and unconditional `not_GapETH`,
   `not_rGapETH`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.FineGrainedRates

open Cslib Cslib.Complexity Cslib.Logic.PL Filter Topology Turing.MultiTapeTM

/-! ### 1. Concrete CNF formulas and kernel-checked `BruteForceCount` / `SharpKSAT` tests -/

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁)`: satisfied iff `x₁ = true` (`2` of the `4` assignments on `{0, 1}`). -/
private def phiTwo : CNF ℕ :=
  [[(0, true), (1, true)], [(0, false), (1, true)]]

/-- Single width-`4` clause `x₀ ∨ x₁ ∨ x₂ ∨ x₃` (`15` of `16` assignments satisfy it). -/
private def phiFour : CNF ℕ :=
  [[(0, true), (1, true), (2, true), (3, true)]]

/-- Unsatisfiable width-`1` formula `x₀ ∧ ¬x₀ ∧ x₀` (`x₀ = true` satisfies `2 / 3` of clauses). -/
private def phiTwoOfThree : CNF ℕ :=
  [[(0, true)], [(0, false)], [(0, true)]]

example : BruteForceCount.count ([] : CNF ℕ) = 1 := rfl
example : BruteForceCount.count ([[]] : CNF ℕ) = 0 := rfl
example : BruteForceCount.count phiTwo = 2 := by decide
example : BruteForceCount.count phiFour = 15 := by decide

-- `SharpKSAT` agrees with `modelCount` within width `k` and returns `0` outside width `k`.
example : SharpKSAT 3 phiTwo = 2 := by
  have hmc : phiTwo.modelCount = 2 := by
    rw [← BruteForceCount.count_eq_modelCount]
    decide
  rw [SharpKSAT_of_width (by decide), hmc]

example : SharpKSAT 3 phiFour = 0 ∧ SharpKSAT 4 phiFour = 15 := by
  refine ⟨SharpKSAT_of_not_width (by decide), ?_⟩
  have hmc : phiFour.modelCount = 15 := by
    rw [← BruteForceCount.count_eq_modelCount]
    decide
  rw [SharpKSAT_of_width (by decide), hmc]

example : SharpKSAT 3 = SharpThreeSAT := SharpKSAT_three

/-! ### 2. `DeclaredCNF` and `SharpDeclaredKSAT` concrete tests -/

-- Declaring `4` variables for `phiTwo` (`2` occurring variables `{0, 1} ⊆ range 4`)
-- scales `modelCount = 2` by `2 ^ (4 - 2) = 4`, giving `8` satisfying assignments.
example : SharpDeclaredKSAT 3 { numVars := 4, formula := phiTwo } = 8 := by
  rw [SharpDeclaredKSAT_of_valid (by decide) (by decide)]
  have hmc : phiTwo.modelCount = 2 := by
    rw [← BruteForceCount.count_eq_modelCount]
    decide
  have hnv : phiTwo.numVars = 2 := by decide
  rw [hmc, hnv]
  rfl

-- Variable `1` lies outside `range 1`, so the guarded declared-variable counter returns `0`.
example : SharpDeclaredKSAT 3 { numVars := 1, formula := phiTwo } = 0 :=
  SharpDeclaredKSAT_of_not_valid (by decide)

/-! ### 3. `ErrorModel` order, symmetry, and concrete majority-vote tail bound -/

example : ErrorModel.rp.symm = ErrorModel.coRP ∧ ErrorModel.coRP.symm = ErrorModel.rp :=
  ⟨ErrorModel.symm_rp, ErrorModel.symm_coRP⟩

example :
    ErrorModel.deterministic ≤ ErrorModel.rp ∧
    ErrorModel.oneSidedRP (1 / 3) (by norm_num) (by norm_num) ≤ ErrorModel.bounded :=
  ⟨ErrorModel.deterministic_le _, ErrorModel.oneSidedRP_le_twoSided le_rfl⟩

-- Concrete instance of `card_filter_card_filter_le_of_err_lt_half` on `Fin 4`:
-- when `3` of `4` seeds succeed (`ε = 1 / 4 < 1 / 2`), among the `4 ^ 4 = 256` 4-tuples of seeds,
-- at most `(4 * (1 / 4) * (3 / 4)) ^ 2 * 4 ^ 4 = 144` have `≤ 2` good coordinates.
example :
    let G : Finset (Fin 4) := {0, 1, 2}
    ((Finset.univ.filter fun ω : Fin 4 → Fin 4 =>
      (Finset.univ.filter fun i : Fin 4 => ω i ∈ G).card ≤ 2).card : ℝ) ≤ 144 := by
  intro G
  have hG : (1 - (1 / 4 : ℝ)) * (Fintype.card (Fin 4) : ℝ) ≤ (G.card : ℝ) := by
    have hcard : G.card = 3 := by decide
    simp only [hcard, Fintype.card_fin]
    norm_num
  have hbound := card_filter_card_filter_le_of_err_lt_half G
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2) hG 2
  simpa only [Fintype.card_fin] using hbound.trans (by norm_num)

/-! ### 4. Imperfect-completeness `GapKSAT`, width-`0` `PromiseP`, and threshold leaves -/

-- On `phiTwoOfThree`, `bitsAssignment [0] 1` sets `x₀ := true` and satisfies `2` of `3` clauses.
example :
    MaxSATThresholdSearch.leafAccepts
      { formula := phiTwoOfThree, varsList := [0], cutoff := 2, index := 1 } = true ∧
    MaxSATThresholdSearch.leafAccepts
      { formula := phiTwoOfThree, varsList := [0], cutoff := 3, index := 1 } = false := by
  decide

private noncomputable def specImperfect : GapKSATSpec where
  width := 1
  completeness := 2 / 3
  soundness := 1 / 3
  soundness_nonneg := by norm_num
  soundness_lt_completeness := by norm_num
  completeness_le_one := by norm_num

-- `phiTwoOfThree` is unsatisfiable (`∉ KSAT 1`) yet is a YES-instance of `GapKSAT specImperfect`
-- (`completeness = 2 / 3`), while `[[]]` is a NO-instance (`soundness = 1 / 3`).
example : phiTwoOfThree ∈ (GapKSAT specImperfect).yes ∧ [[]] ∈ (GapKSAT specImperfect).no := by
  refine ⟨?_, ?_⟩
  · rw [mem_yes_GapKSAT]
    refine ⟨by decide, ?_⟩
    have hle := CNF.unsatVal_le phiTwoOfThree (fun _ => true)
    have hcnt : phiTwoOfThree.countUnsat (fun _ => true) = 1 := by decide
    have hlen : phiTwoOfThree.length = 3 := rfl
    rw [hcnt, hlen] at hle
    simp only [specImperfect]
    linarith
  · rw [mem_no_GapKSAT]
    refine ⟨by decide, ?_⟩
    simp only [specImperfect]
    refine le_trans (by norm_num : (1 : ℝ) - 1 / 3 ≤ 1) ((CNF.le_unsatVal_iff [[]]).mpr fun σ => ?_)
    have hcnt : CNF.countUnsat σ ([[]] : CNF ℕ) = 1 := rfl
    have hlen : ([[]] : CNF ℕ).length = 1 := rfl
    rw [hcnt, hlen]
    norm_num

-- Width-`0` `GapKSAT` with imperfect completeness `(0, 3 / 4, 1 / 4)` lies in `PromiseP encCNF`.
example :
    let P0 : GapKSATSpec :=
      { width := 0
        completeness := 3 / 4
        soundness := 1 / 4
        soundness_nonneg := by norm_num
        soundness_lt_completeness := by norm_num
        completeness_le_one := by norm_num }
    GapKSAT P0 ∈ PromiseP encCNF ∧ gapSatExponent P0 = 0 :=
  ⟨GapKSAT_zero_mem_PromiseP rfl, gapSatExponent_zero_eq_zero rfl⟩

/-! ### 5. Rate inequalities, threshold invariance, hierarchy diamond, and native refutations -/

-- Complete exponent ordering for every clause width `k` and perfect-completeness soundness `s`:
-- `0 ≤ rGapSatExponent ≤ rSatExponent ≤ rpSatExponent ≤ satExponent ≤ sharpSatExponent ≤ 1`,
-- and `0 ≤ rGapSatExponent P ≤ gapSatExponent P ≤ 1` for every `P : GapKSATSpec`.
example (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ rGapSatExponent (GapKSATSpec.perfect k s hs0 hs1) ∧
    rGapSatExponent (GapKSATSpec.perfect k s hs0 hs1) ≤ rSatExponent k ∧
    rSatExponent k ≤ rpSatExponent k ∧
    rpSatExponent k ≤ satExponent k ∧
    satExponent k ≤ sharpSatExponent k ∧
    sharpSatExponent k ≤ 1 :=
  ⟨rGapSatExponent_nonneg _,
    rGapSatExponent_perfect_le_rSatExponent k hs0 hs1,
    rSatExponent_le_rpSatExponent k,
    rpSatExponent_le_satExponent k,
    satExponent_le_sharpSatExponent k,
    sharpSatExponent_le_one k⟩

example (P : GapKSATSpec) :
    0 ≤ rGapSatExponent P ∧ rGapSatExponent P ≤ gapSatExponent P ∧ gapSatExponent P ≤ 1 :=
  ⟨rGapSatExponent_nonneg P, rGapSatExponent_le_gapSatExponent P, gapSatExponent_le_one P⟩

-- Threshold invariance of `rSatExponent`, `rpSatExponent`, `rGapSatExponent`, and `rGapETH`.
example (k : ℕ) (P : GapKSATSpec) :
    rSatExponent k = sInf {δ | 0 ≤ δ ∧
      SolvesWithErrorInExpTime (.ofSet (KSAT k)) encCNF
        (ErrorModel.twoSided (1 / 10) (by norm_num) (by norm_num)) CNF.numVars δ} ∧
    rpSatExponent k = sInf {δ | 0 ≤ δ ∧
      SolvesWithErrorInExpTime (.ofSet (KSAT k)) encCNF
        (ErrorModel.oneSidedRP (9 / 10) (by norm_num) (by norm_num)) CNF.numVars δ} ∧
    rGapSatExponent P = sInf {δ | 0 ≤ δ ∧
      SolvesWithErrorInExpTime (GapKSAT P) encCNF
        (ErrorModel.twoSided (1 / 10) (by norm_num) (by norm_num)) CNF.numVars δ} :=
  ⟨rSatExponent_eq_sInf_twoSided k (by norm_num) (by norm_num),
    rpSatExponent_eq_sInf_oneSidedRP k (by norm_num) (by norm_num),
    rGapSatExponent_eq_sInf_twoSided P (by norm_num) (by norm_num)⟩

-- Single-machine quantifier characterizations and positive implication chains from `rGapETH`.
example :
    (rGapETH → GapETH) ∧
    (rGapETH → rETH) ∧
    (GapETH → ETH) ∧
    (rETH → ETH) ∧
    (rSETH → SETH) ∧
    (SETH → ETH) ∧
    (ETH → SharpETH) ∧
    (SETH → SharpSETH) ∧
    (ETH → SingleETH) ∧
    (SharpETH → SingleSharpETH) ∧
    (SingleETH → SingleSharpETH) ∧
    (rGapETH → SingleSharpETH) ∧
    (rSETH → SingleSharpETH) :=
  ⟨rGapETH.gapETH, rGapETH.rETH, GapETH.eth, rETH.eth, rSETH.seth, SETH.eth, ETH.sharpETH,
    SETH.sharpSETH, ETH.singleETH, SharpETH.singleSharpETH, SingleETH.singleSharpETH,
    fun h => h.gapETH.eth.singleETH.singleSharpETH,
    fun h => h.seth.eth.singleETH.singleSharpETH⟩

-- Positive-`δ` infima, finite-prefix `iSup` characterizations, and unrestricted vs. fixed-width
-- `SAT`.
example (k : ℕ) (P : GapKSATSpec) :
    satExponent k = sInf {δ | 0 < δ ∧ DecidableInExpTime (KSAT k) encCNF CNF.numVars δ} ∧
    sharpSatExponent k =
      sInf {δ | 0 < δ ∧ ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ} ∧
    rSatExponent k = sInf {δ | 0 < δ ∧
      SolvesWithErrorInExpTime (.ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars δ} ∧
    gapSatExponent P =
      sInf {δ | 0 < δ ∧ SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ} ∧
    (SETH ↔ (⨆ m : {m : ℕ // 3 ≤ m}, satExponent m.val) = 1) ∧
    (SharpSETH ↔ (⨆ m : {m : ℕ // 3 ≤ m}, sharpSatExponent m.val) = 1) ∧
    (rSETH ↔ (⨆ m : {m : ℕ // 3 ≤ m}, rSatExponent m.val) = 1) ∧
    (⨆ m : ℕ, satExponent m) ≤ unrestrictedSatExponent ∧
    (SETH → unrestrictedSatExponent = 1) :=
  ⟨satExponent_eq_sInf_pos k, sharpSatExponent_eq_sInf_pos k, rSatExponent_eq_sInf_pos k,
    gapSatExponent_eq_sInf_pos P, SETH_iff_iSup_ge_three_eq_one,
    SharpSETH_iff_iSup_ge_three_eq_one, rSETH_iff_iSup_ge_three_eq_one,
    iSup_satExponent_le_unrestrictedSatExponent, SETH.unrestrictedSatExponent_eq_one⟩

-- Effectively uniform rate-family converse (`DecidableInSingleSubexpTime.of_uniformFamily`):
-- a uniform family deciding `Set.univ : Set ℕ` (unary input `n`, parameter `μ n = n`) converts to
-- `DecidableInSingleSubexpTime` via the identity precision schedule `sched = id`.
example : DecidableInSingleSubexpTime (Set.univ : Set ℕ) encUnary id := by
  have hdec : ComputableInO (fun _ : PrecisionInput ℕ => true)
      (PrecisionInput.encoding encUnary) encBool
      (fun x => (PrecisionInput.encoding encUnary x).length)
      (fun x => (PrecisionInput.encoding encUnary x).length) := .const true
  refine DecidableInSingleSubexpTime.of_uniformFamily hdec (fun _ _ => by simp)
    (c := 2) (d := 1) (e := 1) (fun m a => ?_) ComputableInPolyTime.id'
    fun M => ⟨M, fun _ ha => ha⟩
  have hlen : (PrecisionInput.encoding encUnary { precision := m, input := a }).length =
      2 * m + a + 1 := by
    change (encPair encUnary encUnary (m, a)).length = 2 * m + a + 1
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hL : (encUnary a).length = a := by simp
  rw [hlen, hL]
  dsimp only [id]
  rw [pow_one, pow_one]
  have hX1 : (1 : ℝ) ≤ 2 ^ ((a : ℝ) / (m + 1)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hprod : ((m : ℝ) + 1) * ((a : ℝ) + 1) ≤
      ((m : ℝ) + 1) * (2 ^ ((a : ℝ) / (m + 1)) * ((a : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hX1) (by positivity)
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
  have hlin : ((2 * m + a + 1 : ℕ) : ℝ) ≤ 2 * (((m : ℝ) + 1) * ((a : ℝ) + 1)) + 2 := by
    push_cast
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  linarith

-- Clause-vs-variable counting sparsification equivalence for `SharpETH` and `SETH`-style limits.
example :
    (SharpETH ↔ ¬ComputableInSubexpTime (SharpKSAT 3) encCNF encNat List.length) ∧
    (SharpSETH ↔ Tendsto sharpSatExponent atTop (𝓝 1)) ∧
    (rSETH ↔ Tendsto rSatExponent atTop (𝓝 1)) :=
  ⟨SharpETH_iff_not_computableInSubexpTime_length, SharpSETH_iff_tendsto, rSETH_iff_tendsto⟩

-- Unconditional native single-machine bounds, zero exponents, and refuted hypotheses.
example (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ComputableInSingleSubexpTime (SharpDeclaredKSAT k) encDeclaredCNF encNat
      DeclaredCNF.numVars ∧
    ComputableInSingleSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars ∧
    DecidableInSingleSubexpTime (KSAT k) encCNF CNF.numVars ∧
    sharpSatExponent k = 0 ∧
    rpSatExponent k = 0 ∧
    rSatExponent k = 0 ∧
    gapSatExponent (GapKSATSpec.perfect k s hs0 hs1) = 0 ∧
    rGapSatExponent (GapKSATSpec.perfect k s hs0 hs1) = 0 ∧
    ¬SharpETH ∧ ¬SharpSETH ∧ ¬SingleETH ∧ ¬SingleSharpETH ∧
    ¬rETH ∧ ¬rSETH ∧ ¬GapETH ∧ ¬rGapETH :=
  ⟨computableInSingleSubexpTime_SharpDeclaredKSAT k,
    computableInSingleSubexpTime_SharpKSAT k,
    decidableInSingleSubexpTime_KSAT k,
    sharpSatExponent_eq_zero k,
    rpSatExponent_eq_zero k,
    rSatExponent_eq_zero k,
    gapSatExponent_perfect_eq_zero k hs0 hs1,
    rGapSatExponent_perfect_eq_zero k hs0 hs1,
    not_SharpETH, not_SharpSETH, not_SingleETH, not_SingleSharpETH,
    not_rETH, not_rSETH, not_GapETH, not_rGapETH⟩

end CslibFrontierTests.FineGrainedRates
