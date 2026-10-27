/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CountingSparsification
public import Complexity.Computability.Complexity.FineGrained.ThreeOccurrenceReduction
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingBounds

/-!
# Discharging `CountingTreeBound` for Counting Sparsification

We discharge the quantitative depth and leaf-count hypothesis `CountingSparsify.CountingTreeBound`
of `CountingSparsification` from the actual path budgets and binomial leaf-word bounds in
`CountingBounds` (Appendix A.2–A.3, Lemmas A.2–A.3, printed pp. 46–47 of [OpenAI2026ETH]).

Specifically, for any parameters `M, K, B : ℕ` with `2 ≤ M`, `1 ≤ K`, and `1 ≤ B` satisfying the
integer parameter budget
* `countingBStepCoeff K ≤ M`, and
* `B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M`
whenever `2 ≤ K`, `CountingSparsify.countingTreeBound_of_budget` proves
`CountingSparsify.CountingTreeBound M K B (countingDepthCoeff K M) hM hK`.

We then specialize the correctness and native `ComputableInO` transfer theorems of
`CountingSparsification` and `ThreeOccurrenceReduction` so that downstream clients need only supply
the integer parameter budget on `(M, K, B)` rather than an external `CountingTreeBound` witness.

## Main results

* `Cslib.Complexity.CountingSparsify.countingTreeBound_of_budget`: discharges `CountingTreeBound`
  with linear depth coefficient `countingDepthCoeff K M` from the integer parameter budget.
* `Cslib.Complexity.CountingSparsify.search_eq_ite_modelCount_of_budget`,
  `Cslib.Complexity.CountingSparsify.search_eq_modelCount_of_budget`: model-count correctness of
  `CountingSparsify.search` under the integer parameter budget.
* `Cslib.Complexity.CountingSparsify.exists_computableInO_search_of_budget`: native
  `ComputableInO ... T T` time-and-space transfer certificate for `CountingSparsify.search` under
  the integer parameter budget.
* `Cslib.Complexity.CountingSparsify.exists_computableInO_search_threeOccurrence_of_budget`:
  end-to-end counting-sparsification reduction from a dense occurrence-`≤ 3` model counter under
  the integer parameter budget.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Section 6.4 and
  Appendix A.2–A.3][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Cslib.Logic.PL.ClauseSet.Sparsification
open Turing.MultiTapeTM

namespace CountingSparsify

variable {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K)

include hM hK in
/-- **Discharging `CountingTreeBound` from the integer parameter budget.**
For `2 ≤ M`, `1 ≤ K`, and `1 ≤ B`, if `2 ≤ K` implies `countingBStepCoeff K ≤ M` and
`B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M`, then
`CountingTreeBound M K B (countingDepthCoeff K M) hM hK` holds (Appendix A.3, Lemma A.3, printed
p. 47 [OpenAI2026ETH]). -/
theorem countingTreeBound_of_budget (hM2 : 2 ≤ M) {B : ℕ} (hB : 1 ≤ B)
    (hbudget : 2 ≤ K → countingBStepCoeff K ≤ M ∧
      B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M) :
    CountingTreeBound M K B (countingDepthCoeff K M) hM hK := by
  intro ψ declared hsupport
  have hnt : ∀ C ∈ ψ.1.toClauseSet, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
    intro C' hC' l hl hneg
    obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
    exact ψ.2.nontautological C hC l (List.mem_toFinset.mp hl) (List.mem_toFinset.mp hneg)
  have hsup : ∀ C ∈ ψ.1.toClauseSet, ∀ l ∈ C, l.1 ∈ declared := by
    intro C' hC' l hl
    obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
    exact hsupport C hC l (List.mem_toFinset.mp hl)
  refine ⟨fun w hw => ?_, fun W hW => ?_⟩
  · exact CountingBranchingRule.IsLeafWord.length_le (R := rule hM hK) hM2 ψ.2.reduced
      hnt ψ.2.card_le declared hsup hw
  · exact CountingBranchingRule.card_le_two_pow_of_isLeafWord (R := rule hM hK) hM2
      ψ.2.reduced hnt ψ.2.card_le declared hsup hB hbudget W hW

include hM hK in
/-- **Model-count correctness of `search` under the integer parameter budget.**
If `g` computes `ψ.modelCount` on sparse formulas `ψ` of width at most `k`, then
`search M K k B g φ` returns `φ.modelCount` on formulas of width at most `k` and `0` otherwise. -/
theorem search_eq_ite_modelCount_of_budget (hM2 : 2 ≤ M) {k B : ℕ} (hkK : k ≤ K) (hB : 1 ≤ B)
    (hbudget : 2 ≤ K → countingBStepCoeff K ≤ M ∧
      B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M)
    {g : CNF ℕ → ℕ}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ = ψ.modelCount)
    (φ : CNF ℕ) :
    search M K k B g φ =
      if (φ.all fun c => decide (c.length ≤ k)) then φ.modelCount else 0 :=
  search_eq_ite_modelCount hM hK hM2 hkK (countingTreeBound_of_budget hM hK hM2 hB hbudget) hg φ

include hM hK in
/-- **Model-count correctness of `search` on width-`≤ k` formulas under the integer parameter
budget.** -/
theorem search_eq_modelCount_of_budget (hM2 : 2 ≤ M) {k B : ℕ} (hkK : k ≤ K) (hB : 1 ≤ B)
    (hbudget : 2 ≤ K → countingBStepCoeff K ≤ M ∧
      B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M)
    {g : CNF ℕ → ℕ}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ = ψ.modelCount)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    search M K k B g φ = φ.modelCount :=
  search_eq_modelCount hM hK hM2 hkK (countingTreeBound_of_budget hM hK hM2 hB hbudget) hg hφ

include hM hK in
/-- **Time and space of `search` under the integer parameter budget.**
Given a total leaf routine `g` with `hg : ComputableInO g encCNF encNat t t` satisfying the global
bound `ht` (`O(2 ^ (δ * ψ.length) * (|encCNF ψ| + 1) ^ e)`) for every `ψ : CNF ℕ` and bounded by
`2 ^ ψ.numVars` on sparse width-`≤ k` formulas, `search M K k B g` has a combined time-and-space
certificate `ComputableInO (search M K k B g) encCNF encNat T T` with fixed-parameter transfer
bound `T φ ≤ C₀ * (2 ^ ((1 / B + occBound K M * δ) * φ.numVars) * (|encCNF φ| + 1) ^ E) + C₀`. -/
theorem exists_computableInO_search_of_budget (hM2 : 2 ≤ M) {k B : ℕ} (hkK : k ≤ K) (hB : 1 ≤ B)
    (hbudget : 2 ≤ K → countingBStepCoeff K ≤ M ∧
      B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M)
    {g : CNF ℕ → ℕ} {t : CNF ℕ → ℕ} (hg : ComputableInO g encCNF encNat t t)
    (hg_le : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ ≤ 2 ^ ψ.numVars)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (t ψ : ℝ) ≤ c * (2 ^ (δ * ψ.length) * ((encCNF ψ).length + 1) ^ e) + c) :
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (search M K k B g) encCNF encNat T T ∧
      ∀ φ : CNF ℕ, (T φ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((1 / B + occBound K M * δ) * φ.numVars) *
          (((encCNF φ).length : ℝ) + 1) ^ E) + C₀ :=
  exists_computableInO_search hM hK hM2 hkK (countingTreeBound_of_budget hM hK hM2 hB hbudget)
    hg hg_le hδ ht

include hM hK in
/-- **End-to-end counting sparsification from a dense 3-occurrence model counter under the integer
parameter budget.**
Given `2 ≤ k ≤ K` and a total model counter `f : CNF ℕ → ℕ` that computes `χ.modelCount` on every
dense formula `χ` of width `≤ k` and variable occurrence `≤ 3` and has a combined time-and-space
certificate `ComputableInO f encCNF encNat tf tf` with global bound
`(tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * (|encCNF χ| + 1) ^ e) + c`, the search
`search M K k B (guardOccurrenceCounter k f)` computes `φ.modelCount` on every formula `φ` of width
`≤ k` and has a combined time-and-space certificate with fixed-parameter transfer bound
`O(2 ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) * (|encCNF φ| + 1) ^ E)`. -/
theorem exists_computableInO_search_threeOccurrence_of_budget
    (hM2 : 2 ≤ M) {k B : ℕ} (hk2 : 2 ≤ k) (hkK : k ≤ K) (hB : 1 ≤ B)
    (hbudget : 2 ≤ K → countingBStepCoeff K ≤ M ∧
      B * countingBStepCoeff K * Nat.clog 2 (4 * countingDepthCoeff K M * M) ≤ M)
    {f : CNF ℕ → ℕ} {tf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf tf)
    (hf_eq : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ, (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) →
      search M K k B (guardOccurrenceCounter k f) φ = φ.modelCount) ∧
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (search M K k B (guardOccurrenceCounter k f)) encCNF encNat T T ∧
      ∀ φ : CNF ℕ, (T φ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) *
          (((encCNF φ).length : ℝ) + 1) ^ E) + C₀ :=
  exists_computableInO_search_of_threeOccurrence_counter hM hK hM2 hk2 hkK
    (countingTreeBound_of_budget hM hK hM2 hB hbudget) hf hf_eq hδ ht

end CountingSparsify

end Cslib.Complexity
