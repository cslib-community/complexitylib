/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingSparsification
public import Complexity.Computability.Complexity.FineGrained.Reduction
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Counting
public import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
import Complexity.Logics.Propositional.CNF.ThreeOccurrence.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Bounded-occurrence reductions for fine-grained decision and model counting

Connects the occurrence-splitting compiler (`CNF.toThreeOccurrence`, `toThreeSATThree`,
[Papadimitriou, Proposition 9.3][Papadimitriou94]) with dense variable numbering
(`CNF.denseRelabel`), fine-grained exponential/subexponential reductions (`FineGrained/Reduction`),
and the depth-first counting-sparsification search (`CountingSparsify.search`,
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4 and Appendix A,
pp. 43–47).

## Main definitions

* `Cslib.Complexity.toThreeOccurrenceDense`: split variable occurrences via `CNF.toThreeOccurrence`
  and renumber the resulting copies densely onto `0, …, φ.vars.length - 1` via `CNF.denseRelabel`.
* `Cslib.Complexity.guardOccurrenceCounter`: guard a model counter `f : CNF ℕ → ℕ` by the
  clause-width check `∀ c ∈ ψ, c.length ≤ k` and precompose with `toThreeOccurrenceDense`.

## Main results

* `Cslib.Complexity.computableInPolyTime_toThreeOccurrenceDense`,
  `Cslib.Complexity.modelCount_toThreeOccurrenceDense`,
  `Cslib.Complexity.vars_toThreeOccurrenceDense_toFinset`,
  `Cslib.Complexity.width_toThreeOccurrenceDense`,
  `Cslib.Complexity.count_vars_toThreeOccurrenceDense_le`,
  `Cslib.Complexity.numVars_toThreeOccurrenceDense_le_mul_length`: `toThreeOccurrenceDense` runs in
  polynomial time, preserves `Satisfiable`, `modelCount`, and clause width `≤ k` (for `2 ≤ k`), and
  produces a dense formula on `Finset.range φ.vars.length` (`numVars ≤ k * φ.length`) in which
  every variable occurs at most three times.
* `Cslib.Complexity.DecidableInExpTime.threeSAT_length_of_threeSATThree_numVars`,
  `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_threeSATThree_numVars`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_threeSATThree_numVars`: fine-grained exponential
  and subexponential reductions from `ThreeSAT` to `ThreeSATThree` in both `CNF.numVars` and
  `List.length`.
* `Cslib.Complexity.exists_computableInO_guardOccurrenceCounter_of_promise`,
  `Cslib.Complexity.exists_computableInO_guardOccurrenceCounter`,
  `Cslib.Complexity.CountingSparsify.exists_computableInO_search_threeOccurrence_of_promise`,
  `Cslib.Complexity.CountingSparsify.exists_computableInO_search_of_threeOccurrence_counter`: a
  total model counter `f` running in time and space `O(2 ^ (δ * χ.numVars) * (|encCNF χ| + 1) ^ e)`
  (either globally or on dense width-`≤ k`, occurrence-`≤ 3` formulas) yields a clause-exponential
  leaf counter in time and space `O(2 ^ ((k * δ) * ψ.length) * (|encCNF ψ| + 1) ^ E)`, and hence
  (under `CountingTreeBound`, a library adaptation of Appendix A.2–A.3) a general width-`≤ k` model
  counter via `CountingSparsify.search` in time and space
  `O(2 ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) * (|encCNF φ| + 1) ^ E')`.

* `Cslib.Complexity.exists_computableInO_guardOccurrenceCounter_polySpace_of_promise`,
  `CountingSparsify.exists_computableInO_search_threeOccurrence_polySpace_of_promise`:
  the same guard, compiler, and search with separate leaf time and polynomial workspace promises,
  yielding a total machine with the same time envelope and independent polynomial workspace in the
  full input encoding. Parameters are fixed; no leaf counter or runtime parameter uniformity is
  supplied by these transfer results.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Proposition 9.3][Papadimitriou94]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 2 (pp. 7–14),
  Section 6.4 (pp. 43–44), and Appendix A (pp. 44–47).
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### 1. Dense occurrence-3 compiler (`toThreeOccurrenceDense`) -/

/-- Split literal occurrences via `CNF.toThreeOccurrence` and renumber the resulting `(ℕ × ℕ × ℕ)`
copy variables densely onto `0, …, φ.vars.length - 1` via `CNF.denseRelabel` (a library adaptation
combining [Papadimitriou, Proposition 9.3][Papadimitriou94] with first-occurrence dense variable
numbering). -/
def toThreeOccurrenceDense (φ : CNF ℕ) : CNF ℕ :=
  φ.toThreeOccurrence.denseRelabel

/-- `toThreeOccurrenceDense` preserves satisfiability. -/
@[simp]
theorem satisfiable_toThreeOccurrenceDense (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).Satisfiable ↔ φ.Satisfiable := by
  rw [toThreeOccurrenceDense, CNF.satisfiable_denseRelabel, CNF.satisfiable_toThreeOccurrence]

/-- `toThreeOccurrenceDense` preserves the occurring-variable model count. -/
@[simp]
theorem modelCount_toThreeOccurrenceDense (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).modelCount = φ.modelCount := by
  rw [toThreeOccurrenceDense, CNF.modelCount_denseRelabel, CNF.modelCount_toThreeOccurrence]

/-- The number of distinct occurring variables of `toThreeOccurrenceDense φ` equals the number of
literal occurrences `φ.vars.length` of `φ`. -/
@[simp]
theorem numVars_toThreeOccurrenceDense (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).numVars = φ.vars.length := by
  rw [toThreeOccurrenceDense, CNF.numVars_denseRelabel, CNF.numVars_toThreeOccurrence]

/-- The occurring variables of `toThreeOccurrenceDense φ` are `Finset.range φ.vars.length`. -/
@[simp]
theorem vars_toThreeOccurrenceDense_toFinset (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).vars.toFinset = Finset.range φ.vars.length := by
  rw [toThreeOccurrenceDense, CNF.vars_denseRelabel_toFinset, CNF.numVars_toThreeOccurrence]

/-- The occurring variables of `toThreeOccurrenceDense φ` are `Finset.range` of its own
`numVars`. -/
theorem vars_toThreeOccurrenceDense_eq_range_numVars (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).vars.toFinset =
      Finset.range (toThreeOccurrenceDense φ).numVars := by
  rw [vars_toThreeOccurrenceDense_toFinset, numVars_toThreeOccurrenceDense]

/-- The declared-variable model count of `toThreeOccurrenceDense φ` on
`Finset.range (toThreeOccurrenceDense φ).numVars` equals `φ.modelCount`. -/
theorem modelCountOn_toThreeOccurrenceDense (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).modelCountOn (Finset.range (toThreeOccurrenceDense φ).numVars) =
      φ.modelCount := by
  rw [toThreeOccurrenceDense, CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel,
    CNF.modelCount_toThreeOccurrence]

/-- `toThreeOccurrenceDense φ` has `φ.length + φ.vars.length` clauses. -/
@[simp]
theorem length_toThreeOccurrenceDense (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).length = φ.length + φ.vars.length := by
  rw [toThreeOccurrenceDense, CNF.length_denseRelabel, CNF.length_toThreeOccurrence]

/-- `toThreeOccurrenceDense φ` has `3 * φ.vars.length` total literal occurrences. -/
@[simp]
theorem length_vars_toThreeOccurrenceDense (φ : CNF ℕ) :
    (toThreeOccurrenceDense φ).vars.length = 3 * φ.vars.length := by
  rw [toThreeOccurrenceDense, CNF.denseRelabel, CNF.vars_relabel, List.length_map,
    CNF.length_vars_toThreeOccurrence]

/-- For `2 ≤ k`, `toThreeOccurrenceDense` preserves clause width `≤ k`. -/
theorem width_toThreeOccurrenceDense {k : ℕ} (hk : 2 ≤ k) {φ : CNF ℕ}
    (hφ : ∀ c ∈ φ, c.length ≤ k) :
    ∀ c ∈ toThreeOccurrenceDense φ, c.length ≤ k :=
  (CNF.all_length_le_denseRelabel φ.toThreeOccurrence).mpr (CNF.width_toThreeOccurrence hk hφ)

/-- Every variable occurs at most three times in `toThreeOccurrenceDense φ`. -/
theorem count_vars_toThreeOccurrenceDense_le (φ : CNF ℕ) (v : ℕ) :
    (toThreeOccurrenceDense φ).vars.count v ≤ 3 :=
  CNF.count_vars_denseRelabel_le φ.toThreeOccurrence
    (CNF.count_vars_toThreeOccurrence_le φ) v

/-- On a formula `φ` of clause width at most `k`, `toThreeOccurrenceDense φ` has at most
`k * φ.length` distinct variables. -/
theorem numVars_toThreeOccurrenceDense_le_mul_length {k : ℕ} {φ : CNF ℕ}
    (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toThreeOccurrenceDense φ).numVars ≤ k * φ.length := by
  rw [numVars_toThreeOccurrenceDense]
  exact CNF.length_vars_le_mul_length hφ

/-- On a formula `φ` of clause width at most `k`, `toThreeOccurrenceDense φ` has at most
`(k + 1) * φ.length` clauses. -/
theorem length_toThreeOccurrenceDense_le_mul_length {k : ℕ} {φ : CNF ℕ}
    (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toThreeOccurrenceDense φ).length ≤ (k + 1) * φ.length := by
  rw [length_toThreeOccurrenceDense]
  have hvars := CNF.length_vars_le_mul_length hφ
  calc φ.length + φ.vars.length
      ≤ φ.length + k * φ.length := Nat.add_le_add_left hvars _
    _ = (k + 1) * φ.length := by ring

/-- `toThreeOccurrenceDense` is computable in polynomial time under `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_toThreeOccurrenceDense :
    ComputableInPolyTime toThreeOccurrenceDense encCNF encCNF :=
  (CNF.computableInPolyTime_denseRelabel (encPair encNat (encPair encUnary encUnary))).comp
    (CNF.computableInPolyTime_toThreeOccurrence encNat)

/-! ### 2. Fine-grained `ThreeSATThree` reductions and `ETH` consequences -/

/-- For every `φ : CNF ℕ`, `toThreeSATThree φ` has at most `3 * φ.length` distinct variables. -/
theorem numVars_toThreeSATThree_le_mul_length (φ : CNF ℕ) :
    (toThreeSATThree φ).numVars ≤ 3 * φ.length := by
  unfold toThreeSATThree
  split_ifs with hw
  · have hw' : ∀ c ∈ φ, c.length ≤ 3 := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hw
    rw [CNF.numVars_relabel ThreeSATThree.numberCopy_injective, CNF.numVars_toThreeOccurrence]
    exact CNF.length_vars_le_mul_length hw'
  · simp [CNF.numVars, CNF.vars]

/-- For every `φ : CNF ℕ`, `toThreeSATThree φ` has at most `4 * φ.length + 1` clauses. -/
theorem length_toThreeSATThree_le_mul_length (φ : CNF ℕ) :
    (toThreeSATThree φ).length ≤ 4 * φ.length + 1 := by
  by_cases hw : ∀ c ∈ φ, c.length ≤ 3
  · rw [length_toThreeSATThree φ hw]
    have hvars := CNF.length_vars_le_mul_length hw
    omega
  · have hg : φ.all (fun c => decide (c.length ≤ 3)) = false := by simpa using hw
    simp only [toThreeSATThree, hg, Bool.false_eq_true, ite_false, List.length_singleton]
    omega

/-- **Exponential-time reduction from `ThreeSAT` (`KSAT 3`) in clauses to `ThreeSATThree` in
variables.** Deciding `ThreeSATThree` in time `O(2 ^ (δ * numVars) * poly)` decides `ThreeSAT` in
time `O(2 ^ ((3 * δ) * length) * poly)`. -/
theorem DecidableInExpTime.threeSAT_length_of_threeSATThree_numVars {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime ThreeSATThree encCNF CNF.numVars δ) :
    DecidableInExpTime ThreeSAT encCNF List.length (3 * δ) :=
  DecidableInExpTime.of_reduction computableInPolyTime_toThreeSATThree
    (fun φ => (mem_ThreeSATThree_toThreeSATThree_iff φ).symm)
    (c := 3) (fun φ => (numVars_toThreeSATThree_le_mul_length φ).trans (Nat.le_add_right _ 3)) hδ h

/-- **Exponential-time reduction from `ThreeSAT` (`KSAT 3`) in clauses to `ThreeSATThree` in
clauses.** Deciding `ThreeSATThree` in time `O(2 ^ (δ * length) * poly)` decides `ThreeSAT` in
time `O(2 ^ ((4 * δ) * length) * poly)`. -/
theorem DecidableInExpTime.threeSAT_length_of_threeSATThree_length {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime ThreeSATThree encCNF List.length δ) :
    DecidableInExpTime ThreeSAT encCNF List.length (4 * δ) :=
  DecidableInExpTime.of_reduction computableInPolyTime_toThreeSATThree
    (fun φ => (mem_ThreeSATThree_toThreeSATThree_iff φ).symm)
    (c := 4) (fun φ => (length_toThreeSATThree_le_mul_length φ).trans (by omega)) hδ h

/-- **Subexponential-time reduction from `ThreeSAT` (`KSAT 3`) to `ThreeSATThree` in variables.**
If `ThreeSATThree` is decidable in subexponential time in `CNF.numVars`, then `ThreeSAT` is
decidable in subexponential time in `CNF.numVars` (via the Sparsification Lemma). -/
theorem DecidableInSubexpTime.threeSAT_of_threeSATThree_numVars
    (h : DecidableInSubexpTime ThreeSATThree encCNF CNF.numVars) :
    DecidableInSubexpTime ThreeSAT encCNF CNF.numVars := by
  rw [← KSAT_three]
  refine DecidableInSubexpTime.numVars_of_length ?_
  rw [KSAT_three]
  exact DecidableInSubexpTime.of_reduction computableInPolyTime_toThreeSATThree
    (fun φ => (mem_ThreeSATThree_toThreeSATThree_iff φ).symm)
    (c := 3) (fun φ => (numVars_toThreeSATThree_le_mul_length φ).trans (Nat.le_add_right _ 3)) h

/-- **Subexponential-time reduction from `ThreeSAT` (`KSAT 3`) to `ThreeSATThree` in clauses.** -/
theorem DecidableInSubexpTime.threeSAT_of_threeSATThree_length
    (h : DecidableInSubexpTime ThreeSATThree encCNF List.length) :
    DecidableInSubexpTime ThreeSAT encCNF CNF.numVars := by
  rw [← KSAT_three]
  refine DecidableInSubexpTime.numVars_of_length ?_
  rw [KSAT_three]
  exact DecidableInSubexpTime.of_reduction computableInPolyTime_toThreeSATThree
    (fun φ => (mem_ThreeSATThree_toThreeSATThree_iff φ).symm)
    (c := 4) (fun φ => (length_toThreeSATThree_le_mul_length φ).trans (by omega)) h

/-- **Under `ETH`, `ThreeSATThree` is not decidable in subexponential time in the number of
variables.** -/
theorem ETH.not_decidableInSubexpTime_threeSATThree_numVars (h : ETH) :
    ¬ DecidableInSubexpTime ThreeSATThree encCNF CNF.numVars :=
  fun h' => ETH_iff_not_decidableInSubexpTime.mp h h'.threeSAT_of_threeSATThree_numVars

/-- **Under `ETH`, `ThreeSATThree` is not decidable in subexponential time in the number of
clauses.** -/
theorem ETH.not_decidableInSubexpTime_threeSATThree_length (h : ETH) :
    ¬ DecidableInSubexpTime ThreeSATThree encCNF List.length :=
  fun h' => ETH_iff_not_decidableInSubexpTime.mp h h'.threeSAT_of_threeSATThree_length

/-- Deciding `ThreeSATThree` in subexponential time in `CNF.numVars` refutes `ETH`. -/
theorem not_ETH_of_decidableInSubexpTime_threeSATThree_numVars
    (h : DecidableInSubexpTime ThreeSATThree encCNF CNF.numVars) : ¬ ETH :=
  fun heth => heth.not_decidableInSubexpTime_threeSATThree_numVars h

/-- Deciding `ThreeSATThree` in subexponential time in `List.length` refutes `ETH`. -/
theorem not_ETH_of_decidableInSubexpTime_threeSATThree_length
    (h : DecidableInSubexpTime ThreeSATThree encCNF List.length) : ¬ ETH :=
  fun heth => heth.not_decidableInSubexpTime_threeSATThree_length h

/-! ### 3. Guarded leaf model-counter reduction for `CountingSparsify.search` -/

/-- Guard a model counter `f : CNF ℕ → ℕ` by the clause-width check `∀ c ∈ ψ, c.length ≤ k` and
apply `f` to the dense 3-occurrence formula `toThreeOccurrenceDense ψ`. -/
def guardOccurrenceCounter (k : ℕ) (f : CNF ℕ → ℕ) (ψ : CNF ℕ) : ℕ :=
  if ψ.all fun c => decide (c.length ≤ k) then f (toThreeOccurrenceDense ψ) else 0

/-- If `f` computes `χ.modelCount` on every dense formula `χ : CNF ℕ` of width `≤ k` (`2 ≤ k`) and
at most `3` occurrences per variable (`∀ v, χ.vars.count v ≤ 3` and
`χ.vars.toFinset = Finset.range χ.numVars`), then `guardOccurrenceCounter k f ψ = ψ.modelCount` on
every formula `ψ : CNF ℕ` of width `≤ k` (and `0` otherwise). -/
theorem guardOccurrenceCounter_eq_ite_modelCount {k : ℕ} (hk : 2 ≤ k) {f : CNF ℕ → ℕ}
    (hf : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    (ψ : CNF ℕ) :
    guardOccurrenceCounter k f ψ =
      if (ψ.all fun c => decide (c.length ≤ k)) then ψ.modelCount else 0 := by
  unfold guardOccurrenceCounter
  split_ifs with hψ
  · have hψ' : ∀ c ∈ ψ, c.length ≤ k := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hψ
    rw [hf (toThreeOccurrenceDense ψ) (width_toThreeOccurrenceDense hk hψ')
      (count_vars_toThreeOccurrenceDense_le ψ) (vars_toThreeOccurrenceDense_eq_range_numVars ψ),
      modelCount_toThreeOccurrenceDense]
  · rfl

/-- On formulas `ψ` of width `≤ k` (`2 ≤ k`), `guardOccurrenceCounter k f ψ = ψ.modelCount`
whenever `f` counts dense width-`≤ k`, occurrence-`≤ 3` formulas. -/
theorem guardOccurrenceCounter_eq_modelCount {k : ℕ} (hk : 2 ≤ k) {f : CNF ℕ → ℕ}
    (hf : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {ψ : CNF ℕ} (hψ : ∀ c ∈ ψ, c.length ≤ k) :
    guardOccurrenceCounter k f ψ = ψ.modelCount := by
  have hg : (ψ.all fun c => decide (c.length ≤ k)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hψ
  simp only [guardOccurrenceCounter_eq_ite_modelCount hk hf ψ, hg, ↓reduceIte]

/-- When `f` counts dense width-`≤ k`, occurrence-`≤ 3` formulas (`2 ≤ k`),
`guardOccurrenceCounter k f ψ ≤ 2 ^ ψ.numVars` for all `ψ : CNF ℕ`. -/
theorem guardOccurrenceCounter_le_two_pow_numVars {k : ℕ} (hk : 2 ≤ k) {f : CNF ℕ → ℕ}
    (hf : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    (ψ : CNF ℕ) :
    guardOccurrenceCounter k f ψ ≤ 2 ^ ψ.numVars := by
  rw [guardOccurrenceCounter_eq_ite_modelCount hk hf ψ]
  split_ifs
  · exact CountingSparsify.modelCount_le_two_pow_numVars ψ
  · exact Nat.zero_le _

/-- When `f` counts dense width-`≤ k`, occurrence-`≤ 3` formulas (`2 ≤ k`),
`0 < guardOccurrenceCounter k f ψ` holds if and only if `ψ ∈ KSAT k`. -/
theorem guardOccurrenceCounter_pos_iff_mem_kSAT {k : ℕ} (hk : 2 ≤ k) {f : CNF ℕ → ℕ}
    (hf : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    (ψ : CNF ℕ) :
    0 < guardOccurrenceCounter k f ψ ↔ ψ ∈ KSAT k := by
  rw [guardOccurrenceCounter_eq_ite_modelCount hk hf ψ]
  by_cases hψ : (ψ.all fun c => decide (c.length ≤ k)) = true
  · have hψ' : ∀ c ∈ ψ, c.length ≤ k := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hψ
    simp only [hψ, ↓reduceIte, CNF.modelCount_pos_iff, KSAT, Set.mem_ofPred_eq]
    exact ⟨fun hs => ⟨hψ', hs⟩, fun h => h.2⟩
  · have hψ' : ¬ ∀ c ∈ ψ, c.length ≤ k := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hψ
    simp only [hψ, Bool.false_eq_true, ite_false, lt_irrefl, KSAT, Set.mem_ofPred_eq, hψ',
      false_and]

private theorem exists_computableInO_guardOccurrenceCounter_resources (k : ℕ)
    {f : CNF ℕ → ℕ} {tf sf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf sf) :
    ∃ d l : ℕ, (∀ ψ : CNF ℕ, (encCNF (toThreeOccurrenceDense ψ)).length ≤
      l * (((encCNF ψ).length + 1) ^ d + 1)) ∧
      ComputableInO (guardOccurrenceCounter k f) encCNF encNat
      (fun ψ => ((encCNF ψ).length + 1) ^ d +
        if (ψ.all fun c => decide (c.length ≤ k)) then
          ((encCNF ψ).length + 1) ^ d + tf (toThreeOccurrenceDense ψ)
        else ((encCNF ψ).length + 1) ^ d)
      (fun ψ => ((encCNF ψ).length + 1) ^ d +
        if (ψ.all fun c => decide (c.length ≤ k)) then
          ((encCNF ψ).length + 1) ^ d + sf (toThreeOccurrenceDense ψ)
        else ((encCNF ψ).length + 1) ^ d) := by
  obtain ⟨dc, ec, hc⟩ := (computableInPolyTime_all_length_le k).exists_degree
  obtain ⟨dr, er, hr⟩ := computableInPolyTime_toThreeOccurrenceDense.exists_degree
  obtain ⟨dz, ez, hz⟩ :=
    (show ComputableInPolyTime (fun _ : CNF ℕ => (0 : ℕ)) encCNF encNat
      by fun_prop).exists_degree
  set d := dc + dr + dz + 1
  have hcO := (hc.mono (d' := d) (e' := ec) (by omega) le_rfl).inO
  have hrO := (hr.mono (d' := d) (e' := er) (by omega) le_rfl).inO
  have hzO := (hz.mono (d' := d) (e' := ez) (by omega) le_rfl).inO
  obtain ⟨l, hl⟩ := hrO.length_le
  exact ⟨d, l, hl, hcO.ite (hf.comp hrO) hzO⟩

private theorem guardOccurrenceCounter_time_bound (k d l : ℕ) {tf : CNF ℕ → ℕ}
    (hl : ∀ ψ : CNF ℕ, (encCNF (toThreeOccurrenceDense ψ)).length ≤
      l * (((encCNF ψ).length + 1) ^ d + 1))
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (∀ d ∈ ψ, d.length ≤ k) →
      (tf (toThreeOccurrenceDense ψ) : ℝ) ≤
        c * (2 ^ (δ * (toThreeOccurrenceDense ψ).numVars) *
          ((encCNF (toThreeOccurrenceDense ψ)).length + 1) ^ e) + c) :
    ∃ C₀ E : ℕ, ∀ ψ : CNF ℕ,
      ((((encCNF ψ).length + 1) ^ d +
        if (ψ.all fun c => decide (c.length ≤ k)) then
          ((encCNF ψ).length + 1) ^ d + tf (toThreeOccurrenceDense ψ)
        else ((encCNF ψ).length + 1) ^ d : ℕ) : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((k * δ) * ψ.length) * (((encCNF ψ).length : ℝ) + 1) ^ E) + C₀ := by
  set E := d * e + d
  set K : ℝ := 2 + c * (2 * l + 1) ^ e + c
  refine ⟨⌈K⌉₊, E, fun ψ => ?_⟩
  set P : ℝ := (((encCNF ψ).length : ℝ) + 1) ^ d
  set Q : ℝ := (((encCNF ψ).length : ℝ) + 1) ^ E
  set X : ℝ := (2 : ℝ) ^ ((k * δ) * ψ.length)
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith [(Nat.cast_nonneg (encCNF ψ).length : (0 : ℝ) ≤ _)])
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by linarith [(Nat.cast_nonneg (encCNF ψ).length : (0 : ℝ) ≤ _)])
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hPQ : P ≤ Q := by
    refine pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg (encCNF ψ).length : (0 : ℝ) ≤ _)]) ?_
    omega
  have hPeQ : P ^ e ≤ Q := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg (encCNF ψ).length : (0 : ℝ) ≤ _)]) ?_
    omega
  have hQXQ : Q ≤ X * Q := le_mul_of_one_le_left (by positivity) hX1
  have hPXQ : P ≤ X * Q := hPQ.trans hQXQ
  have hPeXQ : P ^ e ≤ X * Q := hPeQ.trans hQXQ
  have h1XQ : (1 : ℝ) ≤ X * Q := one_le_mul_of_one_le_of_one_le hX1 hQ1
  split_ifs with hψ
  · have hψ' : ∀ c ∈ ψ, c.length ≤ k := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hψ
    have hnv : (toThreeOccurrenceDense ψ).numVars ≤ k * ψ.length :=
      numVars_toThreeOccurrenceDense_le_mul_length hψ'
    have hexp : (2 : ℝ) ^ (δ * (toThreeOccurrenceDense ψ).numVars) ≤ X := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hnvR : ((toThreeOccurrenceDense ψ).numVars : ℝ) ≤ (k : ℝ) * ψ.length := by
        exact_mod_cast hnv
      have hmul := mul_le_mul_of_nonneg_left hnvR hδ
      linarith
    have hlen : ((encCNF (toThreeOccurrenceDense ψ)).length : ℝ) + 1 ≤ (2 * l + 1) * P := by
      have hl' : ((encCNF (toThreeOccurrenceDense ψ)).length : ℝ) ≤ l * (P + 1) := by
        have := hl ψ
        simp only [P]
        exact_mod_cast this
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      nlinarith
    have hpow : (((encCNF (toThreeOccurrenceDense ψ)).length : ℝ) + 1) ^ e ≤
        (2 * l + 1) ^ e * P ^ e := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hlen e
    have htf : (tf (toThreeOccurrenceDense ψ) : ℝ) ≤
        c * (2 * l + 1) ^ e * X * Q + c * (X * Q) := by
      have htψ := ht ψ hψ'
      have hprod := mul_le_mul hexp hpow (by positivity) (by positivity)
      have hprod' : (2 : ℝ) ^ (δ * (toThreeOccurrenceDense ψ).numVars) *
          (((encCNF (toThreeOccurrenceDense ψ)).length : ℝ) + 1) ^ e ≤
          (2 * l + 1) ^ e * (X * Q) := by
        have hPeX : X * ((2 * l + 1) ^ e * P ^ e) ≤ (2 * l + 1) ^ e * (X * Q) := by
          have := mul_le_mul_of_nonneg_left hPeQ (by positivity : (0 : ℝ) ≤ (2 * l + 1) ^ e * X)
          linarith
        exact hprod.trans hPeX
      have hcprod := mul_le_mul_of_nonneg_left hprod' (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
      have hc1 := mul_le_mul_of_nonneg_left h1XQ (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
      linarith
    have hsum : P + (P + (tf (toThreeOccurrenceDense ψ) : ℝ)) ≤ K * (X * Q) := by
      simp only [K]
      linarith
    have hceil : K * (X * Q) ≤ ⌈K⌉₊ * (X * Q) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity)
    have hC0 : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
    push_cast [P] at hsum ⊢
    linarith
  · have hsum : P + P ≤ K * (X * Q) := by
      have hc0 : (0 : ℝ) ≤ c * (2 * l + 1) ^ e + c := by positivity
      have := mul_le_mul_of_nonneg_right hc0 (by positivity : (0 : ℝ) ≤ X * Q)
      simp only [K]
      linarith
    have hceil : K * (X * Q) ≤ ⌈K⌉₊ * (X * Q) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity)
    have hC0 : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
    push_cast [P] at hsum ⊢
    linarith

private theorem exists_computableInO_guardOccurrenceCounter_aux (k : ℕ)
    {f : CNF ℕ → ℕ} {tf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf tf)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (∀ d ∈ ψ, d.length ≤ k) →
      (tf (toThreeOccurrenceDense ψ) : ℝ) ≤
        c * (2 ^ (δ * (toThreeOccurrenceDense ψ).numVars) *
          ((encCNF (toThreeOccurrenceDense ψ)).length + 1) ^ e) + c) :
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (guardOccurrenceCounter k f) encCNF encNat T T ∧
      ∀ ψ : CNF ℕ, (T ψ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((k * δ) * ψ.length) * (((encCNF ψ).length : ℝ) + 1) ^ E) + C₀ := by
  obtain ⟨d, l, hl, h⟩ := exists_computableInO_guardOccurrenceCounter_resources k hf
  obtain ⟨C₀, E, hT⟩ := guardOccurrenceCounter_time_bound k d l hl hδ ht
  exact ⟨_, C₀, E, h, hT⟩

/-- **From variable-exponential occurrence-3 counting to clause-exponential leaf counting (promised
runtime).**
If `2 ≤ k` and `f : CNF ℕ → ℕ` has a combined time-and-space certificate
`ComputableInO f encCNF encNat tf tf` whose time and space `tf χ` satisfy
`(tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * (|encCNF χ| + 1) ^ e) + c` on every dense formula `χ` of
width `≤ k` and variable occurrence `≤ 3`, then `guardOccurrenceCounter k f` has a combined
time-and-space certificate `ComputableInO (guardOccurrenceCounter k f) encCNF encNat T T` with
`(T ψ : ℝ) ≤ C₀ * (2 ^ ((k * δ) * ψ.length) * (|encCNF ψ| + 1) ^ E) + C₀` for all `ψ : CNF ℕ`. -/
theorem exists_computableInO_guardOccurrenceCounter_of_promise {k : ℕ} (hk : 2 ≤ k)
    {f : CNF ℕ → ℕ} {tf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf tf)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ, (∀ d ∈ χ, d.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars →
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (guardOccurrenceCounter k f) encCNF encNat T T ∧
      ∀ ψ : CNF ℕ, (T ψ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((k * δ) * ψ.length) * (((encCNF ψ).length : ℝ) + 1) ^ E) + C₀ :=
  exists_computableInO_guardOccurrenceCounter_aux k hf hδ fun ψ hψ =>
    ht (toThreeOccurrenceDense ψ) (width_toThreeOccurrenceDense hk hψ)
      (count_vars_toThreeOccurrenceDense_le ψ) (vars_toThreeOccurrenceDense_eq_range_numVars ψ)

/-- **From variable-exponential occurrence-3 counting to clause-exponential leaf counting.**
If `f : CNF ℕ → ℕ` has a combined time-and-space certificate `ComputableInO f encCNF encNat tf tf`
with `(tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * (|encCNF χ| + 1) ^ e) + c` for all `χ : CNF ℕ`, then
`guardOccurrenceCounter k f` has a combined time-and-space certificate
`ComputableInO (guardOccurrenceCounter k f) encCNF encNat T T` with
`(T ψ : ℝ) ≤ C₀ * (2 ^ ((k * δ) * ψ.length) * (|encCNF ψ| + 1) ^ E) + C₀` for all `ψ : CNF ℕ`. -/
theorem exists_computableInO_guardOccurrenceCounter (k : ℕ) {f : CNF ℕ → ℕ} {tf : CNF ℕ → ℕ}
    (hf : ComputableInO f encCNF encNat tf tf) {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ, (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (guardOccurrenceCounter k f) encCNF encNat T T ∧
      ∀ ψ : CNF ℕ, (T ψ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((k * δ) * ψ.length) * (((encCNF ψ).length : ℝ) + 1) ^ E) + C₀ :=
  exists_computableInO_guardOccurrenceCounter_aux k hf hδ fun ψ _ => ht (toThreeOccurrenceDense ψ)

/-- The existing width guard and dense occurrence-3 compiler preserve independent polynomial
workspace. `hf` is one total machine; `ht` and `hs` need hold only on the dense width-`≤ k`,
occurrence-`≤ 3` promise. The result is total, including the zero output on rejected widths.
The compiler output, its retained input, and the leaf output are charged by the native composition
rules. All parameters and polynomial constants are fixed before choosing the resulting machine. -/
theorem exists_computableInO_guardOccurrenceCounter_polySpace_of_promise {k : ℕ} (hk : 2 ≤ k)
    {f : CNF ℕ → ℕ} {tf sf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf sf)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e a b : ℕ}
    (ht : ∀ χ : CNF ℕ, (∀ d ∈ χ, d.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars →
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c)
    (hs : ∀ χ : CNF ℕ, (∀ d ∈ χ, d.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → sf χ ≤ a * ((encCNF χ).length + 1) ^ b) :
    ∃ T S : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (guardOccurrenceCounter k f) encCNF encNat T S ∧
      PolyBounded (fun ψ : CNF ℕ => (encCNF ψ).length) S ∧
      ∀ ψ : CNF ℕ, (T ψ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((k * δ) * ψ.length) * (((encCNF ψ).length : ℝ) + 1) ^ E) + C₀ := by
  obtain ⟨d, l, hl, h⟩ := exists_computableInO_guardOccurrenceCounter_resources k hf
  obtain ⟨C₀, E, hT⟩ := guardOccurrenceCounter_time_bound k d l hl hδ fun ψ hψ =>
    ht (toThreeOccurrenceDense ψ) (width_toThreeOccurrenceDense hk hψ)
      (count_vars_toThreeOccurrenceDense_le ψ) (vars_toThreeOccurrenceDense_eq_range_numVars ψ)
  refine ⟨_, _, C₀, E, h, ?_, hT⟩
  refine ⟨fun n => 2 * (n + 1) ^ d + a * (l * ((n + 1) ^ d + 1) + 1) ^ b,
    by fun_prop, fun ψ => ?_⟩
  dsimp only
  split_ifs with hψ
  · have hwidth : ∀ c ∈ ψ, c.length ≤ k := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hψ
    have hsψ := hs (toThreeOccurrenceDense ψ) (width_toThreeOccurrenceDense hk hwidth)
      (count_vars_toThreeOccurrenceDense_le ψ) (vars_toThreeOccurrenceDense_eq_range_numVars ψ)
    have hpow := Nat.mul_le_mul_left a
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hl ψ) 1) b)
    omega
  · omega

namespace CountingSparsify

variable {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K)

include hM hK in
/-- **Counting sparsification from a dense 3-occurrence model counter (promised runtime).**
Under `CountingTreeBound`, given `2 ≤ k ≤ K` and a total model counter `f : CNF ℕ → ℕ` with a
combined time-and-space certificate `ComputableInO f encCNF encNat tf tf` that on every dense
formula `χ` of width `≤ k` and variable occurrence `≤ 3` computes `χ.modelCount` and satisfies
`(tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * (|encCNF χ| + 1) ^ e) + c`, the search
`search M K k B (guardOccurrenceCounter k f)` computes `φ.modelCount` on every formula `φ` of width
`≤ k` and has a combined time-and-space certificate with fixed-parameter transfer bound
`O(2 ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) * (|encCNF φ| + 1) ^ E)`. -/
theorem exists_computableInO_search_threeOccurrence_of_promise
    (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hk2 : 2 ≤ k) (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK)
    {f : CNF ℕ → ℕ} {tf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf tf)
    (hf_eq : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars →
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) →
      search M K k B (guardOccurrenceCounter k f) φ = φ.modelCount) ∧
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (search M K k B (guardOccurrenceCounter k f)) encCNF encNat T T ∧
      ∀ φ : CNF ℕ, (T φ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) *
          (((encCNF φ).length : ℝ) + 1) ^ E) + C₀ := by
  refine ⟨fun φ hφ => search_eq_modelCount hM hK hM2 hkK hTB
    (fun ψ hψ _ => guardOccurrenceCounter_eq_modelCount hk2 hf_eq hψ) hφ, ?_⟩
  obtain ⟨Tg, Cg, Eg, hgO, hgt⟩ :=
    exists_computableInO_guardOccurrenceCounter_of_promise hk2 hf hδ ht
  exact exists_computableInO_search hM hK hM2 hkK hTB hgO
    (fun ψ _ _ => guardOccurrenceCounter_le_two_pow_numVars hk2 hf_eq ψ)
    (by positivity) hgt

include hM hK in
/-- **Counting sparsification from a dense 3-occurrence model counter.**
Under `CountingTreeBound`, given `2 ≤ k ≤ K` and a total model counter `f : CNF ℕ → ℕ` that
computes `χ.modelCount` on every dense formula `χ` of width `≤ k` and variable occurrence `≤ 3` and
has a combined time-and-space certificate `ComputableInO f encCNF encNat tf tf` with global bound
`(tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * (|encCNF χ| + 1) ^ e) + c`, the search
`search M K k B (guardOccurrenceCounter k f)` computes `φ.modelCount` on every formula `φ` of width
`≤ k` and has a combined time-and-space certificate with fixed-parameter transfer bound
`O(2 ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) * (|encCNF φ| + 1) ^ E)`. -/
theorem exists_computableInO_search_of_threeOccurrence_counter (hM2 : 2 ≤ M) {k B L_coeff : ℕ}
    (hk2 : 2 ≤ k) (hkK : k ≤ K) (hTB : CountingTreeBound M K B L_coeff hM hK)
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
  exists_computableInO_search_threeOccurrence_of_promise hM hK hM2 hk2 hkK hTB hf hf_eq
    hδ fun χ _ _ _ => ht χ

include hM hK in
/-- Counting sparsification with independent polynomial workspace from one total dense
occurrence-3 counter whose correctness, time, and space guarantees are promised only on dense
width-`≤ k`, occurrence-`≤ 3` formulas. The unchanged search returns the model count on width
`≤ k` inputs and zero otherwise, in the original exponential time envelope and polynomial space
in the full input encoding. `M`, `K`, `k`, `B`, and `L_coeff` are fixed parameters; this does not
supply a counter or establish uniformity for runtime parameter choices. -/
theorem exists_computableInO_search_threeOccurrence_polySpace_of_promise
    (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hk2 : 2 ≤ k) (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK)
    {f : CNF ℕ → ℕ} {tf sf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf sf)
    (hf_eq : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e a b : ℕ}
    (ht : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars →
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c)
    (hs : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → sf χ ≤ a * ((encCNF χ).length + 1) ^ b) :
    (∀ φ : CNF ℕ, search M K k B (guardOccurrenceCounter k f) φ =
      if (φ.all fun c => decide (c.length ≤ k)) then φ.modelCount else 0) ∧
    ∃ T S : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (search M K k B (guardOccurrenceCounter k f)) encCNF encNat T S ∧
      PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) S ∧
      ∀ φ : CNF ℕ, (T φ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((1 / B + occBound K M * (k * δ)) * φ.numVars) *
          (((encCNF φ).length : ℝ) + 1) ^ E) + C₀ := by
  refine ⟨search_eq_ite_modelCount hM hK hM2 hkK hTB
    (fun ψ hψ _ => guardOccurrenceCounter_eq_modelCount hk2 hf_eq hψ), ?_⟩
  obtain ⟨Tg, Sg, Cg, Eg, hgO, hgS, hgt⟩ :=
    exists_computableInO_guardOccurrenceCounter_polySpace_of_promise hk2 hf hδ ht hs
  obtain ⟨a', b', hgs⟩ := hgS.exists_le
  exact exists_computableInO_search_polySpace hM hK hM2 hkK hTB hgO
    (fun ψ _ _ => guardOccurrenceCounter_le_two_pow_numVars hk2 hf_eq ψ)
    (by positivity) (fun ψ _ _ => hgt ψ) (fun ψ _ _ => hgs ψ)

end CountingSparsify

end Cslib.Complexity
