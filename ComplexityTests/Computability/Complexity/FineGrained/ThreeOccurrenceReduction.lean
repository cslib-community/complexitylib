/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.ThreeOccurrenceReduction

/-!
# Tests for bounded-occurrence reductions and counting-sparsification leaf reductions

Concrete execution and non-vacuity checks for `toThreeOccurrenceDense`, `guardOccurrenceCounter`,
`CountingSparsify.exists_computableInO_search_of_threeOccurrence_counter`.
-/

@[expose] public section

namespace Cslib.Complexity.Tests.ThreeOccurrenceReduction

open Cslib.Logic.PL

/-- A nontrivial formula with non-contiguous variable labels (`2, 5, 9`) and repeated variable
occurrences (`2` occurs 3 times, `5` occurs 2 times, `9` occurs once; 6 literal occurrences in
total). -/
def sampleThreeCNF : CNF ℕ :=
  [[(2, true), (5, false)], [(2, false), (9, true)], [(2, true), (5, true)]]

example :
    (toThreeOccurrenceDense ([] : CNF ℕ)).numVars = 0 ∧
      (toThreeOccurrenceDense ([] : CNF ℕ)).length = 0 ∧
      (toThreeOccurrenceDense ([] : CNF ℕ)).modelCount = 1 ∧
      (toThreeOccurrenceDense ([[]] : CNF ℕ)).numVars = 0 ∧
      (toThreeOccurrenceDense ([[]] : CNF ℕ)).length = 1 ∧
      (toThreeOccurrenceDense ([[]] : CNF ℕ)).modelCount = 0 ∧
      sampleThreeCNF.vars.length = 6 ∧
      (toThreeOccurrenceDense sampleThreeCNF).numVars = 6 ∧
      (toThreeOccurrenceDense sampleThreeCNF).vars.toFinset = Finset.range 6 ∧
      (toThreeOccurrenceDense sampleThreeCNF).length = 9 ∧
      (toThreeOccurrenceDense sampleThreeCNF).vars.length = 18 ∧
      (toThreeOccurrenceDense sampleThreeCNF).all (fun c => decide (c.length ≤ 3)) = true ∧
      ((List.range 6).all fun v =>
        decide ((toThreeOccurrenceDense sampleThreeCNF).vars.count v ≤ 3)) = true ∧
      (toThreeOccurrenceDense sampleThreeCNF).modelCount = sampleThreeCNF.modelCount :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    modelCount_toThreeOccurrenceDense sampleThreeCNF⟩

example :
    guardOccurrenceCounter 3 CNF.modelCount sampleThreeCNF = sampleThreeCNF.modelCount ∧
      guardOccurrenceCounter 3 CNF.modelCount
        [[(0, true), (1, true), (2, true), (3, true)]] = 0 ∧
      CountingSparsify.search 2 3 3 2 (guardOccurrenceCounter 3 CNF.modelCount) sampleThreeCNF =
        sampleThreeCNF.modelCount ∧
      0 < guardOccurrenceCounter 3 CNF.modelCount sampleThreeCNF :=
  ⟨guardOccurrenceCounter_eq_modelCount (by decide : 2 ≤ 3) (fun _ _ _ _ => rfl) (by decide),
    by decide, by decide, by decide⟩

example {B L_coeff : ℕ}
    (hTB : CountingSparsify.CountingTreeBound 2 3 B L_coeff (by decide) (by decide))
    {f tf : CNF ℕ → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInO f encCNF Turing.MultiTapeTM.encNat tf tf)
    (hf_eq : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ 3) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ,
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      CountingSparsify.search 2 3 3 B (guardOccurrenceCounter 3 f) φ = φ.modelCount :=
  (CountingSparsify.exists_computableInO_search_of_threeOccurrence_counter
    (by decide) (by decide) (by decide) (by decide) le_rfl hTB hf hf_eq hδ ht).1

example {B L_coeff : ℕ}
    (hTB : CountingSparsify.CountingTreeBound 2 3 B L_coeff (by decide) (by decide))
    {f tf : CNF ℕ → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInO f encCNF Turing.MultiTapeTM.encNat tf tf)
    (hf_eq : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ 3) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ, (∀ d ∈ χ, d.length ≤ 3) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars →
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      CountingSparsify.search 2 3 3 B (guardOccurrenceCounter 3 f) φ = φ.modelCount :=
  (CountingSparsify.exists_computableInO_search_threeOccurrence_of_promise
    (by decide) (by decide) (by decide) (by decide) le_rfl hTB hf hf_eq hδ ht).1

end Cslib.Complexity.Tests.ThreeOccurrenceReduction
