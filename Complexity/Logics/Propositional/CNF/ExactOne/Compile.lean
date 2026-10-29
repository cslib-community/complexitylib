/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne.FromSAT
public import Complexity.Logics.Propositional.CNF.ExactOne.Positive
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Tactic.Linarith

/-!
# Constant-factor parsimonious compilation to positive exact-one clauses

The two local constructions compose without another occurrence splitter or planarization.
Every source clause contributes at most thirteen signed exact-one clauses; replacing their
negative occurrences contributes at most thirteen times as many positive clauses. These are
bounds on actual emitted lists. Every source variable keeps its occurrence count and no new
variable occurs more than three times.

## Main definitions

* `PositiveExactOneCompile.rawFormula`: the structured-variable positive compiler.
* `PositiveExactOneCompile.formula`: its compact natural-variable output.

## Main results

* `oneModelCount_formula`, `oneSatisfiable_formula`: parsimony and correctness.
* `length_formula_le`, `length_vars_formula_le`: explicit constant-factor bounds.

## References

The local gadgets are from [HuntMaratheRadhakrishnanStearns1998, Theorem 3.8].
The composition and quantitative bounds are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PositiveExactOneCompile

variable {V : Type*}

/-- The two disjoint families of local auxiliary variables. -/
abbrev Variable (V : Type*) := PositiveExactOne.Variable (FromSAT.Variable V)

/-- Replace disjunctions by uniquely extensible exact-one clauses and remove all negations. -/
def rawFormula (φ : CNF V) : CNF (Variable V) :=
  PositiveExactOne.formula (FromSAT.formula φ)

/-- Compact natural names for all output variables. -/
def formula [DecidableEq V] (φ : CNF V) : CNF ℕ := (rawFormula φ).compact

/-- Both local stages have constant size: at most 169 clauses per source clause. -/
theorem length_rawFormula_le (φ : CNF V) : (rawFormula φ).length ≤ 169 * φ.length := by
  have h := PositiveExactOne.length_formula_le
    (fun c hc => (FromSAT.width_formula φ c hc).le)
  have hs := FromSAT.length_formula_le φ
  change (rawFormula φ).length ≤ _ at h
  nlinarith

/-- Every emitted clause has exactly three literal occurrences. -/
theorem width_rawFormula (φ : CNF V) : ∀ c ∈ rawFormula φ, c.length = 3 :=
  PositiveExactOne.exactWidth_formula (FromSAT.width_formula φ)

/-- All output literal polarities are positive. -/
theorem positive_rawFormula (φ : CNF V) :
    ∀ c ∈ rawFormula φ, ∀ l ∈ c, l.2 = true :=
  PositiveExactOne.positive_formula _

/-- Every emitted clause has three distinct variables, including when source literals repeat. -/
theorem nodup_rawFormula (φ : CNF V) :
    ∀ c ∈ rawFormula φ, (c.map Prod.fst).Nodup := by
  apply PositiveExactOne.nodup_formula
  intro c hc
  obtain ⟨⟨a, i⟩, _, hc⟩ := List.mem_flatMap.mp hc
  exact FromSAT.nodup_clause i a c hc

/-- Occurrence-three inputs retain that bound through both local replacements. -/
theorem count_vars_rawFormula_le [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (ho : ∀ v, φ.vars.count v ≤ 3) :
    ∀ v, (rawFormula φ).vars.count v ≤ 3 := by
  have eqCount {A : Type _} (b₁ b₂ : BEq A) (h₁ : @LawfulBEq A b₁)
      (h₂ : @LawfulBEq A b₂) (as : List A) (a : A) :
      @List.count A b₁ a as = @List.count A b₂ a as := by
    apply List.countP_congr
    intro x _
    exact (@beq_iff_eq A b₁ h₁ x a).trans (@beq_iff_eq A b₂ h₂ x a).symm
  have h := PositiveExactOne.count_vars_formula_le (FromSAT.formula φ) (fun v => by
    have hv := FromSAT.count_vars_formula_le φ hw ho v
    have he := eqCount (instBEqOfDecidableEq : BEq (FromSAT.Variable V))
      (inferInstance : BEq (FromSAT.Variable V)) inferInstance inferInstance
      (FromSAT.formula φ).vars v
    exact he.le.trans hv)
  intro v
  have hv := h v
  have he := eqCount (inferInstance : BEq (Variable V))
    (@Sum.instBEq (FromSAT.Variable V) ((ℕ × ℕ) × ℕ) instBEqOfDecidableEq inferInstance)
    inferInstance inferInstance (rawFormula φ).vars v
  exact he.le.trans hv

/-- Model counts are preserved through both uniquely extensible stages. -/
theorem oneModelCount_rawFormula [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) : (rawFormula φ).oneModelCount = φ.modelCount :=
  (PositiveExactOne.oneModelCount_formula _).trans (FromSAT.oneModelCount_formula φ hw)

/-- Compact numbering preserves the constant-factor clause bound. -/
theorem length_formula_le [DecidableEq V] (φ : CNF V) :
    (formula φ).length ≤ 169 * φ.length := by
  simpa only [formula, length_compact] using length_rawFormula_le φ

/-- Every compact output clause has exactly three literal occurrences. -/
theorem width_formula [DecidableEq V] (φ : CNF V) : ∀ c ∈ formula φ, c.length = 3 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [Clause.relabel, List.length_map] using width_rawFormula φ d hd

/-- Compact numbering does not change the positive polarity of any literal. -/
theorem positive_formula [DecidableEq V] (φ : CNF V) :
    ∀ c ∈ formula φ, ∀ l ∈ c, l.2 = true := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  exact positive_rawFormula φ d hd a ha

/-- Compaction preserves distinct variables within every output clause. -/
theorem nodup_formula [DecidableEq V] (φ : CNF V) :
    ∀ c ∈ formula φ, (c.map Prod.fst).Nodup := by
  intro c hc
  let : BEq (Variable V) := instBEqOfDecidableEq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hn := nodup_rawFormula φ d hd
  have he : ((d.relabel (rawFormula φ).vars.idxOf).map Prod.fst) =
      (d.map Prod.fst).map (rawFormula φ).vars.idxOf := by
    simp [Clause.relabel, List.map_map, Function.comp_def]
  change ((d.relabel (rawFormula φ).vars.idxOf).map Prod.fst).Nodup
  rw [he]
  change List.Pairwise _ _ at hn ⊢
  rw [List.pairwise_map]
  apply hn.imp_of_mem
  intro a b ha _ hab heq
  have hsource : a ∈ (rawFormula φ).vars := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact CNF.mem_vars.mpr ⟨d, hd, l.2, hl⟩
  exact hab ((List.idxOf_inj hsource).mp heq)

/-- The actual output has at most 507 literal occurrences per source clause. -/
theorem length_vars_formula_le [DecidableEq V] (φ : CNF V) :
    (formula φ).vars.length ≤ 507 * φ.length := by
  have h := CNF.length_vars_le_mul_length (fun c hc => (width_formula φ c hc).le)
  have hs := length_formula_le φ
  nlinarith

/-- Compact numbering preserves the degree-three restriction. -/
theorem count_vars_formula_le [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (ho : ∀ v, φ.vars.count v ≤ 3) :
    ∀ v, (formula φ).vars.count v ≤ 3 :=
  CNF.count_vars_compact_le _ (count_vars_rawFormula_le φ hw ho)

/-- The final natural-variable output has exactly the source model count. -/
theorem oneModelCount_formula [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) : (formula φ).oneModelCount = φ.modelCount :=
  (CNF.oneModelCount_compact _).trans (oneModelCount_rawFormula φ hw)

/-- The compiler preserves satisfiability between ordinary and exact-one semantics. -/
theorem oneSatisfiable_formula [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) : (formula φ).OneSatisfiable ↔ φ.Satisfiable := by
  rw [← CNF.oneModelCount_pos_iff, oneModelCount_formula φ hw, CNF.modelCount_pos_iff]

end Cslib.Logic.PL.CNF.PositiveExactOneCompile
