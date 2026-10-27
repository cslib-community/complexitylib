/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.OneInThreeSAT
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Size
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Counting
public import Complexity.Logics.Propositional.CNF.ExactOne.Compile
import Complexity.Logics.Propositional.CNF.ExactOne.PolyTime
import Mathlib.Tactic.Linarith

/-!
# Parsimonious constant-factor reductions to positive exact-one SAT

Ordinary occurrence splitting is followed by the two constant-size local replacements of
[Hunt, Marathe, Radhakrishnan and Stearns, Theorem 3.8]
[HuntMaratheRadhakrishnanStearns1998]. The output has three distinct positive variables per
clause and at most three occurrences of every variable. Thus one compiler proves hardness of
all four positive variants, with no negated literals in any target.

The new local compiler contributes at most 169 clauses and 507 literal occurrences per input
clause. Relative to the original width-three input, the composed bounds are 169 and 507 times
its clause-plus-literal count. These measure actual lists, independently of binary label sizes.

## Main definitions

* `toPositiveOneInExactThreeSATThree`: total reduction from ordinary 3SAT.

## Main results

* `oneModelCount_toPositiveOneInExactThreeSATThree`: exact preservation of model counts.
* `PositiveOneInExactThreeSATThree_npComplete`: the strongest nonplanar endpoint.
* `PositiveOneInThreeSAT_npComplete`, `PositiveOneInExactThreeSAT_npComplete`,
  `PositiveOneInThreeSATThree_npComplete`: the other positive variants.

## References

* [Hunt, Marathe, Radhakrishnan and Stearns][HuntMaratheRadhakrishnanStearns1998],
  Theorem 3.8, Figures 3.4–3.5 and Lemma 3.6.

The composition, occurrence accounting, and quantitative bounds are original.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Split ordinary occurrences, then apply the parsimonious positive exact-three compiler. -/
def toPositiveOneInExactThreeSATThree (φ : CNF ℕ) : CNF ℕ :=
  CNF.PositiveExactOneCompile.formula (toThreeSATThree φ)

/-- The complete compiler is native polynomial-time under ordinary binary formula encodings. -/
@[fun_prop]
theorem computableInPolyTime_toPositiveOneInExactThreeSATThree :
    ComputableInPolyTime toPositiveOneInExactThreeSATThree encCNF encCNF :=
  (CNF.PositiveExactOneCompile.computableInPolyTime_formula encNat).comp
    computableInPolyTime_toThreeSATThree

/-- All output clauses have three distinct variables. -/
theorem exactClauses_toPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    ∀ c ∈ toPositiveOneInExactThreeSATThree φ,
      c.length = 3 ∧ (c.map Prod.fst).Nodup :=
  fun c hc => ⟨CNF.PositiveExactOneCompile.width_formula _ c hc,
    CNF.PositiveExactOneCompile.nodup_formula _ c hc⟩

/-- Every emitted target literal is positive. -/
theorem positive_toPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    OneSAT.positiveCheck (toPositiveOneInExactThreeSATThree φ) = true :=
  (OneSAT.positiveCheck_iff _).mpr (CNF.PositiveExactOneCompile.positive_formula _)

/-- Every output variable occurs at most three times. -/
theorem count_vars_toPositiveOneInExactThreeSATThree_le (φ : CNF ℕ) :
    ∀ v, (toPositiveOneInExactThreeSATThree φ).vars.count v ≤ 3 :=
  CNF.PositiveExactOneCompile.count_vars_formula_le _ (width_toThreeSATThree φ)
    (count_vars_toThreeSATThree_le φ)

/-- The actual exact-one model count is the original ordinary model count. -/
theorem oneModelCount_toPositiveOneInExactThreeSATThree (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (toPositiveOneInExactThreeSATThree φ).oneModelCount = φ.modelCount :=
  (CNF.PositiveExactOneCompile.oneModelCount_formula _ (width_toThreeSATThree φ)).trans
    (modelCount_toThreeSATThree φ hw)

/-- Total correctness, including rejected malformed ordinary inputs. -/
theorem oneSatisfiable_toPositiveOneInExactThreeSATThree_iff (φ : CNF ℕ) :
    (toPositiveOneInExactThreeSATThree φ).OneSatisfiable ↔ φ ∈ ThreeSAT := by
  rw [toPositiveOneInExactThreeSATThree,
    CNF.PositiveExactOneCompile.oneSatisfiable_formula _ (width_toThreeSATThree φ)]
  have he : (toThreeSATThree φ).Satisfiable ↔ toThreeSATThree φ ∈ ThreeSATThree :=
    ⟨fun hs => ⟨width_toThreeSATThree φ, count_vars_toThreeSATThree_le φ, hs⟩,
      fun hs => hs.2.2⟩
  exact he.trans (mem_ThreeSATThree_toThreeSATThree_iff φ)

/-- Explicit constant-factor formula bounds relative to the original valid 3SAT instance. -/
theorem size_toPositiveOneInExactThreeSATThree (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (toPositiveOneInExactThreeSATThree φ).length ≤ 169 * (φ.length + φ.vars.length) ∧
      (toPositiveOneInExactThreeSATThree φ).vars.length ≤
        507 * (φ.length + φ.vars.length) := by
  have hc := CNF.PositiveExactOneCompile.length_formula_le (toThreeSATThree φ)
  have hl := CNF.PositiveExactOneCompile.length_vars_formula_le (toThreeSATThree φ)
  rw [length_toThreeSATThree φ hw] at hc hl
  exact ⟨hc, hl⟩

/-- The guarded counting functions agree on every input, including invalid syntax. -/
theorem sharpPositiveOneInExactThreeSATThree_toPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    SharpPositiveOneInExactThreeSATThree (toPositiveOneInExactThreeSATThree φ) =
      SharpThreeSAT φ := by
  have hg := (PositiveOneInExactThreeSATThree.syntaxCheck_iff _).mpr
    ⟨exactClauses_toPositiveOneInExactThreeSATThree φ,
      positive_toPositiveOneInExactThreeSATThree φ,
      count_vars_toPositiveOneInExactThreeSATThree_le φ⟩
  have hs := (ThreeSATThree.syntaxCheck_iff _).mpr
    ⟨width_toThreeSATThree φ, count_vars_toThreeSATThree_le φ⟩
  simp only [SharpPositiveOneInExactThreeSATThree, hg, ↓reduceIte]
  change (toPositiveOneInExactThreeSATThree φ).oneModelCount = _
  rw [toPositiveOneInExactThreeSATThree,
    CNF.PositiveExactOneCompile.oneModelCount_formula _ (width_toThreeSATThree φ)]
  simpa only [SharpThreeSATThree, hs, ↓reduceIte, SharpSAT] using
    sharpThreeSATThree_toThreeSATThree φ

/-- The native compiler is a parsimonious counting reduction on all encoded inputs. -/
theorem parsimoniousReducible_SharpThreeSAT_SharpPositiveOneInExactThreeSATThree :
    ParsimoniousReducible encCNF encCNF SharpThreeSAT SharpPositiveOneInExactThreeSATThree :=
  ⟨toPositiveOneInExactThreeSATThree, computableInPolyTime_toPositiveOneInExactThreeSATThree,
    fun φ => (sharpPositiveOneInExactThreeSATThree_toPositiveOneInExactThreeSATThree φ).symm⟩

/-- The strongest target's membership equivalence. -/
theorem mem_PositiveOneInExactThreeSATThree_toPositiveOneInExactThreeSATThree_iff
    (φ : CNF ℕ) :
    toPositiveOneInExactThreeSATThree φ ∈ PositiveOneInExactThreeSATThree ↔ φ ∈ ThreeSAT := by
  change (_ ∧ _ ∧ _) ∧ _ ↔ _
  rw [and_iff_right (exactClauses_toPositiveOneInExactThreeSATThree φ),
    and_iff_right (positive_toPositiveOneInExactThreeSATThree φ),
    and_iff_left (count_vars_toPositiveOneInExactThreeSATThree_le φ)]
  exact oneSatisfiable_toPositiveOneInExactThreeSATThree_iff φ

/-- The same output proves the unrestricted exact-three target's membership equivalence. -/
theorem mem_PositiveOneInExactThreeSAT_toPositiveOneInExactThreeSATThree_iff (φ : CNF ℕ) :
    toPositiveOneInExactThreeSATThree φ ∈ PositiveOneInExactThreeSAT ↔ φ ∈ ThreeSAT := by
  change _ ∧ _ ∧ _ ↔ _
  rw [and_iff_right (exactClauses_toPositiveOneInExactThreeSATThree φ),
    and_iff_right (positive_toPositiveOneInExactThreeSATThree φ)]
  exact oneSatisfiable_toPositiveOneInExactThreeSATThree_iff φ

/-- The same output proves positive width-three satisfiability's membership equivalence. -/
theorem mem_PositiveOneInThreeSAT_toPositiveOneInExactThreeSATThree_iff (φ : CNF ℕ) :
    toPositiveOneInExactThreeSATThree φ ∈ PositiveOneInThreeSAT ↔ φ ∈ ThreeSAT := by
  change _ ∧ _ ∧ _ ↔ _
  rw [and_iff_right (show ∀ c ∈ toPositiveOneInExactThreeSATThree φ, c.length ≤ 3 from
      fun c hc => (exactClauses_toPositiveOneInExactThreeSATThree φ c hc).1.le),
    and_iff_right (positive_toPositiveOneInExactThreeSATThree φ)]
  exact oneSatisfiable_toPositiveOneInExactThreeSATThree_iff φ

/-- The same output proves the bounded-occurrence width-three target's equivalence. -/
theorem mem_PositiveOneInThreeSATThree_toPositiveOneInExactThreeSATThree_iff (φ : CNF ℕ) :
    toPositiveOneInExactThreeSATThree φ ∈ PositiveOneInThreeSATThree ↔ φ ∈ ThreeSAT := by
  change _ ∧ _ ↔ _
  rw [and_iff_left (count_vars_toPositiveOneInExactThreeSATThree_le φ)]
  exact mem_PositiveOneInThreeSAT_toPositiveOneInExactThreeSATThree_iff φ

/-- Ordinary 3SAT reduces to positive exact-three, occurrence-three exact-one SAT. -/
theorem polyTimeReducible_ThreeSAT_PositiveOneInExactThreeSATThree :
    PolyTimeReducible encCNF encCNF ThreeSAT PositiveOneInExactThreeSATThree :=
  ⟨toPositiveOneInExactThreeSATThree, computableInPolyTime_toPositiveOneInExactThreeSATThree,
    fun φ => (mem_PositiveOneInExactThreeSATThree_toPositiveOneInExactThreeSATThree_iff φ).symm⟩

/-- Positive exact-three, occurrence-three exact-one SAT is NP-hard. -/
theorem PositiveOneInExactThreeSATThree_npHard : NPHard encCNF PositiveOneInExactThreeSATThree :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_PositiveOneInExactThreeSATThree

/-- Positive exact-three, occurrence-three exact-one SAT is NP-complete. -/
theorem PositiveOneInExactThreeSATThree_npComplete :
    NPComplete encCNF PositiveOneInExactThreeSATThree :=
  ⟨PositiveOneInExactThreeSATThree.mem_NP, PositiveOneInExactThreeSATThree_npHard⟩

/-- Positive exact-three exact-one SAT is NP-hard. -/
theorem PositiveOneInExactThreeSAT_npHard : NPHard encCNF PositiveOneInExactThreeSAT :=
  ThreeSAT_npHard.trans ⟨toPositiveOneInExactThreeSATThree,
    computableInPolyTime_toPositiveOneInExactThreeSATThree,
    fun φ => (mem_PositiveOneInExactThreeSAT_toPositiveOneInExactThreeSATThree_iff φ).symm⟩

/-- Positive exact-three exact-one SAT is NP-complete. -/
theorem PositiveOneInExactThreeSAT_npComplete : NPComplete encCNF PositiveOneInExactThreeSAT :=
  ⟨PositiveOneInExactThreeSAT.mem_NP, PositiveOneInExactThreeSAT_npHard⟩

/-- Positive width-three exact-one SAT is NP-hard. -/
theorem PositiveOneInThreeSAT_npHard : NPHard encCNF PositiveOneInThreeSAT :=
  ThreeSAT_npHard.trans ⟨toPositiveOneInExactThreeSATThree,
    computableInPolyTime_toPositiveOneInExactThreeSATThree,
    fun φ => (mem_PositiveOneInThreeSAT_toPositiveOneInExactThreeSATThree_iff φ).symm⟩

/-- Positive width-three exact-one SAT is NP-complete. -/
theorem PositiveOneInThreeSAT_npComplete : NPComplete encCNF PositiveOneInThreeSAT :=
  ⟨PositiveOneInThreeSAT.mem_NP, PositiveOneInThreeSAT_npHard⟩

/-- Positive width-three, occurrence-three exact-one SAT is NP-hard. -/
theorem PositiveOneInThreeSATThree_npHard : NPHard encCNF PositiveOneInThreeSATThree :=
  ThreeSAT_npHard.trans ⟨toPositiveOneInExactThreeSATThree,
    computableInPolyTime_toPositiveOneInExactThreeSATThree,
    fun φ => (mem_PositiveOneInThreeSATThree_toPositiveOneInExactThreeSATThree_iff φ).symm⟩

/-- Positive width-three, occurrence-three exact-one SAT is NP-complete. -/
theorem PositiveOneInThreeSATThree_npComplete : NPComplete encCNF PositiveOneInThreeSATThree :=
  ⟨PositiveOneInThreeSATThree.mem_NP, PositiveOneInThreeSATThree_npHard⟩

end Cslib.Complexity
