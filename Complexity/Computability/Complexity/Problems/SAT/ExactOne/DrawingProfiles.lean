/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesData
public import Complexity.Logics.Propositional.CNF.ExactOne.Blocks
import Mathlib.Tactic.FinCases

/-!
# Actual variable names of local positive exact-one profiles

The finite geometric profiles use source literal positions as placeholder variable names.
Relabelling restores source labels, original clause indices, and the exact signed-clause prefix
offsets of the positive compiler. Repeated source variables may identify distinct placeholders;
their displayed vertices are omitted when the local incidences are spliced to source routes.

## Main definitions

* `clauseProfile`: select the finite profile from source length and polarities.
* `profileVariableMap`: restore actual labels and both families of auxiliary indices.

## Main results

* `profileFormula_relabel`: the relabelled profile is the actual positive output block.
* `rawFormula_eq_profiles`: the profile list has exactly the actual compiler's clause order.

## References

These are original indexing identities for the existing parsimonious compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL

/-- Select one of the fifteen profiles from the first three source literal polarities. -/
def clauseProfile : Clause ℕ → ClauseProfile
  | [] => 0
  | [p] => ⟨1 + p.2.toNat, by have := Bool.toNat_le p.2; omega⟩
  | [p, q] => ⟨3 + 2 * p.2.toNat + q.2.toNat, by
      have := Bool.toNat_le p.2
      have := Bool.toNat_le q.2
      omega⟩
  | p :: q :: r :: _ => ⟨7 + 4 * p.2.toNat + 2 * q.2.toNat + r.2.toNat, by
      have := Bool.toNat_le p.2
      have := Bool.toNat_le q.2
      have := Bool.toNat_le r.2
      omega⟩

/-- Restore actual source labels, the original clause index, and the global signed-clause offset.
The source-slot fallback is irrelevant to every occurring profile variable. -/
def profileVariableMap (i offset : ℕ) (c : Clause ℕ) :
    CNF.PositiveExactOneCompile.Variable ℕ → CNF.PositiveExactOneCompile.Variable ℕ
  | .inl (.inl j) => .inl (.inl (c.getD j (0, true)).1)
  | .inl (.inr (_, k)) => .inl (.inr (i, k))
  | .inr ((j, k), s) => .inr ((offset + j, k), s)

/-- A finite profile has exactly the actual compiler's literals after restoring all indices. -/
theorem profileFormula_relabel (i offset : ℕ) (c : Clause ℕ) :
    (profileFormula (clauseProfile c)).relabel (profileVariableMap i offset c) =
      (CNF.PositiveExactOne.formula (CNF.FromSAT.clause i c)).relabel
        (CNF.PositiveExactOne.shift offset) := by
  rcases c with _ | ⟨⟨p, bp⟩, _ | ⟨⟨q, bq⟩, _ | ⟨⟨r, br⟩, rest⟩⟩⟩
  · simp [clauseProfile, profileFormula, profileSource, profileVariableMap,
      CNF.FromSAT.clause, CNF.FromSAT.core, CNF.FromSAT.padding, CNF.FromSAT.aux,
      CNF.FromSAT.forcePadding, CNF.PositiveExactOne.formula,
      CNF.PositiveExactOne.clauseClauses, CNF.PositiveExactOne.positiveLiteral,
      CNF.PositiveExactOne.complementBlock, CNF.PositiveExactOne.auxiliary,
      CNF.PositiveExactOne.shift, CNF.relabel, Clause.relabel,
      CNF.ExactOneGadget.disjunctionClauses, CNF.ExactOneGadget.forceFalseClauses,
      CNF.ExactOneGadget.complementClauses, Std.Sat.Literal.negate]
  · cases bp <;>
      simp [clauseProfile, profileFormula, profileSource, profileVariableMap,
        CNF.FromSAT.clause, CNF.FromSAT.core, CNF.FromSAT.padding, CNF.FromSAT.aux,
        CNF.FromSAT.lift, CNF.FromSAT.forcePadding, CNF.PositiveExactOne.formula,
        CNF.PositiveExactOne.clauseClauses, CNF.PositiveExactOne.positiveLiteral,
        CNF.PositiveExactOne.complementBlock, CNF.PositiveExactOne.auxiliary,
        CNF.PositiveExactOne.shift, CNF.relabel, Clause.relabel,
        CNF.ExactOneGadget.disjunctionClauses, CNF.ExactOneGadget.forceFalseClauses,
        CNF.ExactOneGadget.complementClauses, Std.Sat.Literal.negate, List.getD]
  · cases bp <;> cases bq <;>
      simp [clauseProfile, profileFormula, profileSource, profileVariableMap,
        CNF.FromSAT.clause, CNF.FromSAT.core, CNF.FromSAT.padding, CNF.FromSAT.aux,
        CNF.FromSAT.lift, CNF.FromSAT.forcePadding, CNF.PositiveExactOne.formula,
        CNF.PositiveExactOne.clauseClauses, CNF.PositiveExactOne.positiveLiteral,
        CNF.PositiveExactOne.complementBlock, CNF.PositiveExactOne.auxiliary,
        CNF.PositiveExactOne.shift, CNF.relabel, Clause.relabel,
        CNF.ExactOneGadget.disjunctionClauses, CNF.ExactOneGadget.forceFalseClauses,
        CNF.ExactOneGadget.complementClauses, Std.Sat.Literal.negate, List.getD]
  · cases bp <;> cases bq <;> cases br <;>
      simp [clauseProfile, profileFormula, profileSource, profileVariableMap,
        CNF.FromSAT.clause, CNF.FromSAT.core, CNF.FromSAT.aux,
        CNF.FromSAT.lift, CNF.PositiveExactOne.formula,
        CNF.PositiveExactOne.clauseClauses, CNF.PositiveExactOne.positiveLiteral,
        CNF.PositiveExactOne.complementBlock, CNF.PositiveExactOne.auxiliary,
        CNF.PositiveExactOne.shift, CNF.relabel, Clause.relabel,
        CNF.ExactOneGadget.disjunctionClauses, CNF.ExactOneGadget.forceFalseClauses,
        CNF.ExactOneGadget.complementClauses, Std.Sat.Literal.negate, List.getD]

/-- The profile partition retains the actual output formula, clause order, and variable names. -/
theorem rawFormula_eq_profiles (φ : CNF ℕ) :
    CNF.PositiveExactOneCompile.rawFormula φ = φ.zipIdx.flatMap fun c =>
      (profileFormula (clauseProfile c.1)).relabel
        (profileVariableMap c.2 (CNF.PositiveExactOneCompile.signedOffset φ c.2) c.1) := by
  rw [CNF.PositiveExactOneCompile.rawFormula_eq_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro c _
  exact (profileFormula_relabel _ _ _).symm

/-- Every actual positive replacement profile has at most twenty-two clauses. -/
theorem profileFormula_length_le (p : ClauseProfile) : (profileFormula p).length ≤ 22 := by
  fin_cases p <;> decide +kernel

/-- The local incidence table has one route per literal, in each actual profile clause. -/
theorem profileGeometry_incidence_count (p : ClauseProfile) (i : Fin 22) :
    ((profileGeometry p).incidenceRoutes.filter fun e => e.1 == i.val).length =
      ((profileFormula p).getD i.val []).length := by
  fin_cases p <;> fin_cases i <;> decide +kernel

/-- Filtering the incidence table by clause retains the actual local literal order and names. -/
theorem profileGeometry_literal_indices (p : ClauseProfile) (i : Fin 22)
    {l : Literal (CNF.PositiveExactOneCompile.Variable ℕ)} {e : LocalIncidence}
    (he : (l, e) ∈ ((profileFormula p).getD i.val []).zip
      ((profileGeometry p).incidenceRoutes.filter fun e => e.1 == i.val)) :
    e.2.1 = (profileVariables p).idxOf l.1 := by
  have hall : (((profileFormula p).getD i.val []).zip
      ((profileGeometry p).incidenceRoutes.filter fun e => e.1 == i.val)).all
        (fun a => a.2.2.1 == (profileVariables p).idxOf a.1.1) = true := by
    fin_cases p <;> fin_cases i <;> decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp hall (l, e) he)

/-- Every profile variable has exactly its indicated source, original-clause, or signed-clause
scope. These finite bounds identify the private auxiliary intervals used by global assembly. -/
theorem profileVariables_scope (p : ClauseProfile) :
    ∀ v ∈ profileVariables p,
      match v with
      | .inl (.inl j) => j < (profileSource p).length
      | .inl (.inr (i, _)) => i = 0
      | .inr ((i, _), _) => i < (CNF.FromSAT.clause 0 (profileSource p)).length := by
  have hall : (profileVariables p).all (fun v =>
      match v with
      | .inl (.inl j) => decide (j < (profileSource p).length)
      | .inl (.inr (i, _)) => decide (i = 0)
      | .inr ((i, _), _) =>
        decide (i < (CNF.FromSAT.clause 0 (profileSource p)).length)) = true := by
    fin_cases p <;> decide +kernel
  intro v hv
  have h := List.all_eq_true.mp hall v hv
  cases v with
  | inl v =>
    cases v with
    | inl j => simpa only [decide_eq_true_eq] using h
    | inr a => rcases a with ⟨i, k⟩; simpa only [decide_eq_true_eq] using h
  | inr a => rcases a with ⟨⟨i, k⟩, s⟩; simpa only [decide_eq_true_eq] using h

/-- Every present source placeholder has a valid local variable index and its prescribed
position in the ordered terminal list. -/
theorem profileSource_terminal_index (p : ClauseProfile) (j : Fin 3)
    (hj : j.val < (profileSource p).length) :
    let v := (profileVariables p).idxOf (Sum.inl (Sum.inl j.val))
    v < (profileGeometry p).variablePositions.length ∧
      v ∈ (profileGeometry p).terminalVariables ∧
      (profileGeometry p).terminalVariables.idxOf v = j.val := by
  have hall : ∀ (p : ClauseProfile) (j : Fin 3), j.val < (profileSource p).length →
      let v := (profileVariables p).idxOf (Sum.inl (Sum.inl j.val))
      v < (profileGeometry p).variablePositions.length ∧
        v ∈ (profileGeometry p).terminalVariables ∧
        (profileGeometry p).terminalVariables.idxOf v = j.val := by
    decide +kernel
  exact hall p j hj

/-- Selecting a profile preserves the source width when the source has width at most three. -/
theorem profileSource_length (c : Clause ℕ) (hc : c.length ≤ 3) :
    (profileSource (clauseProfile c)).length = c.length := by
  rcases c with _ | ⟨⟨p, bp⟩, _ | ⟨⟨q, bq⟩, _ | ⟨⟨r, br⟩, rest⟩⟩⟩
  · rfl
  · cases bp <;> rfl
  · cases bp <;> cases bq <;> rfl
  · have hr : rest = [] := by simpa using hc
    subst rest
    cases bp <;> cases bq <;> cases br <;> rfl

/-- Profiles retain at most the first three original positions. -/
theorem profileSource_length_le (c : Clause ℕ) :
    (profileSource (clauseProfile c)).length ≤ c.length := by
  rcases c with _ | ⟨⟨p, bp⟩, _ | ⟨⟨q, bq⟩, _ | ⟨⟨r, br⟩, rest⟩⟩⟩
  · rfl
  · cases bp <;> rfl
  · cases bp <;> cases bq <;> rfl
  · cases bp <;> cases bq <;> cases br <;>
      simp [clauseProfile, profileSource]

end Cslib.Complexity.SAT.ExactOne
