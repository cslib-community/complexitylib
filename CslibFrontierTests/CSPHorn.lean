/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.CSP.Horn
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Tactic.FinCases

/-! Fixed AND/OR languages, their native P endpoints and template instantiation edge cases. -/

namespace ComplexityTests.CSPHorn

open Cslib.Complexity Cslib.Logic Cslib.Logic.PL Turing.MultiTapeTM

inductive Rel
  | gate | positive | negative | top | bottom | empty
  deriving DecidableEq

instance : Fintype Rel where
  elems := {.gate, .positive, .negative, .top, .bottom, .empty}
  complete := by intro R; cases R <;> simp

private abbrev arity : Rel → ℕ
  | .gate => 3
  | .positive | .negative | .empty => 1
  | .top | .bottom => 0

-- The gate says x ∧ y → z. Both pins prevent either unary constant from trivializing SAT.
-- The last two false relations have different arities.
private def hornSem : Rel → List Bool → Bool
  | .gate, [x, y, z] => !x || !y || z
  | .positive, [x] => x
  | .negative, [x] => !x
  | .top, _ => true
  | _, _ => false

private def localFormula : (R : Rel) → CNF (Fin (arity R))
  | .gate => [[(0, false), (1, false), (2, true)]]
  | .positive => [[(0, true)]]
  | .negative => [[(0, false)]]
  | .top => []
  | .bottom | .empty => [[]]

private theorem models (R : Rel) : CSP.booleanRelation arity hornSem R =
    {a | (localFormula R).eval a = true} := by
  cases R <;> ext a <;>
    simp [CSP.booleanRelation, arity, hornSem, localFormula, List.ofFn_succ,
      CNF.eval, Clause.eval, or_assoc]

private theorem has_and :
    CSP.HasPolymorphism arity hornSem (fun a : Fin 2 → Bool => a 0 && a 1) := by
  intro R
  rw [models R]
  exact CNF.isPolymorphism_and (by cases R <;> simp [localFormula, CNF.IsHorn, Clause.IsHorn])

private def dualSem (R : Rel) (xs : List Bool) : Bool := hornSem R (xs.map Bool.not)

private theorem has_or :
    CSP.HasPolymorphism arity dualSem (fun a : Fin 2 → Bool => a 0 || a 1) := by
  intro R
  rw [isPolymorphism_or_iff_and_complement]
  have heq : {a : Fin (arity R) → Bool | (fun i => !a i) ∈
      CSP.booleanRelation arity dualSem R} = CSP.booleanRelation arity hornSem R := by
    ext a
    simp [CSP.booleanRelation, dualSem, List.map_ofFn, Function.comp_def]
  rw [heq]
  exact has_and R

-- These fixed languages exercise the two unconditional native endpoints.
example : CSPSAT arity hornSem ∈ P (encCSP (encFinite Rel) encNat) :=
  CSPSAT.mem_P_of_and (encFinite Rel) arity hornSem has_and

example : CSPSAT arity dualSem ∈ P (encCSP (encFinite Rel) encNat) :=
  CSPSAT.mem_P_of_or (encFinite Rel) arity dualSem has_or

-- AND-only: two gate models whose coordinatewise OR violates the gate.
example : ¬ CSP.HasPolymorphism arity hornSem (fun a : Fin 2 → Bool => a 0 || a 1) := by
  intro h
  have ht := h .gate (fun j => if j = 0 then ![true, false, false] else ![false, true, false])
    (by intro j; fin_cases j <;> simp only [CSP.booleanRelation, Set.mem_ofPred_eq] <;> decide)
  norm_num [CSP.booleanRelation, arity, hornSem, List.ofFn_succ] at ht

-- OR-only: complemented witnesses violate closure under AND.
example : ¬ CSP.HasPolymorphism arity dualSem (fun a : Fin 2 → Bool => a 0 && a 1) := by
  intro h
  have ht := (isPolymorphism_and_iff _).mp (h .gate)
    ![false, true, true] (by change dualSem _ _ = true; decide) ![true, false, true]
      (by change dualSem _ _ = true; decide)
  norm_num [CSP.booleanRelation, dualSem, arity, hornSem, List.ofFn_succ] at ht

-- Neither language falls into a constant case: both unary pins are present.
example (b : Bool) : ¬ CSP.HasPolymorphism arity hornSem (fun _ : Fin 1 → Bool => b) := by
  intro h
  cases b with
  | false =>
    exact Bool.false_ne_true (h .positive (fun _ => fun _ => true)
      (by intro _; change hornSem _ _ = true; decide))
  | true =>
    exact Bool.false_ne_true (h .negative (fun _ => fun _ => false)
      (by intro _; change hornSem _ _ = true; decide))

example (b : Bool) : ¬ CSP.HasPolymorphism arity dualSem (fun _ : Fin 1 → Bool => b) := by
  intro h
  cases b with
  | false =>
    exact Bool.false_ne_true (h .negative (fun _ => fun _ => true)
      (by intro _; change dualSem _ _ = true; decide))
  | true =>
    exact Bool.false_ne_true (h .positive (fun _ => fun _ => false)
      (by intro _; change dualSem _ _ = true; decide))

private def majorityWitness (j : Fin 3) : Fin 3 → Bool :=
  ![![true, false, false], ![false, true, false], ![true, true, true]] j

private def parityWitness (j : Fin 3) : Fin 3 → Bool :=
  ![![true, false, false], ![false, true, false], ![false, false, false]] j

-- The ternary gate also rules out the majority and affine branches.
example : ¬ CSP.HasPolymorphism arity hornSem (Cslib.majority 3) := by
  intro h
  have ht := h .gate majorityWitness
    (by intro j; fin_cases j <;> simp only [CSP.booleanRelation, Set.mem_ofPred_eq] <;> decide)
  have hf : hornSem .gate (List.ofFn fun i => Cslib.majority 3
      (fun j => majorityWitness j i)) = false := by decide
  exact Bool.false_ne_true (hf ▸ ht)

example : ¬ CSP.HasPolymorphism arity hornSem (Cslib.parity 3) := by
  intro h
  have ht := h .gate parityWitness
    (by intro j; fin_cases j <;> simp only [CSP.booleanRelation, Set.mem_ofPred_eq] <;> decide)
  have hf : hornSem .gate (List.ofFn fun i => Cslib.parity 3
      (fun j => parityWitness j i)) = false := by decide
  exact Bool.false_ne_true (hf ▸ ht)

example : ¬ CSP.HasPolymorphism arity dualSem (Cslib.majority 3) := by
  intro h
  have ht := h .gate (fun j i => !(majorityWitness j i))
    (by intro j; fin_cases j <;> simp only [CSP.booleanRelation, Set.mem_ofPred_eq] <;> decide)
  have hf : dualSem .gate (List.ofFn fun i => Cslib.majority 3
      (fun j => !(majorityWitness j i))) = false := by decide
  exact Bool.false_ne_true (hf ▸ ht)

example : ¬ CSP.HasPolymorphism arity dualSem (Cslib.parity 3) := by
  intro h
  have ht := h .gate (fun j i => !(parityWitness j i))
    (by intro j; fin_cases j <;> simp only [CSP.booleanRelation, Set.mem_ofPred_eq] <;> decide)
  have hf : dualSem .gate (List.ofFn fun i => Cslib.parity 3
      (fun j => !(parityWitness j i))) = false := by decide
  exact Bool.false_ne_true (hf ▸ ht)

-- Sparse binary labels and repeated scope positions; the same gate accepts x ∧ x → y.
example : [(Rel.gate, [2 ^ 100, 2 ^ 100, 7]), (.positive, [2 ^ 100]), (.positive, [7])]
    ∈ CSPSAT arity hornSem := by
  exact ⟨by decide, fun _ => true, by decide⟩

example : [(Rel.gate, [2 ^ 100, 2 ^ 100, 7]), (.positive, [2 ^ 100]), (.negative, [7])]
    ∉ CSPSAT arity hornSem := by
  rintro ⟨_, σ, hσ⟩
  cases hx : σ (2 ^ 100) <;> cases hy : σ 7 <;>
    simp [CSP.eval, Constraint.eval, hornSem, hy] at hσ

example : [(Rel.gate, [2 ^ 100, 2 ^ 100, 7]), (.positive, [2 ^ 100]), (.positive, [7])]
    ∈ CSPSAT arity dualSem := by
  exact ⟨by decide, fun _ => false, by decide⟩

example : [(Rel.gate, [2 ^ 100, 2 ^ 100, 7]), (.positive, [2 ^ 100]), (.negative, [7])]
    ∉ CSPSAT arity dualSem := by
  rintro ⟨_, σ, hσ⟩
  cases hx : σ (2 ^ 100) <;> cases hy : σ 7 <;>
    simp [CSP.eval, Constraint.eval, dualSem, hornSem, hy] at hσ

-- Malformed nullary scopes are semantically true, but CSPSAT rejects them on both branches.
example : CSP.Satisfiable hornSem ([(Rel.top, [7])] : CSP Rel ℕ) ∧
    [(Rel.top, [7])] ∉ CSPSAT arity hornSem := by
  refine ⟨⟨fun _ => false, rfl⟩, ?_⟩
  rintro ⟨hw, _⟩
  have h := hw (.top, [7]) (by simp)
  simp [arity] at h

example : CSP.Satisfiable dualSem ([(Rel.top, [7])] : CSP Rel ℕ) ∧
    [(Rel.top, [7])] ∉ CSPSAT arity dualSem := by
  refine ⟨⟨fun _ => false, rfl⟩, ?_⟩
  rintro ⟨hw, _⟩
  have h := hw (.top, [7]) (by simp)
  simp [arity] at h

example : [(Rel.top, [])] ∈ CSPSAT arity hornSem ∧
    [(Rel.top, [])] ∈ CSPSAT arity dualSem := by
  exact ⟨⟨by decide, fun _ => false, rfl⟩, ⟨by decide, fun _ => false, rfl⟩⟩

example : [(Rel.bottom, [])] ∉ CSPSAT arity hornSem ∧
    [(Rel.empty, [7])] ∉ CSPSAT arity dualSem := by
  constructor <;> rintro ⟨_, σ, hσ⟩
  · exact Bool.false_ne_true hσ
  · simp [CSP.eval, Constraint.eval, dualSem, hornSem] at hσ

-- Empty alphabets satisfy both hypotheses, and their only instance is accepted.
example (arity : Empty → ℕ) (sem : Empty → List Bool → Bool) :
    CSPSAT arity sem ∈ P (encCSP (encFinite Empty) encNat) ∧
    ([] : CSP Empty ℕ) ∈ CSPSAT arity sem := by
  exact ⟨CSPSAT.mem_P_of_and (encFinite Empty) arity sem (fun R => nomatch R),
    by simp [CSPSAT, CSP.WellFormed, CSP.Satisfiable, CSP.eval]⟩

example (arity : Empty → ℕ) (sem : Empty → List Bool → Bool) :
    CSPSAT arity sem ∈ P (encCSP (encFinite Empty) encNat) :=
  CSPSAT.mem_P_of_or (encFinite Empty) arity sem (fun R => nomatch R)

-- Concrete certified reductions and the ordinary native solvers agree on repeated scopes.
private def template (R : Rel) : CNF ℕ := (localFormula R).relabel Fin.val

private theorem templates : CSP.CNFTemplates arity hornSem template :=
  CSP.cnfTemplates_relabel_fin (fun R a => Set.ext_iff.mp (models R) a)

private def dualTemplate (R : Rel) : CNF ℕ := (template R).flip

private theorem dualTemplates : CSP.CNFTemplates arity dualSem dualTemplate := by
  intro R a
  simpa [dualTemplate, CNF.eval_flip, dualSem, List.map_ofFn, Function.comp_def]
    using templates R (fun i => !a i)

example : PolyTimeReducible (encCSP (encFinite Rel) encNat) encCNF
    (CSPSAT arity hornSem) HornSAT :=
  CSPSAT.polyTimeReducible_HornSAT_of_templates (encFinite Rel) arity hornSem template templates
    (fun R => (CNF.isHorn_relabel _ _).mpr
      (by cases R <;> simp [localFormula, CNF.IsHorn, Clause.IsHorn]))

example : CSP.instantiateCNF 0 template [(Rel.gate, [2 ^ 100, 2 ^ 100, 7])] =
    [[(2 ^ 100, false), (2 ^ 100, false), (7, true)]] := by decide

example : HornSAT.solve (CSP.instantiateCNF 0 template
    [(Rel.gate, [2 ^ 100, 2 ^ 100, 7]), (.positive, [2 ^ 100]), (.negative, [7])]) = false := by
  decide

example : PolyTimeReducible (encCSP (encFinite Rel) encNat) encCNF
    (CSPSAT arity dualSem) DualHornSAT :=
  CSPSAT.polyTimeReducible_DualHornSAT_of_templates (encFinite Rel) arity dualSem dualTemplate
    dualTemplates (fun R => by
      simp only [dualTemplate, CNF.IsDualHorn, CNF.flip_flip, template, CNF.isHorn_relabel]
      cases R <;> simp [localFormula, CNF.IsHorn, Clause.IsHorn])

example : DualHornSAT.solve (CSP.instantiateCNF 0 dualTemplate
    [(Rel.gate, [2 ^ 100, 2 ^ 100, 7]), (.positive, [2 ^ 100]), (.negative, [7])]) = false := by
  decide

example : CSP.validArity arity ([(Rel.gate, [2 ^ 100, 7]), (.gate, [0, 1, 2, 3])] : CSP Rel ℕ) =
    false := by decide

-- Identifying variables never deduplicates literal occurrences or makes non-Horn syntax Horn.
example : ¬ Clause.IsHorn
    (Clause.relabel (fun _ => 7) ([(0, true), (1, true)] : Clause ℕ)) := by
  simp [Clause.IsHorn, Clause.relabel]
example : ¬ Clause.IsDualHorn
    (Clause.relabel (fun _ => 7) ([(0, false), (1, false)] : Clause ℕ)) := by
  simp [Clause.isDualHorn_iff, Clause.relabel]
example : Clause.IsHorn
    (Clause.relabel (fun _ => 7) ([(0, false), (1, false), (2, true)] : Clause ℕ)) := by
  simp [Clause.IsHorn, Clause.relabel]

end ComplexityTests.CSPHorn
