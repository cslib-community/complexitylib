/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.CSP.Affine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Tactic.FinCases

/-! Fixed-language affine tractability, including repeated scopes and constant equations. -/

namespace CslibFrontierTests.CSPAffine

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

-- Even/odd binary parity, nullary true/false, and an empty binary relation.
private def arity : Fin 5 → ℕ := ![2, 2, 0, 0, 2]
private def sem : Fin 5 → List Bool → Bool :=
  fun R vs => match R.val with
  | 0 => vs.sum == false
  | 1 => vs.sum == true
  | 2 => true
  | _ => false

private def template : Fin 5 → AffineSystem ℕ :=
  ![[⟨[0, 1], false⟩], [⟨[0, 1], true⟩], [], [⟨[], true⟩], [⟨[], true⟩]]

private theorem templates : CSP.AffineTemplates arity sem template := by
  intro R a
  fin_cases R <;>
    simp [template, arity, sem, AffineSystem.Holds, AffineEquation.Holds,
      List.ofFn_succ, Bool.add_eq_xor, Bool.zero_eq_false]

private theorem preserved : CSP.HasPolymorphism arity sem (parity 3) := by
  intro R
  fin_cases R
  · change Cslib.Logic.IsPolymorphism (parity 3)
      {a : Fin 2 → Bool | sem 0 (List.ofFn a) = true}
    have heq : {a : Fin 2 → Bool | sem 0 (List.ofFn a) = true} =
        {a | AffineEquation.Holds ⟨[0, 1], false⟩ a} := by
      ext a
      simp [sem, List.ofFn_succ, AffineEquation.Holds, Bool.zero_eq_false]
    rw [heq]
    exact AffineEquation.isPolymorphism_parity _
  · change Cslib.Logic.IsPolymorphism (parity 3)
      {a : Fin 2 → Bool | sem 1 (List.ofFn a) = true}
    have heq : {a : Fin 2 → Bool | sem 1 (List.ofFn a) = true} =
        {a | AffineEquation.Holds ⟨[0, 1], true⟩ a} := by
      ext a
      simp [sem, List.ofFn_succ, AffineEquation.Holds, Bool.zero_eq_false]
    rw [heq]
    exact AffineEquation.isPolymorphism_parity _
  · intro a ha
    rfl
  · intro a ha
    exact (Bool.false_ne_true (ha 0)).elim
  · intro a ha
    exact (Bool.false_ne_true (ha 0)).elim

-- The language has satisfying and failing tuples for each nonconstant relation.
example : sem 0 [true, true] = true ∧ sem 0 [true, false] = false := by decide
example : sem 1 [true, false] = true ∧ sem 1 [true, true] = false := by decide

-- This endpoint has no solver, template or width hypothesis.
example : CSPSAT arity sem ∈ P (encCSP (encFinite (Fin 5)) encNat) :=
  CSPSAT.mem_P_of_parity (encFinite (Fin 5)) arity sem preserved

-- Different local positions may map to the same variable and cancel.
example (σ : ℕ → Bool) :
    (Constraint.instantiateAffine 0 template ⟨0, [17, 17]⟩).Holds σ := by
  simp [Constraint.instantiateAffine, template, AffineSystem.relabel, AffineEquation.relabel,
    AffineSystem.Holds, AffineEquation.Holds, Bool.add_eq_xor, Bool.zero_eq_false]

example : [⟨0, [2 ^ 100, 2 ^ 100]⟩, ⟨1, [2 ^ 100, 2 ^ 120]⟩, ⟨2, []⟩] ∈
    CSPSAT arity sem := by
  refine ⟨by decide, fun n => n == 2 ^ 120, ?_⟩
  decide

example : [⟨1, [2 ^ 100, 2 ^ 100]⟩] ∉ CSPSAT arity sem := by
  rintro ⟨_, σ, hσ⟩
  simp [CSP.eval, Constraint.eval, sem, Bool.add_eq_xor, Bool.zero_eq_false] at hσ

-- Compilation retains sparse binary labels rather than expanding their numerical range.
example : CSPSAT.toXORSAT arity template [⟨1, [2 ^ 100, 2 ^ 120]⟩] =
    [⟨[2 ^ 100, 2 ^ 120], true⟩] := by decide

example : XORSAT.solve (CSPSAT.toXORSAT arity template
    [⟨0, [2 ^ 100, 2 ^ 100]⟩, ⟨1, [2 ^ 100, 2 ^ 120]⟩, ⟨2, []⟩]) = true := by decide
example : XORSAT.solve (CSPSAT.toXORSAT arity template
    [⟨1, [2 ^ 100, 2 ^ 100]⟩]) = false := by decide

-- Malformed scopes are rejected, even though sem 2 returns true on every list.
example : [⟨2, [7]⟩] ∉ CSPSAT arity sem := by
  rintro ⟨h, _⟩
  have := h ⟨2, [7]⟩ (by simp)
  simp [arity] at this

example : CSPSAT.toXORSAT arity template [⟨0, [7]⟩] = [⟨[], true⟩] := by decide
example : CSPSAT.toXORSAT arity template [⟨0, [7, 8, 9]⟩] = [⟨[], true⟩] := by decide
example : XORSAT.solve (CSPSAT.toXORSAT arity template [⟨0, [7]⟩]) = false := by decide
example : [⟨2, []⟩] ∈ CSPSAT arity sem := by
  exact ⟨by decide, fun _ => false, by decide⟩
example : [⟨3, []⟩] ∉ CSPSAT arity sem := by
  rintro ⟨_, σ, hσ⟩
  exact Bool.false_ne_true hσ
example : [⟨4, [9, 10]⟩] ∉ CSPSAT arity sem := by
  rintro ⟨_, σ, hσ⟩
  exact Bool.false_ne_true hσ
example : ([] : CSP (Fin 5) ℕ) ∈ CSPSAT arity sem := by
  exact ⟨by decide, fun _ => false, by decide⟩

-- Concrete templates exercise the native reduction certificate as well as its semantics.
example : PolyTimeReducible (encCSP (encFinite (Fin 5)) encNat) XORSAT.encoding (CSPSAT arity sem)
    XORSAT :=
  CSPSAT.polyTimeReducible_XORSAT_of_templates (encFinite (Fin 5)) arity sem template templates

end CslibFrontierTests.CSPAffine
