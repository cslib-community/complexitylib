/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.CSP.Hardness

/-!
# Linear-size Schaefer hardness regression tests

Counts distinguish repeated occurrences from distinct variables. Sparse binary names have no
effect on the combinatorial bounds. The native reduction witness is exercised on a concrete
NAE language and on the zero-size input; malformed inputs are also covered.
-/

namespace ComplexityTests.SchaeferSize

open Cslib.Logic Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

private def template (_ : Unit) : CSP Unit (Bool × ℕ) :=
  [((), [(false, 0), (false, 1), (true, 0)])]

private def input : CSP Unit ℕ := [((), [2 ^ 100, 2 ^ 100]), ((), [0, 1])]

example : (CSP.replaceGadgets 1 template input).length = 2 := by decide
example : (CSP.replaceGadgets 1 template input).vars.length = 6 := by decide
example : (CSP.replaceGadgets 1 template input).numVars = 5 := by decide

example : (CSP.replaceGadgets 1 template input).numVars +
    (CSP.replaceGadgets 1 template input).length ≤ 4 * input.length := by
  apply CSP.numVars_add_length_replaceGadgets_le
  intro r
  cases r
  decide

-- The general guarded bound includes malformed source scopes and arbitrary fixed rejection.
example : ∃ C : ℕ, ∀ F : CSP Unit ℕ,
    (CSP.replaceGadgetsGuarded (fun _ => 2) 1 template [((), [])] F).numVars +
      (CSP.replaceGadgetsGuarded (fun _ => 2) 1 template [((), [])] F).length ≤
        C * F.length :=
  CSP.exists_linear_bound_replaceGadgetsGuarded _ _ _ _

example : CSP.replaceGadgetsGuarded (fun _ => 2) 1 template [((), [])]
    [((), [2 ^ 100])] = [((), [])] := by decide

-- Even a nonempty reject instance cannot introduce an additive constant on empty input.
example : CSP.replaceGadgetsGuarded (fun _ : Unit => 2) 1 template [((), [])] [] = [] := by
  rfl

example : (CSP.replaceGadgets 0 (fun _ : Unit => ([] : CSP Unit (Bool × ℕ))) input).numVars +
    (CSP.replaceGadgets 0 (fun _ : Unit => ([] : CSP Unit (Bool × ℕ))) input).length = 0 := by
  decide

example (φ : CNF ℕ) : (SelfDualThreeSAT.ofExactThreeSAT φ).length ≤ φ.length :=
  SelfDualThreeSAT.length_ofExactThreeSAT_le φ

example : (SelfDualThreeSAT.ofExactThreeSAT [[]]).length = 1 := by decide

private def naeArity (_ : Unit) : ℕ := 3
private def naeSem (_ : Unit) : List Bool → Bool
  | [x, y, z] => !((x == y) && (y == z))
  | _ => false

private theorem nae_missing : ¬ CSP.HasSchaeferPolymorphism naeArity naeSem := by
  unfold CSP.HasSchaeferPolymorphism CSP.HasPolymorphism IsPolymorphism
    CSP.booleanRelation naeArity
  simp only [Set.mem_ofPred_eq, not_or]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

private def encUnit : Unit ↪ List Bool :=
  ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩

-- A single witness has native polynomial time, correctness, and a uniform clause-linear bound.
example : ∃ (f : CNF ℕ → CSP Unit ℕ) (C : ℕ),
    ComputableInPolyTime f encCNF (encCSP encUnit encNat) ∧
    (∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ CSPSAT naeArity naeSem) ∧
    (∀ φ, (f φ).numVars + (f φ).length ≤ C * φ.length) :=
  CSPSAT.exists_linear_size_reduction_from_threeSAT encUnit naeArity naeSem nae_missing

-- The n' + m' ≤ C * (n + m) bound follows from the stronger clause-only bound.
example : ∃ (f : CNF ℕ → CSP Unit ℕ) (C : ℕ),
    ComputableInPolyTime f encCNF (encCSP encUnit encNat) ∧
    (∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ CSPSAT naeArity naeSem) ∧
    (∀ φ, (f φ).numVars + (f φ).length ≤ C * (φ.numVars + φ.length)) := by
  obtain ⟨f, C, hp, hm, hs⟩ :=
    CSPSAT.exists_linear_size_reduction_from_threeSAT encUnit naeArity naeSem nae_missing
  refine ⟨f, C, hp, hm, fun φ => (hs φ).trans ?_⟩
  apply Nat.mul_le_mul_left
  omega

example : ∃ (f : CNF ℕ → CSP Unit ℕ),
    (∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ CSPSAT naeArity naeSem) ∧ f [] = [] := by
  obtain ⟨f, _, _, hm, hs⟩ :=
    CSPSAT.exists_linear_size_reduction_from_threeSAT encUnit naeArity naeSem nae_missing
  refine ⟨f, hm, List.length_eq_zero_iff.mp ?_⟩
  have h := hs []
  simp only [List.length_nil, Nat.mul_zero] at h
  omega

end ComplexityTests.SchaeferSize
