/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Polymorphism.BooleanClone

/-!
# Boolean clone classification regression tests

The not-all-equal language witnesses the nonvacuous negative Schaefer branch. Its negation
polymorphism rules out incorrectly strengthening the conclusion to projections alone.
Arbitrary positive arity is exercised symbolically; nullary operations are explicitly excluded,
whereas empty and nullary relations remain allowed.
-/

namespace ComplexityTests.BooleanClone

open Cslib.Logic Cslib.Logic.BooleanClone Cslib.Logic.PL.CSP

private def naeArity (_ : Unit) : ℕ := 3

private def naeSem (_ : Unit) : List Bool → Bool
  | [x, y, z] => !((x == y) && (y == z))
  | _ => false

private theorem nae_missing : ¬ HasSchaeferPolymorphism naeArity naeSem := by
  unfold HasSchaeferPolymorphism HasPolymorphism IsPolymorphism booleanRelation naeArity
  simp only [Set.mem_ofPred_eq, not_or]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- This is a real language with both positive and negative tuples.
example : ![false, false, true] ∈ booleanRelation naeArity naeSem () := by
  change naeSem () [false, false, true] = true
  decide
example : ![false, false, false] ∉ booleanRelation naeArity naeSem () := by
  change ¬ naeSem () [false, false, false] = true
  decide

-- Boolean negation is allowed by the classification and preserves not-all-equal.
example : HasPolymorphism naeArity naeSem (fun a : Fin 1 → Bool => !(a 0)) := by
  unfold HasPolymorphism IsPolymorphism booleanRelation naeArity
  decide

-- The application does not restrict the arity to the binary/ternary proof cases.
example {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : HasPolymorphism naeArity naeSem f) :
    ∃ i, f = (fun a => a i) ∨ f = (fun a => !(a i)) :=
  projection_or_negation_of_not_hasSchaeferPolymorphism naeArity naeSem nae_missing hn hf

-- Self-dual targets may have arbitrary coordinate types, not just finite CSP arities.
example {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : HasPolymorphism naeArity naeSem f) :
    IsPolymorphism f {a : Bool → Bool | a false ≠ a true} := by
  apply isPolymorphism_selfDual_of_not_hasSchaeferPolymorphism
    naeArity naeSem nae_missing hn hf
  intro a ha
  change (!(a false)) ≠ (!(a true))
  cases h₀ : a false <;> cases h₁ : a true <;> simp_all

-- Constants are essentially unary, and each of the four generators is not.
example : EssentiallyUnary (fun _ : Fin 7 → Bool => false) := ⟨0, fun _ => false, fun _ => rfl⟩
example : ¬ EssentiallyUnary andOp := by
  unfold EssentiallyUnary
  decide
example : ¬ EssentiallyUnary orOp := by
  unfold EssentiallyUnary
  decide
example : ¬ EssentiallyUnary (Cslib.majority 3) := by
  unfold EssentiallyUnary
  decide
example : ¬ EssentiallyUnary (Cslib.parity 3) := by
  unfold EssentiallyUnary
  decide

private def allOperations : BooleanClone where
  operations n := {f | 0 < n}
  nullary := by ext f; simp
  projection i := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  comp _ hn _ _ _ _ := hn

-- A genuine clone inhabits the generator side.
example : andOp ∈ allOperations.operations 2 := by
  change 0 < 2
  decide
example :
    (∀ n, 0 < n → ∀ f ∈ allOperations.operations n, EssentiallyUnary f) ∨
      andOp ∈ allOperations.operations 2 ∨ orOp ∈ allOperations.operations 2 ∨
      Cslib.majority 3 ∈ allOperations.operations 3 ∨ Cslib.parity 3 ∈ allOperations.operations 3 :=
  allOperations.classification

-- Nullary relations do not require nullary operations. A positive-arity operation preserves
-- an empty nullary relation vacuously, including the unary constants.
private def emptyNullary : BooleanClone :=
  ofRelations (fun _ : Unit => 0) (fun _ => ∅)

example : (fun _ : Fin 1 → Bool => false) ∈ emptyNullary.operations 1 := by
  refine ⟨by decide, fun _ a ha => ?_⟩
  exact False.elim (ha 0)

example : (fun _ : Fin 0 → Bool => false) ∉ emptyNullary.operations 0 := by
  intro h
  exact (Nat.lt_irrefl 0 h.1)

-- The true nullary relation is preserved as well.
example : (fun a : Fin 1 → Bool => !(a 0)) ∈
    (ofRelations (fun _ : Unit => 0) (fun _ => Set.univ)).operations 1 :=
  ⟨by decide, fun _ _ _ => Set.mem_univ _⟩

end ComplexityTests.BooleanClone
