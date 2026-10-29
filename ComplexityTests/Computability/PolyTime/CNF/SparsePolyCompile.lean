/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.PolyTime.CNF.SparsePolyCompile

/-! Tests for sparse `𝔽₂` CNF parity-check compilation and heavy-variable restriction. -/

namespace ComplexityTests.SparsePolyCompile

open Cslib.Complexity Cslib.Logic.PL Cslib.BitString Turing.MultiTapeTM

/-! ### 1. Clause compilation: empty, tautological, and duplicate-literal clauses -/

/-- An empty clause compiles to `[[]]` (constant `1` over `𝔽₂`). -/
example : compileClause ([] : Clause ℕ) = [[]] := rfl

/-- A tautological clause `(x₁ ∨ ¬x₁ ∨ x₃)` compiles to `[]` (`0` over `𝔽₂`). -/
def tautClause : Clause ℕ := [(1, true), (1, false), (3, true)]

example : isTautologicalClause tautClause = true := rfl
example : compileClause tautClause = [] := rfl
example (σ : ℕ → Bool) : evalMonomialList (compileClause tautClause) σ = false := rfl
example (σ : ℕ → Bool) : tautClause.eval σ = true := by
  have h := evalMonomialList_compileClause tautClause σ
  cases h₂ : tautClause.eval σ
  · rw [h₂] at h; cases h
  · rfl

/-- Duplicate positive and negative literals are deduplicated and sorted canonically:
`(x₃ ∨ ¬x₁ ∨ x₃ ∨ ¬x₁ ∨ x₀)` has falsification polynomial `x₁ (1 ⊕ x₀) (1 ⊕ x₃)`. -/
def dupClause : Clause ℕ := [(3, true), (1, false), (3, true), (1, false), (0, true)]

example : compileClause dupClause = [[1], [0, 1], [1, 3], [0, 1, 3]] := rfl
example : compileClauseBounded 5 dupClause = compileClause dupClause := rfl
example : compileClauseBounded 2 dupClause ≠ compileClause dupClause := by decide

/-- Check concrete evaluation on a falsifying assignment (`x₀ = false, x₁ = true, x₃ = false`)
and a satisfying assignment (`x₀ = true, x₁ = true, x₃ = false`). -/
example : evalMonomialList (compileClause dupClause) (fun v => v == 1) = true ∧
    dupClause.eval (fun v => v == 1) = false := ⟨rfl, rfl⟩
example : evalMonomialList (compileClause dupClause) (fun v => v == 0 || v == 1) = false ∧
    dupClause.eval (fun v => v == 0 || v == 1) = true := ⟨rfl, rfl⟩

/-! ### 2. Mod-2 cancellation across clauses in `compileParityRow` -/

/-- `c₀ = (¬x₁)` falsifies as `x₁`; `c₁ = (x₂ ∨ ¬x₁)` falsifies as `x₁ ⊕ x₁ x₂`.
Their XOR along `row = [true, true]` cancels `[1]` modulo 2, leaving `[[1, 2]]`. -/
def sampleCNF : CNF ℕ := [[(1, false)], [(2, true), (1, false)], tautClause]

example : compileParityRow sampleCNF [true, true, true] = [[1, 2]] := rfl
example : compileParityRowBounded 3 sampleCNF [true, true, true] = [[1, 2]] := rfl
example : evalSystem (compileParitySystem sampleCNF [[true, true, false]])
    (fun v => v == 1 || v == 2) = false := rfl
example : evalSystem (compileParitySystem sampleCNF [[true, true, false]])
    (fun v => v == 1) = true := rfl

/-! ### 3. Heavy-variable detection and restriction with mod-2 cancellation -/

/-- Restricting `x₁ x₂ ⊕ x₂` (`[[1, 2], [2]]`) at `x₁ = true` triggers mod-2 cancellation
`[2] ⊕ [2] = 0` (`[]`), while restricting at `x₁ = false` drops `[1, 2]` and leaves `[[2]]`. -/
def cancelEq : List (List ℕ) := [[1, 2], [2]]

example : restrictEquation 1 true cancelEq = [] := rfl
example : restrictEquation 1 false cancelEq = [[2]] := rfl

/-- Concrete 3-equation system on `n = 4` variables where `x₁` appears in all 3 scopes (`> b₀ = 2`),
while every other variable appears in at most 1 scope. -/
def heavySys : List (List (List ℕ)) := [cancelEq, [[0, 1]], [[1, 3]]]

example : (varDegree 0 heavySys, varDegree 1 heavySys, varDegree 2 heavySys, varDegree 3 heavySys) =
    (1, 3, 1, 1) := rfl
example : findHeavyVar 4 2 heavySys = some 1 := rfl
example : restrictSystem 1 true heavySys = [[], [[0]], [[3]]] := rfl
example : varDegree 1 (restrictSystem 1 true heavySys) = 0 := rfl
example : findHeavyVar 4 2 (restrictSystem 1 true heavySys) = none := rfl

/-! ### 4. Plain `ComputableInPolyTime` `fun_prop` pipeline compositions -/

/-- Compiling a bounded-width parity system and immediately restricting a variable composes cleanly
via `fun_prop` on the plain `ComputableInPolyTime` surface. -/
example : ComputableInPolyTime
    (fun x : (ℕ × Bool) × (CNF ℕ × List (List Bool)) =>
      restrictSystem x.1.1 x.1.2 (compileParitySystemBounded 3 x.2.1 x.2.2))
    (encPair (encPair encNat encBool) (encPair encCNF (encList encBits)))
    (encList (encList (encList encNat))) := by fun_prop

/-- Restricting a variable and then querying `findHeavyVar` composes cleanly via `fun_prop`. -/
example : ComputableInPolyTime
    (fun x : (ℕ × ℕ) × ((ℕ × Bool) × List (List (List ℕ))) =>
      findHeavyVar x.1.1 x.1.2 (restrictSystem x.2.1.1 x.2.1.2 x.2.2))
    (encPair (encPair encUnary encNat)
      (encPair (encPair encNat encBool) (encList (encList (encList encNat)))))
    (encOption encNat) := by fun_prop

/-- XORing two compiled parity-check rows on the same CNF composes cleanly via `fun_prop`. -/
example : ComputableInPolyTime
    (fun x : CNF ℕ × (List Bool × List Bool) =>
      xorEquation (compileParityRowBounded 3 x.1 x.2.1)
        (compileParityRowBounded 3 x.1 x.2.2))
    (encPair encCNF (encPair encBits encBits))
    (encList (encList encNat)) := by fun_prop

end ComplexityTests.SparsePolyCompile
