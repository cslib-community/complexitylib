/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import ComplexityAbstracts.SubexponentialSATAbstract
import Complexity.Computability.Complexity.FineGrained
import Complexity.Computability.Complexity.FineGrained.CountingScale
import Complexity.Logics.Propositional.CNF.ModelCount.Declared

/-! # Semantic checks for the pending subexponential SAT abstract

These checks identify the displayed definitions with the existing library interfaces and exercise
declared unused variables, empty cases and invalid inputs. They prove no counting algorithm or
refutation headline. The implementation imports are confined to this test module, outside the
abstract's audited statement surface.
-/

namespace ComplexityTests.Abstracts.SubexponentialSATTests

open ComplexityAbstracts.SubexponentialSATAbstract

example (φ : Formula) (σ : ℕ → Bool) : eval φ σ = Cslib.Logic.PL.CNF.eval σ φ := rfl

example (φ : Formula) : Satisfiable φ ↔ Cslib.Logic.PL.CNF.Satisfiable φ := Iff.rfl

example (φ : Formula) : numVars φ = Cslib.Logic.PL.CNF.numVars φ := rfl

example (φ : Formula) (n : ℕ) :
    modelCountOn φ n = Cslib.Logic.PL.CNF.modelCountOn φ (Finset.range n) := rfl

example (k n : ℕ) (φ : Formula) :
    validDeclaredInput k n φ = Cslib.Logic.PL.CNF.validDeclaredInput k n φ := rfl

example : encCNF = Cslib.Complexity.encCNF := rfl

example : encInput = Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary
    Cslib.Complexity.encCNF := rfl

example {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) :
    DecidableInTimeO A enc T ↔ Cslib.Complexity.DecidableInTimeO A enc T := Iff.rfl

example {α : Type} (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) (δ : ℝ) :
    DecidableInExpTime A enc μ δ ↔ Cslib.Complexity.DecidableInExpTime A enc μ δ := Iff.rfl

example (k : ℕ) : KSAT k = Cslib.Complexity.KSAT k := rfl

example (k : ℕ) : satExponent k = Cslib.Complexity.satExponent k := rfl

example : ETH ↔ Cslib.Complexity.ETH := Iff.rfl

example : SETH ↔ Cslib.Complexity.SETH := Iff.rfl

example (n : ℕ) :
    interpolationScale n = Cslib.Complexity.SubexponentialSAT.interpolationScale n := rfl

-- Empty formulas retain all declared free variables; the empty assignment is counted once.
example : modelCountOn [] 0 = 1 := by decide
example : modelCountOn [] 3 = 8 := by decide

-- An empty clause is unsatisfiable, while a single positive literal leaves two variables free.
example : modelCountOn [[]] 3 = 0 := by decide
example : modelCountOn [[(0, true)]] 3 = 4 := by decide
example : modelCountOn [[(0, true)], [(0, false)]] 3 = 0 := by decide

-- Both halves of validity matter, including repetition in the clause-width convention.
example : validDeclaredInput 0 0 [] = true := by decide
example : validDeclaredInput 0 0 [[]] = true := by decide
example : validDeclaredInput 1 1 [[(0, true)]] = true := by decide
example : validDeclaredInput 1 1 [[(0, true), (0, true)]] = false := by decide
example : validDeclaredInput 1 1 [[(1, true)]] = false := by decide

-- The declared unary header survives even on an empty formula.
example : (encInput (3, [])).length = 7 := by decide
example : numVars [[(100, true), (100, false)]] = 1 := by decide

end ComplexityTests.Abstracts.SubexponentialSATTests
