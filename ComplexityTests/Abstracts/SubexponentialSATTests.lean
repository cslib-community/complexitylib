/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import ComplexityAbstracts.SubexponentialSATAbstract
import Complexity.Computability.Complexity.FineGrained
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Complexity.FineGrained.CountingScale
import Complexity.Logics.Propositional.CNF.ModelCount

/-! # Semantic checks for the subexponential SAT abstract

These checks identify the displayed definitions with the existing library interfaces and exercise
empty cases and repeated or non-dense variable labels. They also exercise the exact counter
theorem. The implementation imports stay outside the abstract's audited statement surface.
-/

namespace ComplexityTests.Abstracts.SubexponentialSATTests

open ComplexityAbstracts.SubexponentialSATAbstract

example (φ : Formula) (σ : ℕ → Bool) : eval φ σ = Cslib.Logic.PL.CNF.eval σ φ := rfl

example (φ : Formula) : Satisfiable φ ↔ Cslib.Logic.PL.CNF.Satisfiable φ := Iff.rfl

example (φ : Formula) : vars φ = (Cslib.Logic.PL.CNF.vars φ).toFinset := rfl

example (φ : Formula) : numVars φ = Cslib.Logic.PL.CNF.numVars φ := rfl

example (φ : Formula) : modelCount φ = Cslib.Logic.PL.CNF.modelCount φ := rfl

example (k : ℕ) (φ : Formula) : HasWidth k φ ↔ ∀ c ∈ φ, c.length ≤ k := Iff.rfl

example : encCNF = Cslib.Complexity.encCNF := rfl

example {α β : Type} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (T S : α → ℕ) :
    ComputableInO f encIn encOut T S ↔ Turing.MultiTapeTM.ComputableInO f encIn encOut T S :=
  Iff.rfl

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

-- The empty formula has one satisfying assignment (of no variables); an empty clause has none.
example : modelCount [] = 1 := by decide
example : modelCount [[]] = 0 := by decide

-- The encoding length formula on small inputs: one clause bit plus `10 + 8 · Nat.size v` per
-- literal occurrence.
example : (encCNF [[(2, true)]]).length = 27 := by decide
example : (encCNF [[(0, false)], []]).length = 12 := by decide
example : (encCNF [[(2, true)]]).length = 1 + (10 + 8 * Nat.size 2) := length_encCNF _

-- Variables are counted once each, independent of their labels and repetitions.
example : modelCount [[(0, true)]] = 1 := by decide
example : modelCount [[(5, true), (5, true)], [(9, false)]] = 1 := by decide
example : modelCount [[(0, true), (1, true)]] = 3 := by decide
example : modelCount [[(0, true)], [(0, false)]] = 0 := by decide
example : numVars [[(100, true), (100, false)]] = 1 := by decide

-- One witness counts all these width-`2` inputs exactly.
example : ∃ count : Formula → ℕ,
    count [] = 1 ∧ count [[(7, true), (3, false)]] = 3 ∧
    count [[(0, true)], [(0, false)]] = 0 := by
  obtain ⟨count, _, _, _, hcount, _⟩ := exact_count 2
  refine ⟨count, ?_, ?_, ?_⟩ <;> rw [hcount _ (by simp [HasWidth])] <;> decide

end ComplexityTests.Abstracts.SubexponentialSATTests
