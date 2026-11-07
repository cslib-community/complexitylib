/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (project scaffolding for the PV representation exploration)

public import Complexity.Logics.FirstOrder.Basic

/-!
# Three views of an equational statement

Following Oliver Korten's input in issue #2736, this experiment compares an equation with named
sides, its open first-order formula, and its universally closed sentence. Mathlib supplies terms,
substitution, formulas, and semantics; `Cslib.Logic.FO.closeAll` supplies universal closure.

The example is the `i = 1` defining equation `TR(s₁(x)) = x` in [Cook1975], §2, p. 86. Its one
variable ranges over natural numbers, with Cook's dyadic successor `s₁(x) = 2 * x + 1` and trim
`TR(x) = (x - 1) / 2` (natural subtraction). These are only two symbols from Cook's signature.
The generic `Equation` is not a definition of PV: there is no function-admission mechanism,
collection of defining equations, induction rule, proof predicate, or proof generator here.
Universal closure is a presentation in first-order logic, not an extra PV inference rule.

## Main definitions

* `ComplexityTests.BoundedArithmetic.Equation`: named sides with an explicit number of variables.
* `ComplexityTests.BoundedArithmetic.Equation.toFormula`: the open equality formula.
* `ComplexityTests.BoundedArithmetic.Equation.toSentence`: its universal closure.
* `ComplexityTests.BoundedArithmetic.Trim.trimS1`: the same example in all three views.

## References

* [Stephen A. Cook, *Feasibly Constructive Proofs and the Propositional Calculus*][Cook1975]
-/

public section

open FirstOrder Language

namespace ComplexityTests.BoundedArithmetic

/-- An equational statement with exactly `n` available free-variable names. -/
structure Equation (L : Language) (n : ℕ) where
  /-- The term on the left of the equality. -/
  lhs : L.Term (Fin n)
  /-- The term on the right of the equality. -/
  rhs : L.Term (Fin n)

namespace Equation

variable {L : Language} {n : ℕ}

instance [∀ k, DecidableEq (L.Functions k)] : DecidableEq (Equation L n) :=
  fun ⟨l₁, r₁⟩ ⟨l₂, r₂⟩ => decidable_of_iff (l₁ = l₂ ∧ r₁ = r₂) (by simp)

/-- Read the two sides as an open first-order equality. -/
@[expose] def toFormula (e : Equation L n) : L.Formula (Fin n) :=
  e.lhs.equal e.rhs

/-- Close all available variables; even unused variables are quantified. -/
@[expose] noncomputable def toSentence (e : Equation L n) : L.Sentence :=
  Cslib.Logic.FO.closeAll (Fin n) e.toFormula

/-- Open-formula semantics is equality of the evaluated sides. -/
theorem realize_toFormula {M : Type*} [L.Structure M] (e : Equation L n) (v : Fin n → M) :
    e.toFormula.Realize v ↔ e.lhs.realize v = e.rhs.realize v :=
  Formula.realize_equal

/-- Closing an equation makes the assignment universally quantified. -/
theorem realize_toSentence {M : Type*} [L.Structure M] (e : Equation L n) :
    e.toSentence.Realize M ↔ ∀ v : Fin n → M, e.lhs.realize v = e.rhs.realize v := by
  simp only [toSentence, Cslib.Logic.FO.realize_closeAll, realize_toFormula]

end Equation

namespace Trim

-- The generated equality procedure must reduce in imported certificate checkers.
@[expose] section

/-- Only the two unary symbols needed for the statement experiment. -/
inductive FunctionSymbol : ℕ → Type
  | s1 : FunctionSymbol 1
  | trim : FunctionSymbol 1
  deriving DecidableEq

end

/-- An arity-indexed fragment, with no relation symbols. It is not the PV language. -/
@[expose] def language : Language where
  Functions := FunctionSymbol
  Relations _ := Empty

instance (k : ℕ) : DecidableEq (language.Functions k) :=
  inferInstanceAs (DecidableEq (FunctionSymbol k))

/-- Apply the dyadic-successor symbol to a term. -/
@[expose] def s1 {n : ℕ} (t : language.Term (Fin n)) : language.Term (Fin n) :=
  .func .s1 fun _ => t

/-- Apply the trim symbol to a term. -/
@[expose] def trim {n : ℕ} (t : language.Term (Fin n)) : language.Term (Fin n) :=
  .func .trim fun _ => t

/-- Cook's equation `TR(s₁(x)) = x`, with `x` named by the sole element of `Fin 1`. -/
@[expose] def trimS1 : Equation language 1 where
  lhs := trim (s1 (.var 0))
  rhs := .var 0

/-- The intended natural-number interpretation of the two symbols, in dyadic notation. -/
instance : language.Structure ℕ where
  funMap
    | .s1, v => 2 * v 0 + 1
    | .trim, v => (v 0 - 1) / 2
  RelMap r := nomatch r

-- Named sides, the open formula, and the closed sentence all retain the same equation.
example : trimS1.lhs = trim (s1 (.var 0)) ∧ trimS1.rhs = .var 0 := ⟨rfl, rfl⟩

example : trimS1.toFormula = (trim (s1 (.var 0))).equal (.var 0) := rfl

example (v : Fin 1 → ℕ) :
    trimS1.toFormula.Realize v ↔ (2 * v 0 + 1 - 1) / 2 = v 0 := Iff.rfl

example : trimS1.toSentence.Realize ℕ ↔ ∀ x : ℕ, (2 * x + 1 - 1) / 2 = x := by
  rw [Equation.realize_toSentence]
  exact ⟨fun h x => h (fun _ => x), fun h v => h (v 0)⟩

example : trimS1.toSentence.Realize ℕ := by
  rw [Equation.realize_toSentence]
  intro v
  change (2 * v 0 + 1 - 1) / 2 = v 0
  simp

-- Substitution can both change the term and enlarge its available variable context.
example : trimS1.lhs.subst (fun _ => s1 (.var 1 : language.Term (Fin 2))) =
    trim (s1 (s1 (.var 1))) := rfl

example (v : Fin 2 → ℕ) :
    (trimS1.lhs.subst (fun _ => s1 (.var 1))).realize v = 2 * v 1 + 1 := by
  change (2 * (2 * v 1 + 1) + 1 - 1) / 2 = 2 * v 1 + 1
  simp

-- The arity index rules out a binary use of either of these symbols.
example (f : FunctionSymbol 2) : False := nomatch f

-- Replacing the right side by s₁(x) changes the claim, and x = 0 refutes it.
private def wrongEquation : Equation language 1 where
  lhs := trimS1.lhs
  rhs := s1 (.var 0)

example : ¬ wrongEquation.toSentence.Realize ℕ := by
  rw [Equation.realize_toSentence]
  intro h
  have h0 := h (fun _ => 0)
  change 0 = 1 at h0
  exact Nat.zero_ne_one h0

end Trim

end ComplexityTests.BoundedArithmetic
