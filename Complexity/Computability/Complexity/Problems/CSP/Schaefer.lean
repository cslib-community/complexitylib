/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.Constant
public import Complexity.Computability.Complexity.Problems.CSP.Majority
public import Complexity.Computability.Complexity.Problems.CSP.Horn
public import Complexity.Computability.Complexity.Problems.CSP.Affine
public import Complexity.Computability.Complexity.Problems.CSP.Hardness

/-!
# Boolean Schaefer dichotomy

For every fixed finite Boolean constraint language of arbitrary fixed relation arities, its
exact-arity satisfiability problem is in native P when a common unary constant, AND, OR, ternary
majority or ternary parity preserves the language, and is native NP-complete otherwise.
All solvers, fixed-template compilers, clone classification, gadgets and hardness reductions
are proved in the imported stack. Variable labels are binary; malformed scopes are rejected.
Empty and nullary relations are allowed. No uniform bound on language preprocessing is claimed.

This is [Chen2006CSP], Theorem 3.20 (arXiv v1, p. 12), with explicit binary instance encoding
and an extension allowing empty/nullary relations under standard unary constant operations.
No separation assumption between P and NP is used.

## Main results

* `Cslib.Complexity.CSPSAT.mem_P_of_hasSchaeferPolymorphism`: all six tractable cases.
* `Cslib.Complexity.CSPSAT.schaefer_dichotomy`: the full criterion-based Boolean dichotomy.
* `Cslib.Complexity.CSPSAT.mem_P_or_npComplete`: its unconditional P-or-NP-complete corollary.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

/-- All six common-polymorphism cases have native polynomial-time decision procedures. -/
theorem mem_P_of_hasSchaeferPolymorphism [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : CSP.HasSchaeferPolymorphism arity sem) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  rcases h with h | h | h | h | h | h
  · exact mem_P_of_constant encRel arity sem false h
  · exact mem_P_of_constant encRel arity sem true h
  · exact mem_P_of_and encRel arity sem h
  · exact mem_P_of_or encRel arity sem h
  · exact mem_P_of_majority encRel arity sem h
  · exact mem_P_of_parity encRel arity sem h

/-- **The full Boolean Schaefer dichotomy.** The six common operations give native P;
otherwise the exact-arity CSP is native NP-complete under its explicit binary encoding. -/
theorem schaefer_dichotomy [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    (CSP.HasSchaeferPolymorphism arity sem →
      CSPSAT arity sem ∈ P (encCSP encRel encNat)) ∧
    (¬ CSP.HasSchaeferPolymorphism arity sem →
      NPComplete (encCSP encRel encNat) (CSPSAT arity sem)) :=
  ⟨mem_P_of_hasSchaeferPolymorphism encRel arity sem,
    npComplete_of_not_hasSchaeferPolymorphism encRel arity sem⟩

/-- Each fixed finite Boolean CSP is in native P or is native NP-complete, without assuming
these complexity classes differ. `schaefer_dichotomy` supplies the explicit operation criterion. -/
theorem mem_P_or_npComplete [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) ∨
      NPComplete (encCSP encRel encNat) (CSPSAT arity sem) := by
  classical
  by_cases h : CSP.HasSchaeferPolymorphism arity sem
  · exact Or.inl (mem_P_of_hasSchaeferPolymorphism encRel arity sem h)
  · exact Or.inr (npComplete_of_not_hasSchaeferPolymorphism encRel arity sem h)

end Cslib.Complexity.CSPSAT
