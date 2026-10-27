/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.ParityTests
public import Complexity.Logics.Propositional.CNF

/-!
# Parity tests for CNF formulas

The violation vector of an assignment `σ` to a formula `φ` with `m` clauses is the bit string of
length `m` whose bit `e` records whether `σ` falsifies clause `e` (`Cslib.Logic.PL.CNF.violations`).
It is zero exactly when `σ` satisfies `φ` (`Cslib.Logic.PL.CNF.violations_eq_zero_iff`).

The rows of a matrix over `𝔽₂` with `m` columns each test the parity of the violations of a set of
clauses; every satisfying assignment passes every row. The greedy selection of parity tests
(`Cslib.BitString.numPassing_greedy`) therefore yields [OpenAI2026ETH, Lemma 6.2]: if after the
initial rows every passing nonsatisfying assignment violates at least `m / P` clauses, then `3 n`
greedily chosen rows, `n` the number of variables, are passed exactly by the satisfying
assignments (`Cslib.Logic.PL.CNF.numPassing_greedy`). The initial rows are the subject of
[OpenAI2026ETH, Lemma 6.1], not proved here.

## Main definitions

* `Cslib.Logic.PL.CNF.violations`: the violation vector of an assignment.

## Main results

* `Cslib.Logic.PL.CNF.violations_eq_zero_iff`: the violation vector is zero exactly on
  satisfying assignments.
* `Cslib.Logic.PL.CNF.numPassing_greedy`: after `3 n` greedy rounds the rows accept exactly the
  satisfying assignments.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Cslib.BitString

variable {V : Type*}

/-- The violation vector of the assignment `σ`: bit `e` is `true` when `σ` falsifies clause `e`
of `φ`. -/
def CNF.violations (φ : CNF V) (σ : V → Bool) : Fin φ.length → Bool :=
  fun e => !(φ.get e).eval σ

/-- The violation vector is zero exactly when the assignment satisfies the formula. -/
theorem CNF.violations_eq_zero_iff (φ : CNF V) (σ : V → Bool) :
    φ.violations σ = 0 ↔ φ.eval σ = true := by
  rw [funext_iff, CNF.eval, List.all_eq_true]
  simp only [CNF.violations, Pi.zero_apply]
  constructor
  · intro h c hc
    obtain ⟨e, rfl⟩ := List.get_of_mem hc
    simpa [show (0 : Bool) = false from rfl] using h e
  · intro h e
    simpa [show (0 : Bool) = false from rfl] using h _ (List.get_mem φ e)

/-- **Greedy parity tests for a CNF formula** [OpenAI2026ETH, Lemma 6.2]. Suppose that after the
initial rows `A 0` every passing nonsatisfying assignment violates at least `m / P` of the `m`
clauses of `φ`, and that `φ` has `n ≥ 1` variables. Append rows
`A (i + 1) = A i ++ [testRow (γ i)]`, where each list `γ i` minimizes the number of passing
assignments among all lists of length `P`. After `3 n` rounds, the passing assignments are exactly
the satisfying ones. -/
theorem CNF.numPassing_greedy [Fintype V] [DecidableEq V] (φ : CNF V) {P : ℕ}
    (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P) (A : ℕ → List (Fin φ.length → Bool))
    (hinit : ∀ σ, PassesTests φ.violations (A 0) σ → φ.eval σ = false →
      φ.length ≤ P * weight (φ.violations σ))
    (γ : ℕ → Fin P → Fin φ.length × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (hγ : ∀ i (γ' : Fin P → Fin φ.length × Bool),
      numPassing φ.violations (A i ++ [testRow (γ i)]) ≤
        numPassing φ.violations (A i ++ [testRow γ'])) :
    numPassing φ.violations (A (3 * Fintype.card V)) = #{σ : V → Bool | φ.eval σ = true} := by
  rw [Cslib.BitString.numPassing_greedy φ.violations hn (by simp) hP A
    (fun σ hσ h0 => hinit σ hσ (by simpa [CNF.violations_eq_zero_iff] using h0)) γ hA hγ]
  simp only [CNF.violations_eq_zero_iff]

end Cslib.Logic.PL
