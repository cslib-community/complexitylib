/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.BarringtonBridge

/-! # Barrington: width-five permutation programs capture NC¹

How much computation can be expressed by repeatedly permuting a set of only five elements?
Each instruction reads one selected input bit and chooses one of two permutations; the program
composes these choices and tests the resulting permutation against an acceptance set.
Barrington's theorem says that polynomial-length programs of this form capture exactly the
languages computed by polynomial-size Boolean circuits of logarithmic depth, the class NC¹.

Both circuit families and program families are nonuniform: a separate object may be chosen at
each input length. The theorem asserts no uniform generator or compiler running-time bound.
The elementary monoid-program model is the only explicitly allowed implementation module;
Lean checks the bridge proof and `#check_abstract` audits the statement boundary.

## References

* [D. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [D. Barrington, D. Thérien, *Finite monoids and the fine structure of NC¹*][BarringtonTherien1988]
-/

namespace ComplexityTests.Abstracts.BarringtonAbstract

/-- A nonuniform NC¹ language has a polynomial-size De Morgan circuit at each input length,
with depth at most a constant times `floor(log₂ n)+1`. Every gate, constants included, costs one.
Here `L : Language Bool` is a set of finite bit strings. `L.slice n x` tests whether the word
`List.ofFn x` belongs to `L`; `single` makes that Boolean the sole circuit output, and `Computes`
requires agreement on every input. -/
def InNC1 (L : Language Bool) : Prop :=
  ∃ (c : ℕ) (size : ℕ → ℕ), Cslib.PolynomiallyBounded size ∧ ∀ n,
    ∃ C : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature n 1,
      C.Computes Cslib.Circuits.Boolean.interpretation
        (Cslib.Circuits.single (L.slice n)) ∧
      C.depth ≤ c * (Nat.log 2 n + 1) ∧ C.size ≤ size n

/-- A width-five permutation program reads one input bit per instruction, selects one of two
permutations, and multiplies the selected permutations in instruction order. The elementary
`MonoidProgram` model is explicitly allowed; it is a list of `(position, selection function)`
instructions. Its length is polynomial. Both the program and the acceptance set may depend on
input length; acceptance tests the entire final permutation. -/
def HasWidthFivePrograms (L : Language Bool) : Prop :=
  ∃ size : ℕ → ℕ, Cslib.PolynomiallyBounded size ∧ ∀ n,
    ∃ (P : Cslib.BranchingPrograms.MonoidProgram (Fin n) Bool (Equiv.Perm (Fin 5)))
      (accept : Set (Equiv.Perm (Fin 5))),
      (∀ x, L.slice n x = true ↔ P.eval x ∈ accept) ∧ P.length ≤ size n

/-- **Barrington.** The same language has logarithmic-depth, polynomial-size De Morgan
circuits if and only if it has polynomial-length permutation programs on five states. -/
theorem barrington (L : Language Bool) : InNC1 L ↔ HasWidthFivePrograms L :=
  BarringtonBridge.barrington L

/-- info: abstract audit passed for `ComplexityTests.Abstracts.BarringtonAbstract`: 3 root
declarations -/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.BarringtonAbstract allowing [
  Complexity.Computability.BranchingProgram.MonoidProgram
]

end ComplexityTests.Abstracts.BarringtonAbstract
