/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Circuit.Boolean.BarringtonClass

/-! # Bridge for the width-five characterization of NC¹ -/

namespace ComplexityTests.Abstracts.BarringtonBridge

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
      (∀ x, L.slice n x = true ↔ P.eval x ∈ accept) ∧ P.toList.length ≤ size n

/-- Unfold the two class definitions, retaining the same circuit and program witnesses. -/
theorem barrington (L : Language Bool) : InNC1 L ↔ HasWidthFivePrograms L := by
  have h := Set.ext_iff.mp Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five L
  simpa only [Cslib.Circuits.Boolean.NC, Cslib.Circuits.Boolean.PolylogDepth,
    Cslib.Circuits.Boolean.DepthClass, Cslib.BranchingPrograms.PolyLength, pow_one,
    Set.mem_ofPred_eq, Cslib.BranchingPrograms.MonoidProgram.Decides, InNC1,
    HasWidthFivePrograms, Cslib.Circuits.single] using h

end ComplexityTests.Abstracts.BarringtonBridge
