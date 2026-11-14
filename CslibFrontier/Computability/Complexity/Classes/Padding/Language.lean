/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# The polynomially padded language

The polynomially padded language of `A` with exponent `k`, `Cslib.Complexity.polynomialPadded A k`,
consists of the bit words `x` carrying a word `y = unframe x` of `A` framed at their start, with
`(y.length + 1) ^ k ≤ x.length`. It is the same language for every machine model: the padding
theorems for nondeterministic time
(`CslibFrontier.Computability.Complexity.Classes.Padding.NondeterministicPolynomial`) and for
deterministic space (`CslibFrontier.Computability.Complexity.Classes.Padding.Space`) state their
bounds for it.

## Main definitions

* `Cslib.Complexity.polynomialPadded`: the polynomially padded language.

## Main results

* `Cslib.Complexity.mem_polynomialPadded_iff`: membership of an arbitrary word.
* `Cslib.Complexity.frame_append_replicate_mem_polynomialPadded_iff`: a word padded with at least
  `(|y| + 1) ^ k` ones is in the padded language exactly when `y ∈ A`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The language `A` padded with exponent `k`: the words `x` carrying a word `y = unframe x` of `A`
framed at their start, of length at least `(y.length + 1) ^ k`. -/
def polynomialPadded (A : Set (List Bool)) (k : ℕ) : Set (List Bool) :=
  {x | ((unframe x).length + 1) ^ k ≤ x.length ∧ unframe x ∈ A}

/-- A word is in the padded language when its framed word is in `A` and it is long enough. -/
@[simp]
theorem mem_polynomialPadded_iff {A : Set (List Bool)} {k : ℕ} {x : List Bool} :
    x ∈ polynomialPadded A k ↔ ((unframe x).length + 1) ^ k ≤ x.length ∧ unframe x ∈ A :=
  Iff.rfl

/-- A word `frame y ++ 1^L` with `L ≥ (|y| + 1) ^ k` is in the padded language exactly when
`y ∈ A`. -/
theorem frame_append_replicate_mem_polynomialPadded_iff {A : Set (List Bool)} {k L : ℕ}
    {y : List Bool} (hL : (y.length + 1) ^ k ≤ L) :
    frame y ++ List.replicate L true ∈ polynomialPadded A k ↔ y ∈ A := by
  rw [mem_polynomialPadded_iff, unframe_frame_append, List.length_append, length_frame,
    List.length_replicate]
  exact and_iff_right (by omega)

end Cslib.Complexity
