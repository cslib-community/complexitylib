/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

module
-- upstream: local-only (independent comparator statements)

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Independent polynomial-time contracts for two bitstring algorithms

These definitions use only upstream CSLib machine semantics and polynomial growth. The
algorithms and encodings are stated here without importing complexitylib's efficiency predicate,
Goldreich-Levin definitions or tactics. A machine and its bounds are fixed before its input.
-/

@[expose] public section

namespace ComplexityComparator.Automation

/-- A word is represented by its own bits. -/
def wordEncoding : List Bool ↪ List Bool := Function.Embedding.refl _

/-- A Boolean output is represented by exactly one bit. -/
def bitEncoding : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => List.head_eq_of_cons_eq h⟩

/-- One finite-state binary multi-tape machine computes the function within polynomial bounds
on time and work space, measured in the encoded input length. -/
def PolynomialTime {α β : Type} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ∃ t s : Nat → Nat, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f input output t s

/-- Apply an efficient function to the first half, retaining the remainder,
at every input length. -/
def PaddedFunction : Prop :=
  ∀ (f : List Bool → List Bool), PolynomialTime f wordEncoding wordEncoding →
    PolynomialTime
      (fun seed : List Bool =>
        let half := seed.length / 2
        f (seed.take half) ++ seed.drop half)
      wordEncoding wordEncoding

/-- Compute the inner product of two equal halves, ignoring an odd trailing bit. -/
def DotProductHalves : Prop :=
  PolynomialTime
    (fun seed : List Bool =>
      let half := seed.length / 2
      ((seed.take half).zipWith Bool.and ((seed.drop half).take half)).foldl Bool.xor false)
    wordEncoding bitEncoding

end ComplexityComparator.Automation
