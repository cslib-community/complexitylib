/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.CoinTape.Bounds

/-!
# Coin-tape realizations on a bounded domain

A coin-tape realization of a typed program on a domain of inputs is a deterministic
polynomial-time evaluator together with a coin budget for each input. On every input in the
domain, running the evaluator on a uniform tape of that budget yields exactly the program's
distribution, and every supported encoded output fits the same budget. Reductions that
compose several strict-PPT stages state one such record per stage instead of spelling out the
evaluator, its certificate, its replay law and its output bound separately.

## Main definitions

* `Cslib.Probability.CoinTapeRealization`: a polynomial-time evaluator with exact replay and an
  output-length bound on a domain, for a given per-input coin budget.

## Main results

* `Cslib.Probability.IsPPTOn.exists_coinTapeRealization`: a strict-PPT program has one
  polynomial envelope in its encoded input length such that every domain and budget meeting
  the envelope admit a realization.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- `program` is realized on `domain` from `budget a` uniform coins. The evaluator is one
polynomial-time word program on all inputs and tapes, including inputs outside `domain`. On
`domain`, it replays `program` exactly from a uniform tape of length `budget a`, and every
supported encoded output has length at most `budget a`. -/
structure CoinTapeRealization {α β : Type} (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → ProbComp β) (domain : Set α) (budget : α → ℕ) where
  /-- The deterministic evaluator on an input and a coin tape. -/
  evaluate : α → List Bool → β
  /-- Evaluation is polynomial time on the encoded input and tape. -/
  efficient : ComputableInPolyTime (fun (a, coins) => evaluate a coins)
    (encPair input encBits) output
  /-- On the domain, a uniform tape of the budgeted length replays the program exactly. -/
  eval_eq : ∀ a ∈ domain,
    ProbComp.eval (program a) = (BitString.uniformList (budget a)).map (evaluate a)
  /-- On the domain, every supported encoded output fits the budget. -/
  length_le : ∀ a ∈ domain, ∀ b ∈ (ProbComp.eval (program a)).support,
    (output b).length ≤ budget a

/-- A strict-PPT program has one polynomial envelope `c * (|input a| + 1) ^ d` such that any
domain and budget meeting it on the domain admit a realization. -/
theorem IsPPTOn.exists_coinTapeRealization {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ c d : ℕ, ∀ (domain : Set α) (budget : α → ℕ),
      (∀ a ∈ domain, c * ((input a).length + 1) ^ d ≤ budget a) →
        Nonempty (CoinTapeRealization input output program domain budget) := by
  obtain ⟨c, d, evaluate, hefficient, _, hlaw, hlength⟩ :=
    h.exists_total_seeded_evaluator_with_length
  exact ⟨c, d, fun domain budget hbudget => ⟨{
    evaluate := evaluate
    efficient := hefficient
    eval_eq := fun a ha => hlaw a (budget a) (hbudget a ha)
    length_le := fun a ha b hb => (hlength a b hb).trans (hbudget a ha) }⟩⟩

namespace CoinTapeRealization

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
  {program : α → ProbComp β} {domain : Set α} {budget : α → ℕ}

/-- The replay law and the output bound at one input of the domain. -/
theorem eval_eq_and_length_le (R : CoinTapeRealization input output program domain budget)
    {a : α} (ha : a ∈ domain) :
    ProbComp.eval (program a) = (BitString.uniformList (budget a)).map (R.evaluate a) ∧
      ∀ b ∈ (ProbComp.eval (program a)).support, (output b).length ≤ budget a :=
  ⟨R.eval_eq a ha, R.length_le a ha⟩

end CoinTapeRealization

end Cslib.Probability
