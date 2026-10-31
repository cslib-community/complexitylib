/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Routines
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness

/-!
# Fair-coin transition counts on compact configuration IDs

The nondeterministic compact graph records whether an edge exists. A fair-coin transition needs
its multiplicity: two coincident branches still contribute two. `coinCountWithSymbol` adds the
edge tests for the two fixed-coin machines. Each test reads the same supplied input symbol and
uses the existing guarded radix arithmetic. Halting views are absorbing for this count;
`liveCoinCountWithSymbol` instead gives them zero rows.

The native space certificates charge the binary radix, input length, source and target IDs and
one supplied symbol. The input itself is accessed only at `queryIndex`. The matrix interpretation
is supplied in `Classes.LogSpace.Randomized.ConfigurationReader`.

## Main definitions

* `Turing.MultiTapePTM.ConfigurationGraph.coinCountWithSymbol`: the sum of the two coin edges.
* `Turing.MultiTapePTM.ConfigurationGraph.liveCoinCountWithSymbol`: the count at running IDs.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.coinCountWithSymbol_le_two`: every count is at most two.
* `Turing.MultiTapePTM.ConfigurationGraph.coinCountWithSymbol_budget`,
  `Turing.MultiTapePTM.ConfigurationGraph.liveCoinCountWithSymbol_budget`: native space bounds.

This is a local implementation of the fair-coin configuration matrix, not an enumeration of its
vertices or a time-layered matrix construction. It adds no estimator or derandomization claim.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph
open Cslib.Turing MultiTapeTM ComputableInSpace

variable {k : ℕ} {State : Type} [Fintype State]

/-- The two fixed-coin edge predicates, counted separately even when their successors coincide.
The compact graph guards invalid IDs and successor overflow; its halted vertices are absorbing. -/
@[expose] noncomputable def coinCountWithSymbol (machine : MultiTapePTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) : ℕ :=
  (edgeWithSymbol (machine.withCoin false).toTM.toMultiTapeNTM B n u v symbol).toNat +
    (edgeWithSymbol (machine.withCoin true).toTM.toMultiTapeNTM B n u v symbol).toNat

/-- The live transition count: rows whose control tag is halted are zero. -/
@[expose] noncomputable def liveCoinCountWithSymbol (machine : MultiTapePTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) : ℕ :=
  if readRegisters (k := k) B u .control = stateCode (none : Option State) then 0
  else coinCountWithSymbol machine B n u v symbol

/-- There are exactly two possible coin values, so the multiplicity is at most two. -/
theorem coinCountWithSymbol_le_two (machine : MultiTapePTM k Bool State)
    (B n u v : ℕ) (symbol : Option Bool) :
    coinCountWithSymbol machine B n u v symbol ≤ 2 := by
  unfold coinCountWithSymbol
  cases edgeWithSymbol (machine.withCoin false).toTM.toMultiTapeNTM B n u v symbol <;>
    cases edgeWithSymbol (machine.withCoin true).toTM.toMultiTapeNTM B n u v symbol <;> decide

/-- An ID outside the bounded radix box has no outgoing coin edge. -/
theorem coinCountWithSymbol_eq_zero_of_source_ge (machine : MultiTapePTM k Bool State)
    {B n u v : ℕ} (hu : vertexBound (k := k) B ≤ u) (symbol : Option Bool) :
    coinCountWithSymbol machine B n u v symbol = 0 := by
  have h (bit : Bool) :
      edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B n u v symbol = false := by
    cases he : edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B n u v symbol with
    | false => rfl
    | true => exact False.elim ((not_lt_of_ge hu) (lt_vertexBound_of_edgeWithSymbol he).1)
  simp [coinCountWithSymbol, h]

/-- An ID outside the bounded radix box cannot be the target of a coin edge. -/
theorem coinCountWithSymbol_eq_zero_of_target_ge (machine : MultiTapePTM k Bool State)
    {B n u v : ℕ} (hv : vertexBound (k := k) B ≤ v) (symbol : Option Bool) :
    coinCountWithSymbol machine B n u v symbol = 0 := by
  have h (bit : Bool) :
      edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B n u v symbol = false := by
    cases he : edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B n u v symbol with
    | false => rfl
    | true => exact False.elim ((not_lt_of_ge hv) (lt_vertexBound_of_edgeWithSymbol he).2)
  simp [coinCountWithSymbol, h]

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
  {B n u v : α → ℕ} {symbol : α → Option Bool}

/-- Count the two coin branches within any common native space budget for the short arguments. -/
theorem coinCountWithSymbol_budget (machine : MultiTapePTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => coinCountWithSymbol machine (B a) (n a) (u a) (v a) (symbol a))
      enc encNat S :=
  budget_natAdd
    (budget_finite Bool.toNat
      (edgeWithSymbol_budget (machine.withCoin false).toTM.toMultiTapeNTM hB hn hu hv hs hin))
    (budget_finite Bool.toNat
      (edgeWithSymbol_budget (machine.withCoin true).toTM.toMultiTapeNTM hB hn hu hv hs hin))

/-- Zeroing the halted rows preserves the same native space budget. -/
theorem liveCoinCountWithSymbol_budget (machine : MultiTapePTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace
      (fun a => liveCoinCountWithSymbol machine (B a) (n a) (u a) (v a) (symbol a))
      enc encNat S := by
  have hc : ComputableInSpace (fun a => readRegisters (k := k) (B a) (u a) .control)
      enc encNat S :=
    budget_comp_linear (component_inSpace (Register.control : Register k)) (budget_prod hB hu)
  simpa only [liveCoinCountWithSymbol, decide_eq_true_eq] using
    budget_ite (budget_natEq hc (budget_const (stateCode (none : Option State)) hin))
      (budget_const 0 hin) (coinCountWithSymbol_budget machine hB hn hu hv hs hin)

end Turing.MultiTapePTM.ConfigurationGraph
