/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Value Queries for Set-Function Optimization

`ValueQuery α β` is the query signature for algorithms that access an unknown set function
`f : Finset α → β` through a value oracle ([NemhauserWolsey1978], Section 2): a query
`ValueQuery.value S` asks for the value `f S : β` of a finite subset `S : Finset α`.

In addition to the standard `ask` and `oracleOf` combinators, this module defines
`ValueQuery.queriedSets`, which records the exact `Finset (Finset α)` of subsets inspected along an
execution path, and proves the path-indistinguishability lemma
`ValueQuery.eval_eq_of_agree_on_queriedSets` used in adversarial value-oracle lower bounds.

## Main definitions

* `Cslib.Query.ValueQuery`: query functor with single operation `.value (S : Finset α)`.
* `Cslib.Query.ValueQuery.ask`: lift a subset query into `FreeM (ValueQuery α β) β`.
* `Cslib.Query.ValueQuery.oracleOf`: interpret `f : Finset α → β` as a `ValueQuery` oracle.
* `Cslib.Query.ValueQuery.queriedSets`: finite set of subsets queried along an oracle path.

## Main results

* `ValueQuery.card_queriedSets_le_countQueries`:
  `(queriedSets oracle p).card ≤ p.countQueries oracle`.
* `ValueQuery.eval_and_countQueries_eq_of_agree_on_queriedSets`,
  `ValueQuery.eval_eq_of_agree_on_queriedSets`: two oracles agreeing on all sets in
  `queriedSets o₁ p` induce identical `eval` outputs and `countQueries` counts.

## References

* [NemhauserWolsey1978] George L. Nemhauser and Laurence A. Wolsey,
  *Best Algorithms for Approximating the Maximum of a Submodular Set Function*, 1978.
-/

public section

namespace Cslib.Query

/-- Value-oracle query signature for set functions `Finset α → β`: `.value S` requests `f S : β`. -/
inductive ValueQuery (α β : Type) : Type → Type where
  | value (S : Finset α) : ValueQuery α β β

/-- Query the value of subset `S` in `FreeM (ValueQuery α β) β`. -/
abbrev ValueQuery.ask {α β : Type} (S : Finset α) : FreeM (ValueQuery α β) β :=
  FreeM.lift (.value S)

@[simp] theorem ValueQuery.eval_ask {α β : Type}
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (S : Finset α) :
    (ValueQuery.ask S).eval oracle = oracle (.value S) := rfl

theorem ValueQuery.countQueries_ask {α β : Type}
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (S : Finset α) :
    (ValueQuery.ask S).countQueries oracle = 1 :=
  FreeM.countQueries_lift oracle (.value S)

/-- Turn a set function `f : Finset α → β` into a `ValueQuery α β` oracle. -/
@[expose] def ValueQuery.oracleOf {α β : Type} (f : Finset α → β) :
    {ι : Type} → ValueQuery α β ι → ι
  | _, .value S => f S

@[simp] theorem ValueQuery.oracleOf_value {α β : Type} (f : Finset α → β) (S : Finset α) :
    ValueQuery.oracleOf f (.value S) = f S := rfl

/-- The finite set of subsets queried along the execution path of `p` against `oracle`. -/
@[expose] def ValueQuery.queriedSets {α β γ : Type} [DecidableEq α]
    (oracle : {ι : Type} → ValueQuery α β ι → ι) :
    FreeM (ValueQuery α β) γ → Finset (Finset α)
  | .pure _ => ∅
  | .liftBind (.value S) cont =>
      insert S (ValueQuery.queriedSets oracle (cont (oracle (.value S))))

@[simp] theorem ValueQuery.queriedSets_pure {α β γ : Type} [DecidableEq α]
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (a : γ) :
    ValueQuery.queriedSets oracle (pure a : FreeM (ValueQuery α β) γ) = ∅ := rfl

@[simp] theorem ValueQuery.queriedSets_liftBind {α β γ : Type} [DecidableEq α]
    (oracle : {ι : Type} → ValueQuery α β ι → ι)
    (S : Finset α) (cont : β → FreeM (ValueQuery α β) γ) :
    ValueQuery.queriedSets oracle (FreeM.lift (.value S) >>= cont) =
      insert S (ValueQuery.queriedSets oracle (cont (oracle (.value S)))) := rfl

/-- The number of distinct subsets queried never exceeds the total query count. -/
theorem ValueQuery.card_queriedSets_le_countQueries {α β γ : Type} [DecidableEq α]
    (oracle : {ι : Type} → ValueQuery α β ι → ι)
    (p : FreeM (ValueQuery α β) γ) :
    (ValueQuery.queriedSets oracle p).card ≤ p.countQueries oracle := by
  induction p with
  | pure _ => simp
  | lift_bind op cont ih =>
    cases op with
    | value S =>
      simp only [FreeM.bind_eq_bind, ValueQuery.queriedSets_liftBind, FreeM.countQueries_liftBind]
      exact (Finset.card_insert_le S _).trans (by have := ih (oracle (.value S)); omega)

/-- If two oracles return identical values on every subset in `ValueQuery.queriedSets o₁ p`, then
`p` follows the exact same execution branch under both oracles and produces the same output and
query count. -/
theorem ValueQuery.eval_and_countQueries_eq_of_agree_on_queriedSets {α β γ : Type} [DecidableEq α]
    {o₁ o₂ : {ι : Type} → ValueQuery α β ι → ι}
    (p : FreeM (ValueQuery α β) γ)
    (hagree : ∀ S ∈ ValueQuery.queriedSets o₁ p, o₁ (.value S) = o₂ (.value S)) :
    p.eval o₁ = p.eval o₂ ∧ p.countQueries o₁ = p.countQueries o₂ := by
  induction p with
  | pure a => simp
  | lift_bind op cont ih =>
    cases op with
    | value S =>
      simp only [FreeM.bind_eq_bind, ValueQuery.queriedSets_liftBind] at hagree
      have hS : o₁ (.value S) = o₂ (.value S) :=
        hagree S (Finset.mem_insert_self S _)
      have hcont : ∀ T ∈ ValueQuery.queriedSets o₁ (cont (o₁ (.value S))),
          o₁ (.value T) = o₂ (.value T) :=
        fun T hT => hagree T (Finset.mem_insert_of_mem hT)
      rcases ih (o₁ (.value S)) hcont with ⟨heval, hcount⟩
      simp only [FreeM.bind_eq_bind, FreeM.eval_liftBind, FreeM.countQueries_liftBind]
      rw [← hS]
      exact ⟨heval, congrArg (1 + ·) hcount⟩

theorem ValueQuery.eval_eq_of_agree_on_queriedSets {α β γ : Type} [DecidableEq α]
    {o₁ o₂ : {ι : Type} → ValueQuery α β ι → ι}
    (p : FreeM (ValueQuery α β) γ)
    (hagree : ∀ S ∈ ValueQuery.queriedSets o₁ p, o₁ (.value S) = o₂ (.value S)) :
    p.eval o₁ = p.eval o₂ :=
  (ValueQuery.eval_and_countQueries_eq_of_agree_on_queriedSets p hagree).1

end Cslib.Query
