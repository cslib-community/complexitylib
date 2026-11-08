/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.LogSpaceTruthTable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Bounded disjunctive and conjunctive logspace reductions

The indexed disjunctive and conjunctive reductions of `LogSpaceTruthTable`, with an additional
uniform bound on the active count. These are the `k`-dtt and `k`-ctt restrictions of
[LadnerLynchSelman1975], with the logspace and encoding conventions of that module. The bound
means at most `k`, including zero; an empty disjunction is false and an empty conjunction is true.

## Main definitions

* `Cslib.Complexity.LogSpaceKDTTReducible`: at most `k` disjunctive queries.
* `Cslib.Complexity.LogSpaceKCTTReducible`: at most `k` conjunctive queries.

## Main results

* `Cslib.Complexity.LogSpaceKDTTReducible.logSpaceKTruthTableReducible`: evaluate OR.
* `Cslib.Complexity.LogSpaceKCTTReducible.logSpaceKTruthTableReducible`: evaluate AND.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {A : Set α} {B : Set β} {k : ℕ}

/-- Disjunctive reduction with at most `k` active queries, using the existing indexed data. -/
@[expose] def LogSpaceKDTTReducible (k : ℕ) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    (∀ a, r a ≤ k) ∧ ∀ a, a ∈ A ↔ ∃ i < r a, q (a, i) ∈ B

/-- Conjunctive reduction with at most `k` active queries, using the existing indexed data. -/
@[expose] def LogSpaceKCTTReducible (k : ℕ) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    (∀ a, r a ≤ k) ∧ ∀ a, a ∈ A ↔ ∀ i < r a, q (a, i) ∈ B

/-- Forgetting the query bound gives disjunctive reducibility. -/
theorem LogSpaceKDTTReducible.logSpaceDTTReducible (h : LogSpaceKDTTReducible k encA encB A B) :
    LogSpaceDTTReducible encA encB A B :=
  let ⟨r, q, hr, hq, _, hA⟩ := h
  ⟨r, q, hr, hq, hA⟩

/-- Forgetting the query bound gives conjunctive reducibility. -/
theorem LogSpaceKCTTReducible.logSpaceCTTReducible (h : LogSpaceKCTTReducible k encA encB A B) :
    LogSpaceCTTReducible encA encB A B :=
  let ⟨r, q, hr, hq, _, hA⟩ := h
  ⟨r, q, hr, hq, hA⟩

/-- A bounded disjunctive reduction is a truth-table reduction with the same bound. -/
theorem LogSpaceKDTTReducible.logSpaceKTruthTableReducible
    (h : LogSpaceKDTTReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB A B := by
  classical
  obtain ⟨r, q, hr, hq, hk, hA⟩ := h
  refine ⟨r, q, fun p => p.2.any id, hr, hq, by fun_prop, hk, fun a => ?_⟩
  rw [hA a, truthTableAnswers_eq_map_range]
  simp

/-- A bounded conjunctive reduction is a truth-table reduction with the same bound. -/
theorem LogSpaceKCTTReducible.logSpaceKTruthTableReducible
    (h : LogSpaceKCTTReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB A B := by
  classical
  obtain ⟨r, q, hr, hq, hk, hA⟩ := h
  refine ⟨r, q, fun p => p.2.all id, hr, hq, by fun_prop, hk, fun a => ?_⟩
  rw [hA a, truthTableAnswers_eq_map_range]
  simp

end Cslib.Complexity
