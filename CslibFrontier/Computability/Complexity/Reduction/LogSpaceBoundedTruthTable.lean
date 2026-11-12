/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LogSpaceTruthTable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Bounded disjunctive and conjunctive logspace reductions

The indexed disjunctive and conjunctive reductions of `LogSpaceTruthTable`, with an additional
uniform bound on the active count. These are the `k`-dtt and `k`-ctt restrictions of
[LadnerLynchSelman1975], with the logspace and encoding conventions of that module. The bound
means at most `k`, including zero; an empty disjunction is false and an empty conjunction is true.

Both definitions are by definition instances of the kernels `Cslib.Complexity.DTTReducibleBy` and
`Cslib.Complexity.CTTReducibleBy` of `CslibFrontier.Computability.Reduction.TruthTable`, whose
lemmas prove the results below.

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
    (ComputableInLogSpace r encA encUnary ∧
      ComputableInLogSpace q (encPair encA encUnary) encB ∧ ∀ a, r a ≤ k) ∧
    ∀ a, a ∈ A ↔ ∃ i < r a, q (a, i) ∈ B

/-- Conjunctive reduction with at most `k` active queries, using the existing indexed data. -/
@[expose] def LogSpaceKCTTReducible (k : ℕ) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    (ComputableInLogSpace r encA encUnary ∧
      ComputableInLogSpace q (encPair encA encUnary) encB ∧ ∀ a, r a ≤ k) ∧
    ∀ a, a ∈ A ↔ ∀ i < r a, q (a, i) ∈ B

/-- Forgetting the query bound gives disjunctive reducibility. -/
theorem LogSpaceKDTTReducible.logSpaceDTTReducible (h : LogSpaceKDTTReducible k encA encB A B) :
    LogSpaceDTTReducible encA encB A B :=
  DTTReducibleBy.mono (fun _ _ ⟨hr, hq, _⟩ => ⟨hr, hq⟩) h

/-- Forgetting the query bound gives conjunctive reducibility. -/
theorem LogSpaceKCTTReducible.logSpaceCTTReducible (h : LogSpaceKCTTReducible k encA encB A B) :
    LogSpaceCTTReducible encA encB A B :=
  CTTReducibleBy.mono (fun _ _ ⟨hr, hq, _⟩ => ⟨hr, hq⟩) h

/-- A bounded disjunctive reduction is a truth-table reduction with the same bound. -/
theorem LogSpaceKDTTReducible.logSpaceKTruthTableReducible
    (h : LogSpaceKDTTReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB A B :=
  DTTReducibleBy.truthTableReducibleBy (fun _ _ ⟨hr, hq, hk⟩ => ⟨hr, hq, by fun_prop, hk⟩) h

/-- A bounded conjunctive reduction is a truth-table reduction with the same bound. -/
theorem LogSpaceKCTTReducible.logSpaceKTruthTableReducible
    (h : LogSpaceKCTTReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB A B :=
  CTTReducibleBy.truthTableReducibleBy (fun _ _ ⟨hr, hq, hk⟩ => ⟨hr, hq, by fun_prop, hk⟩) h

end Cslib.Complexity
