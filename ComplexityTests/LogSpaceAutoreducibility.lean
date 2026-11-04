/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.LogSpaceAutoreducibility
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Complement-based autoreduction examples

Negation swaps the member and nonmember of the Boolean singleton. The singleton is also
complete for `L` under the existing encoded many-one reductions, so the class corollary has a
concrete instance. An independent zero-query witness deliberately uses an identity generator
at unused indices, and empty/full sets cannot satisfy the complement-witness premise.
-/

public section

namespace Cslib.Complexity.LogSpaceAutoreducibilityTest

open Turing.MultiTapeTM

/-- Both membership cases of the complement witness, with actual distinct queries. -/
example : (false ∉ ({true} : Set Bool) ↔ (!false) ∈ ({true} : Set Bool)) ∧
    (true ∉ ({true} : Set Bool) ↔ (!true) ∈ ({true} : Set Bool)) ∧
    (!false) ≠ false ∧ (!true) ≠ true := by decide

/-- The complement witness gives an autoreduction of a singleton, despite the many-one
singleton obstruction: its evaluator negates the oracle answer. -/
theorem boolSingleton_autoreducible :
    LogSpaceKTruthTableAutoreducible 1 encBool ({true} : Set Bool) :=
  logSpaceKTruthTableAutoreducible_one_of_complement_witness
    (ComputableInLogSpace.of_finite Bool.not) (by decide)

/-- The same witness is usable through the bounded and unbounded interfaces. -/
example : LogSpaceTruthTableAutoreducible encBool ({true} : Set Bool) :=
  boolSingleton_autoreducible.logSpaceBTTAutoreducible.logSpaceTruthTableAutoreducible

/-- A zero-query evaluator reads the input; unused queries may equal that input. -/
example : LogSpaceKTruthTableAutoreducible 0 encBool ({true} : Set Bool) := by
  refine ⟨fun _ => 0, Prod.fst, Prod.fst, by fun_prop, by fun_prop, by fun_prop,
    fun _ => le_rfl, fun _ i hi => False.elim (Nat.not_lt_zero i hi), fun a => ?_⟩
  simp

/-- The singleton is `L`-complete: a logspace decider itself is the many-one map into Bool. -/
theorem boolSingleton_complete : LogSpaceComplete L encBool ({true} : Set Bool) := by
  refine ⟨⟨id, ComputableInLogSpace.id, fun a => by simp⟩, ?_⟩
  intro α enc B hB
  obtain ⟨f, hf, hB⟩ := hB
  exact ⟨f, hf, fun a => by simpa using hB a⟩

/-- The complement-closed-class corollary applies without postulating an unproved completeness
result for a new complexity class. -/
example : LogSpaceKTruthTableAutoreducible 1 encBool ({true} : Set Bool) :=
  boolSingleton_complete.logSpaceKTruthTableAutoreducible_one
    (fun _ _ h => compl_mem_L h)

/-- The identity self-reduction of the Boolean singleton is not a complement witness. -/
example : ¬ (∀ a : Bool, a ∉ ({true} : Set Bool) ↔ id a ∈ ({true} : Set Bool)) := by
  decide

/-- Empty and full languages on a nonempty domain cannot meet the complement-witness premise. -/
example : (¬ ∃ f : Bool → Bool, ∀ a, a ∉ (∅ : Set Bool) ↔ f a ∈ (∅ : Set Bool)) ∧
    (¬ ∃ f : Bool → Bool, ∀ a, a ∉ (Set.univ : Set Bool) ↔ f a ∈ (Set.univ : Set Bool)) := by
  simp

end Cslib.Complexity.LogSpaceAutoreducibilityTest
