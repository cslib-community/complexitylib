/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.LogSpaceBoundedAutoreducibility
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Equality
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Bounded complement autoreduction regression examples

Both singleton witnesses have active self-queries, on opposite membership branches. Zero-query
witnesses handle the full language for OR and the empty language for AND. We also exercise
encoded word equality and the completeness corollaries on `L`.
-/

public section

namespace Cslib.Complexity.LogSpaceBoundedAutoreducibilityTest

open Turing.MultiTapeTM

private def orCount (a : Bool) : ℕ := if a then 1 else 2
private def orQuery (p : Bool × ℕ) : Bool := if p.1 then false else !decide (p.2 = 0)
private def andCount (a : Bool) : ℕ := if a then 2 else 1
private def andQuery (p : Bool × ℕ) : Bool := if p.1 then decide (p.2 = 0) else true

private theorem orQuery_logspace :
    ComputableInLogSpace orQuery (encPair encBool encUnary) encBool := by
  unfold orQuery
  fun_prop

private theorem andQuery_logspace :
    ComputableInLogSpace andQuery (encPair encBool encUnary) encBool := by
  unfold andQuery
  fun_prop

/-- OR forces nonmembership on the self-query branch; the other branch asks one distinct query. -/
example : activeSelfQuery encBool orCount orQuery false = true ∧
    activeSelfQuery encBool orCount orQuery true = false ∧
    orQuery (false, 0) = false ∧ orQuery (false, 1) = true ∧
    orQuery (true, 0) = false := by decide

/-- AND forces membership on the self-query branch; the other branch asks one distinct query. -/
example : activeSelfQuery encBool andCount andQuery true = true ∧
    activeSelfQuery encBool andCount andQuery false = false ∧
    andQuery (true, 0) = true ∧ andQuery (true, 1) = false ∧
    andQuery (false, 0) = true := by decide

private theorem orWitness : LogSpaceKDTTReducible 2 encBool encBool
    ({true} : Set Bool)ᶜ ({true} : Set Bool) := by
  refine ⟨orCount, orQuery, ComputableInLogSpace.of_finite _, orQuery_logspace, ?_, ?_⟩
  · decide
  · intro a
    cases a
    · constructor
      · intro _
        exact ⟨1, by decide, by decide⟩
      · intro _
        decide
    · simp [orCount, orQuery]

private theorem andWitness : LogSpaceKCTTReducible 2 encBool encBool
    ({true} : Set Bool)ᶜ ({true} : Set Bool) := by
  refine ⟨andCount, andQuery, ComputableInLogSpace.of_finite _, andQuery_logspace, ?_, ?_⟩
  · decide
  · intro a
    cases a
    · simp [andCount, andQuery]
    · constructor
      · intro h
        exact False.elim (h (by decide))
      · intro h
        have hf := h 1 (by decide)
        change false = true at hf
        cases hf

/-- The bounded inclusion API retains the original two-query limit. -/
example : LogSpaceKTruthTableReducible 2 encBool encBool
    ({true} : Set Bool)ᶜ ({true} : Set Bool) ∧
    LogSpaceKTruthTableReducible 2 encBool encBool
      ({true} : Set Bool)ᶜ ({true} : Set Bool) :=
  ⟨orWitness.logSpaceKTruthTableReducible, andWitness.logSpaceKTruthTableReducible⟩

/-- Neither application assumes the original complement witness avoids input. -/
example : LogSpaceKTruthTableAutoreducible 2 encBool ({true} : Set Bool) ∧
    LogSpaceKTruthTableAutoreducible 2 encBool ({true} : Set Bool) :=
  ⟨orWitness.autoreducible_of_compl, andWitness.autoreducible_of_compl⟩

/-- Inactive self-queries are ignored, including every index in the zero-query case. -/
example : activeSelfQuery encBool (fun _ => 0) Prod.fst true = false ∧
    activeSelfQuery encBool (fun _ => 1)
      (fun p => if p.2 = 0 then !p.1 else p.1) true = false := by decide

private theorem full_or_zero :
    LogSpaceKDTTReducible 0 encBool encBool (Set.univ : Set Bool)ᶜ Set.univ := by
  refine ⟨fun _ => 0, Prod.fst, by fun_prop, by fun_prop, fun _ => le_rfl, ?_⟩
  simp

private theorem empty_and_zero :
    LogSpaceKCTTReducible 0 encBool encBool (∅ : Set Bool)ᶜ ∅ := by
  refine ⟨fun _ => 0, Prod.fst, by fun_prop, by fun_prop, fun _ => le_rfl, ?_⟩
  simp

/-- The empty/full edge witnesses produce autoreductions at the exact zero bound. -/
example : LogSpaceKTruthTableAutoreducible 0 encBool (Set.univ : Set Bool) ∧
    LogSpaceKTruthTableAutoreducible 0 encBool (∅ : Set Bool) :=
  ⟨full_or_zero.autoreducible_of_compl, empty_and_zero.autoreducible_of_compl⟩

/-- OR cannot reduce the complement of empty to empty; AND cannot do so for full. -/
example (k : ℕ) : (¬ LogSpaceKDTTReducible k encBool encBool (∅ : Set Bool)ᶜ ∅) ∧
    (¬ LogSpaceKCTTReducible k encBool encBool (Set.univ : Set Bool)ᶜ Set.univ) := by
  constructor
  · rintro ⟨r, q, hr, hq, hk, h⟩
    simpa using h false
  · rintro ⟨r, q, hr, hq, hk, h⟩
    simpa using h false

/-- Self-query detection distinguishes empty words, differing bits, and unequal lengths. -/
example : activeSelfQuery encBits (fun _ => 1) Prod.fst [] = true ∧
    activeSelfQuery encBits (fun _ => 1) (fun _ => [false]) [false] = true ∧
    activeSelfQuery encBits (fun _ => 1) (fun _ => [false]) [true] = false ∧
    activeSelfQuery encBits (fun _ => 1) (fun _ => [false]) [false, true] = false ∧
    activeSelfQuery encBits (fun _ => 1) (fun _ => [false, true]) [false] = false := by
  decide

/-- The generic equality certificate handles variable words, not only a finite domain. -/
example : ComputableInLogSpace (fun p : List Bool × List Bool => decide (p.1 = p.2))
    (encPair encBits encBits) encBool := by fun_prop

/-- Equality also supports a framed-list encoding, without changing its certificate API. -/
example : ComputableInLogSpace (fun p : List Bool × List Bool => decide (p.1 = p.2))
    (encPair (encList encBool) (encList encBool)) encBool := by fun_prop

/-- The Boolean singleton is one-query disjunctive complete for `L`. -/
theorem singleton_kdtt_complete :
    CompleteUnder (fun enc => LogSpaceKDTTReducible 1 enc encBool) L encBool
      ({true} : Set Bool) := by
  refine ⟨⟨id, ComputableInLogSpace.id, fun a => by simp⟩, ?_⟩
  intro α enc B hB
  obtain ⟨f, hf, hB⟩ := hB
  refine ⟨fun _ => 1, fun p => f p.1, by fun_prop, by fun_prop, fun _ => le_rfl, ?_⟩
  intro a
  simpa using hB a

/-- The Boolean singleton is one-query conjunctive complete for `L`. -/
theorem singleton_kctt_complete :
    CompleteUnder (fun enc => LogSpaceKCTTReducible 1 enc encBool) L encBool
      ({true} : Set Bool) := by
  refine ⟨⟨id, ComputableInLogSpace.id, fun a => by simp⟩, ?_⟩
  intro α enc B hB
  obtain ⟨f, hf, hB⟩ := hB
  refine ⟨fun _ => 1, fun p => f p.1, by fun_prop, by fun_prop, fun _ => le_rfl, ?_⟩
  intro a
  simpa using hB a

/-- Both class corollaries apply to proved completeness and complement closure of `L`. -/
example : LogSpaceKTruthTableAutoreducible 1 encBool ({true} : Set Bool) ∧
    LogSpaceKTruthTableAutoreducible 1 encBool ({true} : Set Bool) :=
  ⟨logSpaceKTruthTableAutoreducible_of_kdtt_complete singleton_kdtt_complete
      (fun _ _ h => compl_mem_L h),
    logSpaceKTruthTableAutoreducible_of_kctt_complete singleton_kctt_complete
      (fun _ _ h => compl_mem_L h)⟩

end Cslib.Complexity.LogSpaceBoundedAutoreducibilityTest
