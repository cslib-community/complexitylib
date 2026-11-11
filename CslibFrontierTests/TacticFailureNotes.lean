/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.Operator.LeastFixedPoint.Definability
import CslibFrontier.Tactic.Degree
import CslibFrontier.Tactic.FirstOrder
import CslibFrontier.Tactic.FOOperator
import CslibFrontier.Tactic.LogSpace
import CslibFrontier.Tactic.Space

/-!
# Failure messages of the search tactics

Each search tactic below fails with its backend's error followed by a note saying what the user
must supply, and the supplied input then closes the goal. `degree` and `logspace` first check the
shape of the goal, so that a certificate of another kind in the context is not used for it. For the
Aesop-backed tactics only the note is matched, as a substring, since Aesop's goal dump changes with
its output format and rule sets.
-/

namespace CslibFrontierTests.TacticFailureNotes

open Turing.MultiTapeTM

/-! ### `degree` -/

/--
error: degree expects a goal `ComputableInDegree f encIn encOut d e`, got
  ComputableInPolyTime f encUnary encUnary
-/
#guard_msgs in
example (f : ℕ → ℕ) (h : ComputableInPolyTime f encUnary encUnary) :
    ComputableInPolyTime f encUnary encUnary := by
  degree

/--
error: `fun_prop` was unable to prove `ComputableInDegree (fun n => f n + 1) encUnary encUnary 1 1`

Issues:
  No theorems found for `f` in order to prove `ComputableInDegree (fun a => f a) encUnary encUnary
    ?df ?ef`
  No theorems found for `f` in order to prove `ComputableInDegree (fun n => f n) encUnary ?encMid
    ?dg ?eg`

Note: degree composes `@[fun_prop]` rules for `ComputableInDegree` and does not unfold definitions.
  Unfold a local definition first, or prove a certificate for the operation named above and tag it
  `@[fun_prop]`.
-/
#guard_msgs (whitespace := lax) in
example (f : ℕ → ℕ) : ComputableInDegree (fun n => f n + 1) encUnary encUnary 1 1 := by
  degree

example (f : ℕ → ℕ) (hf : ComputableInDegree f encUnary encUnary 1 1) :
    ComputableInDegree (fun n => f n + 1) encUnary encUnary 1 1 := by
  degree

/-! ### `logspace` -/

/--
error: logspace expects a goal `ComputableInLogSpace f encIn encOut`, got
  (fun w => w.length) = fun w => w.length
-/
#guard_msgs in
example : (fun w : List Bool => w.length) = fun w => w.length := by
  logspace

/--
Note: logspace composes `@[fun_prop]` rules and named `program_certificate`s for
  `ComputableInLogSpace`. Supply a certificate for each local routine, with the goal's encodings. An
  answer vector `(List.range (r a)).map (f a)` also needs a hypothesis `∀ a, r a ≤ k`.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (r : List Bool → ℕ) (g : List Bool → ℕ → Bool)
    (hr : ComputableInLogSpace r encBits encUnary)
    (hg : ComputableInLogSpace (fun p : List Bool × ℕ => g p.1 p.2) (encPair encBits encUnary)
      encBool) :
    ComputableInLogSpace (fun w => (List.range (r w)).map (g w)) encBits encBits := by
  logspace

example (r : List Bool → ℕ) (g : List Bool → ℕ → Bool)
    (hr : ComputableInLogSpace r encBits encUnary) (hrk : ∀ w, r w ≤ 8)
    (hg : ComputableInLogSpace (fun p : List Bool × ℕ => g p.1 p.2) (encPair encBits encUnary)
      encBool) :
    ComputableInLogSpace (fun w => (List.range (r w)).map (g w)) encBits encBits := by
  logspace

/-! ### `space` -/

/--
error: `fun_prop` was unable to prove `ComputableInSpace (fun n => n) encNat encNat S`

Issues:
  Failed to prove necessary assumption `(fun a => (encNat a).length) ≼ S` when applying theorem
    `Turing.MultiTapeTM.ComputableInSpace.budget_id`.

Note: space composes `@[fun_prop]` rules for `ComputableInSpace` within the goal's budget. Supply a
  certificate for each local routine, unfold a program definition with `space [f]`, and supply a
  nontrivial input-length allowance `(fun a => (encIn a).length) ≼ S` as a hypothesis.
-/
#guard_msgs (whitespace := lax) in
example (S : ℕ → ℕ) : ComputableInSpace (fun n : ℕ => n) encNat encNat S := by
  space

example (S : ℕ → ℕ) (hS : (fun n => (encNat n).length) ≼ S) :
    ComputableInSpace (fun n : ℕ => n) encNat encNat S := by
  space

/-! ### `fo_qf`, `fo_iso_closed` and `fo_definable` -/

section FirstOrder

open FirstOrder Language Cslib.Logic Cslib.Logic.FO

variable {L : Language}

/--
Note: fo_qf proves quantifier-freeness from the rules of the Aesop rule set `FirstOrder` and
  hypotheses. Unfold a local definition first, assume `IsQF` for an abstract formula or
  interpretation, or register a lemma for a new combinator with `@[aesop safe apply (rule_sets :=
  [FirstOrder])]`.
-/
#guard_msgs (whitespace := lax, substring := true) in
example {α : Type} {n : ℕ} (φ ψ : L.BoundedFormula α n) (hφ : φ.IsQF) : (φ ⊓ ψ).IsQF := by
  fo_qf

example {α : Type} {n : ℕ} (φ ψ : L.BoundedFormula α n) (hφ : φ.IsQF) (hψ : ψ.IsQF) :
    (φ ⊓ ψ).IsQF := by
  fo_qf

/--
Note: fo_iso_closed proves `IsoClosed K` from lemmas of the Aesop rule set `FirstOrder` and
  hypotheses. Assume it, or prove it for `K` and register the lemma with `@[aesop safe apply
  (rule_sets := [FirstOrder])]`.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (K : Set (CategoryTheory.Bundled L.Structure)) : IsoClosed K := by
  fo_iso_closed

example (K : Set (CategoryTheory.Bundled L.Structure)) (hK : IsoClosed K) : IsoClosed K := by
  fo_iso_closed

/-- The class of all structures is closed under isomorphism, registered as the note advises. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isoClosed_univ : IsoClosed (Set.univ : Set (CategoryTheory.Bundled L.Structure)) :=
  IsoClosed.of_forall_imp fun _ _ _ _ _ => trivial

example : IsoClosed (Set.univ : Set (CategoryTheory.Bundled L.Structure)) := by
  fo_iso_closed

variable {ι : Type} {M : ι → Type} [∀ i, L.Structure (M i)] {α : Type}

/--
Note: fo_definable composes the `Operator.Definable` rules of the Aesop rule set `FODefinable` and
  does not unfold definitions. Unfold a local predicate first, or prove definability of the
  operation and register it with `@[aesop safe apply (rule_sets := [FODefinable])]`;
  `Definable.of_formula` takes an explicit formula.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (p : ∀ i, M i → Prop) (a : α) :
    Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
      (fun _ => Operator.RelEnv.empty) (fun i v => p i (v a)) := by
  fo_definable

example (p : ∀ i, M i → Prop) (a : α)
    (hp : Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
      (fun _ => Operator.RelEnv.empty) (fun i v => p i (v a))) :
    Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
      (fun _ => Operator.RelEnv.empty) (fun i v => p i (v a)) := by
  fo_definable

end FirstOrder

end CslibFrontierTests.TacticFailureNotes
