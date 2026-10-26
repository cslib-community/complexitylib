/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives

/-! Codec instances and direct linear/degree clients, without higher tidy calculus.

Pinned cslib's Tidy.Defs bundles fixed-machine semantics with RawTS/OfLength definitions and mono.
Those inherited constants remain visible; no local high-calculus facade is imported here.
-/

run_cmd do
  let env ← Lean.getEnv
  for n in [`Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInBigO,
      `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.append] do
    if env.contains n then throwError "high tidy calculus in direct codec closure: {n}"
  unless env.contains `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace do
    throwError "update the documented pinned-upstream boundary"

open Turing.MultiTapeTM
universe u

section Generic
variable {α β γ : Type u} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encIn : γ ↪ List Bool} {encL : List α ↪ List Bool} {encO : Option α ↪ List Bool}
  {encP : α × β ↪ List Bool}

-- Arbitrary element types/encodings; no finite-domain or inhabited-type assumption.
example [ListEncoding encA encL] (d : α) :
    ComputableInLinearTimeAndSpace (fun xs : List α => xs.tail.headD d) encL encA :=
  (ListEncoding.headD d).comp (ListEncoding.tail (enc₁ := encA))

example [ListEncoding encA encL] :
    ComputableInLinearTimeAndSpace (fun xs : List α => xs.tail.isEmpty) encL encBool :=
  (ListEncoding.isEmpty (enc₁ := encA)).comp (ListEncoding.tail (enc₁ := encA))

example [OptionEncoding encA encO] (d : α) :
    ComputableInLinearTimeAndSpace (fun a : α => (some a).getD d) encA encA :=
  (OptionEncoding.getD (enc := encO) d).comp OptionEncoding.some

example [OptionEncoding encA encO] : encO none = [] := OptionEncoding.none_eq encA

example [PairEncoding encA encB encP] {f : γ → α} {g : γ → β}
    {t₁ s₁ t₂ s₂ : γ → ℕ}
    (hf : ComputableInTimeAndSpace f encIn encA t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn encB t₂ s₂) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn encP
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + (encP (f x, g x)).length + 1)) :=
  PairEncoding.pair_mono hf hg

example : True := by
  fail_if_success have : ListEncoding encA encL := inferInstance
  fail_if_success have : OptionEncoding encA encO := inferInstance
  fail_if_success have : PairEncoding encA encB encP := inferInstance
  trivial

example [PairEncoding encA encB encP] {f : γ → α} {g : γ → β}
    (hf : ComputableInLinearTimeAndSpace f encIn encA) : hf = hf ∧ g = g := by
  fail_if_success
    have : ComputableInLinearTimeAndSpace (fun x => (f x, g x)) encIn encP :=
      hf.pair (by assumption)
  exact ⟨rfl, rfl⟩
end Generic

-- The actual pair instance allows zero-workspace callbacks with independent time/output charge.
example : ∃ c, ComputableInTimeAndSpace (fun w : List Bool => (w, w)) encBits
    (encPair encBits encBits) (fun w => c * (w.length + 2))
    (fun w => c * ((encPair encBits encBits (w, w)).length + 1)) := by
  obtain ⟨k, Q, hfin, tm, htm⟩ := computableInTimeAndSpace_id (enc := encBits)
  have hi : ComputableInTimeAndSpace id encBits encBits (fun w => w.length + 1) (fun _ => 0) :=
    ⟨k, Q, hfin, tm, htm⟩
  simpa [Nat.add_assoc] using PairEncoding.pair (enc := encPair encBits encBits) hi hi

-- Empty/default and malformed-word behavior remains the original encoding/parser behavior.
example (w : List Bool) : encOption encBits (some w) = true :: w := rfl
example : encOption encBits none = [] := rfl
example (xs : List Bool) : encPair encBits encBits (xs, []) = frame xs ++ [] := rfl
example : encList encBits [] = [] := rfl
example : unframe [true] = [] := rfl
example : dropFrame [true] = [] := rfl
example : unframe [true, false, true] = [false] := rfl
example : dropFrame [true, false, true] = [] := rfl

example (enc : Empty ↪ List Bool) :
    ComputableInDegree (some (α := Empty)) enc (encOption enc) 1 1 :=
  ComputableInDegree.optionSome

example : (encList encBits ([] : List (List Bool))) = [] := rfl
example (d : List Bool) : ([] : List (List Bool)).headD d = d := rfl
example (d : List Bool) : (none : Option (List Bool)).getD d = d := rfl
