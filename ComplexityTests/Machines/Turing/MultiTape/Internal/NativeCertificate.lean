/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Native.Certificate
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! # Plain native certificate fields and output-charge accounting -/

@[expose] public section

open Turing.MultiTapeTM Cslib.GenericRAM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

namespace ComplexityTests.Internal.NativeCertificate

def word : List Bool ↪ List Bool := Function.Embedding.refl _

/-- The copy machine has zero workspace even on unbounded runtime words. -/
theorem rawCopy : ComputableInTimeAndSpace (fun w : List Bool => w) word word
    (fun w => w.length + 1) (fun _ => 0) := computableInTimeAndSpace_id

def copy : NativeCertificate (fun w : List Bool => w) word word :=
  .ofTimeAndSpace rawCopy

example (w : List Bool) : copy.time w = w.length + 1 := rfl
example (w : List Bool) : copy.space w = 0 + (w.length + 1) := rfl

-- The public certificate charges the output although the raw machine has no work tapes.
example (n : ℕ) : copy.space (List.replicate n true) = n + 1 := by
  simp [copy, NativeCertificate.ofTimeAndSpace]

theorem copyPolynomial : copy.IsPolynomial := by
  constructor
  · exact PolyBounded.of_forall_le 1 1 fun _ => by
      simp [copy, NativeCertificate.ofTimeAndSpace, word]
  · exact PolyBounded.of_forall_le 1 1 fun _ => by
      simp [copy, NativeCertificate.ofTimeAndSpace, word]

example : ComputableInPolyTime (fun w : List Bool => w) word word := copy.polyTime copyPolynomial

example (w : List Bool) : (copy.comp copy).time w =
    (w.length + 1) + (w.length + 1) := rfl

example (w : List Bool) : (copy.comp copy).space w =
    (0 + (w.length + 1)) + (0 + (w.length + 1)) := rfl

example : (copy.comp copy).IsPolynomial := copy.comp_isPolynomial copy copyPolynomial copyPolynomial

example : Nonempty (NativeCertificate (fun w : List Bool => w) word word) :=
  NativeCertificate.nonempty_iff_isComputable.mpr copy.isComputable

example : (NativeCertificate.ofPolyTime
    (ComputableInPolyTime.const ([] : List Bool) (encIn := word) (encOut := word))).IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial _

-- Exact independent budgets are retained; only the output charge is added to workspace.
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s) :
    (NativeCertificate.ofTimeAndSpace h).time = t := rfl

example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s) :
    (NativeCertificate.ofTimeAndSpace h).space = fun a => s a + t a := rfl

/-- info: 'Cslib.GenericRAM.NativeCertificate.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.GenericRAM.NativeCertificate.comp

end ComplexityTests.Internal.NativeCertificate
