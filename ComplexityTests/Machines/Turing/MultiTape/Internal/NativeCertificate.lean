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

theorem copyPolynomial : copy.IsPolynomial := by
  constructor
  · exact PolyBounded.of_forall_le 1 1 fun _ => by
      simp [copy, NativeCertificate.ofTimeAndSpace, word]
  · exact PolyBounded.of_forall_le 1 1 fun _ => by
      simp [copy, NativeCertificate.ofTimeAndSpace, word]

-- The public certificate charges the output although the raw machine has no work tapes,
-- and exact independent budgets are retained.
example (w : List Bool) (n : ℕ) {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s) :
    copy.time w = w.length + 1 ∧
    copy.space w = 0 + (w.length + 1) ∧
    copy.space (List.replicate n true) = n + 1 ∧
    ComputableInPolyTime (fun w : List Bool => w) word word ∧
    (copy.comp copy).time w = (w.length + 1) + (w.length + 1) ∧
    (copy.comp copy).space w = (0 + (w.length + 1)) + (0 + (w.length + 1)) ∧
    (copy.comp copy).IsPolynomial ∧
    Nonempty (NativeCertificate (fun w : List Bool => w) word word) ∧
    (NativeCertificate.ofPolyTime
      (ComputableInPolyTime.const ([] : List Bool) (encIn := word) (encOut := word))).IsPolynomial ∧
    (NativeCertificate.ofTimeAndSpace h).time = t ∧
    (NativeCertificate.ofTimeAndSpace h).space = (fun a => s a + t a) :=
  ⟨rfl, rfl, by simp [copy, NativeCertificate.ofTimeAndSpace], copy.polyTime copyPolynomial,
    rfl, rfl, copy.comp_isPolynomial copy copyPolynomial copyPolynomial,
    NativeCertificate.nonempty_iff_isComputable.mpr copy.isComputable,
    NativeCertificate.ofPolyTime_isPolynomial _, rfl, rfl⟩

end ComplexityTests.Internal.NativeCertificate
