/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.Certificate
import Mathlib.Tactic.Ring

/-!
# Finite-machine bounds from charged native certificates

Unpack the existing realizing machine and absorb its fixed constants into previously proved
polynomial/parameterized-exponential bounds. This changes no algorithm or transition semantics.
Concrete callers must derive both certificate bounds; this adapter is not a faster-counter premise.

## Main results

* `NativeCertificate.exists_sharp_machine`: one finite binary machine with independent time,
  workspace and encoded-output bounds, including the certificate's additive constants.
-/

public section
namespace Cslib.GenericRAM.NativeCertificate
open Turing.MultiTapeTM

/-- Reuse the certificate's finite machine and absorb only its fixed multiplicative/additive
constants. The size exponent and parameter scale are unchanged. -/
theorem exists_sharp_machine {α β : Type} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (cs : NativeCertificate f encIn encOut) (C e A : ℕ) (scale : α → ℕ)
    (hs : ∀ x, cs.space x ≤ C * ((encIn x).length + 1) ^ e)
    (ht : ∀ x, cs.time x ≤ C * ((encIn x).length + 1) ^ e * 2 ^ (A * scale x)) :
    ∃ (B k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      (∀ x, tm.ComputesInTimeAndSpace (encIn x) (encOut (f x))
        (B * ((encIn x).length + 1) ^ e * 2 ^ (A * scale x))
        (B * ((encIn x).length + 1) ^ e)) ∧
      (∀ x, (encOut (f x)).length ≤ B * ((encIn x).length + 1) ^ e) := by
  obtain ⟨c, hm, hl⟩ := cs.computes
  have hS (x : α) : c * (cs.space x + 1) ≤ c * (C + 1) * ((encIn x).length + 1) ^ e := by
    have hp : 1 ≤ ((encIn x).length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have h := hs x
    calc _ ≤ c * (C * ((encIn x).length + 1) ^ e + ((encIn x).length + 1) ^ e) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hT (x : α) : c * (cs.time x + 1) ≤ c * (C + 1) * ((encIn x).length + 1) ^ e *
      2 ^ (A * scale x) := by
    have hp : 1 ≤ ((encIn x).length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have hE := Nat.two_pow_pos (A * scale x)
    have h := ht x
    have hPE : 1 ≤ ((encIn x).length + 1) ^ e * 2 ^ (A * scale x) := by nlinarith
    calc _ ≤ c * (C * ((encIn x).length + 1) ^ e * 2 ^ (A * scale x) +
          ((encIn x).length + 1) ^ e * 2 ^ (A * scale x)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  obtain ⟨k, State, hfinite, tm, htm⟩ := hm.mono hT hS
  exact ⟨c * (C + 1), k, State, hfinite, tm, htm, fun x => (hl x).trans (hS x)⟩

end Cslib.GenericRAM.NativeCertificate
