/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds

/-!
# Deterministic function time

`FTIME encIn encOut t` consists of functions computed by one finite-control binary multi-tape
machine in time `c₁ * t n + c₂` on an input whose encoding has length `n`, for constants fixed
before the input. The output encoding is explicit and workspace may have any length-dependent
bound. This is the function analogue of `DTIME`, using the same native computation predicate;
it is not a class of decision problems.

For natural-valued counting functions, use the binary output encoding `Turing.MultiTapeTM.encNat`.
No extra output-length charge is imposed beyond writing the encoded output within the time bound.

## Main definitions

* `Cslib.Complexity.FTIME`: deterministic function time with explicit input and output encodings.

## Main results

* `Cslib.Complexity.mem_FTIME`: the native machine/resource contract.
* `Cslib.Complexity.FTIME_mono`: monotonicity in the time bound.
* `Cslib.Complexity.FTIME.of_computableInTimeAndSpace`: an exact resource certificate gives
  function-time membership.
-/

public section

namespace Cslib.Complexity

open _root_.Turing.MultiTapeTM

variable {α β : Type}

/-- Functions computed in time `O(t n)` by finite-control binary native machines. The output
encoding is explicit; workspace has an arbitrary bound depending on encoded input length. -/
@[expose] def FTIME (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t : ℕ → ℕ) :
    Set (α → β) :=
  {f | ∃ c₁ c₂ : ℕ, ∃ s : ℕ → ℕ, ComputableInTimeAndSpace f encIn encOut
    (fun a => c₁ * t (encIn a).length + c₂) (fun a => s (encIn a).length)}

variable {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t : ℕ → ℕ} {f : α → β}

/-- Membership exposes one machine with an affine time bound and arbitrary length-dependent
workspace. -/
theorem mem_FTIME : f ∈ FTIME encIn encOut t ↔
    ∃ c₁ c₂ : ℕ, ∃ s : ℕ → ℕ, ComputableInTimeAndSpace f encIn encOut
      (fun a => c₁ * t (encIn a).length + c₂) (fun a => s (encIn a).length) :=
  Iff.rfl

/-- Increasing the time bound preserves function-time membership. -/
theorem FTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    FTIME encIn encOut t₁ ⊆ FTIME encIn encOut t₂ := by
  rintro f ⟨c₁, c₂, s, hf⟩
  exact ⟨c₁, c₂, s, hf.mono
    (fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _) (fun _ => le_rfl)⟩

/-- An exact length-dependent time/workspace certificate implies function-time membership. -/
theorem FTIME.of_computableInTimeAndSpace {s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut
      (fun a => t (encIn a).length) (fun a => s (encIn a).length)) :
    f ∈ FTIME encIn encOut t :=
  ⟨1, 0, s, h.mono (fun _ => by rw [Nat.one_mul, Nat.add_zero]) (fun _ => le_rfl)⟩

end Cslib.Complexity
