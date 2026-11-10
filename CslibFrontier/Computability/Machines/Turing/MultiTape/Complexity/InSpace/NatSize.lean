/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists

/-!
# Native binary-width measurement

The binary size of a runtime natural is computed by measuring its encoded digits.
`natSize` returns that width in binary; `natSizeUnary` returns it in unary. Neither
operation expands the original natural to unary.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Measure the binary width of a runtime natural in linear encoded-input space. -/
theorem natSize :
    ComputableInSpace Nat.size encNat encNat (fun n => (encNat n).length) := by
  have hlen := (of_inO ComputableInO.lengthNat).weaken
    (show (fun w : List Bool => w.length) ≼ fun w => (encBits w).length from
      .of_le_linear 1 1 fun w => by simp [encBits_apply])
  refine (hlen.of_encIn_eq Nat.bits (fun _ => rfl)).of_enc_eq ?_
  intro n
  rw [Nat.size_eq_bits_len]

/-- The binary width, returned in unary, in linear encoded-input space. -/
theorem natSizeUnary :
    ComputableInSpace Nat.size encNat encUnary (fun n => (encNat n).length) :=
  ((of_inO ComputableInO.lengthUnary).of_encIn_eq Nat.bits fun _ => rfl).of_enc_eq fun n => by
    rw [Nat.size_eq_bits_len]

end Turing.MultiTapeTM.ComputableInSpace
