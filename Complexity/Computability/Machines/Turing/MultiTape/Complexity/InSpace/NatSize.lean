/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# Native binary-width measurement

The binary size of a runtime natural is computed by measuring its encoded digits.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Measure the binary width of a runtime natural in linear encoded-input space. -/
theorem natSize :
    ComputableInSpace Nat.size encNat encNat (fun n => (encNat n).length) := by
  have hlen := (of_inO ComputableInO.lengthNat).weaken
    (show (fun w : List Bool => w.length + 1) ≼ fun w => (encBits w).length from
      .of_le_linear 1 1 fun w => by simp [encBits_apply])
  refine (hlen.of_encIn_eq Nat.bits (fun _ => rfl)).of_enc_eq ?_
  intro n
  rw [Nat.size_eq_bits_len]

end Turing.MultiTapeTM.ComputableInSpace
