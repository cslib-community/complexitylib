/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Reverse

/-!
# Direct charged bounds for binary-word normalization

Reverse the raw little-endian word, drop its leading false symbols with the existing transducer,
and reverse back. Both component machines have linear clocks and zero work tapes; composition
retains linear time and linear workspace, including the encoded output charge. No qualitative
polynomial-time certificate supplies the quantitative bound.

## Main results

* `Turing.MultiTapeTM.ComputableInO.bitsToNat`: linear-time, charged linear-space binary decoding.
-/

public section
namespace Turing.MultiTapeTM.ComputableInO

private theorem reverse_linear :
    ComputableInO List.reverse encBits encBits List.length List.length := by
  have h : ComputableInTimeAndSpace List.reverse encBits encBits
      (fun w => 2 * w.length + 2) (fun _ => 0) :=
    ⟨0, Bool, inferInstance, reverseInput Bool, fun w => ReverseInput.computesInTimeAndSpace w⟩
  exact ComputableInO.of_bounds h 2 (fun _ => by omega) (fun _ => by omega)
    (fun w => by simp only [encBits_apply, List.length_reverse]; omega)
private theorem drop_linear :
    ComputableInO (fun w : List Bool => w.dropWhile (!·)) encBits encBits
      List.length List.length := by
  have h : ComputableInTimeAndSpace (fun w : List Bool => w.dropWhile (!·)) encBits encBits
      (fun w => 2 * w.length + 3) (fun _ => 0) := by
    refine ⟨0, _, inferInstance, dropFalsesT.toTM, fun w => ?_⟩
    simpa only [show dropFalsesT.q₀ = false from rfl, dropFalsesT_run,
      encBits, Function.Embedding.refl_apply] using dropFalsesT.computesInTimeAndSpace_toTM w
  exact ComputableInO.of_bounds h 3 (fun _ => by omega) (fun _ => by omega)
    (fun w => by simpa only [encBits_apply] using
      (List.length_dropWhile_le (!·) w).trans (by omega))
/-- Read arbitrary little-endian words in linear time and charged linear workspace,
including empty words and noncanonical trailing false symbols. -/
theorem bitsToNat :
    ComputableInO ofBits encBits encNat List.length List.length := by
  have h := reverse_linear.comp_linear (drop_linear.comp_linear reverse_linear)
  exact h.of_enc_eq fun w => by rw [encNat_apply, bits_ofBits]; rfl

end Turing.MultiTapeTM.ComputableInO
