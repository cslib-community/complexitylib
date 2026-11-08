/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.ZMod.ModulusSwitch
public import CslibFrontier.Computability.PolyTime.Int.ExactDiv

/-!
# Native binary modulus switching

The source and target moduli use binary `encNat`; representatives and rounded integers use
signed binary `encIntBin`. The certificates charge the complete input bit length and reuse
native signed multiplication, division and remainder. No rational-arithmetic machine or
unary expansion of the moduli is needed.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_roundScale`: exact rationally specified
  nearest-integer scaling, realized by integer arithmetic.
* `Turing.MultiTapeTM.ComputableInPolyTime.modulusSwitchResidue`: the canonical-residue
  implementation, with both moduli supplied at runtime.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Scale a signed binary integer by the ratio of two binary naturals and round exactly.
At source modulus zero, the rational specification and the implementation both return zero. -/
@[fun_prop] theorem intBin_roundScale :
    ComputableInPolyTime
      (fun a : (ℕ × ℕ) × ℤ => round ((a.1.2 : ℚ) / a.1.1 * a.2))
      (encPair (encPair encNat encNat) encIntBin) encIntBin := by
  have h : ComputableInPolyTime
      (fun a : (ℕ × ℕ) × ℤ =>
        (2 * (a.1.2 : ℤ) * a.2 + a.1.1) / (2 * (a.1.1 : ℤ)))
      (encPair (encPair encNat encNat) encIntBin) encIntBin := by fun_prop
  refine h.of_enc_eq fun a => congrArg encIntBin ?_
  rcases Nat.eq_zero_or_pos a.1.1 with hq | hq
  · simp [hq]
  · exact ZMod.round_scale_eq_div hq a.1.2 a.2

/-- Compute the integer implementation of modulus switching on binary parameters and a signed
binary representative, returning a binary natural residue. The implementation is total. -/
@[fun_prop] theorem modulusSwitchResidue :
    ComputableInPolyTime
      (fun a : (ℕ × ℕ) × ℤ => ZMod.modulusSwitchResidue a.1.1 a.1.2 a.2)
      (encPair (encPair encNat encNat) encIntBin) encNat := by
  unfold ZMod.modulusSwitchResidue
  fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime
