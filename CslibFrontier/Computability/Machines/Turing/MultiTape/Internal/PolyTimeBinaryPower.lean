/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
public import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Direct binary powers with unary exponents

The captured repeated-multiplication algorithm is the existing binary-power recipe. Its
reachable encoded lengths are bounded directly; no high-level tidy certificate is transported.
The resulting number may have exponential value, but only polynomially many encoded bits.
Like the direct binary-addition rule, this is a named certificate: it does not add an automatic
binary branch to goals with an undetermined intermediate encoding.
-/

public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Raise a binary natural to a unary exponent using direct captured multiplication. -/
theorem binary_pow : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^ p.2)
    (encPair encNat encUnary) encNat := by
  have hstep := binary_mul' (snd encNat encNat) (fst encNat encNat)
  have h := iterateWith (par := Prod.fst) (count := Prod.snd)
    (init := fun _ : ℕ × ℕ => 1) (step := fun b acc => acc * b)
    (fst encNat encUnary) (snd encNat encUnary) (const 1) hstep
    (bound := fun p => (encPair encNat encUnary p).length * (encPair encNat encUnary p).length + 1)
    ((PolyBounded.self.mul .self).add (.const 1)) (by
      intro p i hi
      rw [mul_right_iterate_apply_one]
      change (p.1 ^ i).bits.length ≤ _
      rw [Nat.size_eq_bits_len]
      have hs := Nat.size_pow_le p.1 i
      have hb : p.1.size ≤ (encPair encNat encUnary p).length := by
        simpa [Nat.size_eq_bits_len] using length_le_encPair_left encNat encUnary p
      have hk : i ≤ (encPair encNat encUnary p).length := by
        have hp := length_le_encPair_right encNat encUnary p
        simp only [encUnary_apply, List.length_replicate] at hp
        exact hi.trans hp
      exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul hk hb) 1))
  simpa only [mul_right_iterate_apply_one] using h

end Turing.MultiTapeTM.ComputableInPolyTime
