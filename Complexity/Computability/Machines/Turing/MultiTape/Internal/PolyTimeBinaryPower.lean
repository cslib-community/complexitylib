/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
public import Complexity.Foundations.Data.Nat.BinarySize
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

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Raise a binary natural to a unary exponent using direct captured multiplication. -/
theorem binary_pow : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^ p.2)
    (encPair encNat encUnary) encNat := by
  have hfold (b k : ℕ) : (List.replicate k true).foldl (fun acc _ => acc * b) 1 = b ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih]
      simp [pow_succ]
  have hb := fst (encPair encNat encNat) encBool
  have hstep := binary_mul' hb.snd' hb.fst'
  have hlist : ComputableInPolyTime (fun p : ℕ × ℕ => List.replicate p.2 true)
      (encPair encNat encUnary) encBits :=
    (of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl).comp (snd encNat encUnary)
  have h := foldlWith (encA := encBool) (encL := encBits) (encP := encNat) (encB := encNat)
    (par := Prod.fst) (list := fun p : ℕ × ℕ => List.replicate p.2 true)
    (init := fun _ => 1) (step := fun b acc _ => acc * b)
    (fst encNat encUnary) hlist (const 1) hstep
    (B := fun p => (encPair encNat encUnary p).length * (encPair encNat encUnary p).length + 1)
    ((PolyBounded.self.mul .self).add (.const 1)) (by
      intro p i _
      rw [List.take_replicate, hfold]
      change (p.1 ^ min i p.2).bits.length ≤ _
      rw [Nat.size_eq_bits_len]
      have hs := Nat.size_pow_le p.1 (min i p.2)
      have hb : p.1.size ≤ (encPair encNat encUnary p).length := by
        simpa [Nat.size_eq_bits_len] using length_le_encPair_left encNat encUnary p
      have hk : min i p.2 ≤ (encPair encNat encUnary p).length := by
        have hp := length_le_encPair_right encNat encUnary p
        simp only [encUnary_apply, List.length_replicate] at hp
        exact (Nat.min_le_right _ _).trans hp
      have hm := Nat.mul_le_mul hk hb
      exact hs.trans (Nat.add_le_add_right hm 1))
  simpa only [hfold] using h

end Turing.MultiTapeTM.ComputableInPolyTime
