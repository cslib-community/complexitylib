/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary

/-!
# Subtraction and comparison in binary

Truncated subtraction `b - a` iterates the predecessor `a` times, counting in binary. It takes time
linear in the value `a` and work space linear in the lengths of the binary encodings. The order
`a < b` tests whether `b - a` is zero.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInO.natSub`: truncated subtraction in binary.
* `Turing.MultiTapeTM.ComputableTidilyInO.natLt`: the strict order in binary.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace ComputableTidilyInO

open Internal.BinaryCounter


/-- **Truncated subtraction in binary**, `b - a` from `(a, b)`. -/
public theorem natSub :
    ComputableTidilyInO (fun p : ℕ × ℕ => p.2 - p.1) (encPair encNat encNat) encNat
      (fun p => (p.1 + 1) * ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 := by
  have hfst : ComputableTidilyInO (fun p : ℕ × ℕ => p.1) (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) fun p => (encPair encNat encNat p).length :=
    fst encNat encNat
  have hsnd : ComputableTidilyInO (fun p : ℕ × ℕ => p.2) (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) fun p => (encPair encNat encNat p).length :=
    snd encNat encNat
  have hle (p : ℕ × ℕ) (k : ℕ) : (encNat ((· - 1)^[k] p.2)).length ≤ (encNat p.2).length := by
    rw [iterate_sub_one]; exact length_encNat_mono (Nat.sub_le _ _)
  have h := iterate (n := fun p : ℕ × ℕ => p.1) (init := fun p => p.2) (step := (· - 1))
    hfst hsnd natPred (R := fun p => ((encNat p.2).length + 1) ^ 2)
    (Q := fun p => (encNat p.2).length + 1) (B := fun p => (encNat p.2).length)
    (fun p k _ => Nat.pow_le_pow_left (by have := hle p k; omega) 2)
    (fun p k _ => by have := hle p k; omega) (fun p k _ => hle p k)
  refine (h.mono 8 (fun p => ?_) fun p => ?_).of_enc_eq fun p => by rw [iterate_sub_one]
  · simp only [length_encPair]
    nlinarith [Nat.zero_le ((encNat p.1).length), Nat.zero_le ((encNat p.2).length),
      Nat.zero_le (p.1 * (encNat p.1).length), Nat.zero_le (p.1 * (encNat p.2).length)]
  · simp only [length_encPair]
    omega

/-- **The strict order in binary.** -/
public theorem natLt :
    ComputableTidilyInO (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      (fun p => (p.1 + 1) * ((encPair encNat encNat p).length + 1) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 := by
  have hnot : ComputableTidilyInO (fun b : Bool => !b) encBool encBool
      (fun b => (encBool b).length) fun b => (encBool b).length :=
    (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool) _).inO_one
  have h := hnot.comp (natIsZero.comp natSub)
  refine (h.mono 4 (fun p => ?_) fun p => ?_).of_enc_eq fun p => ?_
  · have := length_encNat_mono (Nat.sub_le p.2 p.1)
    simp only [length_encPair, encBool_apply, List.length_singleton] at this ⊢
    generalize (encNat p.1).length = a at *
    generalize (encNat p.2).length = b at *
    have h1 : 2 * a + 1 + b + 1 ≤ (2 * a + 1 + b + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2 : (2 * a + 1 + b + 1) ^ 2 ≤ (p.1 + 1) * (2 * a + 1 + b + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have := length_encNat_mono (Nat.sub_le p.2 p.1)
    simp only [length_encPair, encBool_apply, List.length_singleton] at this ⊢
    omega
  · simp only [Function.comp_apply]
    congr 1
    by_cases h : p.1 < p.2 <;> simp [h] <;> omega

end ComputableTidilyInO

end Turing.MultiTapeTM
