/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Schoolbook subtraction: borrow execution, orientation and independent resources

The word fold subtracts the second operand from the first. The quantitative `natSub` certificate
instead consumes `(subtrahend, minuend)`, while the ordinary `binary_sub` facade uses the usual
`(minuend, subtrahend)` order. Concrete asymmetric cases and pair-encoding lengths distinguish
these conventions. The composed client reserves one unit after taking the truncated difference.
-/

open Turing.MultiTapeTM

-- Empty inputs, a zero subtrahend, equality and a negative difference exercise the actual fold.
example :
    let run (a b : ℕ) := (BinarySub.digitPairs (a, b)).foldl BinarySub.subStep (false, []);
    run 0 0 = (false, []) ∧
    (run 9 0).1 = false ∧ (run 9 0).2.foldr Nat.bit 0 = 9 ∧
    run 7 7 = (false, List.replicate 6 false) ∧
    (run 0 9).1 = true ∧ (run 3 10).1 = true ∧
    (run 10 3).1 = false ∧ (run 10 3).2.foldr Nat.bit 0 = 7 := by
  decide +kernel

-- Exercise the consuming realization itself, including both emptied cursors, long borrow,
-- and underflow. The padded output is decoded only when its final borrow is false.
example :
    let run (a b : ℕ) := (a.bits ++ b.bits).foldl BinarySub.cursorStep
      ((a.bits, b.bits), (false, []));
    run 65536 1 = (([], []), (false, List.replicate 16 true ++ [false, false])) ∧
    run 3 10 = (([], []), (true, [true, false, false, true, true, true])) ∧
    (if (run 65536 1).2.1 then 0 else ofBits (run 65536 1).2.2) = 65535 ∧
    (if (run 3 10).2.1 then 0 else ofBits (run 3 10).2.2) = 0 := by
  decide +kernel

-- Reuse the retained correctness law for the two decoded boundary results.
example : (65536 : ℕ) - 1 = 65535 ∧ (3 : ℕ) - 10 = 0 := by
  constructor
  · rw [BinarySub.sub_eq (65536, 1)]; decide +kernel
  · rw [BinarySub.sub_eq (3, 10)]; decide +kernel

-- Pair framing is asymmetric. Large values still have short encoded budgets.
example :
    let L (p : ℕ × ℕ) := (encPair encNat encNat p).length;
    L (3, 10) = 9 ∧ L (10, 3) = 11 ∧
    (L (3, 10) + 1) ^ 2 = 100 ∧ (L (10, 3) + 1) ^ 2 = 144 ∧
    (encNat (10 - 3)).length = 3 ∧ (encNat (3 - 10)).length = 0 ∧
    L (65536, 65537) = 52 ∧ (L (65536, 65537) + 1) ^ 2 = 2809 := by
  decide +kernel

-- The client reserves one unit after b-a. It consumes the new quantitative contract, keeps
-- linear space independently of quadratic time, and exercises the ordinary arithmetic facade.
example :
    let L (p : ℕ × ℕ) := (encPair encNat encNat p).length;
    let remaining (p : ℕ × ℕ) := p.2 - p.1 - 1;
    ComputableInO remaining (encPair encNat encNat) encNat
      (fun p => (L p + 1) ^ 2) (fun p => L p + 1) ∧
    ComputableInSpace remaining (encPair encNat encNat) encNat (fun p => L p + 1) ∧
    ComputableInPolyTime remaining (encPair encNat encNat) encNat ∧
    remaining (3, 10) = 6 ∧ remaining (10, 3) = 0 ∧ remaining (65536, 65537) = 0 := by
  dsimp only
  have h := ComputableInO.natPred.comp ComputableInO.natSub
  have hlen (p : ℕ × ℕ) :
      (encNat (p.2 - p.1)).length ≤ (encPair encNat encNat p).length := by
    have hsize : (encNat (p.2 - p.1)).length ≤ (encNat p.2).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using
        Nat.size_le_size (Nat.sub_le p.2 p.1)
    exact hsize.trans (length_le_encPair_right encNat encNat p)
  have hremaining : ComputableInO (fun p : ℕ × ℕ => p.2 - p.1 - 1)
      (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      (fun p => (encPair encNat encNat p).length + 1) := by
    refine h.mono 2 (fun p => ?_) (fun p => ?_)
    · have hpow := Nat.pow_le_pow_left (Nat.succ_le_succ (hlen p)) 2
      nlinarith
    · have := hlen p
      omega
  refine ⟨hremaining, ComputableInSpace.of_inO hremaining, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  exact ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.binary_sub' (ComputableInPolyTime.snd encNat encNat)
      (ComputableInPolyTime.fst encNat encNat)) (ComputableInPolyTime.const 1)

-- Consume the low normalizer in a numeric client. Malformed padding must not enlarge output
-- or force the workspace budget to match the quadratic time of the following predecessor.
example : ComputableInO (fun w : List Bool => ofBits w - 1) encBits encNat
      (fun w => (w.length + 1) ^ 2) (fun w => w.length + 1) ∧
    ofBits ([] : List Bool) - 1 = 0 ∧
    ofBits (List.replicate 17 false) - 1 = 0 ∧
    ofBits [false, false, true, false, false] - 1 = 3 := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have h := ComputableInO.natPred.comp ComputableInO.bitsToNat
  refine h.mono 2 (fun w => ?_) (fun w => ?_)
  · have hlen : (encNat (ofBits w)).length ≤ w.length := by
      rw [encNat_apply, bits_ofBits]
      exact (List.rdropWhile_prefix (!·) w).length_le
    have hpow := Nat.pow_le_pow_left (Nat.succ_le_succ hlen) 2
    nlinarith
  · have hlen : (encNat (ofBits w)).length ≤ w.length := by
      rw [encNat_apply, bits_ofBits]
      exact (List.rdropWhile_prefix (!·) w).length_le
    omega

-- The retained normalization law exposes precisely which padding the real decoder discards.
example : encNat (ofBits []) = [] ∧
    encNat (ofBits (List.replicate 17 false)) = [] ∧
    encNat (ofBits [false, false, true, false, false]) = [false, false, true] := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [encNat_apply, bits_ofBits] <;> decide +kernel
