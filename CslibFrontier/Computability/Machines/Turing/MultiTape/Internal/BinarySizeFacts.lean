/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-! # Pure binary-size facts

Moved from the legacy binary calculus. No computability predicate is imported or introduced here.
`length_encNat_add_le` keeps its legacy qualified name in `ComputableTidilyInO`, a staged cleanup
item.
-/

namespace Turing.MultiTapeTM

/-- The length of `encNat` is monotone. -/
public lemma length_encNat_mono {m n : ℕ} (h : m ≤ n) : (encNat m).length ≤ (encNat n).length := by
  simpa [Nat.size_eq_bits_len] using Nat.size_le_size h

namespace ComputableTidilyInO

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `length_encNat_add_le` below, from that revision's `CslibFrontier/Binary`

/-- Adding `i` adds at most `i` bits. -/
public lemma length_encNat_add_le (n i : ℕ) : (encNat (n + i)).length ≤ (encNat n).length + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    refine le_trans ?_ (Nat.add_le_add_right ih 1)
    simp only [encNat_apply, Nat.size_eq_bits_len, ← Nat.add_assoc]
    refine Nat.size_le.mpr ((Nat.succ_le_of_lt (Nat.lt_size_self _)).trans_lt ?_)
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := (n + i).size)
    omega


end ComputableTidilyInO

end Turing.MultiTapeTM
