/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD

/-!
# Binary digit access in linear work space

A bit of a binary natural is obtained by iterating the tail of its binary encoding and reading
its head, with a missing bit read as false. Every intermediate word is a suffix of the input
word. The iteration count is binary; its value is not charged as work space.

This proof was extracted unchanged from Christian Reitwiessner's tree-evaluation reader so that
numeric algorithms can reuse it without depending on tree evaluation.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.natTestBit`: binary digit access in work space
  linear in the binary encodings of both the value and the index.

## References

* [N. Immerman, *Descriptive Complexity*, proof of Theorem 3.1][Immerman1999].
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace ComputableInSpace

/-- **A bit of a binary natural**, `k.testBit j` from `(k, j)`. -/
theorem natTestBit :
    ComputableInSpace (fun q : ℕ × ℕ => q.1.testBit q.2) (encPair encNat encNat) encBool
      fun q => 32 * ((encPair encNat encNat q).length + 1) := by
  have hl : (fun q => (encPair encNat encNat q).length) ≼
      fun q => 8 * ((encPair encNat encNat q).length + 1) := .of_le fun _ => by omega
  have hbits : ComputableInSpace (fun q : ℕ × ℕ => q.1.bits) (encPair encNat encNat) encBits
      fun q => 8 * ((encPair encNat encNat q).length + 1) :=
    ((fst encNat encNat).weaken hl).of_enc_eq fun _ => rfl
  have htail : ComputableInSpace List.tail encBits encBits fun l => (encBits l).length :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have hlen (q : ℕ × ℕ) (i : ℕ) :
      (encBits (List.tail^[i] q.1.bits)).length ≤ (encNat q.1).length := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      simp only [encBits_apply, List.length_tail] at ih ⊢
      omega
  have h := iterate (n := fun q : ℕ × ℕ => q.2) ((snd encNat encNat).weaken hl) hbits htail
    (Q := fun q => (encNat q.1).length) (B := fun q => (encNat q.1).length)
    (fun q k _ => hlen q k) (fun q k _ => hlen q k)
  have hhead : ComputableInSpace (fun l : List Bool => l.headD false) encBits encBool
      fun l => (encBits l).length :=
    of_inO (.of_linear (ListEncoding.headD false))
  refine (budget_comp_linear hhead h).mono_le (fun q => ?_) |>.of_enc_eq fun q => ?_
  · simp only [length_encPair]; omega
  · rw [List.tail_iterate, Nat.testBit_eq_inth]
    congr 1
    rw [List.headD_eq_head?_getD, List.head?_drop, List.getI_eq_getElem?_getD]
    rfl

end ComputableInSpace

namespace ComputableTidilyInSpace

/-- **A bit of a binary natural**, `k.testBit j` from `(k, j)`. -/
theorem natTestBit :
    ComputableTidilyInSpace (fun q : ℕ × ℕ => q.1.testBit q.2) (encPair encNat encNat) encBool
      fun q => 32 * ((encPair encNat encNat q).length + 1) :=
  ComputableInSpace.natTestBit.tidy

end ComputableTidilyInSpace

end Turing.MultiTapeTM
