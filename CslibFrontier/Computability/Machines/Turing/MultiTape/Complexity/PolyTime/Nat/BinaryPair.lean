/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# The pairing function on binary naturals in polynomial time

Mathlib's pairing function `Nat.pair a b` is `b * b + a` when `a < b` and `a * a + a + b`
otherwise. It is therefore a case distinction between binary sums and products, and is computable
in polynomial time on the binary encoding `Turing.MultiTapeTM.encNat`. The unary version is
`Turing.MultiTapeTM.ComputableInPolyTime.unary_pair`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_pair`: the pairing function, with both arguments
  and the result in binary.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_pair'`: the same for computed arguments, for
  `fun_prop`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The natural-number pairing function `Nat.pair`, with both arguments and the result in binary.
-/
theorem binary_pair :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2) (encPair encNat encNat) encNat := by
  have hfst := fst encNat encNat
  have hsnd := snd encNat encNat
  have h : (fun p : ℕ × ℕ => Nat.pair p.1 p.2) = fun p =>
      if decide (p.1 < p.2) then p.2 * p.2 + p.1 else p.1 * p.1 + p.1 + p.2 := by
    funext p
    simp [Nat.pair]
  rw [h]
  exact ite' (binary_lt' hfst hsnd) (binary_add' (binary_mul' hsnd hsnd) hfst)
    (binary_add' (binary_add' (binary_mul' hfst hfst) hfst) hsnd)

/-- Pair computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_pair' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => Nat.pair (left a) (right a)) input encNat :=
  binary_pair.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime
