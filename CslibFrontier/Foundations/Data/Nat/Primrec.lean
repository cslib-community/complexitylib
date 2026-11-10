/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/Primrec/List.lean`)

public import CslibFrontier.Foundations.Data.Nat.Bits
public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursiveness of binary-digit reconstruction

## Main results

* `Primrec.list_foldr_nat_bit`: folding `Nat.bit` over a binary string is primitive recursive.
-/

@[expose] public section

/-- Folding `Nat.bit` over a binary string, which inverts `Nat.bits` (`Nat.foldr_bit_bits`), is
primitive recursive. -/
theorem Primrec.list_foldr_nat_bit : Primrec fun l : List Bool => l.foldr Nat.bit 0 := by
  have hbit : Primrec₂ fun (_ : List Bool) (bn : Bool × ℕ) => Nat.bit bn.1 bn.2 :=
    Primrec₂.mk <| (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_double_succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_double.comp (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hbit).of_eq fun _ => rfl
