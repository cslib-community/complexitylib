/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Division
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
public import CslibFrontier.Tactic.PolyTime.Init

/-!
# Polynomial-time division and remainder on binary naturals

Schoolbook shift-and-subtract long division over the binary encoding `Turing.MultiTapeTM.encNat`.
The dividend's binary digits are reversed to most-significant-bit-first order and folded with
`Turing.MultiTapeTM.BinaryDiv.divModStep`, which shifts the running remainder by one bit, adds the
next dividend bit, and subtracts the divisor whenever it fits. A zero divisor never subtracts, so
the quotient stays `0` and the remainder reconstructs the dividend, matching `a / 0 = 0` and
`a % 0 = a`.

After consuming any prefix `word` of the reversed digits, the state `(q, r)` is the quotient and
remainder of `Cslib.BitString.binaryValue word` by the divisor (`BinaryDiv.foldl_divModStep`). Both
components are therefore at most `binaryValue word < 2 ^ word.length`, so their binary encodings
have length at most `word.length`, keeping the encoded pair linearly bounded throughout the fold.

## Main definitions

* `Turing.MultiTapeTM.BinaryDiv.divModStep`: one shift-and-subtract step of binary long division.

## Main results

* `Turing.MultiTapeTM.BinaryDiv.foldl_divModStep`: folding `divModStep` over a
  most-significant-first bit word computes the quotient and remainder of its `binaryValue`.
* `Turing.MultiTapeTM.BinaryDiv.divMod_eq`: folding over `a.bits.reverse` computes
  `(a / b, a % b)`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_divMod`: joint quotient and remainder on
  `encNat`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div`, `.binary_mod`: binary division and
  remainder on `encNat`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div'`, `.binary_mod'`: composition rules
  for `fun_prop` and `polytime`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section



namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute both quotient and remainder of binary naturals by shift-and-subtract long division. -/
theorem binary_divMod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encNat encNat) (encPair encNat encNat) :=
  ComputableInPolyTime.binary_divMod.tidy

/-- Division of binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_div : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encNat encNat) encNat :=
  binary_divMod.fst'

/-- Remainder of binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_mod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encNat encNat) encNat :=
  binary_divMod.snd'

/-- Divide computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop, program_certificate]
theorem binary_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a / right a) input encNat :=
  binary_div.comp (hleft.prod hright)

/-- Remainder of computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop, program_certificate]
theorem binary_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a % right a) input encNat :=
  binary_mod.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
