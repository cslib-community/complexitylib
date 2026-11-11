/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Rat.Cast.Defs

/-!
# Polynomial-time primitives on rational numbers

Polynomial-time computability lemmas for `Turing.MultiTapeTM.encRat`: extracting the signed binary
numerator and binary denominator, and embedding integers into rationals.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.rat_pair`: projecting `q : ℚ` to `(q.num, q.den)`.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_num`: extracting `Rat.num`.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_den`: extracting `Rat.den`.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_intCast`: casting `ℤ → ℚ`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Projecting a rational number `q` to its numerator-denominator pair `(q.num, q.den)` is
computable in polynomial time under `encRat` and `encRatData`. -/
theorem rat_pair :
    ComputableInPolyTime (fun q : ℚ => (q.num, q.den)) encRat encRatData :=
  (ComputableTidilyInPolyTime.of_eq (f := fun q : ℚ => (q.num, q.den))
    (encIn := encRat) (encMid := encRatData) fun _ => rfl).computableInPolyTime

/-- Extracting the binary numerator `q.num` from `encRat q` is computable in polynomial time. -/
@[fun_prop]
theorem rat_num : ComputableInPolyTime Rat.num encRat encIntBin :=
  rat_pair.fst'

/-- Extracting the binary denominator `q.den` from `encRat q` is computable in polynomial time. -/
@[fun_prop]
theorem rat_den : ComputableInPolyTime Rat.den encRat encNat :=
  rat_pair.snd'

/-- Casting a binary integer `z : ℤ` to `(z : ℚ)` is computable in polynomial time under
`encIntBin` and `encRat`. -/
@[fun_prop]
theorem rat_intCast :
    ComputableInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encRat := by
  have h : ComputableInPolyTime (fun z : ℤ => (z, (1 : ℕ))) encIntBin encRatData := by
    fun_prop
  exact h.of_enc_eq fun z => by
    change encPair encIntBin encNat ((z : ℚ).num, (z : ℚ).den) =
      encPair encIntBin encNat (z, 1)
    rw [Rat.num_intCast, Rat.den_intCast]

end Turing.MultiTapeTM.ComputableInPolyTime
