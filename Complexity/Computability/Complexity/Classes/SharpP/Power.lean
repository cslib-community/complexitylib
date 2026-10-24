/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Uniform powers of #P functions

A polynomial-time unary repetition count permits a verifier to check an input-dependent
number of certificate rows. The number of accepted tuples is the corresponding power,
including exponent zero. Exact false-bit padding supplies a length-polynomial certificate.

## Main definitions

* `SharpP.powerVerifier`: accept precisely when every certificate row is accepted.

## Main results

* `SharpP.acceptCount_powerVerifier`: exact counting identity, including zero rows and width.
* `SharpP.pow_mem_polyTime`: unary polynomial-time powers preserve #P.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
-/

@[expose] public section

namespace Cslib.Complexity.SharpP

open Turing.MultiTapeTM Finset

variable {α : Type} {enc : α ↪ List Bool}

/-- Check every row of the repeated certificate, accepting the empty tuple. -/
def powerVerifier (r k : α → ℕ) (V : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  (BitString.listRows (r x.1) (k x.1) x.2).all fun row => V (x.1, row)

/-- A row count and width computed in unary give a polynomial-time repeated verifier. -/
@[fun_prop]
theorem polyTime_powerVerifier {r k : α → ℕ} {V : α × List Bool → Bool}
    (hr : ComputableInPolyTime r enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (powerVerifier r k V) (encPair enc encBits) encBool := by
  have hr := hr.tidy
  have hk := hk.tidy
  have hV := hV.tidy
  refine .of_tidy ?_
  unfold powerVerifier
  fun_prop

/-- The number of accepted row tuples is the power of the number of accepted rows. -/
theorem acceptCount_powerVerifier (r k : α → ℕ) (V : α × List Bool → Bool) (a : α) :
    acceptCount (powerVerifier r k V) a (r a * k a) = acceptCount V a (k a) ^ r a := by
  rw [show acceptCount V a (k a) ^ r a =
    ∏ _ : Fin (r a), acceptCount V a (k a) by simp]
  simp only [acceptCount]
  rw [← Fintype.card_piFinset]
  exact card_equiv BitString.blocksEquiv fun x => by
    simp [powerVerifier, BitString.listRows_eq_ofFn, Fintype.mem_piFinset]

/-- A #P function raised to an input-dependent polynomial-time unary exponent remains in #P. -/
theorem pow_mem_polyTime {f : α → ℕ} {r : α → ℕ} (hf : f ∈ SharpP enc)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => f a ^ r a) ∈ SharpP enc := by
  have hr := hr.tidy
  obtain ⟨p, V, hV, hf⟩ := mem_SharpP.mp hf
  let k : α → ℕ := fun a => p.eval (enc a).length
  have hk : ComputableTidilyInPolyTime k enc encUnary := by dsimp [k]; fun_prop
  convert mem_SharpP_of_polyTime_length (polyTime_powerVerifier (.of_tidy hr) (.of_tidy hk) hV)
    (.of_tidy (ComputableTidilyInPolyTime.unary_mul.comp (hr.prod hk))) using 1
  ext a
  change f a ^ r a = acceptCount (powerVerifier r k V) a (r a * k a)
  rw [acceptCount_powerVerifier, hf]

end Cslib.Complexity.SharpP
