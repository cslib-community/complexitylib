/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.PolyTime

/-! Complete cross-layer carry queries, including finishing gates and boundary carries. -/

namespace CslibFrontierTests.CarryLookaheadQuery

open Cslib Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarryLookahead.Query
open Turing.MultiTapeTM ComputableInPolyTime

/-- At width zero the outgoing carry is precisely the incoming carry. -/
example (b : Bool) : value 0 0 (fun _ => b) (.generate 0 0) = b := by
  have h := value_carry_eq 0 (fun _ => b)
  rw [eval_carryLookahead_carry] at h
  simpa [CarryLookahead.inputCarry] using h

/-- An arbitrary addressed sum bit agrees with the real width-parametric adder. -/
example (w : ℕ) (u : BitString (w + w + 1)) (i : Fin w) :
    value w (Nat.clog 2 (w + 1)) u (.sum i) =
      (carryLookahead w).eval interpretation u i.castSucc := value_sum_eq w u i

/-- The finishing gate routes into the logarithmic carry row, not an enumerated circuit. -/
example (w r i : ℕ) (u : BitString (w + w + 1)) :
    (decoder w r u).child (.sumAnd i) true = .generate r (w - i) := rfl

/-- A large row's carry query loses only two rank units per doubling round. -/
example (r i : ℕ) : rank 100 (.generate (r + 1) i) = rank 100 (.generate r i) + 2 := by
  simp [rank, Nat.mul_add, Nat.add_assoc]

/-- A single native machine handles binary runtime widths and arbitrary encoded addresses. -/
example : ComputableInPolyTime
    (fun p : ℕ × AddressData => childData p.1 10 p.2 true)
    (encPair encNat encAddressData) encAddressData :=
  childData_polyTime (by fun_prop) (.const _) (by fun_prop) (.const _)

/-- Input bits remain runtime data: the decoder reads them through charged list lookup. -/
example : ComputableInPolyTime
    (fun p : List Bool × AddressData => opData 4 p.1 p.2)
    (encPair encBits encAddressData) encOp :=
  opData_polyTime (.const _) (by fun_prop) (by fun_prop)

/-- The native child computation jumps from a finishing query into the carry row. -/
example : childData 1024 11 (Address.sumAnd 5).toData true =
    (Address.generate 11 1019).toData := rfl

end CslibFrontierTests.CarryLookaheadQuery
