/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Clients for uniform signed counting aggregation -/

open Cslib.Complexity Turing.MultiTapeTM

/-- A genuinely input-dependent power of a negative gap. -/
example : (fun w : List Bool => (-1 : ℤ) ^ w.length) ∈ GapP encBits := by
  have hneg : (fun _ : List Bool => (-1 : ℤ)) ∈ GapP encBits :=
    GapP.neg_mem GapP.one_mem
  exact GapP.pow_mem_polyTime hneg (.of_tidy (ComputableTidilyInPolyTime.encoding_length encBits))

/-- The exponent-zero case includes a zero base and returns one. -/
example : (fun _ : List Bool => (0 : ℤ) ^ (0 : ℕ)) ∈ GapP encBits :=
  GapP.pow_mem_polyTime GapP.zero_mem (.of_tidy (ComputableTidilyInPolyTime.const 0))

/-- Summing negative weights over an input-dependent Boolean cube. -/
example : (fun w : List Bool => -(2 : ℤ) ^ w.length) ∈ GapP encBits := by
  have hneg : (fun _ : List Bool × List Bool => (-1 : ℤ)) ∈ GapP (encPair encBits encBits) :=
    GapP.neg_mem GapP.one_mem
  convert GapP.sum_bits_mem hneg (.of_tidy (ComputableTidilyInPolyTime.encoding_length encBits))
    using 1
  ext w
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  simp


/-- Completely overlapping row verifiers cancel, even though each accepts every row. -/
example (n : ℕ) :
    (acceptCount (SignedProduct.verifier (fun _ : Unit => n + 1) (fun _ => 2)
      (fun _ => true) (fun _ => true) false) () ((n + 1) * 2) : ℤ) -
      acceptCount (SignedProduct.verifier (fun _ : Unit => n + 1) (fun _ => 2)
        (fun _ => true) (fun _ => true) true) () ((n + 1) * 2) = 0 := by
  rw [SignedProduct.count_sub]
  simp

/-- An empty product has positive signed count one, also for fully overlapping row verifiers. -/
example :
    (acceptCount (SignedProduct.verifier (fun _ : Unit => 0) (fun _ => 2)
      (fun _ => true) (fun _ => true) false) () 0 : ℤ) -
      acceptCount (SignedProduct.verifier (fun _ : Unit => 0) (fun _ => 2)
        (fun _ => true) (fun _ => true) true) () 0 = 1 := by
  have h := SignedProduct.count_sub (fun _ : Unit => 0) (fun _ => 2)
    (fun _ => true) (fun _ => true) ()
  simpa using h

/-- info: 'Cslib.Complexity.GapP.pow_mem_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.pow_mem_polyTime

/-- info: 'Cslib.Complexity.GapP.sum_bits_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.sum_bits_mem
