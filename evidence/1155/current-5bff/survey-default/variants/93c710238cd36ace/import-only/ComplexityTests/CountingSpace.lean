/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Counting.OracleSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain


import Diag1155.Measure
/-! Clients for exact polynomial-space counting: zero-width certificates, a nonconstant verifier,
negative integer outputs, composite and degenerate moduli, and word-oracle space bounds. -/

@[expose] public section

open Cslib.Complexity Turing.MultiTapeTM

namespace CountingSpaceTests

def firstBit (x : List Bool × List Bool) : Bool := x.2.headD false

theorem firstBit_polyTime :
    ComputableTidilyInPolyTime firstBit (encPair encBits encBits) encBool := by
  unfold firstBit
  fun_prop

example : acceptCount firstBit [] 0 = 0 := by decide

example : acceptCount firstBit [] 4 = 8 := by decide

example : acceptCount (fun _ : List Bool × List Bool => true) [] 0 = 1 := by decide

-- The streaming counter runs through all `2 ^ 4` certificates and agrees with `acceptCount`.
example : streamAcceptCount firstBit [] 4 = 8 := by decide

example : streamAcceptCount firstBit [] 4 = acceptCount firstBit [] 4 :=
  streamAcceptCount_eq_acceptCount firstBit [] 4

example : ComputableTidilyInPolySpace
    (fun w : List Bool => acceptCount firstBit w (w.length + 1)) encBits encNat :=
  (computableInPolySpace_acceptCount (.of_tidy firstBit_polyTime) (.of_tidy (by fun_prop))).tidy

example : ComputableTidilyInPolySpace
    (fun w : List Bool => acceptCount firstBit w 0) encBits encNat :=
  (computableInPolySpace_acceptCount (.of_tidy firstBit_polyTime) (.of_tidy (.const 0))).tidy

theorem power_mem : (fun w : List Bool => 2 ^ w.length) ∈ SharpP encBits := by
  simpa using SharpP.two_pow_mem (enc := encBits) Polynomial.X

example : ComputableInPolySpace (fun w : List Bool => -((2 ^ w.length : ℕ) : ℤ))
    encBits encIntBin :=
  GapP.computableInPolySpace (GapP.neg_mem (SharpP.natCast_mem_GapP power_mem))

example (k : ℕ) : {w : List Bool | 2 ^ w.length % k ≠ 0} ∈ PSPACE encBits :=
  ModP_subset_PSPACE k ⟨_, power_mem, fun _ => Iff.rfl⟩

theorem shiftedPower_mem : (fun w : List Bool => 2 ^ w.length + 2) ∈ SharpP encBits :=
  SharpP.add_mem power_mem (SharpP.natCast_mem 2)

example : {w : List Bool | (2 ^ w.length + 2) % 6 = 0} ∈ PSPACE encBits :=
  coModP_subset_PSPACE 6
    (mem_coModP_iff_exists_SharpP.mpr ⟨_, shiftedPower_mem, fun _ => Iff.rfl⟩)

example : (2 ^ ([false, true] : List Bool).length + 2) % 6 = 0 := by decide

example : (2 ^ ([false] : List Bool).length + 2) % 6 ≠ 0 := by decide

example : {w : List Bool | 2 ^ w.length % 0 ≠ 0} ∈ PSPACE encBits :=
  ModP_subset_PSPACE 0 ⟨_, power_mem, fun _ => Iff.rfl⟩

example : {w : List Bool | 2 ^ w.length % 1 ≠ 0} ∈ PSPACE encBits :=
  ModP_subset_PSPACE 1 ⟨_, power_mem, fun _ => Iff.rfl⟩

example {A : Set (List Bool)} (hA : A ∈ PP encBits) : A ∈ PSPACE encBits :=
  PP_subset_PSPACE hA

example {A : Set (List Bool)} (hA : A ∈ PP encBits) :
    NPWithOracle A encBits ⊆ PSPACE encBits :=
  NPWithOracle_subset_PSPACE_of_mem_PP hA

example {α : Type} {enc : α ↪ List Bool} : PWithPPOracle enc ⊆ PSPACE enc :=
  PWithPPOracle_subset_PSPACE

example {α : Type} {enc : α ↪ List Bool} : PWithSharpPOracle enc ⊆ PSPACE enc :=
  PWithSharpPOracle_subset_PSPACE

-- The extension agrees on singleton codes without constraining its other answers.
example : ∃ g ∈ SharpP encBits, ∀ b : Bool, g [b] = 0 :=
  SharpP.exists_extension (enc := encBool) SharpP.zero_mem

end CountingSpaceTests
