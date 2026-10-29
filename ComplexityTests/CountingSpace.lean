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

/-! Clients for exact polynomial-space counting: zero-width certificates, a nonconstant verifier,
negative integer outputs, composite and degenerate moduli, and word-oracle space bounds. -/

@[expose] public section

open Cslib.Complexity Turing.MultiTapeTM

namespace CountingSpaceTests

def firstBit (x : List Bool × List Bool) : Bool := x.2.headD false

theorem firstBit_polyTime :
    ComputableInPolyTime firstBit (encPair encBits encBits) encBool := by
  unfold firstBit
  fun_prop

example : acceptCount firstBit [] 0 = 0 := by decide

example : acceptCount firstBit [] 4 = 8 := by decide

example : acceptCount (fun _ : List Bool × List Bool => true) [] 0 = 1 := by decide

-- The streaming counter runs through all `2 ^ 4` certificates and agrees with `acceptCount`.
example : streamAcceptCount firstBit [] 4 = 8 := by
  rw [streamAcceptCount_eq_acceptCount]
  decide

example : ComputableInPolySpace
    (fun w : List Bool => acceptCount firstBit w (w.length + 1)) encBits encNat :=
  computableInPolySpace_acceptCount firstBit_polyTime (by fun_prop)

example : ComputableInPolySpace
    (fun w : List Bool => acceptCount firstBit w 0) encBits encNat :=
  computableInPolySpace_acceptCount firstBit_polyTime (.const 0)

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

example :
    {w : List Bool | 2 ^ w.length % 0 ≠ 0} ∈ PSPACE encBits ∧
    {w : List Bool | 2 ^ w.length % 1 ≠ 0} ∈ PSPACE encBits :=
  ⟨ModP_subset_PSPACE 0 ⟨_, power_mem, fun _ => Iff.rfl⟩,
   ModP_subset_PSPACE 1 ⟨_, power_mem, fun _ => Iff.rfl⟩⟩

example {A L : Set (List Bool)} (hA : A ∈ PP encBits) (hL : L ∈ NPWithOracle A encBits) :
    Aᶜ ∈ PSPACE encBits ∧ Lᶜ ∈ PSPACE encBits :=
  ⟨compl_mem_PSPACE (PP_subset_PSPACE hA),
   compl_mem_PSPACE (NPWithOracle_subset_PSPACE_of_mem_PP hA hL)⟩

example : {w : List Bool | w.headD false = true} ∈ PSPACE encBits :=
  PWithPPOracle_subset_PSPACE
    (P_subset_PWithPPOracle ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

example : {w : List Bool | (2 ^ w.length).testBit 0 = true} ∈ PSPACE encBits :=
  PWithSharpPOracle_subset_PSPACE
    (mem_PWithSharpPOracle_of_testBit power_mem (p := 0) fun _ => by simp)

-- The extension agrees on singleton codes without constraining its other answers.
example : ∃ g ∈ SharpP encBits, g [false] = 1 ∧ g [true] = 1 := by
  obtain ⟨g, hg, h⟩ := SharpP.exists_extension (enc := encBool) SharpP.one_mem
  exact ⟨g, hg, h false, h true⟩

end CountingSpaceTests
