/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Mathlib.Data.List.Perm.Basic

/-!
# Stable radix partition on an actual multitape machine

A runtime unary bit position selects two streaming filters on binary key/payload
records. A linear append puts the false-bit partition before the true-bit
partition. Payloads, collisions and multiplicities are preserved. Time is linear
in record count times a polynomial in the position and maximum record wire;
charged peak space includes the input, output and per-record machine workspace.

This is one real radix pass, not a complete sorting or dissection algorithm.
-/

public section
namespace Turing.MultiTapeTM.RadixPartition

/-- Binary key followed by binary payload, which can carry a packed witness. -/
def recordEncoding : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat

/-- Unary bit position followed by the actual binary records. -/
def inputEncoding : (ℕ × List (ℕ × ℕ)) ↪ List Bool :=
  encPair encUnary (encList recordEncoding)

/-- Retain exactly the records with the selected key bit, in their original order. -/
def select (bit : Bool) (input : ℕ × List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let (position, rows) := input
  rows.filter (fun row => row.1.testBit position == bit)

/-- One least-significant-bit radix pass. -/
def pass (input : ℕ × List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  select false input ++ select true input

/-- The selected key-bit test is computed from the actual binary key and unary position. -/
theorem select_computable (bit : Bool) :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (select bit) inputEncoding (encList recordEncoding)
        (fun input => (inputEncoding input).length + (input.2.length + 1) *
          P (streamFilterWidth encUnary recordEncoding input))
        (fun input => (inputEncoding input).length +
          P (streamFilterWidth encUnary recordEncoding input)) := by
  have key := (ComputableTidilyInPolyTime.fst encNat encNat).comp
    (ComputableTidilyInPolyTime.snd encUnary recordEncoding)
  have position := ComputableTidilyInPolyTime.fst encUnary recordEncoding
  have test := (key.binary_testBit position).beq
    (ComputableTidilyInPolyTime.const bit)
  exact ComputableInO.filter_stream (ComputableInPolyTime.of_tidy test)

/-- Two actual streaming machines, with linear append and all simultaneous buffers charged. -/
theorem pass_computable :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO pass inputEncoding (encList recordEncoding)
        (fun input => 2 * (inputEncoding input).length + (input.2.length + 1) *
          P (streamFilterWidth encUnary recordEncoding input))
        (fun input => 2 * (inputEncoding input).length +
          P (streamFilterWidth encUnary recordEncoding input)) := by
  obtain ⟨P₀, h₀, hm₀, c₀⟩ := select_computable false
  obtain ⟨P₁, h₁, hm₁, c₁⟩ := select_computable true
  refine ⟨fun B => P₀ B + P₁ B, h₀.add h₁, hm₀.add hm₁, ?_⟩
  have h := (ComputableInO.append' (enc := recordEncoding)).comp_linear (c₀.prod c₁)
  convert h using 1 <;> first | rfl | (funext input; dsimp only; ring)

/-- No key, payload, collision or multiplicity is lost by a pass. -/
theorem pass_perm (input : ℕ × List (ℕ × ℕ)) : (pass input).Perm input.2 := by
  simpa [pass, select] using
    List.filter_append_perm (fun row : ℕ × ℕ => !row.1.testBit input.1) input.2

/-- The pass preserves the exact encoded record volume, not just the number of records. -/
theorem pass_encoding_length (input : ℕ × List (ℕ × ℕ)) :
    (encList recordEncoding (pass input)).length = (encList recordEncoding input.2).length := by
  exact (List.Perm.flatMap_right (fun row => frame (recordEncoding row))
    (pass_perm input)).length_eq

/-- The output cannot acquire a wider record. -/
theorem pass_recordLength (input : ℕ × List (ℕ × ℕ)) :
    streamRecordLength recordEncoding (pass input) =
      streamRecordLength recordEncoding input.2 := by
  unfold streamRecordLength
  apply le_antisymm <;> apply listMax_le
  · intro row hr
    exact le_listMax (f := fun row => (recordEncoding row).length)
      ((pass_perm input).mem_iff.mp hr)
  · intro row hr
    exact le_listMax (f := fun row => (recordEncoding row).length)
      ((pass_perm input).mem_iff.mpr hr)

/-- Each selected part is a stable sublist; relative order of equal keys is unchanged. -/
theorem select_sublist (bit : Bool) (input : ℕ × List (ℕ × ℕ)) :
    (select bit input).Sublist input.2 := List.filter_sublist

end Turing.MultiTapeTM.RadixPartition
