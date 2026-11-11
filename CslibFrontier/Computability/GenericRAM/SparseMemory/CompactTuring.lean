/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.SparseMemory.Compact
public import CslibFrontier.Computability.GenericRAM.SparseMemory.Turing
import all CslibFrontier.Computability.GenericRAM.SparseMemory.Compact
import all CslibFrontier.Computability.GenericRAM.SparseMemory.Turing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists

/-!
# Charged bit-machine compaction of sparse memory

One native multitape machine filters every explicit default binding. Both the
surviving encoded store and the filtering workspace are linear in the input wire;
the scan/copying implementation has a cubic time bound. Compaction removes the
historical-zero obstruction, without making association-list access efficient.
-/

public section
namespace Cslib.GenericRAM.SparseMemory
open Turing.MultiTapeTM ComputableInO

variable {Address Value : Type} [DecidableEq Value]
variable (encA : Address ↪ List Bool) (encV : Value ↪ List Bool)

/-- Default followed by all actually stored bindings. -/
def compactEncoding : (Value × SparseMemory Address Value) ↪ List Bool :=
  encPair encV (encoding encA encV)

private def testTime (q : Value × (Address × Value)) : ℕ :=
  2 * (encPair encV (encPair encA encV) q).length +
    ((encV q.1).length + 1) * ((encV q.1).length + (encV q.2.2).length + 1)

private def testSpace (q : Value × (Address × Value)) : ℕ :=
  2 * (encPair encV (encPair encA encV) q).length +
    (encPair encV encV (q.1, q.2.2)).length

private theorem test_inO : ComputableInO
    (fun q : Value × (Address × Value) => decide (q.2.2 ≠ q.1))
    (encPair encV (encPair encA encV)) encBool (testTime encA encV) (testSpace encA encV) := by
  have h := (ComputableInO.eq encV).comp
    ((fst encV (encPair encA encV)).prod (snd encV (encPair encA encV)).snd')
  have hn := (ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) Bool.not).inO_one.comp_linear h
  convert hn using 1 <;> funext q <;> simp [testTime, testSpace, two_mul, ne_comm]

/-- Actual scan, comparison and output-copying time. -/
def compactTime (q : Value × SparseMemory Address Value) : ℕ :=
  3 * (compactEncoding encA encV q).length + ((entries q.2).length + 1) *
    ((encV q.1).length + (encoding encA encV q.2).length +
      listMax (fun e => testTime encA encV (q.1, e)) (entries q.2))

/-- Simultaneous filtering workspace, including the full retained output. -/
def compactSpace (q : Value × SparseMemory Address Value) : ℕ :=
  3 * (compactEncoding encA encV q).length + (encV q.1).length +
    (encoding encA encV q.2).length +
      listMax (fun e => testSpace encA encV (q.1, e)) (entries q.2)

/-- An actual bit machine implements compaction, with no supplied memory-normalization oracle. -/
theorem compact_inO : ComputableInO
    (fun q : Value × SparseMemory Address Value => compact q.1 q.2)
    (compactEncoding encA encV) (encoding encA encV)
    (compactTime encA encV) (compactSpace encA encV) := by
  have hlist : ComputableInO (fun q : Value × SparseMemory Address Value => entries q.2)
      (compactEncoding encA encV) (encList (encPair encA encV))
      (fun q => (compactEncoding encA encV q).length)
      (fun q => (compactEncoding encA encV q).length) :=
    (snd encV (encoding encA encV)).of_enc_eq (fun _ => rfl)
  have h := filterWith (test_inO encA encV) (fst encV (encoding encA encV)) hlist
  have hc := h.of_enc_eq (g := fun q : Value × SparseMemory Address Value => compact q.1 q.2)
    (encC := encoding encA encV) (fun q => by
      simp only [encoding_apply, entries_compact])
  convert hc using 1 <;> first | rfl |
    (funext q; simp only [compactTime, compactSpace, compactEncoding, encoding_apply]; omega)

omit [DecidableEq Value] in
/-- Filtering uses linear simultaneous workspace, even when most stored bindings are default. -/
theorem compactSpace_le (q : Value × SparseMemory Address Value) :
    compactSpace encA encV q ≤ 10 * ((compactEncoding encA encV q).length + 1) := by
  have hmax : listMax (fun e => testSpace encA encV (q.1, e)) (entries q.2) ≤
      3 * (compactEncoding encA encV q).length := by
    apply listMax_le
    intro e he
    have hl := length_le_encList_of_mem (encPair encA encV) he
    simp only [← encoding_apply, length_encPair] at hl
    simp only [testSpace, compactEncoding, length_encPair]
    omega
  simp only [compactSpace, compactEncoding, length_encPair] at hmax ⊢
  omega

omit [DecidableEq Value] in
/-- The concrete scan has cubic time in its entire encoded input, not in native support alone. -/
theorem compactTime_le (q : Value × SparseMemory Address Value) :
    compactTime encA encV q ≤ 30 * ((compactEncoding encA encV q).length + 1) ^ 3 := by
  let I := (compactEncoding encA encV q).length
  have hd : (encV q.1).length ≤ I := by
    dsimp only [I, compactEncoding]
    simp only [length_encPair]
    omega
  have hm : (encoding encA encV q.2).length ≤ I := by
    dsimp only [I, compactEncoding]
    simp only [length_encPair]
    omega
  have hc : (entries q.2).length ≤ I :=
    (length_le_length_encList (encPair encA encV) (entries q.2)).trans hm
  have ht : listMax (fun e => testTime encA encV (q.1, e)) (entries q.2) ≤
      10 * (I + 1) ^ 2 := by
    apply listMax_le
    intro e he
    have hl := length_le_encList_of_mem (encPair encA encV) he
    simp only [← encoding_apply, length_encPair] at hl
    have hv : (encV e.2).length ≤ I := by omega
    have hin : (encPair encV (encPair encA encV) (q.1, e)).length ≤ 3 * I + 1 := by
      simp only [length_encPair]
      omega
    have mul := Nat.mul_le_mul (Nat.add_le_add_right hd 1)
      (show (encV q.1).length + (encV e.2).length + 1 ≤ 2 * I + 1 by omega)
    dsimp only [testTime]
    nlinarith
  dsimp only [compactTime]
  change 3 * I + _ ≤ _
  have mul := Nat.mul_le_mul (Nat.add_le_add_right hc 1)
    (show (encV q.1).length + (encoding encA encV q.2).length +
      listMax (fun e => testTime encA encV (q.1, e)) (entries q.2) ≤
        2 * I + 10 * (I + 1) ^ 2 by omega)
  nlinarith

/-- Cubic scan time and linear simultaneous bit workspace, for one actual compaction machine. -/
theorem compact_inO_cube : ComputableInO
    (fun q : Value × SparseMemory Address Value => compact q.1 q.2)
    (compactEncoding encA encV) (encoding encA encV)
    (fun q => ((compactEncoding encA encV q).length + 1) ^ 3)
    (fun q => (compactEncoding encA encV q).length + 1) :=
  (compact_inO encA encV).mono 30
    (fun q => (compactTime_le encA encV q).trans (by omega))
    (fun q => (compactSpace_le encA encV q).trans (by omega))

/-- Filtering never increases the actual encoded memory length. -/
theorem length_encoding_compact_le (default : Value)
    (s : SparseMemory Address Value) :
    (encoding encA encV (compact default s)).length ≤ (encoding encA encV s).length := by
  simp only [encoding_apply, entries_compact]
  exact ComputableTidilyInDegree.length_encList_filter_le (encPair encA encV) _ _

end Cslib.GenericRAM.SparseMemory
