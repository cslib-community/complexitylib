/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter

/-!
# Normalized bit clocks of the installed radix matcher

The actual `runCertificate` includes both tagging streams, radix sorting and the
original witness scan. Its clocks and prefix-workspace profiles are bounded by
record volume times a fixed polynomial in physical key/record width. No unit
record-cost or supplied runtime contract is used. This theorem concerns the
matching phases, not their input producers or a complete dissection algorithm.

## Main definitions

* `inputWidth`: unary key width plus maximum physical record wire and one.

## Main results

* `runCertificate_bounds`: the installed matcher's actual time and workspace profiles.
-/

public section
namespace Turing.MultiTapeTM.SortedMatch
open Cslib.GenericRAM

/-- Physical scalar width seen by tagging, sorting and the witness scan. -/
def inputWidth (input : Input) : ℕ :=
  let (width, (left, right)) := input
  width + streamRecordLength RadixPartition.recordEncoding (left ++ right) + 1

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er

private theorem profile_eq (input : Input) :
    runCertificate.time input = 5 * (encoding input).length +
      tagCertificate.time (false, input.2.1) + tagCertificate.time (true, input.2.2) +
      sortCertificate.time (input.1, tagged input) +
      scanCertificate.time (RadixSort.sort (input.1, tagged input)) ∧
    runCertificate.space input = 5 * (encoding input).length +
      tagCertificate.space (false, input.2.1) + tagCertificate.space (true, input.2.2) +
      sortCertificate.space (input.1, tagged input) +
      scanCertificate.space (RadixSort.sort (input.1, tagged input)) := by
  constructor <;>
    dsimp only [runCertificate, NativeCertificate.congr, NativeCertificate.comp,
      NativeCertificate.prod, NativeCertificate.post, NativeCertificate.fst,
      NativeCertificate.snd, NativeCertificate.const, NativeCertificate.linear,
      Function.comp_def, id_eq, tagged] <;> ring

/-- Both actual matcher resource profiles, including bit arithmetic, sorting passes,
framing, simultaneous inputs/intermediates and output readback, have a linear volume factor.
The polynomial is fixed before all runtime widths/lists. -/
theorem runCertificate_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : Input,
      let (_, (left, right)) := input
      runCertificate.time input + runCertificate.space input ≤
        (left.length+right.length+1) * P (inputWidth input) := by
  obtain ⟨A, hA, mA, boundA⟩ := exists_mono_poly
    (ComputableInPolyTime.of_tidy tag_polyTime).polyBounded_length
  let T := Classical.choose tag_computable
  have hT := (Classical.choose_spec tag_computable).1
  have mT : Monotone T := (Classical.choose_spec tag_computable).2.1
  let R := Classical.choose RadixSort.computable
  have hR := (Classical.choose_spec RadixSort.computable).1
  have mR : Monotone R := (Classical.choose_spec RadixSort.computable).2.1
  let S := Classical.choose scan_computable
  have hS := (Classical.choose_spec scan_computable).1
  have mS : Monotone S := (Classical.choose_spec scan_computable).2.1
  let D := fun B => B + A (B+3) + 3
  let E := fun B => D B + 1 + T (B+2) + R (D B) + S (D B)
  let P := fun B => 200 * (B+1) * E B
  have monoD : Monotone D := by
    intro a b hab
    have h := mA (by omega : a+3 ≤ b+3)
    dsimp only [D]; omega
  have monoE : Monotone E := by
    intro a b hab
    have hd := monoD hab
    have ht : T (a+2) ≤ T (b+2) := mT (by omega)
    have hr : R (D a) ≤ R (D b) := mR hd
    have hs : S (D a) ≤ S (D b) := mS hd
    dsimp only [E]; omega
  refine ⟨P, by dsimp only [P, E, D]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 200 (by omega)) (monoE hab)
  · rintro ⟨width, left, right⟩
    let input : Input := (width, (left, right))
    let n := left.length+right.length
    let B := inputWidth input
    let V := (n+1) * E B
    have hb : width ≤ B := by dsimp only [B, inputWidth, input]; omega
    have hd : B+1 ≤ D B+1 := by dsimp only [D]; omega
    have de : D B+1 ≤ E B := by dsimp only [E]; omega
    have te : T (B+2) ≤ E B := by dsimp only [E]; omega
    have re : R (D B) ≤ E B := by dsimp only [E]; omega
    have se : S (D B) ≤ E B := by dsimp only [E]; omega
    have originalRow (row : Record) (h : row ∈ left ++ right) : (er row).length ≤ B := by
      have hw := le_listMax (f := fun row => (er row).length) h
      change (er row).length ≤ streamRecordLength er (left ++ right) at hw
      change (er row).length ≤ width + streamRecordLength er (left ++ right) + 1
      omega
    have listWire (rows : List Record) (sub : ∀ r ∈ rows, r ∈ left ++ right) :
        (el rows).length ≤ rows.length * (2*B+1) :=
      length_encList_le er rows (fun r hr => originalRow r (sub r hr))
    have leftWire := listWire left (fun _ h => List.mem_append_left _ h)
    have rightWire := listWire right (fun _ h => List.mem_append_right _ h)
    have inputWire : (encoding input).length ≤ 10 * V := by
      have hE : (left.length+right.length+1)*(B+1) ≤ V :=
        Nat.mul_le_mul_left (n+1) (hd.trans de)
      dsimp only [encoding, input]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      change 2*width+1+(2*(el left).length+1+(el right).length) ≤ 10*V
      nlinarith only [leftWire, rightWire, hE, hb, Nat.zero_le B]
    have tagWidth (side : Bool) (rows : List Record)
        (sub : ∀ r ∈ rows, r ∈ left ++ right) :
        streamRecordLength er (rows.map (tag side)) ≤ A (B+3) := by
      apply listMax_le
      intro row hr
      obtain ⟨r, h, rfl⟩ := List.mem_map.mp hr
      have ha : (er (tag side r)).length ≤ A ((encPair encBool er) (side, r)).length :=
        boundA (side, r)
      have hw := originalRow r (sub r h)
      apply ha.trans (mA ?_)
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega
    have taggedWidth : streamRecordLength er (tagged input) ≤ A (B+3) := by
      apply listMax_le
      intro row hr
      rcases List.mem_append.mp hr with h | h
      · exact le_trans (le_listMax (f := fun row => (er row).length) h)
          (tagWidth false left (fun _ h => List.mem_append_left _ h))
      · exact le_trans (le_listMax (f := fun row => (er row).length) h)
          (tagWidth true right (fun _ h => List.mem_append_right _ h))
    have taggedLength : (tagged input).length = n := by simp [tagged, input, n]
    have sortedLength : (RadixSort.sort (width, tagged input)).length = n := by
      exact (sorted_perm input).length_eq.trans taggedLength
    have sortedWidth : streamRecordLength er (RadixSort.sort (width, tagged input)) ≤ A (B+3) := by
      apply listMax_le
      intro row hr
      exact (le_listMax (f := fun row => (er row).length)
        ((sorted_perm input).mem_iff.mp hr)).trans taggedWidth
    have taggedWire := length_encList_le er (tagged input)
      (fun row hr => (le_listMax (f := fun row => (er row).length) hr).trans taggedWidth)
    rw [taggedLength] at taggedWire
    have sortedWire := length_encList_le er (RadixSort.sort (width, tagged input))
      (fun row hr => (le_listMax (f := fun row => (er row).length) hr).trans sortedWidth)
    rw [sortedLength] at sortedWire
    have tagBound (side : Bool) (rows : List Record)
        (sub : ∀ r ∈ rows, r ∈ left ++ right) :
        tagCertificate.time (side, rows) ≤ 5 * (rows.length+1) * E B ∧
        tagCertificate.space (side, rows) = tagCertificate.time (side, rows) := by
      have hw := listWire rows sub
      have maxRow : streamRecordLength er rows ≤ B :=
        listMax_le (fun r hr => originalRow r (sub r hr))
      have arg : streamFilterWidth encBool er (side, rows) ≤ B+2 := by
        dsimp only [streamFilterWidth]
        simp only [encBool_apply, List.length_singleton]
        omega
      have ht := (mT arg).trans te
      have hE := hd.trans de
      constructor
      · change (encPair encBool el (side, rows)).length +
          (rows.length+1) * T (streamFilterWidth encBool er (side, rows)) ≤ _
        simp only [length_encPair, encBool_apply, List.length_singleton]
        nlinarith [Nat.mul_le_mul_left (rows.length+1) ht,
          Nat.mul_le_mul_left (rows.length+1) hE]
      · rfl
    have leftBound := tagBound false left (fun _ h => List.mem_append_left _ h)
    have rightBound := tagBound true right (fun _ h => List.mem_append_right _ h)
    have tags : tagCertificate.time (false, left) + tagCertificate.time (true, right) ≤ 10*V := by
      dsimp only [V, n]
      nlinarith [leftBound.1, rightBound.1]
    have sortArg : streamFilterWidth encUnary er (width, tagged input) ≤ D B := by
      dsimp only [streamFilterWidth]
      simp only [encUnary_apply, List.length_replicate]
      dsimp only [D]
      omega
    have wireBound (rows : List Record) (hn : rows.length = n)
        (hw : streamRecordLength er rows ≤ A (B+3)) : (el rows).length ≤ 3*V := by
      have h := length_encList_le er rows (fun r hr =>
        (le_listMax (f := fun row => (er row).length) hr).trans hw)
      rw [hn] at h
      have row : A (B+3) ≤ D B := by dsimp only [D]; omega
      have hi : (el rows).length ≤ 3*((n+1)*(D B+1)) := by
        nlinarith only [h, row, Nat.zero_le n, Nat.zero_le (D B)]
      exact hi.trans (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (n+1) de))
    have sortedWire' := wireBound _ sortedLength sortedWidth
    have sortWire : (RadixPartition.inputEncoding (width, tagged input)).length ≤ 5*V := by
      have rows := wireBound _ taggedLength taggedWidth
      have ev : B+1 ≤ V := (hd.trans de).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
      dsimp only [RadixPartition.inputEncoding]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      change 2*width+1+(el (tagged input)).length ≤ 5*V
      omega
    have sortCallback := (mR sortArg).trans re
    have sortTime : sortCertificate.time (width, tagged input) ≤ 6*(B+1)*V := by
      change (width+1) * ((RadixPartition.inputEncoding (width, tagged input)).length +
        ((tagged input).length+1)*R (streamFilterWidth encUnary er (width, tagged input))) ≤ _
      rw [taggedLength]
      have hm := Nat.mul_le_mul_left (n+1) sortCallback
      have hi : (RadixPartition.inputEncoding (width, tagged input)).length +
          (n+1)*R (streamFilterWidth encUnary er (width, tagged input)) ≤ 6*V := by
        change (n+1)*R (streamFilterWidth encUnary er (width, tagged input)) ≤ V at hm
        omega
      exact (Nat.mul_le_mul (by omega : width+1 ≤ B+1) hi).trans_eq (by ring)
    have sortSpace : sortCertificate.space (width, tagged input) ≤ sortCertificate.time
        (width, tagged input) := by
      change (RadixPartition.inputEncoding (width, tagged input)).length +
        R (streamFilterWidth encUnary er (width, tagged input)) ≤
        (width+1) * ((RadixPartition.inputEncoding (width, tagged input)).length +
          ((tagged input).length+1)*R (streamFilterWidth encUnary er (width, tagged input)))
      exact (Nat.add_le_add_left (Nat.le_mul_of_pos_left _
        (Nat.succ_pos (tagged input).length)) _).trans
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos width))
    have scanArg : streamRecordLength er (RadixSort.sort (width, tagged input))+1 ≤ D B := by
      dsimp only [D]; omega
    have scanCallback := (mS scanArg).trans se
    have scanTime : scanCertificate.time (RadixSort.sort (width, tagged input)) ≤ 4*V := by
      change (el (RadixSort.sort (width, tagged input))).length +
        ((RadixSort.sort (width, tagged input)).length+1)*
          S (streamRecordLength er (RadixSort.sort (width, tagged input))+1) ≤ _
      rw [sortedLength]
      have hm : (n+1)*S (streamRecordLength er (RadixSort.sort (width, tagged input))+1) ≤ V :=
        Nat.mul_le_mul_left (n+1) scanCallback
      omega
    have scanSpace : scanCertificate.space (RadixSort.sort (width, tagged input)) =
        scanCertificate.time (RadixSort.sort (width, tagged input)) := rfl
    have ht := (profile_eq input).1
    have hs := (profile_eq input).2
    rw [ht, hs, leftBound.2, rightBound.2, scanSpace]
    change _ ≤ (n+1)*P B
    have norm : (n+1)*P B = 200*(B+1)*V := by dsimp only [P, V]; ring
    rw [norm]
    nlinarith only [inputWire, tags, sortTime, sortSpace, scanTime, Nat.zero_le (B*V)]

end Turing.MultiTapeTM.SortedMatch
