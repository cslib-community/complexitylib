/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Certificate
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary

/-!
# Fixed-width binary certificates for labelled branches

Each occurrence index occupies one fixed-width binary block. The width is fixed by the machine,
not by its input. Distinct indices remain distinct even when their actions or successors agree.

## Main definitions

* `Turing.MultiTapeCTM.binaryCertificate`: concatenate the fixed-width index codes.
* `Turing.MultiTapeCTM.binaryIndices`: read a fixed number of binary blocks as indices.

## Main results

* `Turing.MultiTapeCTM.binaryIndices_binaryCertificate`: decoding the code recovers its indices.
* `Turing.MultiTapeCTM.binaryCertificate_binaryIndices`: full-width words are recovered exactly.
* `Turing.MultiTapeCTM.card_binaryCertificateAccepts`: binary words preserve exact branch counts.
* `Turing.MultiTapeCTM.decodeCertificate_indices_lt`: a transition-list bound also bounds every
  index in a successful canonical certificate, including terminal padding.

## References

The binary representation is the existing `Cslib.BitString.binaryWord`; its module records the
original formalization credit. The occurrence and padding semantics are `MultiTape.Counting` and
`MultiTape.Counting.Certificate`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib

/-- Encode each occurrence index as one fixed-width block, in chronological order. -/
def binaryCertificate (width : ℕ) (indices : List ℕ) : List Bool :=
  indices.flatMap (BitString.binaryWord width)

/-- Decode a specified number of fixed-width blocks using the existing bit-string row view. -/
def binaryIndices (count width : ℕ) (word : List Bool) : List ℕ :=
  (BitString.listRows count width word).map BitString.binaryValue

@[simp]
theorem length_binaryIndices (count width : ℕ) (word : List Bool) :
    (binaryIndices count width word).length = count := by
  simp [binaryIndices]

/-- Bounded indices each contribute exactly one full block. -/
theorem length_binaryCertificate {width : ℕ} {indices : List ℕ}
    (h : ∀ index ∈ indices, index < 2 ^ width) :
    (binaryCertificate width indices).length = indices.length * width := by
  induction indices with
  | nil => simp [binaryCertificate]
  | cons index rest ih =>
    simp only [binaryCertificate, List.flatMap_cons, List.length_append, List.length_cons]
    change (BitString.binaryWord width index).length + (binaryCertificate width rest).length =
      (rest.length + 1) * width
    rw [BitString.length_binaryWord (h index (by simp)),
      ih (fun i hi => h i (by simp [hi])), Nat.add_mul]
    simp [Nat.add_comm]

/-- Encoding followed by block decoding preserves every bounded occurrence index. -/
theorem binaryIndices_binaryCertificate {width : ℕ} {indices : List ℕ}
    (h : ∀ index ∈ indices, index < 2 ^ width) :
    binaryIndices indices.length width (binaryCertificate width indices) = indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [binaryCertificate, List.flatMap_cons, List.length_cons, binaryIndices]
    rw [BitString.listRows_succ_append rest.length width
      (BitString.length_binaryWord (h index (by simp)))]
    simp only [List.map_cons, BitString.binaryValue_binaryWord]
    exact congrArg (index :: ·) (ih (fun i hi => h i (by simp [hi])))

/-- Decoding and re-encoding a full-width word preserves all bits, including leading zeros. -/
theorem binaryCertificate_binaryIndices {count width : ℕ} {word : List Bool}
    (h : word.length = count * width) :
    binaryCertificate width (binaryIndices count width word) = word := by
  induction count generalizing word with
  | zero =>
    have : word = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst word
    rfl
  | succ count ih =>
    have htake : (word.take width).length = width := by
      simp only [List.length_take]
      apply Nat.min_eq_left
      rw [h, Nat.succ_mul]
      exact Nat.le_add_left _ _
    have hdrop : (word.drop width).length = count * width := by
      simp only [List.length_drop, h, Nat.succ_mul, Nat.add_sub_cancel]
    have hrows := BitString.listRows_succ_append count width htake (word.drop width)
    rw [List.take_append_drop] at hrows
    have hblock : BitString.binaryWord width (BitString.binaryValue (word.take width)) =
        word.take width := by
      apply BitString.binaryValue_injective_of_length_eq
      · rw [BitString.length_binaryWord (by
          simpa only [htake] using BitString.binaryValue_lt_two_pow (word.take width)), htake]
      · simp
    simp only [binaryIndices, hrows, List.map_cons, binaryCertificate, List.flatMap_cons]
    rw [hblock]
    change word.take width ++ binaryCertificate width
      (binaryIndices count width (word.drop width)) = word
    rw [ih hdrop, List.take_append_drop]

/-- Every used index is below the occurrence-list bound, without identifying equal successors. -/
theorem runBranch_indices_lt {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (machine : MultiTapeCTM k Symbol State) {bound : ℕ}
    (hbound : ∀ cfg : Cfg k Symbol State input, (machine.actions cfg).length ≤ bound)
    {cfg final : Cfg k Symbol State input} {choices : List ℕ}
    (hrun : machine.runBranch cfg choices = some final) :
    ∀ index ∈ choices, index < bound := by
  induction choices generalizing cfg with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨hlt, _⟩ := (machine.step?_eq_some_iff cfg next first).mp hstep
    intro index hindex
    rcases List.mem_cons.mp hindex with rfl | hindex
    · exact hlt.trans_le (hbound cfg)
    · exact ih hrest index hindex

/-- The same positive bound covers actual indices and the forced zero padding after halting. -/
theorem decodeCertificate_indices_lt {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (machine : MultiTapeCTM k Symbol State) {bound : ℕ} (hpos : 0 < bound)
    (hbound : ∀ cfg : Cfg k Symbol State input, (machine.actions cfg).length ≤ bound)
    {cfg final : Cfg k Symbol State input} {word choices : List ℕ}
    (hdecode : machine.decodeCertificate cfg word = some (choices, final)) :
    ∀ index ∈ word, index < bound := by
  obtain ⟨hrun, _, hword⟩ := machine.decodeCertificate_sound hdecode
  rw [hword]
  intro index hindex
  rcases List.mem_append.mp hindex with hindex | hindex
  · exact machine.runBranch_indices_lt hbound hrun index hindex
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hindex
    exact hpos

/-- Fixed-width binary words count the canonical occurrence certificates exactly, for any
terminal verdict. This is the common counting bijection for executable certificate checkers
and native binary-choice replay machines. The proof is extracted from
`Checker.acceptCount_checkBinary` by Samuel Schlesinger. -/
theorem card_binaryCertificateAccepts {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (machine : MultiTapeCTM k Symbol State) {width : ℕ}
    (cfg : Cfg k Symbol State input)
    (hbound : ∀ cfg : Cfg k Symbol State input, (machine.actions cfg).length ≤ 2 ^ width)
    (count : ℕ) (verdict : List Symbol → Bool) :
    (Finset.univ.filter fun word : BitString (count * width) =>
      machine.certificateAccepts verdict cfg
        (binaryIndices count width (List.ofFn word)) = true).card =
      machine.branchCount verdict count cfg := by
  rw [← machine.certificateCount_eq_branchCount]
  unfold certificateCount
  refine Finset.card_bij (fun word _ => binaryIndices count width (List.ofFn word)) ?_ ?_ ?_
  · intro word hword
    have hcheck := (Finset.mem_filter.mp hword).2
    refine Finset.mem_filter.mpr ⟨(machine.mem_certificates_iff _ _ _).mpr ⟨by simp, ?_⟩,
      hcheck⟩
    unfold certificateAccepts at hcheck
    cases hdecode : machine.decodeCertificate cfg
        (binaryIndices count width (List.ofFn word)) <;>
      simp_all
  · intro left _ right _ heq
    apply List.ofFn_injective
    calc
      List.ofFn left = binaryCertificate width (binaryIndices count width (List.ofFn left)) :=
        (binaryCertificate_binaryIndices List.length_ofFn).symm
      _ = binaryCertificate width (binaryIndices count width (List.ofFn right)) :=
        congrArg (binaryCertificate width) heq
      _ = List.ofFn right := binaryCertificate_binaryIndices List.length_ofFn
  · intro indices hindices
    obtain ⟨hcert, hverdict⟩ := Finset.mem_filter.mp hindices
    obtain ⟨hlen, hvalid⟩ := (machine.mem_certificates_iff _ _ _).mp hcert
    obtain ⟨⟨choices, final⟩, hdecode⟩ := Option.isSome_iff_exists.mp hvalid
    have hsmall := machine.decodeCertificate_indices_lt (Nat.two_pow_pos _) hbound hdecode
    have hlength : (binaryCertificate width indices).length = count * width := by
      rw [length_binaryCertificate hsmall, hlen]
    let word := BitString.ofList (count * width) (binaryCertificate width indices)
    have hword : List.ofFn word = binaryCertificate width indices :=
      BitString.ofFn_ofList hlength
    have hround : binaryIndices count width (List.ofFn word) = indices := by
      rw [hword, ← hlen, binaryIndices_binaryCertificate hsmall]
    refine ⟨word, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hround⟩
    rw [hround]
    exact hverdict

end Turing.MultiTapeCTM
