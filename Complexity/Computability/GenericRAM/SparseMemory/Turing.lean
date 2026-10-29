/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.SparseMemory.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops

/-!
# Native Turing-machine certificates for sparse memory

The association list is encoded as a list of encoded address/value pairs. Equality, first-match
search and filtering are implemented by the existing native multitape-machine calculus. No
memory operation is an oracle. Bounds depend on encoded address lengths, rather than allocating
space up to the numeric address. The cost functions are asymptotic bound expressions for
`ComputableInO`, not exact native step counts: one finite machine and a constant factor
work for all inputs, for each fixed choice of address and value encodings.

## Main definitions

* `SparseMemory.encoding`: the binary encoding of a finite sparse store.
* `SparseMemory.scanTime`, `SparseMemory.scanSpace`: parameterized scan bounds.

## Main results

* `SparseMemory.read_inO`, `insert_inO`: native TM read/write implementations with
  parameterized time and space, including argument extraction and a uniform read default.
* `SparseMemory.length_encoding_le`: stored-cell and word-length bound on the encoding.
* `SparseMemory.read_inO_cube`, `insert_inO_cube`: cubic time and linear workspace in full
  encoded input length; these conservative bounds are not optimality claims.
* `SparseMemory.read_polytime`, `insert_polytime`: registered polynomial-time corollaries.

## References

Uses Mathlib's association lists and Christian Reitwiessner's encoded native multitape-machine
calculus (`ComputableInO.eq`, `findWith`, and `filterWith`).
-/

@[expose] public section

namespace Cslib.GenericRAM.SparseMemory

open Turing.MultiTapeTM
open ComputableInO

variable {Address Value : Type}
variable (encA : Address ↪ List Bool) (encV : Value ↪ List Bool)

/-- Encode the distinct bindings using the existing framed pair and list encodings. -/
def encoding : SparseMemory Address Value ↪ List Bool :=
  ⟨fun s => encList (encPair encA encV) (entries s),
    fun _ _ h => entries_injective ((encList (encPair encA encV)).injective h)⟩

@[simp] theorem encoding_apply (s : SparseMemory Address Value) :
    encoding encA encV s = encList (encPair encA encV) (entries s) := rfl

/-- Encode a queried address and the store. -/
def queryEncoding : (Address × SparseMemory Address Value) ↪ List Bool :=
  encPair encA (encoding encA encV)

/-- The cost expression of the certified address comparison, including argument extraction. -/
def compareTime (q : Address × (Address × Value)) : ℕ :=
  2 * (encPair encA (encPair encA encV) q).length +
    ((encA q.1).length + 1) * ((encA q.1).length + (encA q.2.1).length + 1)

/-- Workspace for the certified address comparison, including argument extraction. -/
def compareSpace (q : Address × (Address × Value)) : ℕ :=
  2 * (encPair encA (encPair encA encV) q).length +
    (encPair encA encA (q.1, q.2.1)).length

/-- First-match search time: encoded input overhead plus one bounded scan round per binding. -/
def scanTime (q : Address × SparseMemory Address Value) : ℕ :=
  3 * (queryEncoding encA encV q).length + ((entries q.2).length + 1) *
    ((encA q.1).length + (encoding encA encV q.2).length +
      listMax (fun e => compareTime encA encV (q.1, e)) (entries q.2))

/-- First-match search workspace: input, store and the largest comparison workspace. -/
def scanSpace (q : Address × SparseMemory Address Value) : ℕ :=
  3 * (queryEncoding encA encV q).length + (encA q.1).length +
    (encoding encA encV q.2).length +
      listMax (fun e => compareSpace encA encV (q.1, e)) (entries q.2)

/-- Maximum encoded address length among stored cells, zero for the empty store. -/
def maxKeyLength (s : SparseMemory Address Value) : ℕ :=
  listMax (fun e => (encA e.1).length) (entries s)

/-- Maximum encoded value length among stored cells, zero for the empty store. -/
def maxValueLength (s : SparseMemory Address Value) : ℕ :=
  listMax (fun e => (encV e.2).length) (entries s)

/-- The encoded store depends on the number and encoded sizes of stored cells. -/
theorem length_encoding_le (s : SparseMemory Address Value) :
    (encoding encA encV s).length ≤ (entries s).length *
      (4 * maxKeyLength encA s + 2 * maxValueLength encV s + 3) := by
  have h := length_encList_le (encPair encA encV) (entries s)
    (b := 2 * maxKeyLength encA s + 1 + maxValueLength encV s) (fun e he => by
      have hk := le_listMax (f := fun e : Address × Value => (encA e.1).length) he
      have hv := le_listMax (f := fun e : Address × Value => (encV e.2).length) he
      simp only [length_encPair]
      change 2 * (encA e.1).length + 1 + (encV e.2).length ≤ _
      change (encA e.1).length ≤ maxKeyLength encA s at hk
      change (encV e.2).length ≤ maxValueLength encV s at hv
      omega)
  simp only [encoding_apply]
  convert h using 1
  congr 1
  omega

/-- A bound using entry count, encoded input length, and maximum key/value lengths. -/
theorem scanTime_le (q : Address × SparseMemory Address Value) :
    scanTime encA encV q ≤
      3 * (queryEncoding encA encV q).length + ((entries q.2).length + 1) *
        ((encA q.1).length + (encoding encA encV q.2).length +
          2 * (2 * (encA q.1).length + 2 * maxKeyLength encA q.2 +
            maxValueLength encV q.2 + 2) +
          ((encA q.1).length + 1) * ((encA q.1).length + maxKeyLength encA q.2 + 1)) := by
  have hm : listMax (fun e => compareTime encA encV (q.1, e)) (entries q.2) ≤
      2 * (2 * (encA q.1).length + 2 * maxKeyLength encA q.2 +
        maxValueLength encV q.2 + 2) +
      ((encA q.1).length + 1) * ((encA q.1).length + maxKeyLength encA q.2 + 1) := by
    apply listMax_le
    intro e he
    have hk := le_listMax (f := fun e : Address × Value => (encA e.1).length) he
    have hv := le_listMax (f := fun e : Address × Value => (encV e.2).length) he
    change (encA e.1).length ≤ maxKeyLength encA q.2 at hk
    change (encV e.2).length ≤ maxValueLength encV q.2 at hv
    simp only [compareTime, length_encPair]
    nlinarith
  have := Nat.mul_le_mul_left ((entries q.2).length + 1) hm
  unfold scanTime
  nlinarith

/-- Scan workspace is linear in the retained encoding and the largest encoded words. -/
theorem scanSpace_le (q : Address × SparseMemory Address Value) :
    scanSpace encA encV q ≤
      3 * (queryEncoding encA encV q).length + (encA q.1).length +
        (encoding encA encV q.2).length +
          2 * (2 * (encA q.1).length + 2 * maxKeyLength encA q.2 +
            maxValueLength encV q.2 + 2) +
          (2 * (encA q.1).length + maxKeyLength encA q.2 + 1) := by
  have hm : listMax (fun e => compareSpace encA encV (q.1, e)) (entries q.2) ≤
      2 * (2 * (encA q.1).length + 2 * maxKeyLength encA q.2 +
        maxValueLength encV q.2 + 2) +
      (2 * (encA q.1).length + maxKeyLength encA q.2 + 1) := by
    apply listMax_le
    intro e he
    have hk := le_listMax (f := fun e : Address × Value => (encA e.1).length) he
    have hv := le_listMax (f := fun e : Address × Value => (encV e.2).length) he
    change (encA e.1).length ≤ maxKeyLength encA q.2 at hk
    change (encV e.2).length ≤ maxValueLength encV q.2 at hv
    simp only [compareSpace, length_encPair]
    omega
  unfold scanSpace
  omega

/-- Every stored address is bounded by the total encoded store. -/
theorem maxKeyLength_le_encoding (s : SparseMemory Address Value) :
    maxKeyLength encA s ≤ (encoding encA encV s).length := by
  apply listMax_le
  intro e he
  have h := length_le_encList_of_mem (encPair encA encV) he
  simp only [length_encPair] at h
  simpa only [encoding_apply] using (show (encA e.1).length ≤ _ by omega)

/-- Every stored value is bounded by the total encoded store. -/
theorem maxValueLength_le_encoding (s : SparseMemory Address Value) :
    maxValueLength encV s ≤ (encoding encA encV s).length := by
  apply listMax_le
  intro e he
  have h := length_le_encList_of_mem (encPair encA encV) he
  simp only [length_encPair] at h
  simpa only [encoding_apply] using (show (encV e.2).length ≤ _ by omega)

/-- In particular, the scan's parameterized time bound is cubic in its encoded input length. -/
theorem scanTime_le_cube (q : Address × SparseMemory Address Value) :
    scanTime encA encV q ≤ 30 * ((queryEncoding encA encV q).length + 1) ^ 3 := by
  let E := (queryEncoding encA encV q).length
  have hE : E = 2 * (encA q.1).length + 1 + (encoding encA encV q.2).length :=
    length_encPair q
  have ha : (encA q.1).length ≤ E := by omega
  have hm : (encoding encA encV q.2).length ≤ E := by omega
  have hk := (maxKeyLength_le_encoding encA encV q.2).trans hm
  have hv := (maxValueLength_le_encoding encA encV q.2).trans hm
  have hn : (entries q.2).length ≤ E :=
    (length_le_length_encList (encPair encA encV) (entries q.2)).trans hm
  calc
    scanTime encA encV q ≤ _ := scanTime_le encA encV q
    _ ≤ 3 * E + (E + 1) *
        (E + E + 2 * (2 * E + 2 * E + E + 2) + (E + 1) * (E + E + 1)) := by
      gcongr
    _ ≤ 30 * (E + 1) ^ 3 := by ring_nf; omega

/-- The scan's workspace bound is linear in its encoded input length. -/
theorem scanSpace_le_linear (q : Address × SparseMemory Address Value) :
    scanSpace encA encV q ≤ 30 * ((queryEncoding encA encV q).length + 1) := by
  have hE : (queryEncoding encA encV q).length =
      2 * (encA q.1).length + 1 + (encoding encA encV q.2).length := length_encPair q
  have hk := maxKeyLength_le_encoding encA encV q.2
  have hv := maxValueLength_le_encoding encA encV q.2
  have h := scanSpace_le encA encV q
  omega

variable [DecidableEq Address]

open ComputableTidilyInDegree
  (findStep foldl_findStep filterStep foldl_filterStep length_encList_filter_le)

private theorem findWith {γ α π : Type} {encIn : γ ↪ List Bool} {enc : α ↪ List Bool}
    {encP : π ↪ List Bool} {par : γ → π} {list : γ → List α} {Tp Tl Sp Sl : γ → ℕ}
    {t : π × α → Bool} {Tt St : π × α → ℕ}
    (ht : ComputableInO t (encPair encP enc) encBool Tt St)
    (hpar : ComputableInO par encIn encP Tp Sp)
    (hlist : ComputableInO list encIn (encList enc) Tl Sl) :
    ComputableInO (fun x => (list x).find? fun a => t (par x, a)) encIn (encOption enc)
      (fun x => (encIn x).length + Tp x + Tl x + ((list x).length + 1) *
        ((encP (par x)).length + (encList enc (list x)).length +
          listMax (fun a => Tt (par x, a)) (list x)))
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length + listMax (fun a => St (par x, a)) (list x) := by
  have hq := fst (encPair encP (encOption enc)) enc
  have hel := snd (encPair encP (encOption enc)) enc
  have hisSome := (ComputableInDegree.isSome enc).inO_one.comp_linear hq.snd'
  have h := hisSome.ite hq.snd' ((ht.comp (hq.fst'.prod hel)).ite
    ((ComputableInDegree.optionSome (enc₁ := enc)).inO_one.comp_linear hel) (const none))
  have hstep : ComputableInO (fun q : (π × Option α) × α => findStep t q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encOption enc)) enc) (encOption enc)
      (fun q => (encPair (encPair encP (encOption enc)) enc q).length + Tt (q.1.1, q.2))
      fun q => (encPair (encPair encP (encOption enc)) enc q).length + St (q.1.1, q.2) := by
    refine (h.mono 4 (fun q => ?_) fun q => ?_).of_enc_eq fun ⟨⟨p, acc⟩, a⟩ => ?_
    · split_ifs <;> omega
    · split_ifs <;> omega
    · cases acc <;> simp [findStep]
  have hst (x : γ) (i : ℕ) :
      (encOption enc (((list x).take i).foldl (findStep t (par x)) none)).length ≤
        (encList enc (list x)).length + 1 := by
    rw [foldl_findStep, Option.none_or]
    exact (length_encOption_find?_le enc _ _).trans
      (Nat.add_le_add_right (length_encList_take_le enc _ _) 1)
  have hfold := foldlWith (encL := encList enc) (encB := encOption enc) hpar hlist
    (const none) hstep (R := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => Tt (par x, a)) (list x))
    (Q := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => St (par x, a)) (list x))
    (B := fun x => (encList enc (list x)).length + 1)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Tt (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => St (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i _ => by have := hst x i; omega)
  refine (hfold.mono 16 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · have h₁ := length_le_length_encList enc (list x)
    have h₂ : (list x).length ≤ (list x).length * (encList enc (list x)).length := by
      rcases Nat.eq_zero_or_pos (list x).length with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    ring_nf
    omega
  · omega
  · rw [foldl_findStep, Option.none_or]

private theorem filterWith {γ α π : Type} {encIn : γ ↪ List Bool} {enc : α ↪ List Bool}
    {encP : π ↪ List Bool} {par : γ → π} {list : γ → List α} {Tp Tl Sp Sl : γ → ℕ}
    {t : π × α → Bool} {Tt St : π × α → ℕ}
    (ht : ComputableInO t (encPair encP enc) encBool Tt St)
    (hpar : ComputableInO par encIn encP Tp Sp)
    (hlist : ComputableInO list encIn (encList enc) Tl Sl) :
    ComputableInO (fun x => (list x).filter fun a => t (par x, a)) encIn (encList enc)
      (fun x => (encIn x).length + Tp x + Tl x + ((list x).length + 1) *
        ((encP (par x)).length + (encList enc (list x)).length +
          listMax (fun a => Tt (par x, a)) (list x)))
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length + listMax (fun a => St (par x, a)) (list x) := by
  have hq := fst (encPair encP (encList enc)) enc
  have hel := snd (encPair encP (encList enc)) enc
  have h := (ht.comp (hq.fst'.prod hel)).ite
    ((ComputableInDegree.snoc enc).inO_one.comp_linear (hq.snd'.prod hel)) hq.snd'
  have hstep : ComputableInO
      (fun q : (π × List α) × α => filterStep t q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encList enc)) enc) (encList enc)
      (fun q => (encPair (encPair encP (encList enc)) enc q).length + Tt (q.1.1, q.2))
      fun q => (encPair (encPair encP (encList enc)) enc q).length + St (q.1.1, q.2) := by
    refine (h.mono 4 (fun q => ?_) fun q => ?_).of_enc_eq fun ⟨⟨p, acc⟩, a⟩ => ?_
    · split_ifs <;> omega
    · split_ifs <;> omega
    · simp [filterStep]
  have hst (x : γ) (i : ℕ) :
      (encList enc (((list x).take i).foldl (filterStep t (par x)) [])).length ≤
        (encList enc (list x)).length := by
    rw [foldl_filterStep, List.nil_append]
    exact (length_encList_filter_le enc _ _).trans (length_encList_take_le enc _ _)
  have hfold := foldlWith (encL := encList enc) (encB := encList enc) hpar hlist
    (const []) hstep (R := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => Tt (par x, a)) (list x))
    (Q := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length + 5 + listMax (fun a => St (par x, a)) (list x))
    (B := fun x => (encList enc (list x)).length + 1)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Tt (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => St (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i _ => by have := hst x i; omega)
  refine (hfold.mono 16 (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · have h₁ := length_le_length_encList enc (list x)
    have h₂ : (list x).length ≤ (list x).length * (encList enc (list x)).length := by
      rcases Nat.eq_zero_or_pos (list x).length with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    ring_nf
    omega
  · omega
  · rw [foldl_filterStep, List.nil_append]

private theorem compare_inO :
    ComputableInO (fun q : Address × (Address × Value) => decide (q.1 = q.2.1))
      (encPair encA (encPair encA encV)) encBool (compareTime encA encV)
      (compareSpace encA encV) := by
  have h := (ComputableInO.eq encA).comp
    ((fst encA (encPair encA encV)).prod (snd encA (encPair encA encV)).fst')
  convert h using 1 <;> funext q <;> simp [compareTime, compareSpace, two_mul]

/-- A native multitape machine searches the finite store, with parameterized time and space. -/
theorem find_inO :
    ComputableInO
      (fun q : Address × SparseMemory Address Value =>
        (entries q.2).find? (fun e => decide (q.1 = e.1)))
      (queryEncoding encA encV) (encOption (encPair encA encV))
      (scanTime encA encV) (scanSpace encA encV) := by
  have hpar := fst encA (encoding encA encV)
  have hlist : ComputableInO (fun q : Address × SparseMemory Address Value => entries q.2)
      (queryEncoding encA encV) (encList (encPair encA encV))
      (fun q => (queryEncoding encA encV q).length)
      (fun q => (queryEncoding encA encV q).length) :=
    (snd encA (encoding encA encV)).of_enc_eq fun _ => rfl
  have h := findWith (compare_inO encA encV) hpar hlist
  convert h using 1 <;> first | rfl |
    (funext q; simp only [scanTime, scanSpace, queryEncoding, encoding_apply]; omega)

/-- Filtering implements erasure using the same parameterized scan bounds. -/
theorem erase_entries_inO :
    ComputableInO
      (fun q : Address × SparseMemory Address Value =>
        (entries q.2).filter (fun e => decide (q.1 ≠ e.1)))
      (queryEncoding encA encV) (encList (encPair encA encV))
      (scanTime encA encV) (scanSpace encA encV) := by
  have hnot := (ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) Bool.not).inO_one
  have hcmp := hnot.comp_linear (compare_inO encA encV)
  have hlist : ComputableInO (fun q : Address × SparseMemory Address Value => entries q.2)
      (queryEncoding encA encV) (encList (encPair encA encV))
      (fun q => (queryEncoding encA encV q).length)
      (fun q => (queryEncoding encA encV q).length) :=
    (snd encA (encoding encA encV)).of_enc_eq fun _ => rfl
  have h := filterWith hcmp (fst encA (encoding encA encV)) hlist
  convert h using 1 <;> first | rfl |
    (funext q; simp only [scanTime, scanSpace, queryEncoding, encoding_apply]; omega)

/-- Binary input convention for a write: a new binding followed by the finite store. -/
def writeEncoding : ((Address × Value) × SparseMemory Address Value) ↪ List Bool :=
  encPair (encPair encA encV) (encoding encA encV)

/-- Charged write time, including preparing the scan and the new binding. -/
def writeTime (q : (Address × Value) × SparseMemory Address Value) : ℕ :=
  3 * (writeEncoding encA encV q).length + scanTime encA encV (q.1.1, q.2)

/-- Charged write workspace. -/
def writeSpace (q : (Address × Value) × SparseMemory Address Value) : ℕ :=
  3 * (writeEncoding encA encV q).length + scanSpace encA encV (q.1.1, q.2)

/-- Native TM implementation of insertion/replacement, including all argument preparation. -/
theorem insert_inO :
    ComputableInO
      (fun q : (Address × Value) × SparseMemory Address Value => q.2.insert q.1.1 q.1.2)
      (writeEncoding encA encV) (encoding encA encV)
      (writeTime encA encV) (writeSpace encA encV) := by
  have hb := fst (encPair encA encV) (encoding encA encV)
  have hs := snd (encPair encA encV) (encoding encA encV)
  have hf := (erase_entries_inO encA encV).comp (hb.fst'.prod hs)
  have hc := (ComputableInDegree.cons (encPair encA encV)).inO_one.comp_linear
    (hb.prod hf)
  have hout := hc.of_enc_eq (g := fun q => q.2.insert q.1.1 q.1.2)
    (encC := encoding encA encV) (fun q => by
      simp only [encoding_apply, entries_insert, Function.comp_def])
  convert hout using 1 <;> first | rfl |
    (funext q; simp only [writeTime, writeSpace, writeEncoding]; omega)

omit [DecidableEq Address] in
private theorem readResult_inO :
    ComputableInO
      (fun q : Option (Address × Value) × Value => (q.1.map Prod.snd).getD q.2)
      (encPair (encOption (encPair encA encV)) encV) encV
      (fun q => (encPair (encOption (encPair encA encV)) encV q).length)
      (fun q => (encPair (encOption (encPair encA encV)) encV q).length) := by
  have hd := snd (encOption (encPair encA encV)) encV
  rcases isEmpty_or_nonempty (Address × Value) with h | h
  · convert hd using 1
    funext q
    cases q.1 with
    | none => rfl
    | some e => exact isEmptyElim e
  · obtain ⟨e⟩ := h
    have ho := fst (encOption (encPair encA encV)) encV
    have ht := (ComputableInDegree.isSome (encPair encA encV)).inO_one.comp_linear ho
    have hv := ((ComputableInDegree.getD (enc₁ := encPair encA encV) e).inO_one
      |>.comp_linear ho).snd'
    have hr := (ht.ite hv hd).mono
      (T' := fun q => (encPair (encOption (encPair encA encV)) encV q).length)
      (S' := fun q => (encPair (encOption (encPair encA encV)) encV q).length) 2
      (fun q => by split <;> omega) (fun q => by split <;> omega)
    convert hr using 1
    funext q
    rcases q with ⟨o, d⟩
    cases o <;> rfl

/-- A read input supplies both the queried store and its default value. -/
def readEncoding : ((Address × SparseMemory Address Value) × Value) ↪ List Bool :=
  encPair (queryEncoding encA encV) encV

/-- Read time, including extraction of the query and the input-supplied default. -/
def readTime (q : (Address × SparseMemory Address Value) × Value) : ℕ :=
  2 * (readEncoding encA encV q).length + scanTime encA encV q.1

/-- Read workspace, including the input-supplied default. -/
def readSpace (q : (Address × SparseMemory Address Value) × Value) : ℕ :=
  2 * (readEncoding encA encV q).length + scanSpace encA encV q.1

/-- Native TM implementation of total memory reads, uniform also in the default value. -/
theorem read_inO :
    ComputableInO
      (fun q : (Address × SparseMemory Address Value) × Value => read q.2 q.1.1 q.1.2)
      (readEncoding encA encV) encV (readTime encA encV) (readSpace encA encV) := by
  have hf := (find_inO encA encV).comp (fst (queryEncoding encA encV) encV)
  have hd := snd (queryEncoding encA encV) encV
  have h := (readResult_inO encA encV).comp_linear (hf.prod hd)
  convert h using 1 <;> first | rfl |
    (funext q; exact read_eq_find q.2 q.1.1 q.1.2) |
    (funext q; simp only [readTime, readSpace, readEncoding]; omega)

/-- A cubic-time, linear-space specialization of the parameterized write certificate. -/
theorem insert_inO_cube :
    ComputableInO
      (fun q : (Address × Value) × SparseMemory Address Value => q.2.insert q.1.1 q.1.2)
      (writeEncoding encA encV) (encoding encA encV)
      (fun q => ((writeEncoding encA encV q).length + 1) ^ 3)
      (fun q => (writeEncoding encA encV q).length) := by
  apply (insert_inO encA encV).mono 40
  · intro q
    have hq : (queryEncoding encA encV (q.1.1, q.2)).length ≤
        (writeEncoding encA encV q).length := by
      simp only [queryEncoding, writeEncoding, length_encPair]
      omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3
    have ht := scanTime_le_cube encA encV (q.1.1, q.2)
    have he : (writeEncoding encA encV q).length ≤
        ((writeEncoding encA encV q).length + 1) ^ 3 := by ring_nf; omega
    unfold writeTime
    nlinarith
  · intro q
    have hs := scanSpace_le_linear encA encV (q.1.1, q.2)
    simp only [writeSpace, queryEncoding, writeEncoding, length_encPair] at hs ⊢
    omega

/-- A cubic-time, linear-space specialization of the parameterized read certificate. -/
theorem read_inO_cube :
    ComputableInO
      (fun q : (Address × SparseMemory Address Value) × Value => read q.2 q.1.1 q.1.2)
      (readEncoding encA encV) encV
      (fun q => ((readEncoding encA encV q).length + 1) ^ 3)
      (fun q => (readEncoding encA encV q).length) := by
  apply (read_inO encA encV).mono 40
  · intro q
    have hq : (queryEncoding encA encV q.1).length ≤ (readEncoding encA encV q).length := by
      simp only [readEncoding, length_encPair]
      omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3
    have ht := scanTime_le_cube encA encV q.1
    have he : (readEncoding encA encV q).length ≤
        ((readEncoding encA encV q).length + 1) ^ 3 := by ring_nf; omega
    unfold readTime
    nlinarith
  · intro q
    have hs := scanSpace_le_linear encA encV q.1
    simp only [readSpace, readEncoding, length_encPair] at hs ⊢
    omega

/-- Polynomial-time writes are a corollary of the native parameterized certificate. -/
@[fun_prop]
theorem insert_polytime :
    ComputableInPolyTime
      (fun q : (Address × Value) × SparseMemory Address Value => q.2.insert q.1.1 q.1.2)
      (writeEncoding encA encV) (encoding encA encV) :=
  (insert_inO_cube encA encV).computableInPolyTime
    (.of_forall_le 1 3 (by simp)) .self

/-- Polynomial-time reads are uniform in the queried address, store, and default value. -/
@[fun_prop]
theorem read_polytime :
    ComputableInPolyTime
      (fun q : (Address × SparseMemory Address Value) × Value => read q.2 q.1.1 q.1.2)
      (readEncoding encA encV) encV :=
  (read_inO_cube encA encV).computableInPolyTime
    (.of_forall_le 1 3 (by simp)) .self

/-- Writing preserves maximum key length up to the newly supplied address. -/
theorem maxKeyLength_insert_le (a : Address) (v : Value) (s : SparseMemory Address Value) :
    maxKeyLength encA (s.insert a v) ≤ max (encA a).length (maxKeyLength encA s) := by
  apply listMax_le
  intro e he
  rcases mem_entries_insert.mp he with rfl | ⟨he, _⟩
  · exact le_max_left _ _
  · exact (le_listMax (f := fun e : Address × Value => (encA e.1).length) he).trans
      (le_max_right _ _)

/-- Writing preserves maximum value length up to the newly supplied value. -/
theorem maxValueLength_insert_le (a : Address) (v : Value) (s : SparseMemory Address Value) :
    maxValueLength encV (s.insert a v) ≤ max (encV v).length (maxValueLength encV s) := by
  apply listMax_le
  intro e he
  rcases mem_entries_insert.mp he with rfl | ⟨he, _⟩
  · exact le_max_left _ _
  · exact (le_listMax (f := fun e : Address × Value => (encV e.2).length) he).trans
      (le_max_right _ _)

end Cslib.GenericRAM.SparseMemory
