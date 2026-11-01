/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List.Binary
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn

/-!
# Compact binary codes for segmented marked supports

A segment contains marked positions with offsets below `2 ^ k`. An entry is encoded by a
`true` bit, its `k`-bit offset, and its mark. A `false` bit ends a segment. Thus a list of `b`
segments containing `q` entries has a binary encoding of exactly `b + (k + 2) * q` bits.
The decoder and its round trip are explicit. Empty segments, zero-width offsets, and empty
lists of segments are included.

`supportSegments` supplies the canonical segment lists for a ternary support, represented by
an `Option Bool` at each position. Its membership theorem identifies precisely the marked
positions, and `supportCode_injective` proves that distinct supports have distinct codes.
This is the compact support representation used in Charlie Cruz's sublinear-space counting
argument [Cruz2026SublinearSpace]. The results here certify representation size and
decoding correctness; they do not assert a Turing-machine resource bound for the decoder.

## Main definitions

* `Cslib.BitString.Segmented.encode`: binary encoding of a list of segments.
* `Cslib.BitString.Segmented.decode`: executable decoder.
* `Cslib.BitString.Segmented.supportCode`: canonical code of a segmented ternary support.

## Main results

* `Cslib.BitString.Segmented.decode_encode`: decoding recovers all segments.
* `Cslib.BitString.Segmented.length_encode`: exact storage cost.
* `Cslib.BitString.Segmented.supportCode_injective`: canonical support codes are injective.
* `Cslib.BitString.Segmented.length_supportCode_le`: storage bound for sparse supports.
-/

public section

namespace Cslib.BitString.Segmented

/-- A marked position within a segment of `2 ^ k` positions. -/
abbrev Entry (k : ℕ) := Fin (2 ^ k) × Bool

/-- The code of an entry or of a segment terminator (`none`). -/
@[expose] def tokenCode {k : ℕ} : Option (Entry k) → List Bool
  | none => [false]
  | some (offset, mark) => true :: (binaryWord k offset.val ++ [mark])

/-- Read one tagged entry or terminator, retaining the unread suffix. -/
@[expose] def readToken (k : ℕ) : List Bool → Option (Option (Entry k) × List Bool)
  | [] => none
  | false :: rest => some (none, rest)
  | true :: rest =>
    if h : k ≤ rest.length then
      let offset : Fin (2 ^ k) := ⟨binaryValue (rest.take k), by
        have hlt := binaryValue_lt_two_pow (rest.take k)
        simpa only [List.length_take, Nat.min_eq_left h] using hlt⟩
      match rest.drop k with
      | [] => none
      | mark :: tail => some (some (offset, mark), tail)
    else none

/-- Reading an encoded token recovers the token and leaves the suffix unchanged. -/
theorem readToken_tokenCode {k : ℕ} (entry : Option (Entry k)) (tail : List Bool) :
    readToken k (tokenCode entry ++ tail) = some (entry, tail) := by
  cases entry with
  | none => rfl
  | some entry =>
    obtain ⟨offset, mark⟩ := entry
    have hw := length_binaryWord offset.isLt
    have hwidth : k ≤ (binaryWord k offset.val ++ mark :: tail).length := by
      simp only [List.length_append, hw, List.length_cons]
      omega
    simp only [tokenCode, List.cons_append, List.append_assoc, List.nil_append,
      readToken, dite_eq_left hwidth, List.take_left' hw, List.drop_left' hw,
      binaryValue_binaryWord]

/-- Concatenate the codes of tagged entries and segment terminators. -/
@[expose] def tokensCode {k : ℕ} : List (Option (Entry k)) → List Bool
  | [] => []
  | entry :: entries => tokenCode entry ++ tokensCode entries

/-- Read all tokens with an explicit upper bound on their number. -/
@[expose] def readTokens (k : ℕ) : ℕ → List Bool → Option (List (Option (Entry k)))
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, word@(_ :: _) => do
    let (entry, tail) ← readToken k word
    let entries ← readTokens k fuel tail
    pure (entry :: entries)

/-- A sufficient token budget makes decoding a left inverse of token encoding. -/
theorem readTokens_tokensCode {k : ℕ} (entries : List (Option (Entry k)))
    (fuel : ℕ) (hfuel : entries.length ≤ fuel) :
    readTokens k fuel (tokensCode entries) = some entries := by
  induction entries generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons entry entries ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have htail : entries.length ≤ fuel := by simpa using hfuel
      have hne : tokenCode entry ++ tokensCode entries ≠ [] := by
        cases entry <;> simp [tokenCode]
      rw [tokensCode]
      cases he : tokenCode entry ++ tokensCode entries with
      | nil => exact (hne he).elim
      | cons bit bits =>
        simp only [readTokens, ← he, readToken_tokenCode, bind, Option.bind_some, ih fuel htail,
          pure]

/-- Every token contributes at least one bit to its code. -/
theorem length_le_tokensCode {k : ℕ} (entries : List (Option (Entry k))) :
    entries.length ≤ (tokensCode entries).length := by
  induction entries with
  | nil => exact le_rfl
  | cons entry entries ih =>
    cases entry with
    | none => simpa [tokensCode, tokenCode] using Nat.succ_le_succ ih
    | some entry =>
      obtain ⟨offset, mark⟩ := entry
      simp only [tokensCode, tokenCode, List.length_append, List.length_cons,
        List.length_nil, length_binaryWord offset.isLt]
      omega

/-- Separate segment entries by a `none` terminator after each segment. -/
@[expose] def segmentTokens {k : ℕ} : List (List (Entry k)) → List (Option (Entry k))
  | [] => []
  | entries :: segments => entries.map some ++ none :: segmentTokens segments

/-- Split tokens into segments at their terminators; retain an unterminated final segment. -/
@[expose] def groupTokens {k : ℕ} : List (Option (Entry k)) → List (List (Entry k))
  | [] => []
  | none :: tokens => [] :: groupTokens tokens
  | some entry :: tokens =>
    match groupTokens tokens with
    | [] => [[entry]]
    | entries :: segments => (entry :: entries) :: segments

/-- A terminated segment is recovered before all subsequent segments. -/
theorem groupTokens_map_append {k : ℕ} (entries : List (Entry k))
    (tokens : List (Option (Entry k))) :
    groupTokens (entries.map some ++ none :: tokens) = entries :: groupTokens tokens := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp [groupTokens, ih]

/-- Grouping the tokens of segment lists recovers the lists. -/
@[simp] theorem groupTokens_segmentTokens {k : ℕ} (segments : List (List (Entry k))) :
    groupTokens (segmentTokens segments) = segments := by
  induction segments with
  | nil => rfl
  | cons entries segments ih => rw [segmentTokens, groupTokens_map_append, ih]

/-- Encode each entry as a tag, a fixed-width offset and its mark, ending each segment in `false`.
No separator between successive entries is needed because their widths are fixed. -/
@[expose] def encode {k : ℕ} (segments : List (List (Entry k))) : List Bool :=
  tokensCode (segmentTokens segments)

/-- Parse the tags and fixed-width offsets, then split the entries at segment terminators.
The input length is a sufficient recursion budget because every token consumes a bit. -/
@[expose] def decode (k : ℕ) (word : List Bool) : Option (List (List (Entry k))) :=
  (readTokens k word.length word).map groupTokens

/-- Decoding the encoding of a list of segments recovers it exactly. -/
@[simp] theorem decode_encode {k : ℕ} (segments : List (List (Entry k))) :
    decode k (encode segments) = some segments := by
  rw [decode, encode, readTokens_tokensCode _ _ (length_le_tokensCode _)]
  simp only [Option.map_some, groupTokens_segmentTokens]

/-- Distinct segment lists have distinct binary codes. -/
theorem encode_injective {k : ℕ} : Function.Injective (encode (k := k)) := by
  intro segments segments' h
  have := congrArg (decode k) h
  simpa only [decode_encode, Option.some.injEq] using this

/-- The number of marked entries across all segments. -/
@[expose] def entryCount {k : ℕ} (segments : List (List (Entry k))) : ℕ :=
  (segments.map List.length).sum

/-- Encoding a prefix of marked entries contributes exactly `k + 2` bits per entry. -/
theorem length_tokensCode_map_append {k : ℕ} (entries : List (Entry k))
    (tokens : List (Option (Entry k))) :
    (tokensCode (entries.map some ++ tokens)).length =
      (k + 2) * entries.length + (tokensCode tokens).length := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    obtain ⟨offset, mark⟩ := entry
    simp only [List.map_cons, List.cons_append, tokensCode, tokenCode, List.length_append,
      List.length_cons, List.length_nil, length_binaryWord offset.isLt, ih, Nat.mul_add,
      Nat.mul_one]
    omega

/-- One bit per segment and `k + 2` bits per marked entry is the exact encoded length. -/
@[simp] theorem length_encode {k : ℕ} (segments : List (List (Entry k))) :
    (encode segments).length = segments.length + (k + 2) * entryCount segments := by
  induction segments with
  | nil => simp [encode, segmentTokens, tokensCode, entryCount]
  | cons entries segments ih =>
    change (tokensCode (entries.map some ++ none :: segmentTokens segments)).length = _
    rw [length_tokensCode_map_append]
    change (tokensCode (segmentTokens segments)).length = _ at ih
    simp only [tokensCode, tokenCode, List.length_append, List.length_cons, List.length_nil,
      ih, entryCount, List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- The marked entries of one segment, in increasing offset order. -/
@[expose] def supportSegment {k : ℕ} (support : Fin (2 ^ k) → Option Bool) : List (Entry k) :=
  (List.finRange (2 ^ k)).filterMap fun offset => (support offset).map (offset, ·)

/-- The entries of a canonical segment are exactly its marked positions and their marks. -/
@[simp] theorem mem_supportSegment {k : ℕ} (support : Fin (2 ^ k) → Option Bool)
    (offset : Fin (2 ^ k)) (mark : Bool) :
    (offset, mark) ∈ supportSegment support ↔ support offset = some mark := by
  simp [supportSegment, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]

/-- A canonical segment uniquely determines the ternary support on its positions. -/
theorem supportSegment_injective {k : ℕ} :
    Function.Injective (supportSegment (k := k)) := by
  intro support support' heq
  funext offset
  cases h : support offset with
  | none =>
    cases h' : support' offset with
    | none => rfl
    | some mark =>
      have hm : (offset, mark) ∈ supportSegment support' := (mem_supportSegment _ _ _).2 h'
      rw [← heq, mem_supportSegment, h] at hm
      contradiction
  | some mark =>
    have hm : (offset, mark) ∈ supportSegment support := (mem_supportSegment _ _ _).2 h
    rw [heq, mem_supportSegment] at hm
    exact hm.symm

/-- A canonical segment contains one entry for each position whose mark is present. -/
theorem length_supportSegment {k : ℕ} (support : Fin (2 ^ k) → Option Bool) :
    (supportSegment support).length =
      (Finset.univ.filter fun offset => (support offset).isSome).card := by
  rw [supportSegment, List.length_filterMap_eq_countP]
  simp only [Option.isSome_map]
  simpa using ((List.nodup_finRange (2 ^ k)).card_eq_countP
    (P := fun offset => (support offset).isSome)).symm

/-- Canonical segments of a ternary support on `blocks` consecutive blocks of `2 ^ k` positions. -/
@[expose] def supportSegments {k blocks : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool) : List (List (Entry k)) :=
  List.ofFn fun block => supportSegment (support block)

/-- The canonical segment list has exactly one segment per block, including empty blocks. -/
@[simp] theorem length_supportSegments {k blocks : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool) :
    (supportSegments support).length = blocks := by
  simp [supportSegments]

/-- Canonical segment lists uniquely determine their ternary supports. -/
theorem supportSegments_injective {k blocks : ℕ} :
    Function.Injective (supportSegments (k := k) (blocks := blocks)) := by
  intro support support' h
  have hrows := List.ofFn_injective h
  funext block
  exact supportSegment_injective (congrFun hrows block)

/-- Counting the entries of canonical segments agrees with counting nonzero support positions. -/
theorem entryCount_supportSegments {k blocks : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool) :
    entryCount (supportSegments support) =
      ∑ block, (Finset.univ.filter fun offset => (support block offset).isSome).card := by
  simp [entryCount, supportSegments, List.sum_ofFn, length_supportSegment]

/-- The compact code of a ternary support, with positions identified by block and offset. -/
@[expose] def supportCode {k blocks : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool) : List Bool :=
  encode (supportSegments support)

/-- Distinct ternary supports have distinct compact codes. -/
theorem supportCode_injective {k blocks : ℕ} :
    Function.Injective (supportCode (k := k) (blocks := blocks)) :=
  encode_injective.comp supportSegments_injective

/-- The code length in terms of the actual number of marked positions. -/
theorem length_supportCode {k blocks : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool) :
    (supportCode support).length = blocks + (k + 2) *
      ∑ block, (Finset.univ.filter fun offset => (support block offset).isSome).card := by
  rw [supportCode, length_encode, length_supportSegments, entryCount_supportSegments]

/-- A ternary support with at most `q` marked positions takes at most `blocks + (k + 2) * q`
bits. In the counting application, `blocks = ⌈N / 2 ^ k⌉`. -/
theorem length_supportCode_le {k blocks q : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool)
    (hq : (∑ block, (Finset.univ.filter fun offset => (support block offset).isSome).card) ≤ q) :
    (supportCode support).length ≤ blocks + (k + 2) * q := by
  rw [length_supportCode]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _

/-- A division-free sparse-support bound. If the number of blocks is at most `N / 2 ^ k + 1`
and the number of marked positions is at most `c * N / 2 ^ k`, the code uses at most
`(1 + (k + 2) * c) * N / 2 ^ k + 1` bits. The hypotheses and conclusion are multiplied by the
positive segment width so that no rounding convention is implicit. -/
theorem mul_length_supportCode_le {k blocks N c : ℕ}
    (support : Fin blocks → Fin (2 ^ k) → Option Bool)
    (hblocks : blocks * 2 ^ k ≤ N + 2 ^ k)
    (hsupport :
      (∑ block, (Finset.univ.filter fun offset => (support block offset).isSome).card) *
        2 ^ k ≤ c * N) :
    (supportCode support).length * 2 ^ k ≤ (1 + (k + 2) * c) * N + 2 ^ k := by
  calc
    (supportCode support).length * 2 ^ k = blocks * 2 ^ k + (k + 2) *
        ((∑ block, (Finset.univ.filter fun offset => (support block offset).isSome).card) *
          2 ^ k) := by rw [length_supportCode, Nat.add_mul, Nat.mul_assoc]
    _ ≤ (N + 2 ^ k) + (k + 2) * (c * N) :=
      Nat.add_le_add hblocks (Nat.mul_le_mul_left _ hsupport)
    _ = (1 + (k + 2) * c) * N + 2 ^ k := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega

end Cslib.BitString.Segmented
