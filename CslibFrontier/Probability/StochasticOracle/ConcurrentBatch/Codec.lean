/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.SelfDelimiting
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Concrete packets for concurrent stochastic-oracle batches

[Wang2027], model PDF pp. 4--6. One optional preformed query is encoded for each
of finitely many labeled opportunities. A decoded batch is nonempty by
construction and has at most one call per label. Canonical re-encoding rejects
malformed packets; no semantic parser-validity assumption is used.

Response packets distinguish cancellation from an empty returned word and encode
reported natural token counts. Real physical durations remain external receipt
metadata, not an asserted finite encoding of arbitrary real numbers.

## Main results

* `decodeSlots_encode`: exact slot framing with an arbitrary suffix.
* `decodeBatch_encode`: every nonempty preformed batch has its actual wire representation.
* `decodeReport_encode`: completed/canceled words and token reports roundtrip.
-/

public section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open Cslib.Kolmogorov

/-- Binary words exchanged on the actual native oracle channel. -/
abbrev Word := List Bool

/-- One optional word per opportunity, framed before any response is sampled. -/
@[expose] def encodeSlots : (n : ℕ) → (Fin n → Option Word) → Word
  | 0, _ => []
  | n + 1, f => match f 0 with
    | none => false :: encodeSlots n (fun i => f i.succ)
    | some w => true :: (selfDelimitingCode w ++ encodeSlots n (fun i => f i.succ))

/-- Decode a fixed number of slots, returning the unused suffix. -/
@[expose] def decodeSlots : (n : ℕ) → Word → Option ((Fin n → Option Word) × Word)
  | 0, w => some (Fin.elim0, w)
  | _n + 1, [] => none
  | n + 1, false :: w => (decodeSlots n w).map fun (f, rest) => (Fin.cons none f, rest)
  | n + 1, true :: w =>
    let (word, tail) := decodeSelfDelimiting w
    (decodeSlots n tail).map fun (f, rest) => (Fin.cons (some word) f, rest)

/-- Exact decoder for the concrete framed request slots. -/
theorem decodeSlots_encode (n : ℕ) (f : Fin n → Option Word) (suffix : Word) :
    decodeSlots n (encodeSlots n f ++ suffix) = some (f, suffix) := by
  induction n generalizing suffix with
  | zero =>
    have hf : f = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [encodeSlots, decodeSlots, hf]
  | succ n ih =>
    cases h : f 0 with
    | none =>
      simp only [encodeSlots, h, List.cons_append, decodeSlots, ih, Option.map_some,
        Option.some.injEq, Prod.mk.injEq, and_true]
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact h.symm
    | some w =>
      simp only [encodeSlots, h, List.cons_append, decodeSlots, List.append_assoc,
        decodeSelfDelimiting_selfDelimitingCode_append, ih, Option.map_some,
        Option.some.injEq, Prod.mk.injEq, and_true]
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact h.symm

/-- All selected labeled opportunities, each occurring at most once. -/
@[expose] def active {n : ℕ} (f : Fin n → Option Word) : Finset (Fin n) :=
  Finset.univ.filter fun i => (f i).isSome

/-- A source batch contains at least one preformed query. -/
structure Batch (n : ℕ) where
  /-- Complete per-opportunity requests, available before sampling responses. -/
  slots : Fin n → Option Word
  /-- Empty batches are not oracle turns. -/
  nonempty : (active slots).Nonempty

/-- Actual binary request packet. -/
@[expose] def encodeBatch {n : ℕ} (b : Batch n) : Word := encodeSlots n b.slots

/-- Checked canonical decoder: validates framing, full consumption and nonemptiness. -/
@[expose] def decodeBatch (n : ℕ) (w : Word) : Option (Batch n) :=
  match decodeSlots n w with
  | none => none
  | some (f, rest) =>
    if rest = [] ∧ encodeSlots n f = w then
      if h : (active f).Nonempty then some ⟨f, h⟩ else none
    else none

/-- Arbitrary nonempty concurrent batches are represented, without a supplied
codec correctness or validity contract. -/
theorem decodeBatch_encode {n : ℕ} (b : Batch n) :
    decodeBatch n (encodeBatch b) = some b := by
  have hd := decodeSlots_encode n b.slots []
  simp only [List.append_nil] at hd
  simp [decodeBatch, encodeBatch, hd, b.nonempty]

/-- Every accepted raw packet re-encodes exactly; malformed bytes cannot acquire
source validity through an arbitrary semantic parser. -/
theorem decodeBatch_sound {n : ℕ} {w : Word} {b : Batch n}
    (h : decodeBatch n w = some b) : encodeBatch b = w := by
  unfold decodeBatch at h
  split at h
  · cases h
  · split_ifs at h with hc hn
    · cases h
      exact hc.2

/-- A canceled or completed visible word and its billed tokens. -/
abbrev CallReport := Option Word × ℕ

/-- Encode completion separately from cancellation, followed by billed-token bits. -/
@[expose] def encodeCall : CallReport → Word
  | (none, tokens) => false :: tokens.bits
  | (some w, tokens) => true :: (selfDelimitingCode w ++ tokens.bits)

/-- Concrete decoder of a single usage report. -/
@[expose] def decodeCall : Word → Option CallReport
  | [] => none
  | false :: bits => some (none, bits.foldr Nat.bit 0)
  | true :: bits =>
    let (word, tail) := decodeSelfDelimiting bits
    some (some word, tail.foldr Nat.bit 0)

/-- Both cancellation and completed words retain their exact token report. -/
theorem decodeCall_encode (r : CallReport) : decodeCall (encodeCall r) = some r := by
  rcases r with ⟨w, tokens⟩
  cases w <;> simp [encodeCall, decodeCall]

/-- Per-opportunity visible reports; inactive opportunities have no report. -/
abbrev Report (n : ℕ) := Fin n → Option CallReport

/-- Accepted response packets have a success tag; rejected requests use `[false]`. -/
@[expose] def encodeReport {n : ℕ} (r : Report n) : Word :=
  true :: encodeSlots n (fun i => (r i).map encodeCall)

/-- Decode actual canonical response slots and reported tokens. -/
@[expose] def decodeReport (n : ℕ) : Word → Option (Report n)
  | true :: payload => match decodeSlots n payload with
    | none => none
    | some (f, rest) =>
      let report := fun i => (f i).bind decodeCall
      if rest = [] ∧ encodeReport report = true :: payload then some report else none
  | _ => none

/-- The entire visible correlated batch report is recoverable from its raw word. -/
theorem decodeReport_encode {n : ℕ} (r : Report n) :
    decodeReport n (encodeReport r) = some r := by
  have hd := decodeSlots_encode n (fun i => (r i).map encodeCall) []
  simp only [List.append_nil] at hd
  have hr : (fun i => ((r i).map encodeCall).bind decodeCall) = r := by
    funext i
    cases r i <;> simp [decodeCall_encode]
  change decodeReport n (true :: encodeSlots n (fun i => (r i).map encodeCall)) = some r
  rw [decodeReport, hd]
  change (if [] = [] ∧ encodeReport ((fun i => ((r i).map encodeCall).bind decodeCall)) =
    true :: encodeSlots n (fun i => (r i).map encodeCall) then some _ else none) = some r
  rw [hr]
  simp [encodeReport]

/-- Candidate-index families use an actual fixed-length membership mask. -/
@[expose] def encodeFamily {m : ℕ} (C : Finset (Fin m)) : Word :=
  List.ofFn fun i : Fin m => decide (i ∈ C)

/-- Reject malformed masks rather than interpreting arbitrary bytes as valid
candidate indices. Canceled calls have no word and are handled separately. -/
@[expose] def decodeFamily (m : ℕ) (word : Word) : Option (Finset (Fin m)) :=
  if word.length = m then some (Finset.univ.filter fun i => word[i.val]?.getD false) else none

/-- Every actual family mask decodes with bounded, valid candidate indices. -/
theorem decodeFamily_encode {m : ℕ} (C : Finset (Fin m)) :
    decodeFamily m (encodeFamily C) = some C := by
  simp only [decodeFamily, encodeFamily, List.length_ofFn, ite_true]
  congr 1
  ext i
  simp

/-- All valid candidate proposals actually returned by active noncanceled calls. -/
@[expose] def proposals (m : ℕ) {n : ℕ} (r : Report n) : List (Finset (Fin m)) :=
  (List.ofFn fun i : Fin n =>
    (r i).bind (fun receipt => receipt.1.bind (decodeFamily m))).filterMap id

/-- The concrete native response parser first validates the whole report packet. -/
@[expose] def parseProposals (n m : ℕ) (word : Word) : List (Finset (Fin m)) :=
  (decodeReport n word).toList.flatMap (proposals m)

/-- Every batch proposal comes from the actually completed raw response words. -/
theorem parseProposals_report {n m : ℕ} (r : Report n) :
    parseProposals n m (encodeReport r) = proposals m r := by
  simp [parseProposals, decodeReport_encode]

end Cslib.Probability.StochasticOracle.ConcurrentBatch
