/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.NavigationFeatures
public import Complexity.Computability.Circuit.Boolean.Iteration.SharedDictionary
public import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestNavigation

/-!
# Bit-vector records and fixed dictionaries for compressed-forest navigation

This module encodes the subtree interval labels `(low x, high x)` and the edge-anchor records
`(a, low a, high a, depthWord f a)` of a compressed checkpoint forest as fixed-width bit strings,
wraps `synthesis_lookupOr` into `synthesis_fixed_dictionary` returning hit flags and value records,
and packages the nonconstructive forest tables (`ForestCircuitTables`) needed by the reachability
circuit.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.forestLabelWord`: packs `(low x, high x)` as two `(n + 1)`-bit
  words.
* `Cslib.Circuits.Boolean.Iteration.forestAnchorWord`: packs `(x, forestLabelWord low high x,
  depthWord f x)`.
* `Cslib.Circuits.Boolean.Iteration.dictionaryCost`: gate count of a shared fixed-dictionary lookup.
* `Cslib.Circuits.Boolean.Iteration.ForestCircuitTables`: combined mark and compressed-edge tables
  for a functional graph on `BitString n`.

## Main results

* `Cslib.Circuits.Boolean.Iteration.forest_label_interval`: interval containment on unpacked
  `(n + 1)`-bit words matches `low y ≤ low x ∧ low x ≤ high y`.
* `Cslib.Circuits.Boolean.Iteration.synthesis_fixed_dictionary`: synthesizes hit flags and value
  records for `Q` queries into an `M`-entry dictionary.
* `Cslib.Circuits.Boolean.Iteration.exists_forest_circuit_tables`: existence of
  `ForestCircuitTables f L` for `0 < L`.

## References

* Adapted from lean/Proofs/ForestCircuitRecords.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n : ℕ}

/-- Two `(n + 1)`-bit words holding the lower and upper subtree ranks of a state. -/
def forestLabelWord (low high : BitString n → Fin (Nat.card (BitString n)))
    (x : BitString n) : BitString (n + 1 + (n + 1)) :=
  Fin.append
    (fun i : Fin (n + 1) => (BitVec.ofNat (n + 1) (low x).val).getLsbD i.val)
    (fun i : Fin (n + 1) => (BitVec.ofNat (n + 1) (high x).val).getLsbD i.val)

/-- Unpack the lower subtree rank word from a forest label record. -/
def forestLowWord (r : BitString (n + 1 + (n + 1))) : BitVec (n + 1) :=
  word fun i : Fin (n + 1) => r (Fin.castAdd (n + 1) i)

/-- Unpack the upper subtree rank word from a forest label record. -/
def forestHighWord (r : BitString (n + 1 + (n + 1))) : BitVec (n + 1) :=
  word fun i : Fin (n + 1) => r (Fin.natAdd (n + 1) i)

@[simp] theorem forestLowWord_bits (low high : BitString n → Fin (Nat.card (BitString n)))
    (x : BitString n) :
    forestLowWord (forestLabelWord low high x) = BitVec.ofNat (n + 1) (low x).val := by
  simp [forestLowWord, forestLabelWord, word_getLsbD]

@[simp] theorem forestHighWord_bits (low high : BitString n → Fin (Nat.card (BitString n)))
    (x : BitString n) :
    forestHighWord (forestLabelWord low high x) = BitVec.ofNat (n + 1) (high x).val := by
  simp only [forestHighWord, forestLabelWord, Fin.append_right, word_getLsbD]

private theorem forestLowWord_toNat (low high : BitString n → Fin (Nat.card (BitString n)))
    (x : BitString n) :
    (forestLowWord (forestLabelWord low high x)).toNat = (low x).val := by
  have hlt : (low x).val < 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using (low x).isLt
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
  rw [forestLowWord_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem forestHighWord_toNat (low high : BitString n → Fin (Nat.card (BitString n)))
    (x : BitString n) :
    (forestHighWord (forestLabelWord low high x)).toNat = (high x).val := by
  have hlt : (high x).val < 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using (high x).isLt
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
  rw [forestHighWord_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Word-level interval containment on unpacked `(n + 1)`-bit words matches rank containment. -/
theorem forest_label_interval (low high : BitString n → Fin (Nat.card (BitString n)))
    (a h : BitString n) :
    ((!(forestLowWord (forestLabelWord low high h)).ult
        (forestLowWord (forestLabelWord low high a))) &&
      (!(forestHighWord (forestLabelWord low high a)).ult
        (forestLowWord (forestLabelWord low high h)))) = true ↔
      (low a ≤ low h ∧ low h ≤ high a) := by
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', BitVec.ult, BitVec.ult,
    decide_eq_false_iff_not, decide_eq_false_iff_not, not_lt, not_lt,
    forestLowWord_toNat, forestLowWord_toNat, forestHighWord_toNat]
  rfl

/-- An anchor record packs a marked state, its two interval words, and its `(n + 3)`-bit depth. -/
noncomputable def forestAnchorWord (f : BitString n → BitString n)
    (low high : BitString n → Fin (Nat.card (BitString n))) (x : BitString n) :
    BitString (n + (n + 1 + (n + 1)) + (n + 3)) :=
  Fin.append (Fin.append x (forestLabelWord low high x))
    (fun i : Fin (n + 3) => (depthWord f x).getLsbD i.val)

/-- Unpack the marked state from an anchor record. -/
def forestAnchorState (r : BitString (n + (n + 1 + (n + 1)) + (n + 3))) : BitString n :=
  fun i => r (Fin.castAdd (n + 3) (Fin.castAdd (n + 1 + (n + 1)) i))

/-- Unpack the interval label pair from an anchor record. -/
def forestAnchorLabels (r : BitString (n + (n + 1 + (n + 1)) + (n + 3))) :
    BitString (n + 1 + (n + 1)) :=
  fun i => r (Fin.castAdd (n + 3) (Fin.natAdd n i))

/-- Unpack the `(n + 3)`-bit transient depth word from an anchor record. -/
def forestAnchorDepth (r : BitString (n + (n + 1 + (n + 1)) + (n + 3))) : BitVec (n + 3) :=
  word fun i : Fin (n + 3) => r (Fin.natAdd (n + (n + 1 + (n + 1))) i)

@[simp] theorem forestAnchorState_bits (f : BitString n → BitString n)
    (low high : BitString n → Fin (Nat.card (BitString n))) (x : BitString n) :
    forestAnchorState (forestAnchorWord f low high x) = x := by
  funext i
  simp [forestAnchorState, forestAnchorWord]

@[simp] theorem forestAnchorLabels_bits (f : BitString n → BitString n)
    (low high : BitString n → Fin (Nat.card (BitString n))) (x : BitString n) :
    forestAnchorLabels (forestAnchorWord f low high x) = forestLabelWord low high x := by
  funext i
  simp [forestAnchorLabels, forestAnchorWord]

@[simp] theorem forestAnchorDepth_bits (f : BitString n → BitString n)
    (low high : BitString n → Fin (Nat.card (BitString n))) (x : BitString n) :
    forestAnchorDepth (forestAnchorWord f low high x) = depthWord f x := by
  simp only [forestAnchorDepth, forestAnchorWord, Fin.append_right, word_getLsbD]

/-- Gate bound for a shared fixed-dictionary lookup with `M` keys and `Q` queries of `v`-bit
records. -/
def dictionaryCost (n v M Q : ℕ) : ℕ :=
  256 * (M + Q + 1) * (Nat.clog 2 (M + Q + 1) + n + (1 + v) + 3) ^ 3

/-- Shared lookup for a fixed injective dictionary, returning hit flags and `v`-bit records. -/
theorem synthesis_fixed_dictionary {a v M Q : ℕ} (s : Set (BooleanFunction a))
    (keys : Fin M → BitString n) (hkeys : Function.Injective keys)
    (values : Fin M → BitString v)
    (queries : BitString a → Fin Q → BitString n)
    (hq : ∀ j : Fin Q, wires (fun z => queries z j) ⊆ s) :
    ∃ (flags : BitString a → Fin Q → Bool) (records : BitString a → Fin Q → BitString v),
      (∀ z j, (flags z j = true ↔ ∃ i, keys i = queries z j) ∧
        ∀ i, keys i = queries z j → records z j = values i) ∧
      Synthesis interpretation s
        (Set.range (fun j z => flags z j) ∪ ⋃ j, wires (fun z => records z j))
        (dictionaryCost n v M Q) := by
  let stored : Fin M → BitString (v + 1) := fun i => Fin.cons true (values i)
  let flags : BitString a → Fin Q → Bool := fun z j => lookupOr keys stored (queries z j) 0
  let records : BitString a → Fin Q → BitString v :=
    fun z j bit => lookupOr keys stored (queries z j) bit.succ
  have hd := synthesis_lookupOr s keys stored queries fun j bit => hq j ⟨bit, rfl⟩
  refine ⟨flags, records, fun z j => ⟨?_, fun i hi => ?_⟩, hd.mono Set.Subset.rfl ?_ ?_⟩
  · simp [flags, lookupOr, stored]
  · funext bit
    simpa [records, stored] using congrFun (lookupOr_of_eq stored hkeys hi) bit.succ
  · rintro _ (⟨j, rfl⟩ | h)
    · exact Set.mem_iUnion.mpr ⟨j, 0, rfl⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      obtain ⟨bit, rfl⟩ := hj
      exact Set.mem_iUnion.mpr ⟨j, bit.succ, rfl⟩
  · unfold dictionaryCost
    have hclog : Nat.clog 2 (Q + M) ≤ Nat.clog 2 (M + Q + 1) :=
      Nat.clog_mono_right _ (by omega)
    set c := Nat.clog 2 (Q + M)
    set c' := Nat.clog 2 (M + Q + 1)
    have hc1 : c + 1 ≤ c' + n + (1 + v) + 3 := by omega
    have hnv : n + (v + 1) + 1 ≤ c' + n + (1 + v) + 3 := by omega
    have hpow : (c + 1) ^ 2 * (n + (v + 1) + 1) ≤ (c' + n + (1 + v) + 3) ^ 3 := by
      calc (c + 1) ^ 2 * (n + (v + 1) + 1)
          ≤ (c' + n + (1 + v) + 3) ^ 2 * (c' + n + (1 + v) + 3) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hc1 2) hnv
        _ = (c' + n + (1 + v) + 3) ^ 3 := by ring
    have hQM : 48 * (Q + M + 1) ≤ 256 * (M + Q + 1) := by omega
    calc 48 * (Q + M + 1) * (c + 1) ^ 2 * (n + (v + 1) + 1)
        = (48 * (Q + M + 1)) * ((c + 1) ^ 2 * (n + (v + 1) + 1)) := by ring
      _ ≤ (256 * (M + Q + 1)) * (c' + n + (1 + v) + 3) ^ 3 := Nat.mul_le_mul hQM hpow
      _ = 256 * (M + Q + 1) * (c' + n + (1 + v) + 3) ^ 3 := by ring

/-- Combined checkpoint-mark and compressed-edge tables for a functional graph on `BitString n`. -/
structure ForestCircuitTables (f : BitString n → BitString n) (L : ℕ) where
  /-- Underlying checkpoint set. -/
  H : Finset (BitString n)
  /-- Every `L`-step prefix either repeats or hits `H` within `2 * L` steps. -/
  cover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H
  /-- Lower subtree rank label. -/
  low : BitString n → Fin (Nat.card (BitString n))
  /-- Upper subtree rank label. -/
  high : BitString n → Fin (Nat.card (BitString n))
  /-- Subtree interval containment characterizes ancestry before cycle entry. -/
  interval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
    ∃ t ≤ transientDepth f x, f^[t] x = y
  /-- Number of refined forest marks. -/
  markCount : ℕ
  /-- Enumeration of the refined forest marks. -/
  marks : Fin markCount → BitString n
  /-- Refined marks are pairwise distinct. -/
  marks_injective : Function.Injective marks
  /-- `marks` enumerates `forestMarks f H` exactly. -/
  marks_mem : ∀ x, x ∈ forestMarks f H ↔ ∃ i, marks i = x
  /-- At most `2 * (2 ^ n / L)` refined marks exist. -/
  markCount_le : markCount ≤ 2 * (2 ^ n / L)
  /-- Compressed-edge table for non-root marks. -/
  edgeTable : ForestEdgeTable f H L
  /-- At most `2 * (2 ^ n / L)` compressed edges exist. -/
  edgeCount_le : edgeTable.count ≤ 2 * (2 ^ n / L)

/-- Existence of `ForestCircuitTables f L` for any `0 < L`. -/
theorem exists_forest_circuit_tables (f : BitString n → BitString n) (L : ℕ) (hL : 0 < L) :
    Nonempty (ForestCircuitTables f L) := by
  classical
  obtain ⟨H, hHcard, hcover⟩ := exists_checkpoints_finite f hL
  have hHcard' : H.card ≤ 2 ^ n / L := by simpa using hHcard
  obtain ⟨low, high, hinterval⟩ := exists_forest_intervals f
  obtain ⟨edgeTable⟩ := exists_forest_edge_table f H L hL hcover
  let M := forestMarks f H
  let marks : Fin M.card → BitString n := fun j => (M.equivFin.symm j).val
  have hmarks_inj : Function.Injective marks := by
    intro i j hij
    exact M.equivFin.symm.injective (Subtype.ext hij)
  have hmarks_mem (x : BitString n) : x ∈ forestMarks f H ↔ ∃ i, marks i = x := by
    constructor
    · intro hx
      exact ⟨M.equivFin ⟨x, hx⟩, by simp [marks]⟩
    · rintro ⟨i, rfl⟩
      exact (M.equivFin.symm i).property
  have hMcard : M.card ≤ 2 * (2 ^ n / L) :=
    (forestMarks_card f H).trans (Nat.mul_le_mul_left 2 hHcard')
  exact ⟨⟨H, hcover, low, high, hinterval, M.card, marks, hmarks_inj, hmarks_mem, hMcard,
    edgeTable, edgeTable.card_le.trans hMcard⟩⟩

end Cslib.Circuits.Boolean.Iteration
