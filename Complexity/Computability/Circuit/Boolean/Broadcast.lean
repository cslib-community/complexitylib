/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Equality
public import Complexity.Computability.Circuit.Boolean.Propagation
public import Complexity.Computability.Circuit.Replication
public import Complexity.Computability.Circuit.Wiring
public import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Ring

/-!
# Broadcast circuits for sorted records

Each record has a retained header followed by a value. Keys and source/destination tags are
selected from the header. False tags seed source values; equal-key links carry their bitwise
OR forward. When records are sorted by key followed by tag, each destination receives the OR
of all matching sources. A unique matching source is therefore copied exactly. All header
bits, including routing metadata, are preserved even on unsorted inputs.

Adjacent-key tests are computed once and shared across the value-bit scans. The construction
uses native circuit composition, replication and wiring. It allows any record count, repeated
keys and selectors, and empty key or value fields. With zero records, each value scan still
contains its initial false constant. With zero value width, the shared key-test gates remain.
The constructor is executable; its gate bounds do not certify the constructor's running time.

## Main definitions

* `Cslib.Circuits.Boolean.broadcastCircuit`: a full record scan preserving the header.
* `Cslib.Circuits.Boolean.broadcastCircuit.values`: scans with arbitrary input selectors.
* `Cslib.Circuits.Boolean.broadcastCircuit.header`,
  `Cslib.Circuits.Boolean.broadcastCircuit.value`: projections of row-major record fields.

## Main results

* `Cslib.BitString.propagate_sorted_tagged_eq_true_iff`: the propagated value at a destination
  is true precisely when a matching source has a true value.
* `Cslib.Circuits.Boolean.eval_broadcastCircuit_header`: every header is preserved.
* `Cslib.Circuits.Boolean.eval_broadcastCircuit_value_eq_true_iff`: sorted destination semantics.
* `Cslib.Circuits.Boolean.eval_broadcastCircuit_value_of_unique_source`: exact source copying.
* `Cslib.Circuits.Boolean.cost_program_broadcastCircuit`: exact arbitrary weighted cost.
* `Cslib.Circuits.Boolean.size_broadcastCircuit`: exact gate count.

## References

* Adapts MassProduction/Nonuniform/{BroadcastCircuit,BroadcastCorrectness,BroadcastRecords}.lean
  from [S. Schlesinger,
  *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  sharing the adjacent-key tests across value bits.
-/

@[expose] public section

namespace Cslib.BitString

private theorem snoc_lt_of_lt {k : ℕ} {x y : BitString k} (a b : Bool)
    (h : toLex x < toLex y) :
    toLex (Fin.snoc (α := fun _ => Bool) x a) <
      toLex (Fin.snoc (α := fun _ => Bool) y b) := by
  obtain ⟨i, heq, hlt⟩ := h
  refine ⟨i.castSucc, ?_, ?_⟩
  · intro j hj
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last
      (ne_of_lt (hj.trans (Fin.castSucc_lt_last i)))
    simpa using heq j (by simpa using hj)
  · simpa using hlt

private theorem prefix_le_of_snoc_le {k : ℕ} {x y : BitString k} {a b : Bool}
    (h : toLex (Fin.snoc (α := fun _ => Bool) x a) ≤
      toLex (Fin.snoc (α := fun _ => Bool) y b)) : toLex x ≤ toLex y := by
  by_contra hn
  exact (not_lt_of_ge h) (snoc_lt_of_lt b a (lt_of_not_ge hn))

private theorem false_lt_true {k : ℕ} (key : BitString k) :
    toLex (Fin.snoc (α := fun _ => Bool) key false) <
      toLex (Fin.snoc (α := fun _ => Bool) key true) := by
  refine ⟨Fin.last k, ?_, ?_⟩
  · intro i hi
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hi)
    simp
  · simp

/-- At a destination in key/tag order, propagation is the OR of all matching source values.
False tags mark sources and true tags mark destinations. Sources and destinations may repeat,
and sortedness is required only within the indicated prefix. -/
theorem propagate_sorted_tagged_eq_true_iff {k n d : ℕ} (key : ℕ → BitString k)
    (tag payload : ℕ → Bool) (hd : d < n) (htag : tag d = true)
    (sorted : MonotoneOn (fun i => toLex (Fin.snoc (α := fun _ => Bool) (key i) (tag i)))
      (Set.Iio n)) :
    propagate (fun i => !tag i && payload i)
      (keyLinks (fun i => toLex (key i))) (d + 1) = true ↔
        ∃ s, s < n ∧ key s = key d ∧ tag s = false ∧ payload s = true := by
  have monoKey : MonotoneOn (fun i => toLex (key i)) (Set.Iio (d + 1)) := by
    intro a ha b hb hab
    apply prefix_le_of_snoc_le
    exact sorted (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ ha) hd)
      (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hb) hd) hab
  rw [propagate_sorted_eq_true_iff (fun i => toLex (key i))
    (fun i => !tag i && payload i) (d + 1) monoKey]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.add_sub_cancel_right, toLex_inj]
  constructor
  · rintro ⟨s, hs, ⟨htag, hpayload⟩, hkey⟩
    exact ⟨s, by lia, hkey, htag, hpayload⟩
  · rintro ⟨s, hs, hkey, hsource, hpayload⟩
    have hsd : s < d := by
      apply sorted.reflect_lt hs hd
      rw [hsource, htag, hkey]
      exact false_lt_true _
    exact ⟨s, by lia, ⟨hsource, hpayload⟩, hkey⟩

end Cslib.BitString

namespace Cslib.Circuits.Boolean

namespace broadcastCircuit

open Formula (equalBits cost_equalBits)
open propagateCircuit (inputBlock)

/-- Run one shared propagation scan per value bit, reusing a single block of links. -/
def scans (count width : ℕ) : Circuit signature (width * count + count) (width * count) :=
  ((propagateCircuit count).replicate width).comp (Circuit.wiringOn signature
    ((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv)
    (((Equiv.refl _).prodCongr finSumFinEquiv).trans finProdFinEquiv)
    (fun (bit, field) => field.elim (fun record => Sum.inl (bit, record)) Sum.inr))

private theorem eval_scans {count width : ℕ} (source : Fin width → BitString count)
    (link : BitString count) (bit : Fin width) (record : Fin count) :
    (scans count width).eval interpretation
      (Fin.append (fun index => source (finProdFinEquiv.symm index).1
        (finProdFinEquiv.symm index).2) link) (finProdFinEquiv (bit, record)) =
      (propagateCircuit count).eval interpretation (Fin.append (source bit) link) record := by
  rw [scans, Circuit.eval_comp, Circuit.eval_replicate_apply]
  congr 2
  funext index
  cases index using Fin.addCases <;>
    simp [Circuit.eval_wiringOn, directProductInput,
      -finProdFinEquiv_symm_apply, -Fin.natAdd_eq_addNat]

private theorem cost_scans (count width : ℕ) (cost : signature.Op → ℕ) :
    (scans count width).program.cost cost =
      width * (cost (.const false) + count * (cost .and + cost .or)) := by
  simp only [scans, Circuit.cost_program_comp, Circuit.cost_program_replicate,
    cost_program_propagateCircuit, Circuit.cost_program_wiringOn, Nat.zero_add]

/-- Only false-tagged source records seed a value bit. -/
def sources {input count width : ℕ} (tag : Fin count → Fin input)
    (payload : Fin count → Fin width → Fin input) : Circuit signature input (width * count) :=
  Circuit.pi fun index =>
    let pair := finProdFinEquiv.symm index
    ((Formula.input (tag pair.2)).not.and (Formula.input (payload pair.2 pair.1))).toCircuit

/-- Broadcast all selected value bits, sharing adjacent-key tests between the scans. -/
def values {input count keyWidth width : ℕ} (key : Fin count → Fin keyWidth → Fin input)
    (tag : Fin count → Fin input) (payload : Fin count → Fin width → Fin input) :
    Circuit signature input (width * count) :=
  (scans count width).comp ((sources tag payload).append (adjacentEqualityCircuit key))

private theorem eval_sources {input count width : ℕ} (tag : Fin count → Fin input)
    (payload : Fin count → Fin width → Fin input) (x : BitString input)
    (bit : Fin width) (record : Fin count) :
    (sources tag payload).eval interpretation x (finProdFinEquiv (bit, record)) =
      (!x (tag record) && x (payload record bit)) := by
  simp only [sources, Circuit.eval_pi, Formula.eval_toCircuit, Equiv.symm_apply_apply,
    Formula.eval_and, Formula.eval_not, Formula.eval_input]

private theorem cost_sources {input count width : ℕ} (tag : Fin count → Fin input)
    (payload : Fin count → Fin width → Fin input) (cost : signature.Op → ℕ) :
    (sources tag payload).program.cost cost = width * count * (cost .not + cost .and) := by
  simp only [sources, Circuit.cost_program_pi, Formula.cost_toCircuit, Formula.and,
    Formula.not, Formula.cost_gate, Formula.cost_input, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Nat.zero_add, Nat.add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem cost_values {input count keyWidth width : ℕ}
    (key : Fin count → Fin keyWidth → Fin input) (tag : Fin count → Fin input)
    (payload : Fin count → Fin width → Fin input) (cost : signature.Op → ℕ) :
    (values key tag payload).program.cost cost =
      (adjacentEqualityCircuit key).program.cost cost + width *
        (cost (.const false) + count * (cost .not + 2 * cost .and + cost .or)) := by
  simp only [values, Circuit.cost_program_comp, Circuit.cost_program_append,
    cost_scans, cost_sources]
  ring

private def inputKey {input count keyWidth : ℕ} (key : Fin count → Fin keyWidth → Fin input)
    (x : BitString input) (index : ℕ) : BitString keyWidth :=
  fun bit => inputBlock (fun record => x (key record bit)) index

private theorem inputKey_fin {input count keyWidth : ℕ} (key : Fin count → Fin keyWidth → Fin input)
    (x : BitString input) (record : Fin count) : inputKey key x record.val = x ∘ key record := by
  funext bit
  simp only [inputKey, inputBlock, dite_eq_left record.isLt, Function.comp_apply]

private theorem eval_links {input count keyWidth : ℕ} (key : Fin count → Fin keyWidth → Fin input)
    (x : BitString input) (record : Fin count) :
    (adjacentEqualityCircuit key).eval interpretation x record =
      BitString.keyLinks (fun i => toLex (inputKey key x i)) record.val := by
  by_cases h : 0 < record.val
  · simp only [adjacentEqualityCircuit, Circuit.eval_pi, dite_eq_left h, Formula.eval_toCircuit]
    apply Bool.eq_iff_iff.mpr
    rw [Formula.eval_equalBits_iff]
    simp only [BitString.keyLinks, ite_eq_right (by lia : record.val ≠ 0),
      decide_eq_true_eq, toLex_inj]
    rw [inputKey_fin key x record, inputKey_fin key x ⟨record.val - 1, by lia⟩]
  · have hz : record.val = 0 := by lia
    simp [adjacentEqualityCircuit, BitString.keyLinks, hz]

private theorem eval_values {input count keyWidth width : ℕ}
    (key : Fin count → Fin keyWidth → Fin input) (tag : Fin count → Fin input)
    (payload : Fin count → Fin width → Fin input) (x : BitString input)
    (bit : Fin width) (record : Fin count) :
    (values key tag payload).eval interpretation x (finProdFinEquiv (bit, record)) =
      BitString.propagate (fun i => !inputBlock (x ∘ tag) i &&
        inputBlock (fun r => x (payload r bit)) i)
        (BitString.keyLinks (fun i => toLex (inputKey key x i))) (record.val + 1) := by
  rw [values, Circuit.eval_comp, Circuit.eval_append]
  have hs : (sources tag payload).eval interpretation x =
      fun index => !x (tag (finProdFinEquiv.symm index).2) &&
        x (payload (finProdFinEquiv.symm index).2 (finProdFinEquiv.symm index).1) := by
    funext index
    obtain ⟨⟨bit, record⟩, rfl⟩ := finProdFinEquiv.surjective index
    simp only [eval_sources, Equiv.symm_apply_apply]
  rw [hs, eval_scans (fun bit record => !x (tag record) && x (payload record bit)),
    eval_propagateCircuit]
  simp only [Function.comp_def, Fin.append_left, Fin.append_right]
  apply BitString.propagate_congr
  · intro index before
    have hi : index < count := by lia
    simp only [inputBlock, dite_eq_left hi]
  · intro index before
    have hi : index < count := by lia
    simp only [inputBlock, dite_eq_left hi]
    exact eval_links key x ⟨index, hi⟩

/-- At a destination in sorted key/tag order, each output bit is the OR of all matching
source bits. The selectors may overlap or repeat; source keys need not be unique. -/
theorem eval_values_eq_true_iff {input count keyWidth width : ℕ}
    (key : Fin count → Fin keyWidth → Fin input) (tag : Fin count → Fin input)
    (payload : Fin count → Fin width → Fin input) (x : BitString input)
    (sorted : Monotone (fun record =>
      toLex (Fin.snoc (α := fun _ => Bool) (x ∘ key record) (x (tag record)))))
    (bit : Fin width) (destination : Fin count) (htag : x (tag destination) = true) :
    (values key tag payload).eval interpretation x (finProdFinEquiv (bit, destination)) = true ↔
      ∃ source, x ∘ key source = x ∘ key destination ∧
        x (tag source) = false ∧ x (payload source bit) = true := by
  rw [eval_values]
  have sortedNat : MonotoneOn (fun i =>
      toLex (Fin.snoc (α := fun _ => Bool) (inputKey key x i) (inputBlock (x ∘ tag) i)))
      (Set.Iio count) := by
    intro a ha b hb hab
    change a < count at ha
    change b < count at hb
    have hs := sorted (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hab
    dsimp only
    rw [inputKey_fin key x ⟨a, ha⟩, inputKey_fin key x ⟨b, hb⟩]
    simpa only [inputBlock, dite_eq_left ha, dite_eq_left hb, Function.comp_apply] using hs
  rw [BitString.propagate_sorted_tagged_eq_true_iff (inputKey key x) (inputBlock (x ∘ tag))
    (inputBlock (fun r => x (payload r bit))) destination.isLt
    (by simpa only [inputBlock, dite_eq_left destination.isLt, Function.comp_apply] using htag)
    sortedNat]
  rw [inputKey_fin]
  constructor
  · rintro ⟨source, before, hkey, htag, hpayload⟩
    refine ⟨⟨source, before⟩, ?_, ?_, ?_⟩
    · exact (inputKey_fin key x ⟨source, before⟩).symm.trans hkey
    · simpa only [inputBlock, dite_eq_left before, Function.comp_apply] using htag
    · simpa only [inputBlock, dite_eq_left before] using hpayload
  · rintro ⟨source, hkey, htag, hpayload⟩
    refine ⟨source.val, source.isLt, ?_, ?_, ?_⟩
    · exact (inputKey_fin key x source).trans hkey
    · simpa only [inputBlock, dite_eq_left source.isLt, Function.comp_apply] using htag
    · simpa only [inputBlock, dite_eq_left source.isLt] using hpayload

/-- Read the retained header of a row-major record array. -/
def header {count headerWidth width : ℕ} (x : BitString (count * (headerWidth + width)))
    (record : Fin count) : BitString headerWidth := directProductInput x record ∘ Fin.castAdd width

/-- Read the value field following the retained header. -/
def value {count headerWidth width : ℕ} (x : BitString (count * (headerWidth + width)))
    (record : Fin count) : BitString width := directProductInput x record ∘ Fin.natAdd headerWidth

/-- Keep every header wire and replace value wires by the corresponding scan outputs. -/
def outputWire (count headerWidth width : ℕ) (index : Fin (count * (headerWidth + width))) :
    Fin (count * (headerWidth + width) + width * count) :=
  let pair := finProdFinEquiv.symm index
  Fin.addCases (fun bit => Fin.castAdd (width * count)
      (finProdFinEquiv (pair.1, Fin.castAdd width bit)))
    (fun bit => Fin.natAdd (count * (headerWidth + width)) (finProdFinEquiv (bit, pair.1))) pair.2

end broadcastCircuit

open broadcastCircuit

/-- Broadcast values in a record array, preserving the entire retained header. Keys and tags
are selected from that header; the value field follows it. Sorted destination semantics is
proved separately. Gate counts include unused work at zero output width or zero records. -/
def broadcastCircuit {headerWidth keyWidth : ℕ}
    (key : Fin keyWidth → Fin headerWidth) (tag : Fin headerWidth)
    (count width : ℕ) : Circuit signature (count * (headerWidth + width))
      (count * (headerWidth + width)) :=
  (Circuit.wiring signature (outputWire count headerWidth width)).comp
    ((Circuit.id signature (count * (headerWidth + width))).append
      (broadcastCircuit.values
        (fun record bit => finProdFinEquiv (record, Fin.castAdd width (key bit)))
        (fun record => finProdFinEquiv (record, Fin.castAdd width tag))
        (fun record bit => finProdFinEquiv (record, Fin.natAdd headerWidth bit))))

/-- Every header bit is preserved, including keys, tags and arbitrary routing metadata. -/
theorem eval_broadcastCircuit_header {count headerWidth keyWidth width : ℕ}
    (key : Fin keyWidth → Fin headerWidth) (tag : Fin headerWidth)
    (x : BitString (count * (headerWidth + width))) (record : Fin count) :
    header ((broadcastCircuit key tag count width).eval interpretation x) record =
      header x record := by
  funext bit
  simp only [header, directProductInput, Function.comp_apply, broadcastCircuit, Circuit.eval_comp,
    Circuit.eval_wiring, Circuit.eval_append, Circuit.id, outputWire, Equiv.symm_apply_apply,
    Fin.addCases_left, Fin.append_left, id_eq]

/-- The value field is supplied by the shared scans. -/
theorem eval_broadcastCircuit_value {count headerWidth keyWidth width : ℕ}
    (key : Fin keyWidth → Fin headerWidth) (tag : Fin headerWidth)
    (x : BitString (count * (headerWidth + width))) (record : Fin count) (bit : Fin width) :
    value ((broadcastCircuit key tag count width).eval interpretation x) record bit =
      (broadcastCircuit.values
        (fun record bit => finProdFinEquiv (record, Fin.castAdd width (key bit)))
        (fun record => finProdFinEquiv (record, Fin.castAdd width tag))
        (fun record bit => finProdFinEquiv (record, Fin.natAdd headerWidth bit))).eval
        interpretation x
        (finProdFinEquiv (bit, record)) := by
  simp only [value, directProductInput, Function.comp_apply, broadcastCircuit, Circuit.eval_comp,
    Circuit.eval_wiring, Circuit.eval_append, outputWire, Equiv.symm_apply_apply,
    Fin.addCases_right, Fin.append_right]

/-- Each sorted destination receives the OR of all sources with its selected key. -/
theorem eval_broadcastCircuit_value_eq_true_iff {count headerWidth keyWidth width : ℕ}
    (key : Fin keyWidth → Fin headerWidth) (tag : Fin headerWidth)
    (x : BitString (count * (headerWidth + width)))
    (sorted : Monotone (fun record =>
      toLex (Fin.snoc (α := fun _ => Bool) (header x record ∘ key) (header x record tag))))
    (destination : Fin count) (htag : header x destination tag = true) (bit : Fin width) :
    value ((broadcastCircuit key tag count width).eval interpretation x) destination bit = true ↔
      ∃ source, header x source ∘ key = header x destination ∘ key ∧
        header x source tag = false ∧ value x source bit = true := by
  rw [eval_broadcastCircuit_value]
  exact broadcastCircuit.eval_values_eq_true_iff _ _ _ x sorted bit destination htag

/-- A sorted destination copies its unique matching source value exactly. -/
theorem eval_broadcastCircuit_value_of_unique_source {count headerWidth keyWidth width : ℕ}
    (key : Fin keyWidth → Fin headerWidth) (tag : Fin headerWidth)
    (x : BitString (count * (headerWidth + width)))
    (sorted : Monotone (fun record =>
      toLex (Fin.snoc (α := fun _ => Bool) (header x record ∘ key) (header x record tag))))
    (source destination : Fin count) (hkey : header x source ∘ key = header x destination ∘ key)
    (hsource : header x source tag = false) (hdestination : header x destination tag = true)
    (unique : ∀ record, header x record ∘ key = header x source ∘ key →
      header x record tag = false → record = source) :
    value ((broadcastCircuit key tag count width).eval interpretation x) destination =
      value x source := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  rw [eval_broadcastCircuit_value_eq_true_iff key tag x sorted destination hdestination bit]
  constructor
  · rintro ⟨record, hrecord, htag, hvalue⟩
    exact unique record (hrecord.trans hkey.symm) htag ▸ hvalue
  · intro hvalue
    exact ⟨source, hkey, hsource, hvalue⟩

/-- Exact arbitrary weighted cost: shared adjacent-key tests plus one scan per value bit. -/
theorem cost_program_broadcastCircuit {headerWidth keyWidth : ℕ}
    (key : Fin keyWidth → Fin headerWidth)
    (tag : Fin headerWidth) (count width : ℕ) (cost : signature.Op → ℕ) :
    (broadcastCircuit key tag count width).program.cost cost =
      (if count = 0 then 0 else cost (.const false) + (count - 1) *
        (cost (.const true) + keyWidth * (3 * cost .and + 2 * cost .not + cost .or))) +
      width * (cost (.const false) + count * (cost .not + 2 * cost .and + cost .or)) := by
  simp only [broadcastCircuit, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.id, Circuit.cost_program_wiring, Nat.zero_add, Nat.add_zero,
    broadcastCircuit.cost_values, cost_program_adjacentEqualityCircuit]

/-- Exact gate count, including constants and unused gates at empty dimensions. -/
theorem size_broadcastCircuit {headerWidth keyWidth : ℕ} (key : Fin keyWidth → Fin headerWidth)
    (tag : Fin headerWidth) (count width : ℕ) :
    (broadcastCircuit key tag count width).size =
      (if count = 0 then 0 else 1 + (count - 1) * (6 * keyWidth + 1)) +
      width * (1 + 4 * count) := by
  simpa [Program.cost_const, Nat.mul_comm, Nat.add_comm] using
    cost_program_broadcastCircuit key tag count width (fun _ => 1)

end Cslib.Circuits.Boolean
