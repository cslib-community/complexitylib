/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Record
public import Complexity.Computability.Circuit.Synthesis
public import Complexity.Computability.Circuit.Boolean.Equality
import Mathlib.Tactic.Linarith

/-!
# Gate counts for sorting and detecting records

A family of records is available when every bit of every encoded record is (`Record.wireSet`).
Sorting an available array inserts one Batcher circuit (`Record.synthesis_sorted`); its native
gate count is at most `18 * d ^ 2 * 2 ^ d` per record bit and comparison layer. Testing every
adjacent pair for a collision and selecting one costs linearly in the array
(`Record.synthesis_detect`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.wires`: the coordinate functions of a family of bit strings.
* `Cslib.Circuits.Boolean.Iteration.Record.wireSet`, `Record.recordsWires`: available records.

## Main results

* `Cslib.Circuits.Boolean.Iteration.Record.size_sortCircuit_le`: the native sorter's size.
* `Cslib.Circuits.Boolean.Iteration.Record.synthesis_sorted`: sorting an available array.
* `Cslib.Circuits.Boolean.Iteration.Record.synthesis_detect`: detecting a colliding pair.

## References

* Adapted from lean/Proofs/{RecordCircuits,Construction}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n w R : ℕ}

/-- The coordinate functions of a family of bit strings. -/
def wires {m : ℕ} (a : BitString n → BitString m) : Set (BooleanFunction n) :=
  Set.range fun i x => a x i

/-- Equality of two available bit strings, by the native equality formula. -/
theorem synthesis_bits_eq {m : ℕ} (s : Set (BooleanFunction n))
    (a b : BitString n → BitString m) (ha : wires a ⊆ s) (hb : wires b ⊆ s) :
    Synthesis interpretation s {fun x => decide (a x = b x)} (6 * m + 1) := by
  have h := Synthesis.circuit (I := interpretation) (s := s)
    (Formula.equalBits (Fin.castAdd m) (Fin.natAdd m)).toCircuit
    (Fin.append (fun i x => a x i) fun i x => b x i) fun i => by
      induction i using Fin.addCases with
      | left i => simpa only [Fin.append_left] using ha ⟨i, rfl⟩
      | right i => simpa only [Fin.append_right] using hb ⟨i, rfl⟩
  refine h.mono Set.Subset.rfl ?_ (by simp)
  rintro _ rfl
  refine ⟨0, funext fun x => Bool.eq_iff_iff.mpr ?_⟩
  have hl : (fun i => Fin.append (fun i x => a x i) (fun i x => b x i) i x) ∘ Fin.castAdd m =
      a x := funext fun i => by simp only [Function.comp_apply, Fin.append_left]
  have hr : (fun i => Fin.append (fun i x => a x i) (fun i x => b x i) i x) ∘ Fin.natAdd m =
      b x := funext fun i => by simp only [Function.comp_apply, Fin.append_right]
  simp only [Formula.eval_toCircuit, Formula.eval_equalBits_iff, decide_eq_true_eq, hl, hr]

theorem synthesis_bits_mux {m : ℕ} (s : Set (BooleanFunction n))
    (a b : BitString n → BitString m) (flag : BooleanFunction n)
    (ha : wires a ⊆ s) (hb : wires b ⊆ s) (hf : flag ∈ s) :
    Synthesis interpretation s (wires fun x => if flag x then a x else b x) (4 * m) := by
  have h := Synthesis.family (I := interpretation) (s := s)
    (fun i x => if flag x then a x i else b x i) (fun _ => 4)
    fun i => Synthesis.mux hf (ha ⟨i, rfl⟩) (hb ⟨i, rfl⟩)
  simpa only [wires, ite_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

/-- Choosing between two constructions by a third adds four gates per output bit. -/
theorem synthesis_ite {m A B F : ℕ} {s : Set (BooleanFunction n)}
    {a b : BitString n → BitString m} {flag : BooleanFunction n}
    (ha : Synthesis interpretation s (wires a) A) (hb : Synthesis interpretation s (wires b) B)
    (hf : Synthesis interpretation s {flag} F) :
    Synthesis interpretation s (wires fun x => if flag x then a x else b x)
      (A + B + F + 4 * m) :=
  ((ha.union hb).union hf).trans (synthesis_bits_mux _ a b flag
    (fun _ h => Or.inr (Or.inl (Or.inl h)))
    (fun _ h => Or.inr (Or.inl (Or.inr h))) (Or.inr (Or.inr rfl)))

namespace Record

/-- The bits of an available family of records. -/
def wireSet (a : BitString n → Record n w) : Set (BooleanFunction n) := wires fun x => encode (a x)

theorem padding_mem {s : Set (BooleanFunction n)} {a : BitString n → Record n w}
    (ha : wireSet a ⊆ s) : (fun x => (a x).padding) ∈ s := by
  simpa [encode] using ha ⟨Fin.castAdd (w + n + 1) 0, rfl⟩

theorem state_mem {s : Set (BooleanFunction n)} {a : BitString n → Record n w}
    (ha : wireSet a ⊆ s) (i : Fin n) : (fun x => (a x).state i) ∈ s := by
  simpa [encode] using ha ⟨Fin.castAdd (w + n + 1) i.succ, rfl⟩

theorem checkpoint_mem {s : Set (BooleanFunction n)} {a : BitString n → Record n w}
    (ha : wireSet a ⊆ s) : (fun x => (a x).checkpoint) ∈ s := by
  simpa [encode] using ha ⟨Fin.natAdd (n + 1) 0, rfl⟩

theorem index_mem {s : Set (BooleanFunction n)} {a : BitString n → Record n w}
    (ha : wireSet a ⊆ s) (i : Fin w) : (fun x => (a x).index.getLsbD i.val) ∈ s := by
  simpa [encode] using ha ⟨Fin.natAdd (n + 1) (Fin.castAdd n i).succ, rfl⟩

theorem payload_mem {s : Set (BooleanFunction n)} {a : BitString n → Record n w}
    (ha : wireSet a ⊆ s) (i : Fin n) : (fun x => (a x).payload i) ∈ s := by
  simpa [encode] using ha ⟨Fin.natAdd (n + 1) (Fin.natAdd w i).succ, rfl⟩

private theorem synthesis_collision (s : Set (BooleanFunction n)) (a b : BitString n → Record n w)
    (ha : wireSet a ⊆ s) (hb : wireSet b ⊆ s) :
    Synthesis interpretation s {fun x => collision (a x) (b x)} (20 * (width n w + 1)) := by
  have hs := synthesis_bits_eq s (fun x => (a x).state) (fun x => (b x).state)
    (by rintro _ ⟨i, rfl⟩; exact state_mem ha i) (by rintro _ ⟨i, rfl⟩; exact state_mem hb i)
  have he := synthesis_bits_eq s (fun x => encode (a x)) (fun x => encode (b x)) ha hb
  have hne : Synthesis interpretation s {fun x => decide (a x ≠ b x)} (6 * width n w + 1 + 1) := by
    simpa only [encode_injective.eq_iff, decide_not] using he.not
  have h := (((Synthesis.of_mem (padding_mem ha)).not.and
    (Synthesis.of_mem (padding_mem hb)).not).and hs).and hne
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by unfold width; omega)

/-- The bits of a pair of records, the first record first. -/
def pairEncode (pair : Record n w × Record n w) : BitString (width n w + width n w) :=
  Fin.append (encode pair.1) (encode pair.2)

/-- The bits of an available family of pairs of records. -/
def pairWires (p : BitString n → Record n w × Record n w) : Set (BooleanFunction n) :=
  wires fun x => pairEncode (p x)

theorem wireSet_fst_subset (p : BitString n → Record n w × Record n w) :
    wireSet (fun x => (p x).1) ⊆ pairWires p := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castAdd (width n w) i, by simp only [pairEncode, Fin.append_left]⟩

theorem wireSet_snd_subset (p : BitString n → Record n w × Record n w) :
    wireSet (fun x => (p x).2) ⊆ pairWires p := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.natAdd (width n w) i, by simp only [pairEncode, Fin.append_right]⟩

/-- Testing all adjacent pairs and selecting a colliding one. -/
theorem synthesis_detect (s : Set (BooleanFunction n)) (records : BitString n → Fin R → Record n w)
    (hr : ∀ j, wireSet (fun x => records x j) ⊆ s)
    (hconst : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Synthesis interpretation s (pairWires fun x => detect (records x))
      (30 * R * (width n w + 1)) := by
  let flags := fun (j : Fin (R - 1)) x =>
    collision (adjacentPair (records x) j).1 (adjacentPair (records x) j).2
  have hf := Synthesis.family (I := interpretation) (s := s) flags
    (fun _ => 20 * (width n w + 1)) fun j => synthesis_collision s _ _ (hr _) (hr _)
  have hs := synthesis_chooseRecord (s ∪ Set.range flags)
    (fun x j => flags j x) (fun x j => pairEncode (adjacentPair (records x) j))
    (fun _ => pairEncode (pad, pad)) (fun j => Or.inr ⟨j, rfl⟩) (fun j bit => ?_)
    fun bit => Or.inl (hconst _)
  · have he : (pairWires fun x => detect (records x)) =
        Set.range fun bit x => chooseRecord (fun j => flags j x)
          (fun j => pairEncode (adjacentPair (records x) j)) (pairEncode (pad, pad))
          (R - 1) bit := by
      unfold pairWires wires detect
      congr 1
      funext bit x
      exact congrFun (chooseRecord_map pairEncode (fun j => flags j x)
        (adjacentPair (records x)) (pad, pad) (R - 1)) bit
    rw [he]
    apply (hf.trans hs).mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    nlinarith [Nat.sub_le R 1, Nat.mul_le_mul_right (width n w + 1) (Nat.sub_le R 1)]
  · induction bit using Fin.addCases with
    | left bit =>
      refine Or.inl ?_
      simpa only [pairEncode, Fin.append_left, adjacentPair] using hr _ ⟨bit, rfl⟩
    | right bit =>
      refine Or.inl ?_
      simpa only [pairEncode, Fin.append_right, adjacentPair] using hr _ ⟨bit, rfl⟩

/-- The bits of every record of an available array. -/
def recordsWires (records : BitString n → Fin R → Record n w) : Set (BooleanFunction n) :=
  ⋃ j, wireSet fun x => records x j

theorem wireSet_subset_recordsWires (records : BitString n → Fin R → Record n w) (j : Fin R) :
    wireSet (fun x => records x j) ⊆ recordsWires records :=
  Set.subset_iUnion_of_subset j Set.Subset.rfl

/-- The native sorter has at most `18 * d ^ 2 * 2 ^ d * (width + 1)` gates. -/
theorem size_sortCircuit_le (d : ℕ) :
    (bitonicSortCircuit (keyBits (n := n) (w := w)) d true).size ≤
      18 * d ^ 2 * 2 ^ d * (width n w + 1) := by
  have h := four_mul_size_bitonicSortCircuit (keyBits (n := n) (w := w)) d true
  have hite : (if width n w = 0 then 0 else 6 * (n + 1) + 6 * width n w + 2) ≤
      12 * (width n w + 1) := by
    split_ifs <;> unfold width <;> omega
  have hd : d * (d + 1) ≤ 2 * d ^ 2 := by nlinarith
  have := Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ d) hd) hite
  nlinarith

/-- Sorting an available array inserts one native sorting circuit. -/
theorem synthesis_sorted (s : Set (BooleanFunction n)) (d : ℕ)
    (records : BitString n → Fin (BitonicSort.arity d) → Record n w)
    (hr : recordsWires records ⊆ s) :
    Synthesis interpretation s (recordsWires fun x => sorted d (records x))
      (18 * d ^ 2 * 2 ^ d * (width n w + 1)) := by
  have h := Synthesis.circuit (I := interpretation) (s := s)
    (bitonicSortCircuit (keyBits (n := n) (w := w)) d true) (fun bit x => pack (records x) bit)
    fun bit => hr (wireSet_subset_recordsWires records _ ⟨_, rfl⟩)
  apply h.mono Set.Subset.rfl ?_ (size_sortCircuit_le d)
  intro fn hfn
  obtain ⟨j, bit, rfl⟩ := Set.mem_iUnion.mp hfn
  exact ⟨finProdFinEquiv (j, bit), by simp [sorted, directProductInput]⟩

end Record

end Cslib.Circuits.Boolean.Iteration
