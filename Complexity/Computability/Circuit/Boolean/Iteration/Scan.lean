/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.RecordCircuit
public import Mathlib.Order.PiLex
import Complexity.Computability.Circuit.Boolean.CompareSwap

/-!
# Linear scans for a least state and a first flagged position

A linear scan keeps the least of a sequence of values (`scanMin`). For bit strings ordered
lexicographically with coordinate zero most significant (`lexOrder`), each step compares the next
state with the current minimum once and selects one of them, at `10 * n + 1` gates for `n`-bit
states (`synthesis_scanMin`). Scanning the records in reverse order selects the first flagged one
(`chooseFirst`), and the first flagged position, written in binary, costs four gates per
position and bit (`synthesis_firstIndex`).

All gates of the native De Morgan basis, including constants, are charged; wiring and fanout
are free.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.lexOrder`: the lexicographic order on bit strings.
* `Cslib.Circuits.Boolean.Iteration.scanMin`: the least of the first values and a fallback.
* `Cslib.Circuits.Boolean.Iteration.chooseFirst`: the first flagged record.
* `Cslib.Circuits.Boolean.Iteration.firstIndex`: the first flagged position as a word.

## Main results

* `Cslib.Circuits.Boolean.Iteration.scanMin_spec`: the scan is a least value.
* `Cslib.Circuits.Boolean.Iteration.chooseFirst_spec`, `firstIndex_spec`: the first flagged
  record and position.
* `Cslib.Circuits.Boolean.Iteration.synthesis_scanMin`,
  `Cslib.Circuits.Boolean.Iteration.synthesis_firstIndex`: their gate counts.

## References

* Adapted from lean/Proofs/ScanSelection.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

/-- The lexicographic order on bit strings, with coordinate zero most significant and `false`
below `true`. -/
noncomputable abbrev lexOrder (n : ℕ) : LinearOrder (BitString n) :=
  LinearOrder.lift' toLex fun _ _ h => h

/-! ### Least values -/

section MinScan

variable {α : Type*} [LinearOrder α] {R : ℕ}

/-- The least of the values at positions below `t` and the fallback. -/
def scanMin (values : Fin R → α) (fallback : α) : ℕ → α
  | 0 => fallback
  | t + 1 => if h : t < R then min (values ⟨t, h⟩) (scanMin values fallback t)
    else scanMin values fallback t

/-- The scan is the fallback or one of the scanned values, and below all of them. -/
theorem scanMin_spec (values : Fin R → α) (fallback : α) (t : ℕ) :
    (scanMin values fallback t = fallback ∨
      ∃ j : Fin R, j.val < t ∧ scanMin values fallback t = values j) ∧
    scanMin values fallback t ≤ fallback ∧
      ∀ j : Fin R, j.val < t → scanMin values fallback t ≤ values j := by
  induction t with
  | zero => exact ⟨Or.inl rfl, le_rfl, fun j hj => by omega⟩
  | succ t ih =>
    by_cases ht : t < R
    · rw [scanMin, dite_eq_left ht]
      refine ⟨?_, (min_le_right _ _).trans ih.2.1, fun j hj => ?_⟩
      · rcases min_cases (values ⟨t, ht⟩) (scanMin values fallback t) with h | h
        · exact Or.inr ⟨⟨t, ht⟩, by simp, h.1⟩
        · rcases ih.1 with hh | ⟨j, hj, he⟩
          · exact Or.inl (h.1.trans hh)
          · exact Or.inr ⟨j, by omega, h.1.trans he⟩
      · by_cases he : j.val = t
        · rw [show j = ⟨t, ht⟩ from Fin.ext he]
          exact min_le_left _ _
        · exact (min_le_right _ _).trans (ih.2.2 j (by omega))
    · rw [scanMin, dite_eq_right ht]
      refine ⟨?_, ih.2.1, fun j _ => ih.2.2 j (by have := j.isLt; omega)⟩
      rcases ih.1 with h | ⟨j, hj, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, he⟩

end MinScan

variable {n a R w : ℕ}

open Classical in
/-- Lexicographic comparison of two available bit strings, by the native comparison formula. -/
private theorem synthesis_lexLt (s : Set (BooleanFunction a)) (x y : BitString a → BitString n)
    (hx : wires x ⊆ s) (hy : wires y ⊆ s) :
    Synthesis interpretation s {fun z => decide (toLex (x z) < toLex (y z))} (6 * n + 1) := by
  have h := Synthesis.circuit (I := interpretation) (s := s)
    (Formula.lexLt (Fin.castAdd n) (Fin.natAdd n)).toCircuit
    (Fin.append (fun i z => x z i) fun i z => y z i) fun i => by
      induction i using Fin.addCases with
      | left i => simpa only [Fin.append_left] using hx ⟨i, rfl⟩
      | right i => simpa only [Fin.append_right] using hy ⟨i, rfl⟩
  refine h.mono Set.Subset.rfl ?_ (by simp)
  rintro _ rfl
  refine ⟨0, funext fun z => Bool.eq_iff_iff.mpr ?_⟩
  have hl : (fun i => Fin.append (fun i z => x z i) (fun i z => y z i) i z) ∘ Fin.castAdd n =
      x z := funext fun i => by simp only [Function.comp_apply, Fin.append_left]
  have hr : (fun i => Fin.append (fun i z => x z i) (fun i z => y z i) i z) ∘ Fin.natAdd n =
      y z := funext fun i => by simp only [Function.comp_apply, Fin.append_right]
  simp only [Formula.eval_toCircuit, Formula.eval_lexLt_iff, decide_eq_true_eq, hl, hr]

/-- **Minimum scan.** The lexicographically least of `R` available states and a fallback costs
one comparison and one selection per state. -/
theorem synthesis_scanMin (s : Set (BooleanFunction a)) (values : BitString a → Fin R → BitString n)
    (fallback : BitString a → BitString n) (hv : ∀ j bit, (fun x => values x j bit) ∈ s)
    (hf : ∀ bit, (fun x => fallback x bit) ∈ s) :
    Synthesis interpretation s
      (wires fun x => @scanMin _ (lexOrder n) _ (values x) (fallback x) R) (R * (10 * n + 1)) := by
  classical
  let := lexOrder n
  let current := fun t x => scanMin (values x) (fallback x) t
  let q := fun t => wires (current t)
  have hz : q 0 ⊆ s := by rintro _ ⟨bit, rfl⟩; exact hf bit
  have hs := Synthesis.steps (I := interpretation) q (10 * n + 1) R hz fun t ht => ?_
  · exact hs.mono Set.Subset.rfl (Synthesis.subset_stages q le_rfl) le_rfl
  · let src := s ∪ Synthesis.stages q t
    have hcur : wires (current t) ⊆ src := fun _ h => Or.inr (Synthesis.subset_stages q le_rfl h)
    have hval : wires (fun x => values x ⟨t, ht⟩) ⊆ src := by
      rintro _ ⟨bit, rfl⟩
      exact Or.inl (hv _ bit)
    let less := fun x => decide (toLex (values x ⟨t, ht⟩) < toLex (current t x))
    have hl := synthesis_lexLt src (fun x => values x ⟨t, ht⟩) (current t) hval hcur
    have hm := synthesis_bits_mux (src ∪ {less}) (fun x => values x ⟨t, ht⟩) (current t) less
      (fun _ h => Or.inl (hval h)) (fun _ h => Or.inl (hcur h)) (Or.inr rfl)
    have he : (fun x => if less x then values x ⟨t, ht⟩ else current t x) = current (t + 1) := by
      funext x
      change _ = scanMin (values x) (fallback x) (t + 1)
      rw [scanMin, dite_eq_left ht]
      by_cases hh : toLex (values x ⟨t, ht⟩) < toLex (current t x)
      · simp only [less, hh, decide_true, ite_true]
        exact (min_eq_left hh.le).symm
      · simp only [less, hh, decide_false, Bool.false_eq_true, ite_false]
        exact (min_eq_right (le_of_not_gt hh)).symm
    rw [he] at hm
    exact (hl.trans hm).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-! ### First flagged positions -/

/-- If position `j` is flagged and no later position below `t` is, the scan returns its record. -/
private theorem chooseRecord_eq_of_last {α : Type*} (flags : Fin R → Bool) (records : Fin R → α)
    (fallback : α) (j : Fin R) (hj : flags j = true) (t : ℕ) (hjt : j.val < t)
    (hlast : ∀ i : Fin R, j.val < i.val → i.val < t → flags i = false) :
    chooseRecord flags records fallback t = records j := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht : t < R
    · rw [chooseRecord, dite_eq_left ht]
      by_cases he : j.val = t
      · rw [show (⟨t, ht⟩ : Fin R) = j from Fin.ext he.symm, hj, ite_eq_left rfl]
      · rw [hlast ⟨t, ht⟩ (by simp only; omega) (by simp only; omega),
          ite_eq_right Bool.false_ne_true]
        exact ih (by omega) fun i hi hit => hlast i hi (by omega)
    · rw [chooseRecord, dite_eq_right ht]
      exact ih (by have := j.isLt; omega) fun i hi hit => hlast i hi (by omega)

/-- The first flagged record, or the fallback if none is flagged: the last flagged record in
reverse order. -/
def chooseFirst {α : Type*} (flags : Fin R → Bool) (records : Fin R → α) (fallback : α) : α :=
  chooseRecord (fun j => flags j.rev) (fun j => records j.rev) fallback R

theorem chooseFirst_spec {α : Type*} (flags : Fin R → Bool) (records : Fin R → α)
    (fallback : α) (j : Fin R) (hj : flags j = true)
    (hfirst : ∀ i : Fin R, i.val < j.val → flags i = false) :
    chooseFirst flags records fallback = records j := by
  have h := chooseRecord_eq_of_last (fun i => flags i.rev) (fun i => records i.rev)
    fallback j.rev (by simpa using hj) R j.rev.isLt fun i hi _ => by
      apply hfirst
      simp only [Fin.val_rev] at hi ⊢
      omega
  simpa only [chooseFirst, Fin.rev_rev] using h

/-- The first flagged position in `w` bits, or zero if none is flagged. -/
def firstIndex (flags : Fin R → Bool) : BitVec w :=
  word (chooseFirst flags (fun j bit => (BitVec.ofNat w j.val).getLsbD bit.val) fun _ => false)

theorem firstIndex_spec (flags : Fin R → Bool) (j : Fin R) (hj : flags j = true)
    (hfirst : ∀ i : Fin R, i.val < j.val → flags i = false) :
    firstIndex (w := w) flags = BitVec.ofNat w j.val := by
  rw [firstIndex, chooseFirst_spec flags _ _ j hj hfirst, word_getLsbD]

/-- The first flagged position among `R` available flags costs four gates per position and
bit. -/
theorem synthesis_firstIndex (s : Set (BooleanFunction a)) (flags : BitString a → Fin R → Bool)
    (hf : ∀ j, (fun x => flags x j) ∈ s) (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) :
    Synthesis interpretation s (wordWires fun x => firstIndex (w := w) (flags x))
      (R * (4 * w)) := by
  have h := synthesis_chooseRecord (w := w) s (fun x j => flags x j.rev)
    (fun _ j bit => (BitVec.ofNat w j.rev.val).getLsbD bit.val) (fun _ _ => false)
    (fun j => hf j.rev) (fun _ _ => hc _) fun _ => hc false
  simpa only [wordWires, firstIndex, chooseFirst, getLsbD_word] using h

end Cslib.Circuits.Boolean.Iteration
