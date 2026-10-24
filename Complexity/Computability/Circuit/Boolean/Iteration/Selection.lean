/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Word
public import Complexity.Computability.Circuit.Iteration
public import Complexity.Foundations.Data.List.OfFn
public import Mathlib.Order.Monotone.Defs

/-!
# Finding and selecting a colliding pair

After sorting, two different records with equal keys force an adjacent pair of different records
with that key, even when complete records repeat (`adjacent_distinct_collision`). A linear scan
then retains the last flagged record (`chooseRecord`), at four gates per record bit
(`synthesis_chooseRecord`). The scan works with any number of flagged records and avoids an
all-pairs priority test.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.chooseRecord`: the last flagged record, or a fallback.

## Main results

* `Cslib.Circuits.Boolean.Iteration.adjacent_distinct_collision`: sorting makes a collision
  between different records adjacent.
* `Cslib.Circuits.Boolean.Iteration.chooseRecord_spec`: a flagged record is selected if any.
* `Cslib.Circuits.Boolean.Iteration.synthesis_chooseRecord`: the cost of the scan.
* `Cslib.Circuits.Boolean.Iteration.synthesis_flaggedRecords`: construct and select records,
  sharing each flag across the output bits.

## References

* Adapted from lean/Proofs/{Collisions,Selection}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

universe u v

variable {α : Type u} {R : ℕ}

/-! ### Adjacent collisions -/

section Collision

variable {β : Type v} [LinearOrder β]

/-- In an array with monotone keys, two different records with equal keys force an adjacent pair
of different records with that key. -/
private theorem adjacent_distinct_of_equal_keys (records : Fin R → α) (key : α → β)
    (hs : Monotone (key ∘ records)) (i j : Fin R) (hij : i < j)
    (hne : records i ≠ records j) (heq : key (records i) = key (records j)) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      records ⟨p, by omega⟩ ≠ records ⟨p + 1, hp⟩ ∧
      key (records ⟨p, by omega⟩) = key (records ⟨p + 1, hp⟩) ∧
      key (records ⟨p, by omega⟩) = key (records i) := by
  classical
  have hex : ∃ q, ∃ hq : q < R, i.val < q ∧ q ≤ j.val ∧ records ⟨q, hq⟩ ≠ records i :=
    ⟨j.val, j.isLt, hij, le_rfl, hne.symm⟩
  obtain ⟨hq, hiq, hqj, hdiff⟩ := Nat.find_spec hex
  generalize hqdef : Nat.find hex = q at hq hiq hqj hdiff
  have hmin : ∀ q' < q, ¬∃ hq : q' < R, i.val < q' ∧ q' ≤ j.val ∧ records ⟨q', hq⟩ ≠ records i :=
    fun q' hq' => Nat.find_min hex (by omega)
  have hsame : records ⟨q - 1, by omega⟩ = records i := by
    by_contra h
    have hlt : i.val < q - 1 := by
      have hne : i.val ≠ q - 1 := fun he => h (congrArg records (Fin.ext he.symm))
      omega
    exact hmin (q - 1) (by omega) ⟨by omega, hlt, by omega, h⟩
  have hqkey : key (records ⟨q, hq⟩) = key (records i) :=
    le_antisymm ((hs (show (⟨q, hq⟩ : Fin R) ≤ j from hqj)).trans_eq heq.symm)
      (hs (show i ≤ (⟨q, hq⟩ : Fin R) from hiq.le))
  have hqp : q - 1 + 1 = q := by omega
  refine ⟨q - 1, by omega, ?_, ?_, congrArg key hsame⟩
  · simpa only [hqp, hsame] using hdiff.symm
  · simpa only [hqp, hsame] using hqkey.symm

/-- A sorter preserving complete records makes some collision between different records adjacent,
with the original key. Identical adjacent records can therefore be rejected safely. -/
theorem adjacent_distinct_collision (input output : Fin R → α) (key : α → β)
    (hperm : (List.ofFn output).Perm (List.ofFn input)) (hs : Monotone (key ∘ output))
    (i j : Fin R) (hne : input i ≠ input j) (heq : key (input i) = key (input j)) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      output ⟨p, by omega⟩ ≠ output ⟨p + 1, hp⟩ ∧
      key (output ⟨p, by omega⟩) = key (output ⟨p + 1, hp⟩) ∧
      key (output ⟨p, by omega⟩) = key (input i) := by
  obtain ⟨a, ha⟩ := (hperm.exists_ofFn_iff (· = input i)).mpr ⟨i, rfl⟩
  obtain ⟨b, hb⟩ := (hperm.exists_ofFn_iff (· = input j)).mpr ⟨j, rfl⟩
  have hdiff : output a ≠ output b := by rwa [ha, hb]
  have hkeys : key (output a) = key (output b) := by rwa [ha, hb]
  rcases lt_or_gt_of_ne fun h : a = b => hdiff (h ▸ rfl) with hlt | hlt
  · obtain ⟨p, hp, hd, hk, hi⟩ := adjacent_distinct_of_equal_keys output key hs a b hlt hdiff hkeys
    exact ⟨p, hp, hd, hk, hi.trans (congrArg key ha)⟩
  · obtain ⟨p, hp, hd, hk, hi⟩ :=
      adjacent_distinct_of_equal_keys output key hs b a hlt hdiff.symm hkeys.symm
    exact ⟨p, hp, hd, hk, hi.trans ((congrArg key hb).trans heq.symm)⟩

end Collision

/-! ### Selecting a flagged record -/

/-- The last flagged record among the first `t` positions, or the fallback if there is none. -/
def chooseRecord (flags : Fin R → Bool) (records : Fin R → α) (fallback : α) : ℕ → α
  | 0 => fallback
  | t + 1 => if h : t < R then
      if flags ⟨t, h⟩ then records ⟨t, h⟩ else chooseRecord flags records fallback t
    else chooseRecord flags records fallback t

/-- Selection commutes with applying a function to every record. -/
theorem chooseRecord_map {β : Type*} (g : α → β) (flags : Fin R → Bool)
    (records : Fin R → α) (fallback : α) (t : ℕ) :
    g (chooseRecord flags records fallback t) =
      chooseRecord flags (g ∘ records) (g fallback) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [chooseRecord]
    split_ifs <;> simp only [Function.comp_apply, ih]

/-- If no record is flagged, the scan returns the fallback. -/
theorem chooseRecord_of_forall_eq_false (flags : Fin R → Bool) (records : Fin R → α)
    (fallback : α) (h : ∀ j, flags j = false) (t : ℕ) :
    chooseRecord flags records fallback t = fallback := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [chooseRecord, h, Bool.false_eq_true, ite_false, ih, dite_eq_ite,
      ite_self]

/-- If some record among the first `t` is flagged, the scan returns a flagged record. -/
theorem chooseRecord_spec (flags : Fin R → Bool) (records : Fin R → α) (fallback : α)
    (t : ℕ) (hex : ∃ j : Fin R, j.val < t ∧ flags j = true) :
    ∃ j : Fin R, j.val < t ∧ flags j = true ∧
      chooseRecord flags records fallback t = records j := by
  induction t with
  | zero => obtain ⟨j, hj, _⟩ := hex; omega
  | succ t ih =>
    by_cases ht : t < R
    · by_cases hf : flags ⟨t, ht⟩ = true
      · exact ⟨⟨t, ht⟩, by simp, hf, by simp [chooseRecord, ht, hf]⟩
      · obtain ⟨j, hj, hflag, hout⟩ := ih (by
          obtain ⟨j, hj, hflag⟩ := hex
          refine ⟨j, ?_, hflag⟩
          have hne : j.val ≠ t := fun h => hf ((Fin.ext h : j = ⟨t, ht⟩) ▸ hflag)
          omega)
        exact ⟨j, by omega, hflag, by simp [chooseRecord, ht, hf, hout]⟩
    · obtain ⟨j, hj, hflag, hout⟩ := ih (by
        obtain ⟨j, _, hflag⟩ := hex
        exact ⟨j, by have := j.isLt; omega, hflag⟩)
      exact ⟨j, by omega, hflag, by simp [chooseRecord, ht, hout]⟩

/-- Selecting among available records costs four gates per record bit. -/
theorem synthesis_chooseRecord {n w : ℕ} (s : Set (BooleanFunction n))
    (flags : BitString n → Fin R → Bool)
    (records : BitString n → Fin R → Fin w → Bool)
    (fallback : BitString n → Fin w → Bool)
    (hf : ∀ j, (fun x => flags x j) ∈ s)
    (hr : ∀ j bit, (fun x => records x j bit) ∈ s)
    (hzero : ∀ bit, (fun x => fallback x bit) ∈ s) :
    Synthesis interpretation s
      (Set.range fun bit x => chooseRecord (flags x) (records x) (fallback x) R bit)
      (R * (4 * w)) := by
  let q := fun t => Set.range fun bit x =>
    chooseRecord (flags x) (records x) (fallback x) t bit
  have hs := Synthesis.steps (I := interpretation) (s := s) q (4 * w) R
    (by rintro _ ⟨bit, rfl⟩; exact hzero bit) fun t ht => ?_
  · exact hs.mono Set.Subset.rfl (Synthesis.subset_stages q le_rfl) le_rfl
  · have h := Synthesis.family (I := interpretation) (s := s ∪ Synthesis.stages q t)
      (fun bit x => if flags x ⟨t, ht⟩ then records x ⟨t, ht⟩ bit
        else chooseRecord (flags x) (records x) (fallback x) t bit)
      (fun _ => 4) fun bit => Synthesis.mux
        (Or.inl (hf ⟨t, ht⟩)) (Or.inl (hr ⟨t, ht⟩ bit))
        (Or.inr (Synthesis.subset_stages q le_rfl ⟨bit, rfl⟩))
    simpa [q, chooseRecord, ht, ite_apply, Nat.mul_comm] using h

/-- Construct all flagged records and select one, sharing every flag across its
output bits. The all-false fallback is an already available constant. -/
theorem synthesis_flaggedRecords {n w : ℕ} (s : Set (BooleanFunction n))
    (flags : Fin R → (Fin n → Bool) → Bool)
    (records : Fin R → (Fin n → Bool) → Fin w → Bool) (K : ℕ)
    (hz : (fun _ => false) ∈ s)
    (hrows : ∀ j, Synthesis Boolean.interpretation s
      ({flags j} ∪ Set.range (fun i x => records j x i)) K) :
    Synthesis Boolean.interpretation s
      (Set.range fun i x => chooseRecord (fun j => flags j x)
        (fun j => records j x) (fun _ => false) R i)
      (R * (K + 4 * w)) := by
  have hall := Synthesis.iUnion
    (fun j => {flags j} ∪ Set.range (fun i x => records j x i)) (fun _ => K) hrows
  have hselect := synthesis_chooseRecord
    (s ∪ ⋃ j, {flags j} ∪ Set.range (fun i x => records j x i))
    (fun x j => flags j x) (fun x j => records j x) (fun _ _ => false)
    (fun j => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inl rfl⟩))
    (fun j bit => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inr ⟨bit, rfl⟩⟩))
    (fun _ => Or.inl hz)
  simpa [Nat.mul_add] using hall.trans hselect

end Cslib.Circuits.Boolean.Iteration
