/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Scan
public import Complexity.Computability.Circuit.Boolean.Iteration.Remainder
public import Complexity.Foundations.Combinatorics.FunctionalGraph.HittingTime

/-!
# Canonical cycle labels as bit strings

Order `n`-bit states lexicographically, coordinate zero first (`lexOrder`). The canonical label
of a state `x` under `f` lists the least state of its eventual cycle, the cycle length and the
phase of `x` on the cycle, the last two in `n + 3` bits (`canonicalLabel`). Labels along an
orbit differ only in the phase, so the label of `x` is recovered from the label of `f^[j] x` by
subtracting `j` modulo the cycle length (`correctLabel_canonicalLabel`).

On a cycle of length at most `K`, the first `K + 1` states of the orbit of a periodic state
contain the whole cycle. A scan for the least of them, the first return to `x` and the first
visit to the least state give its label directly (`shortLabel_eq_canonicalLabel`), in
`O(K * n + n ^ 2)` gates once the orbit prefix is available (`synthesis_shortLabel`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.canonicalLabel`: representative, cycle length and phase.
* `Cslib.Circuits.Boolean.Iteration.correctLabel`: shift a label back along the orbit.
* `Cslib.Circuits.Boolean.Iteration.shortLabel`: the label read from one traversal of a short
  cycle.

## Main results

* `Cslib.Circuits.Boolean.Iteration.correctLabel_canonicalLabel`: correcting a later label.
* `Cslib.Circuits.Boolean.Iteration.shortLabel_eq_canonicalLabel`: short cycles.
* `Cslib.Circuits.Boolean.Iteration.synthesis_correctLabel`,
  `Cslib.Circuits.Boolean.Iteration.synthesis_shortLabel`: their gate counts.

## References

* Adapted from lean/Proofs/{ShortCycle,LabelEncoding}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n a w : ℕ}

/-! ### Label words -/

/-- A state followed by two words. -/
def labelBits (c : BitString n) (ell phi : BitVec w) : BitString (n + (w + w)) :=
  Fin.append c (Fin.append (fun i => ell.getLsbD i.val) fun i => phi.getLsbD i.val)

/-- The state of a label. -/
def labelRepresentative (r : BitString (n + (w + w))) : BitString n :=
  fun i => r (Fin.castAdd (w + w) i)

/-- The first word of a label: the cycle length. -/
def labelLength (r : BitString (n + (w + w))) : BitVec w :=
  word fun i => r (Fin.natAdd n (Fin.castAdd w i))

/-- The second word of a label: the phase. -/
def labelPhase (r : BitString (n + (w + w))) : BitVec w :=
  word fun i => r (Fin.natAdd n (Fin.natAdd w i))

@[simp] theorem labelRepresentative_labelBits (c : BitString n) (ell phi : BitVec w) :
    labelRepresentative (labelBits c ell phi) = c := by
  funext i
  simp only [labelRepresentative, labelBits, Fin.append_left]

@[simp] theorem labelLength_labelBits (c : BitString n) (ell phi : BitVec w) :
    labelLength (labelBits c ell phi) = ell := by
  simp only [labelLength, labelBits, Fin.append_left, Fin.append_right, word_getLsbD]

@[simp] theorem labelPhase_labelBits (c : BitString n) (ell phi : BitVec w) :
    labelPhase (labelBits c ell phi) = phi := by
  simp only [labelPhase, labelBits, Fin.append_right, word_getLsbD]

/-- The width of a canonical label: a state, then two words of `n + 3` bits. -/
abbrev labelWidth (n : ℕ) : ℕ := n + ((n + 3) + (n + 3))

/-- **Canonical labels.** The lexicographically least state of the eventual cycle of `x`, the
cycle length, and the phase of `x` on the cycle, the last two in `n + 3` bits. -/
noncomputable def canonicalLabel (f : BitString n → BitString n) (x : BitString n) :
    BitString (labelWidth n) :=
  labelBits (canonicalCycle f x) (BitVec.ofNat (n + 3) (cycleLength f x))
    (BitVec.ofNat (n + 3) (phase f x))

theorem cycleLength_le_two_pow (f : BitString n → BitString n) (x : BitString n) :
    cycleLength f x ≤ 2 ^ n := by
  have h := transientDepth_add_cycleLength_le_card f x
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  omega

theorem toNat_ofNat_cycleLength (f : BitString n → BitString n) (x : BitString n) :
    (BitVec.ofNat (n + 3) (cycleLength f x)).toNat = cycleLength f x := by
  have h := cycleLength_le_two_pow f x
  have hpos := cycleLength_pos f x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [Nat.pow_succ]
  omega

theorem toNat_ofNat_phase (f : BitString n → BitString n) (x : BitString n) :
    (BitVec.ofNat (n + 3) (phase f x)).toNat = phase f x := by
  have h := (phase_lt f x).trans_le (cycleLength_le_two_pow f x)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [Nat.pow_succ]
  omega

/-! ### Correcting labels along an orbit -/

/-- Shift a label back by `j` steps: subtract `j` from its phase modulo its cycle length. -/
def correctLabel (r : BitString (n + (w + w))) (j : ℕ) : BitString (n + (w + w)) :=
  labelBits (labelRepresentative r) (labelLength r)
    (subMod (labelPhase r) (BitVec.ofNat w j) (labelLength r))

/-- The label of `x` is the label of `f^[j] x` shifted back by `j`, for `j < 2 ^ (n + 3)`. -/
theorem correctLabel_canonicalLabel (f : BitString n → BitString n) (x : BitString n) (j : ℕ)
    (hj : j < 2 ^ (n + 3)) : correctLabel (canonicalLabel f (f^[j] x)) j = canonicalLabel f x := by
  simp only [correctLabel, canonicalLabel, labelRepresentative_labelBits, labelLength_labelBits,
    labelPhase_labelBits, canonicalCycle_iterate, cycleLength_iterate]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hl := cycleLength_le_two_pow f x
  have hpos := cycleLength_pos f x
  rw [toNat_subMod _ _ _ (by rwa [toNat_ofNat_cycleLength])
      (by rw [toNat_ofNat_cycleLength, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega),
    toNat_ofNat_cycleLength, toNat_ofNat_phase, toNat_ofNat_phase, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hj, phase_iterate]
  exact add_sub_mod_mod_eq_of_modEq hpos (phase_lt f x) (Nat.mod_modEq _ _).symm

/-- The bits of a label of available parts are available. -/
theorem labelBits_wires_subset (s : Set (BooleanFunction a)) (c : BitString a → BitString n)
    (ell phi : BitString a → BitVec w) (hc : wires c ⊆ s) (he : wordWires ell ⊆ s)
    (hp : wordWires phi ⊆ s) : wires (fun x => labelBits (c x) (ell x) (phi x)) ⊆ s := by
  rintro _ ⟨bit, rfl⟩
  induction bit using Fin.addCases with
  | left bit => simpa only [labelBits, Fin.append_left] using hc ⟨bit, rfl⟩
  | right bit =>
    induction bit using Fin.addCases with
    | left bit => simpa only [labelBits, Fin.append_right, Fin.append_left] using he ⟨bit, rfl⟩
    | right bit => simpa only [labelBits, Fin.append_right] using hp ⟨bit, rfl⟩

/-- Correcting an available label costs one modular difference. -/
theorem synthesis_correctLabel (s : Set (BooleanFunction a))
    (r : BitString a → BitString (n + (w + w))) (hr : wires r ⊆ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) (j : ℕ) :
    Synthesis interpretation s (wires fun x => correctLabel (r x) j) (50 * (w + 1) ^ 2) := by
  have hlen : wordWires (fun x => labelLength (r x)) ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [labelLength, getLsbD_word] using hr ⟨_, rfl⟩
  have hp := synthesis_subMod s (fun x => labelPhase (r x)) (fun _ => BitVec.ofNat w j)
    (fun x => labelLength (r x))
    (fun i => by simpa only [labelPhase, getLsbD_word] using hr ⟨_, rfl⟩) (fun _ => hc _)
    (fun i => hlen ⟨i, rfl⟩) (hc false)
  refine (hp.trans (Synthesis.of_subset (labelBits_wires_subset _ _ _ _ ?_ ?_ ?_))).mono
    Set.Subset.rfl Set.Subset.rfl (by omega)
  · rintro _ ⟨bit, rfl⟩
    exact Or.inl (hr ⟨_, rfl⟩)
  · exact fun _ h => Or.inl (hlen h)
  · exact fun _ h => Or.inr h

/-! ### Short cycles -/

/-- The least of the first `K + 1` states of the orbit of `x`. -/
noncomputable def shortRepresentative (f : BitString n → BitString n) (K : ℕ) (x : BitString n) :
    BitString n :=
  scanMin (fun j : Fin (K + 1) => f^[j.val] x) x (K + 1)

/-- The first positive time up to `K` at which the orbit of `x` returns to `x`. -/
def shortLength (f : BitString n → BitString n) (K : ℕ) (x : BitString n) : BitVec w :=
  firstIndex fun j : Fin (K + 1) => decide (0 < j.val ∧ f^[j.val] x = x)

/-- The first time up to `K` at which the orbit of `x` visits its short representative. -/
noncomputable def shortTime (f : BitString n → BitString n) (K : ℕ) (x : BitString n) :
    BitVec w :=
  firstIndex fun j : Fin (K + 1) => decide (f^[j.val] x = shortRepresentative f K x)

/-- The label read from the first `K + 1` states of the orbit of `x`. -/
noncomputable def shortLabel (f : BitString n → BitString n) (K : ℕ) (x : BitString n) :
    BitString (labelWidth n) :=
  labelBits (shortRepresentative f K x) (shortLength f K x)
    (subMod 0 (shortTime f K x) (shortLength f K x))

section Short

variable (f : BitString n → BitString n) (K : ℕ) {x : BitString n}
  (hx : x ∈ Function.periodicPts f) (hK : cycleLength f x ≤ K)

include hx hK in
private theorem shortRepresentative_eq : shortRepresentative f K x = canonicalCycle f x := by
  have hs := scanMin_spec (fun j : Fin (K + 1) => f^[j.val] x) x (K + 1)
  apply @le_antisymm _ (lexOrder n).toPartialOrder
  · have ht := canonicalTime_lt_cycleLength f x hx
    have h := hs.2.2 ⟨canonicalTime f x, by omega⟩ (by simp only; omega)
    rwa [canonicalTime_spec] at h
  · apply canonicalCycle_le f x
    rcases hs.1 with hh | ⟨j, -, hh⟩
    · rw [shortRepresentative, hh]
      simpa using iterate_mem_cycleSet f hx 0
    · rw [shortRepresentative, hh]
      exact iterate_mem_cycleSet f hx j.val

include hx hK in
private theorem shortLength_eq : shortLength (w := w) f K x = BitVec.ofNat w (cycleLength f x) := by
  have hmin : Function.minimalPeriod f x = cycleLength f x :=
    (cycleLength_eq_minimalPeriod_of_mem_periodicPts f hx).symm
  apply firstIndex_spec _ ⟨cycleLength f x, by omega⟩
  · apply decide_eq_true
    refine ⟨cycleLength_pos f x, ?_⟩
    change f^[cycleLength f x] x = x
    rw [← hmin]
    exact Function.isPeriodicPt_minimalPeriod f x
  · intro i hi
    apply decide_eq_false
    rintro ⟨hip, he⟩
    have hm := Function.IsPeriodicPt.minimalPeriod_le hip he
    rw [hmin] at hm
    exact absurd hi (not_lt.mpr hm)

include hx hK in
private theorem shortTime_eq : shortTime (w := w) f K x = BitVec.ofNat w (canonicalTime f x) := by
  unfold shortTime
  rw [shortRepresentative_eq f K hx hK]
  exact firstIndex_spec _ ⟨canonicalTime f x, (canonicalTime_lt_cycleLength f x hx).trans_le
    (by omega)⟩ (decide_eq_true (canonicalTime_spec f x))
    fun i hi => decide_eq_false (canonicalTime_min f x hi)

include hx hK in
/-- **Short cycles.** On a periodic state whose cycle has length at most `K`, the label read
from the first `K + 1` states of its orbit is its canonical label. -/
theorem shortLabel_eq_canonicalLabel : shortLabel f K x = canonicalLabel f x := by
  simp only [shortLabel, canonicalLabel, shortRepresentative_eq f K hx hK, shortLength_eq f K hx hK,
    shortTime_eq f K hx hK]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hl := cycleLength_le_two_pow f x
  have hpos := cycleLength_pos f x
  rw [toNat_subMod _ _ _ (by rwa [toNat_ofNat_cycleLength])
      (by rw [toNat_ofNat_cycleLength, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega),
    toNat_ofNat_cycleLength, toNat_ofNat_phase, BitVec.toNat_ofNat,
    show (0 : BitVec (n + 3)).toNat = 0 from rfl, Nat.zero_add,
    Nat.mod_eq_of_lt ((canonicalTime_lt_cycleLength f x hx).trans_le hl |>.trans
      (by simp only [Nat.pow_succ]; omega))]
  rfl

end Short

/-- **Short-cycle labels.** Once the first `K + 1` states of an orbit are available, its short
label costs one minimum scan, two first-position scans, their equality tests and one modular
difference. -/
theorem synthesis_shortLabel (s : Set (BooleanFunction a)) (f : BitString n → BitString n)
    (init : BitString a → BitString n) (K : ℕ)
    (hp : ∀ j : Fin (K + 1), ∀ bit, (fun x => f^[j.val] (init x) bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) :
    Synthesis interpretation s (wires fun x => shortLabel f K (init x))
      ((K + 1) * (30 * n + 27) + 50 * (n + 4) ^ 2) := by
  let rep := fun x => shortRepresentative f K (init x)
  have hm : Synthesis interpretation s (wires rep) ((K + 1) * (10 * n + 1)) :=
    synthesis_scanMin s (fun x j => f^[j.val] (init x)) init (fun j bit => hp j bit) (hp 0)
  let src := s ∪ wires rep
  have hprefix (j : Fin (K + 1)) : wires (fun x => f^[j.val] (init x)) ⊆ src := by
    rintro _ ⟨bit, rfl⟩
    exact Or.inl (hp j bit)
  let back := fun x (j : Fin (K + 1)) => decide (0 < j.val ∧ f^[j.val] (init x) = init x)
  have hback := Synthesis.family (I := interpretation) (s := src) (fun j x => back x j)
    (fun _ => 6 * n + 1) fun j => by
      by_cases hj : 0 < j.val
      · simpa only [back, hj, true_and] using synthesis_bits_eq src (fun x => f^[j.val] (init x))
          init (hprefix j) (hprefix 0)
      · simpa only [back, hj, false_and, decide_false] using
          (Synthesis.of_mem (s := src) (I := interpretation) (Or.inl (hc false))).mono
            Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _)
  have hl := synthesis_firstIndex (w := n + 3) (src ∪ Set.range fun j x => back x j) back
    (fun j => Or.inr ⟨j, rfl⟩) fun b => Or.inl (Or.inl (hc b))
  let hit := fun x (j : Fin (K + 1)) => decide (f^[j.val] (init x) = rep x)
  have hhit := Synthesis.family (I := interpretation) (s := src) (fun j x => hit x j)
    (fun _ => 6 * n + 1) fun j =>
      synthesis_bits_eq src (fun x => f^[j.val] (init x)) rep (hprefix j) fun _ h => Or.inr h
  have ht := synthesis_firstIndex (w := n + 3) (src ∪ Set.range fun j x => hit x j) hit
    (fun j => Or.inr ⟨j, rfl⟩) fun b => Or.inl (Or.inl (hc b))
  let ell := fun x => shortLength (w := n + 3) f K (init x)
  let time := fun x => shortTime (w := n + 3) f K (init x)
  have hscans := hm.comp ((hback.trans hl).union (hhit.trans ht))
  let src2 := s ∪ (wires rep ∪ (wordWires ell ∪ wordWires time))
  have hphase := synthesis_subMod src2 (fun _ => (0 : BitVec (n + 3))) time ell
    (fun i => by
      rw [show (fun _ : BitString a => (0 : BitVec (n + 3)).getLsbD i.val) = fun _ => false from
        funext fun _ => BitVec.getLsbD_zero]
      exact Or.inl (hc false))
    (fun i => Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
    (fun i => Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))) (Or.inl (hc false))
  have hout := Synthesis.of_subset (I := interpretation)
    (labelBits_wires_subset (src2 ∪ wordWires fun x => subMod 0 (time x) (ell x)) rep ell
      (fun x => subMod 0 (time x) (ell x)) (fun _ h => Or.inl (Or.inr (Or.inl h)))
      (fun _ h => Or.inl (Or.inr (Or.inr (Or.inl h)))) fun _ h => Or.inr h)
  refine (hscans.trans (hphase.trans hout)).mono Set.Subset.rfl Set.Subset.rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.le_of_eq (by ring)

end Cslib.Circuits.Boolean.Iteration
