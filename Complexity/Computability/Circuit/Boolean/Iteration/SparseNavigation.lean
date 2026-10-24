/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.SparseTime
public import Complexity.Computability.Circuit.Boolean.Iteration.VisitScheduleCircuits

import Mathlib.Tactic.Linarith

/-!
# Sparse-counter reachability, first hitting times, and visit schedules

Two cycle labels suffice for every pair query `(x, y)` on a permutation. Because both phases are
already reduced modulo the cycle length, modular subtraction costs only linearly many gates
(`subtractResidues`), so full visit-schedule records and first hitting times for sparsely edited
counter permutations have circuits of size `O((n + 1) * (r + 1))`.

## Main definitions

* `cycleLabelDistance`, `cycleLabelVisits`: phase distance and visit schedule from two cycle labels.

## Main results

* `cycleLabelVisits_spec`, `synthesis_cycleLabelVisits`: correctness and linear gate bound for
  combining two cycle labels into a visit schedule.
* `cycle_label_visit_circuit`: visit-schedule circuit from any cycle-label circuit.
* `sparse_counter_visit_circuit`, `sparse_counter_visit_schedule`, `sparse_counter_hitting_time`:
  `O((n + 1) * (r + 1))` circuits for visit-schedule records and first hitting times.
* `sparse_coordinate_visit_schedule`: coordinate transfer charging only two forward encodings.

## References

* Adapted from lean/Proofs/SparseNavigation.lean at revision `c4cfa198`
  of [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

attribute [local instance] counterChartWordOrder

open Cslib.FunctionalGraph

variable {n a : ℕ}

/-- Phase difference from label `x` to label `y` modulo the cycle length of `x`. -/
def cycleLabelDistance (x y : BitString (n + (chartWidth n + chartWidth n))) :
    BitVec (chartWidth n) :=
  subtractResidues (labelPhase y) (labelPhase x) (labelLength x)

/-- A flag, first time, and return period in the visit-schedule format. -/
def cycleLabelVisits (x y : BitString (n + (chartWidth n + chartWidth n))) :
    BitString (visitScheduleWidth n) :=
  Fin.append (Fin.append
    (fun _ : Fin 1 => decide (labelRepresentative x = labelRepresentative y))
    (fun i => ((cycleLabelDistance x y).setWidth (n + 1)).getLsbD i.val))
    (fun i => ((labelLength y).setWidth (n + 1)).getLsbD i.val)

private theorem cycleLabelVisits_flag (f : BitVec n → BitVec n) (hf : Function.Injective f)
    (x y : BitVec n) :
    cycleLabelVisits (wordCycleLabel f x) (wordCycleLabel f y)
      (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) = true ↔ ∃ t, f^[t] x = y := by
  have hrep :
      ((fun i : Fin n => (canonicalCycle f x).getLsbD i.val) =
        fun i : Fin n => (canonicalCycle f y).getLsbD i.val) ↔
        canonicalCycle f x = canonicalCycle f y :=
    ⟨fun h => by rw [← word_getLsbD (canonicalCycle f x), ← word_getLsbD (canonicalCycle f y), h],
      fun h => by rw [h]⟩
  simp only [cycleLabelVisits, wordCycleLabel, Fin.append_left, labelRepresentative_labelBits, hrep]
  change decide (canonicalCycle f x = canonicalCycle f y) = true ↔ _
  rw [decide_eq_true_eq]
  exact (exists_iterate_eq_iff_canonicalCycle_eq f x y (hf.mem_periodicPts y)).symm

private theorem cycleLabelDistance_toNat (f : BitVec n → BitVec n) (hf : Function.Injective f)
    (x y : BitVec n) (hc : canonicalCycle f x = canonicalCycle f y) :
    (cycleLabelDistance (wordCycleLabel f x) (wordCycleLabel f y)).toNat =
      cyclicDistance f x y := by
  obtain ⟨t, ht⟩ := (exists_iterate_eq_iff_canonicalCycle_eq f x y (hf.mem_periodicPts y)).mpr hc
  have hl : cycleLength f y = cycleLength f x := by rw [← ht, cycleLength_iterate]
  have hp (z : BitVec n) : (BitVec.ofNat (chartWidth n) (phase f z)).toNat = phase f z :=
    chart_ofNat_toNat ((phase_lt f z).le.trans (cycleLength_le_words f z))
  have he : (BitVec.ofNat (chartWidth n) (cycleLength f x)).toNat = cycleLength f x :=
    chart_ofNat_toNat (cycleLength_le_words f x)
  have hdepth : transientDepth f x = 0 :=
    transientDepth_eq_zero_of_mem_periodicPts f (hf.mem_periodicPts x)
  simp only [cycleLabelDistance, wordCycleLabel, labelPhase_labelBits, labelLength_labelBits]
  rw [toNat_subtractResidues _ _ _ (by rw [hp, he, ← hl]; exact phase_lt f y)
    (by rw [hp, he]; exact phase_lt f x), hp, hp, he]
  simp only [cyclicDistance, hdepth, Nat.add_zero]

private theorem cycleLabelVisits_first (f : BitVec n → BitVec n) (hf : Function.Injective f)
    (x y : BitVec n) (hr : ∃ t, f^[t] x = y) :
    let d := (visitScheduleFirst (cycleLabelVisits (wordCycleLabel f x) (wordCycleLabel f y))).toNat
    f^[d] x = y ∧ (∀ j < d, f^[j] x ≠ y) ∧ d < 2 ^ n := by
  have hc := (exists_iterate_eq_iff_canonicalCycle_eq f x y (hf.mem_periodicPts y)).mp hr
  have hdepth : transientDepth f x = 0 :=
    transientDepth_eq_zero_of_mem_periodicPts f (hf.mem_periodicPts x)
  have hd : cyclicDistance f x y < 2 ^ n :=
    (Nat.mod_lt _ (cycleLength_pos f x)).trans_le (cycleLength_le_words f x)
  have hwide : cyclicDistance f x y < 2 ^ (n + 1) :=
    hd.trans_le (Nat.pow_le_pow_right (by decide) (by lia))
  have hfirst := cyclic_first_hit f x y (hf.mem_periodicPts y) hc
  dsimp only
  simp only [visitScheduleFirst, cycleLabelVisits, Fin.append_left, Fin.append_right,
    word_getLsbD, BitVec.toNat_setWidth, cycleLabelDistance_toNat f hf x y hc,
    Nat.mod_eq_of_lt hwide]
  exact ⟨by simpa only [hdepth, Nat.zero_add] using hfirst.1,
    by simpa only [hdepth, Nat.zero_add] using hfirst.2, hd⟩

private theorem cycleLabelVisits_period (f : BitVec n → BitVec n) (hf : Function.Injective f)
    (x y : BitVec n) :
    (visitSchedulePeriod (cycleLabelVisits (wordCycleLabel f x) (wordCycleLabel f y))).toNat =
      Function.minimalPeriod f y := by
  have hwide : cycleLength f y < 2 ^ (n + 1) :=
    (cycleLength_le_words f y).trans_lt (Nat.pow_lt_pow_right (by decide) (by lia))
  simp only [visitSchedulePeriod, cycleLabelVisits, Fin.append_right, word_getLsbD,
    wordCycleLabel, labelLength_labelBits, BitVec.toNat_setWidth]
  rw [chart_ofNat_toNat (cycleLength_le_words f y), Nat.mod_eq_of_lt hwide,
    cycleLength_eq_minimalPeriod_of_mem_periodicPts f (hf.mem_periodicPts y)]

theorem cycleLabelVisits_spec (f : BitVec n → BitVec n) (hf : Function.Injective f)
    (x y : BitVec n) (t : ℕ) :
    f^[t] x = y ↔ visitScheduleContains
      (cycleLabelVisits (wordCycleLabel f x) (wordCycleLabel f y)) t := by
  unfold visitScheduleContains
  rw [cycleLabelVisits_flag f hf, cycleLabelVisits_period f hf]
  constructor
  · intro ht
    have hr : ∃ t, f^[t] x = y := ⟨t, ht⟩
    have hd := cycleLabelVisits_first f hf x y hr
    exact ⟨hr, (visit_schedule_of_first f x y _ hd.1 hd.2.1 t).mp ht⟩
  · rintro ⟨hr, ht⟩
    have hd := cycleLabelVisits_first f hf x y hr
    exact (visit_schedule_of_first f x y _ hd.1 hd.2.1 t).mpr ht

/-- Querying two already computed labels uses only linear arithmetic and wiring. -/
theorem synthesis_cycleLabelVisits (s : Set (BitString a → Bool))
    (x y : BitString a → BitString (n + (chartWidth n + chartWidth n)))
    (hx : wires x ⊆ s) (hy : wires y ⊆ s) :
    Synthesis Boolean.interpretation s (wires fun z => cycleLabelVisits (x z) (y z))
      (200 * (n + 3)) := by
  have fields (v : BitString a → BitString (n + (chartWidth n + chartWidth n))) (hv : wires v ⊆ s) :
      wires (fun z => labelRepresentative (v z)) ⊆ s ∧
      wordWires (fun z => labelLength (v z)) ⊆ s ∧
      wordWires (fun z => labelPhase (v z)) ⊆ s := by
    refine ⟨?_, ?_, ?_⟩ <;> rintro _ ⟨i, rfl⟩
    · exact hv ⟨_, rfl⟩
    · simpa only [labelLength, getLsbD_word] using hv ⟨_, rfl⟩
    · simpa only [labelPhase, getLsbD_word] using hv ⟨_, rfl⟩
  obtain ⟨hcx, hlx, hpx⟩ := fields x hx
  obtain ⟨hcy, hly, hpy⟩ := fields y hy
  let s0 := s ∪ {fun _ : BitString a => false}
  have hdist := synthesis_subtractResidues s0 (fun z => labelPhase (y z))
    (fun z => labelPhase (x z)) (fun z => labelLength (x z))
    (fun _ h => Or.inl (hpy h)) (fun _ h => Or.inl (hpx h)) (fun _ h => Or.inl (hlx h))
  have hflag := synthesis_bits_eq s0 (fun z => labelRepresentative (x z))
    (fun z => labelRepresentative (y z))
    (fun _ h => Or.inl (hcx h)) (fun _ h => Or.inl (hcy h))
  let src := s0 ∪ (wordWires (fun z => cycleLabelDistance (x z) (y z)) ∪
    {fun z => decide (labelRepresentative (x z) = labelRepresentative (y z))})
  have hz : (fun _ : BitString a => false) ∈ src := Or.inl (Or.inr rfl)
  have hd := wordWires_setWidth_subset (v := n + 1) (s := src)
    (value := fun z => cycleLabelDistance (x z) (y z)) (fun _ h => Or.inr (Or.inl h)) hz
  have he := wordWires_setWidth_subset (v := n + 1) (s := src)
    (value := fun z => labelLength (y z)) (fun _ h => Or.inl (Or.inl (hly h))) hz
  have hout : wires (fun z => cycleLabelVisits (x z) (y z)) ⊆ src := by
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        simpa only [cycleLabelVisits, Fin.append_left] using
          (show (fun z => decide (labelRepresentative (x z) =
            labelRepresentative (y z))) ∈ src from Or.inr (Or.inr rfl))
      | right i =>
        simpa only [cycleLabelVisits, Fin.append_left, Fin.append_right] using hd ⟨i, rfl⟩
    | right i =>
      simpa only [cycleLabelVisits, Fin.append_right] using he ⟨i, rfl⟩
  exact ((Synthesis.const (s := s) false).trans
    ((hdist.union hflag).trans (Synthesis.of_subset hout))).mono
      Set.Subset.rfl Set.Subset.rfl (by dsimp [chartWidth]; lia)

/-- Any cheap cycle-label circuit for a permutation gives cheap navigation. -/
theorem cycle_label_visit_circuit (f : BitVec n → BitVec n)
    (labels : Circuit Boolean.signature n (n + (chartWidth n + chartWidth n)))
    (hl : labels.Computes Boolean.interpretation (fun x => wordCycleLabel f (word x))) :
    ∃ out : Circuit Boolean.signature (n + n) (visitScheduleWidth n),
      out.Computes Boolean.interpretation (fun z =>
        cycleLabelVisits (wordCycleLabel f (word (inputLeft z)))
          (wordCycleLabel f (word (inputRight z)))) ∧
      out.size ≤ 2 * labels.size + 200 * (n + 3) := by
  let x := fun z : BitString (n + n) => wordCycleLabel f (word (inputLeft z))
  let y := fun z : BitString (n + n) => wordCycleLabel f (word (inputRight z))
  have hle : labels.eval Boolean.interpretation = fun x => wordCycleLabel f (word x) :=
    funext hl
  have hx : Synthesis Boolean.interpretation (inputs (n + n)) (wires x) labels.size := by
    simpa only [hle, wires] using Synthesis.circuit (I := Boolean.interpretation)
      (s := inputs (n + n)) labels (fun i z => inputLeft z i) (fun _ => ⟨_, rfl⟩)
  have hy : Synthesis Boolean.interpretation (inputs (n + n)) (wires y) labels.size := by
    simpa only [hle, wires] using Synthesis.circuit (I := Boolean.interpretation)
      (s := inputs (n + n)) labels (fun i z => inputRight z i) (fun _ => ⟨_, rfl⟩)
  have hnav := synthesis_cycleLabelVisits (inputs (n + n) ∪ (wires x ∪ wires y)) x y
    (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inr h))
  obtain ⟨out, ho, hs⟩ := ((hx.union hy).trans hnav).exists_circuit_outputs
  exact ⟨out, ho, by lia⟩

theorem sparse_counter_visit_circuit (f : Equiv.Perm (BitVec n)) :
    ∃ out : Circuit Boolean.signature (n + n) (visitScheduleWidth n),
      out.Computes Boolean.interpretation (fun z =>
        cycleLabelVisits (wordCycleLabel f (word (inputLeft z)))
          (wordCycleLabel f (word (inputRight z)))) ∧
      out.size ≤ 1200 * (n + 3) * ((disagreement f (fun x => x + 1)).card + 1) := by
  obtain ⟨labels, hl, hls⟩ := sparse_counter_labels f
  obtain ⟨out, ho, hs⟩ := cycle_label_visit_circuit f labels hl
  refine ⟨out, ho, ?_⟩
  nlinarith only [hls, hs, Nat.zero_le ((n + 3) * (disagreement f (fun x => x + 1)).card)]

/-- The sparse bound covers the complete visit set and its bounded-count interpretation. -/
theorem sparse_counter_visit_schedule (f : Equiv.Perm (BitVec n)) :
    ∃ out : Circuit Boolean.signature (n + n) (visitScheduleWidth n),
      (∀ z t, (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z) ↔
        visitScheduleContains (out.eval Boolean.interpretation z) t) ∧
      (∀ z T, Set.ncard {t : ℕ | t ≤ T ∧
        (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z)} =
          visitScheduleCount (out.eval Boolean.interpretation z) T) ∧
      out.size ≤ 1200 * (n + 3) * ((disagreement f (fun x => x + 1)).card + 1) := by
  obtain ⟨out, ho, hs⟩ := sparse_counter_visit_circuit f
  have hspec (z : BitString (n + n)) (t : ℕ) :
      (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z) ↔
        visitScheduleContains (out.eval Boolean.interpretation z) t := by
    rw [ho z]
    exact cycleLabelVisits_spec f f.injective _ _ t
  refine ⟨out, hspec, fun z T => ?_, hs⟩
  rw [← visitScheduleCount_spec]
  congr 1
  ext t
  exact and_congr_right (fun _ => hspec z t)

/-- The existence flag and first hitting time have the same sparse circuit bound. -/
theorem sparse_counter_hitting_time (f : Equiv.Perm (BitVec n)) :
    ∃ out : Circuit Boolean.signature (n + n) (1 + (n + 1)),
      (∀ z, out.eval Boolean.interpretation z 0 = true ↔
        ∃ t, (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z)) ∧
      (∀ z, out.eval Boolean.interpretation z 0 = true →
        let t := (word fun i : Fin (n + 1) =>
          out.eval Boolean.interpretation z (Fin.natAdd 1 i)).toNat
        (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z) ∧
          (∀ j < t, (f : BitVec n → BitVec n)^[j]
            (word (inputLeft z)) ≠ word (inputRight z)) ∧ t < 2 ^ n) ∧
      out.size ≤ 1200 * (n + 3) * ((disagreement f (fun x => x + 1)).card + 1) := by
  obtain ⟨full, hf, hs⟩ := sparse_counter_visit_circuit f
  let output := fun z : BitString (n + n) => fun i : Fin (1 + (n + 1)) =>
    full.eval Boolean.interpretation z (Fin.castAdd (n + 1) i)
  have hfull := Synthesis.circuit (I := Boolean.interpretation)
    (s := inputs (n + n)) full (fun i z => z i) (fun i => ⟨i, rfl⟩)
  have hout : wires output ⊆ wires (full.eval Boolean.interpretation) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd (n + 1) i, rfl⟩
  obtain ⟨out, ho, hsize⟩ := (hfull.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  have hnav (z : BitString (n + n)) : out.eval Boolean.interpretation z =
      fun i => cycleLabelVisits (wordCycleLabel f (word (inputLeft z)))
        (wordCycleLabel f (word (inputRight z))) (Fin.castAdd (n + 1) i) := by
    rw [ho z]
    dsimp only [output]
    rw [hf z]
  refine ⟨out, fun z => ?_, fun z hz => ?_, hsize.trans hs⟩
  · rw [hnav z]
    exact cycleLabelVisits_flag f f.injective _ _
  · rw [hnav z] at hz ⊢
    exact cycleLabelVisits_first f f.injective _ _
      ((cycleLabelVisits_flag f f.injective _ _).mp hz)

/-- Pair queries need the forward coordinate map twice, but no inverse circuit. -/
theorem sparse_coordinate_visit_schedule (f g e : Equiv.Perm (BitVec n))
    (hcycle : ∀ x, e (g x) = e x + 1)
    (encode : Circuit Boolean.signature n n)
    (he : encode.Computes Boolean.interpretation (fun x i => (e (word x)).getLsbD i.val)) :
    ∃ out : Circuit Boolean.signature (n + n) (visitScheduleWidth n),
      (∀ z t, (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z) ↔
        visitScheduleContains (out.eval Boolean.interpretation z) t) ∧
      (∀ z T, Set.ncard {t : ℕ | t ≤ T ∧
        (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z)} =
          visitScheduleCount (out.eval Boolean.interpretation z) T) ∧
      out.size ≤ 2 * encode.size + 1200 * (n + 3) * ((disagreement f g).card + 1) := by
  have hcounter : e ∘ g ∘ e.symm = fun x => x + 1 := by
    funext x
    simp only [Function.comp_apply, hcycle, Equiv.apply_symm_apply]
  have hr := disagreement_conjugate_card (f : BitVec n → BitVec n)
    (g : BitVec n → BitVec n) e
  rw [hcounter] at hr
  let conjugate := e.permCongrHom f
  obtain ⟨middle, hm, _, hs⟩ := sparse_counter_visit_schedule conjugate
  change middle.size ≤ 1200 * (n + 3) *
    ((disagreement (e ∘ f ∘ e.symm) (fun x => x + 1)).card + 1) at hs
  rw [hr] at hs
  let x := fun z : BitString (n + n) => encode.eval Boolean.interpretation (inputLeft z)
  let y := fun z : BitString (n + n) => encode.eval Boolean.interpretation (inputRight z)
  have hx := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + n))
    encode (fun i z => inputLeft z i) (fun _ => ⟨_, rfl⟩)
  have hy := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + n))
    encode (fun i z => inputRight z i) (fun _ => ⟨_, rfl⟩)
  let src := inputs (n + n) ∪ (wires x ∪ wires y)
  let args := fun z => Fin.append (x z) (y z)
  have hargs (i : Fin (n + n)) : (fun z => args z i) ∈ src := by
    induction i using Fin.addCases with
    | left i => exact Or.inr (Or.inl ⟨i, by simp only [args, Fin.append_left]⟩)
    | right i => exact Or.inr (Or.inr ⟨i, by simp only [args, Fin.append_right]⟩)
  have hquery := Synthesis.circuit (I := Boolean.interpretation) (s := src)
    middle (fun i z => args z i) hargs
  obtain ⟨out, ho, hsize⟩ := ((hx.union hy).trans hquery).exists_circuit_outputs
  have hconj : Function.Semiconj (e : BitVec n → BitVec n) f conjugate := by
    intro x
    simp only [conjugate, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have hex (z : BitString (n + n)) : word (inputLeft (args z)) = e (word (inputLeft z)) := by
    change word (fun i => Fin.append (x z) (y z) (Fin.castAdd n i)) = _
    simp only [Fin.append_left, x]
    change word (encode.eval Boolean.interpretation (inputLeft z)) = _
    rw [he (inputLeft z), word_getLsbD]
  have hey (z : BitString (n + n)) : word (inputRight (args z)) = e (word (inputRight z)) := by
    change word (fun i => Fin.append (x z) (y z) (Fin.natAdd n i)) = _
    simp only [Fin.append_right, y]
    change word (encode.eval Boolean.interpretation (inputRight z)) = _
    rw [he (inputRight z), word_getLsbD]
  have hspec (z : BitString (n + n)) (t : ℕ) :
      (f : BitVec n → BitVec n)^[t] (word (inputLeft z)) = word (inputRight z) ↔
        visitScheduleContains (out.eval Boolean.interpretation z) t := by
    rw [ho z]
    change _ ↔ visitScheduleContains (middle.eval Boolean.interpretation (args z)) t
    rw [← hm (args z) t, hex z, hey z]
    rw [← hconj.iterate_right t]
    exact e.injective.eq_iff.symm
  refine ⟨out, hspec, fun z T => ?_, by lia⟩
  rw [← visitScheduleCount_spec]
  congr 1
  ext t
  exact and_congr_right (fun _ => hspec z t)

end Cslib.Circuits.Boolean.Iteration
