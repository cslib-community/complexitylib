/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.NavigationCircuits
public import Complexity.Computability.Circuit.Boolean.Iteration.Permutation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Circuits returning complete visit schedules

For any finite map `f : BitString n → BitString n` and state pair `(x, y)`, the set of times `t` at
which `f^[t] x = y` is either empty or an arithmetic progression `d + k * p` where `d < 2 ^ n` is
the first hitting time and `p = Function.minimalPeriod f y` is the minimal return period of `y`
(with `p = 0` when `y` is transient, encoding the singleton `{d}`).

Combining `navigation_circuit` (which computes the reachability bit and the `(n + 1)`-bit first
hitting time `d`) with `minimal_period_circuit` (which computes the `(n + 1)`-bit minimal period `p`
of `y` from `cycle_label_circuit` and `periodicPts_circuit`) yields a circuit of size
`O(powerBudget n c.size (2 ^ n) L)` returning the complete visit schedule record
(`visit_schedule_circuit`), and `O(optimizedBudget n c.size (2 ^ n))` at the balanced checkpoint
spacing (`visit_schedule_optimized`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.visitScheduleWidth`: bit width `(1 + (n + 1)) + (n + 1)` of a
  visit-schedule record.
* `Cslib.Circuits.Boolean.Iteration.visitScheduleFirst`: unpacks the `(n + 1)`-bit first visit time.
* `Cslib.Circuits.Boolean.Iteration.visitSchedulePeriod`: unpacks the `(n + 1)`-bit return period.
* `Cslib.Circuits.Boolean.Iteration.visitScheduleContains`: membership of a time `t` in the schedule
  encoded by a record.
* `Cslib.Circuits.Boolean.Iteration.visitScheduleCount`: number of visits up to a deadline `T`
  encoded by a record.

## Main results

* `Cslib.Circuits.Boolean.Iteration.minimal_period_circuit`: computes `Function.minimalPeriod f x`
  in `n + 1` bits within `110000 * powerBudget n c.size (2 ^ n) L` gates.
* `Cslib.Circuits.Boolean.Iteration.visitScheduleCount_spec`: `visitScheduleCount v T` equals the
  cardinality of `{t ≤ T | visitScheduleContains v t}`.
* `Cslib.Circuits.Boolean.Iteration.visit_schedule_circuit`: computes the complete visit-schedule
  record within `5000000 * powerBudget n c.size (2 ^ n) L` gates.
* `Cslib.Circuits.Boolean.Iteration.visit_schedule_optimized`: square-root-size circuit returning
  complete visit schedules and bounded visit counts.

## References

* Adapted from lean/Proofs/VisitScheduleCircuits.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ}

/-- **Minimal return period**, with zero denoting a transient state. -/
theorem minimal_period_circuit (c : Circuit signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n (n + 1),
      (∀ x, (word (out.eval interpretation x)).toNat =
        Function.minimalPeriod (c.eval interpretation) x) ∧
      out.size ≤ 110000 * powerBudget n c.size (2 ^ n) L := by
  let f := c.eval interpretation
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  obtain ⟨cyclic, hc, hcs⟩ := periodicPts_circuit c L hL hLN
  let src : Set (BooleanFunction n) := inputs n ∪ {fun _ => false}
  have hlabels := Synthesis.circuit (I := interpretation) (s := src) labels (fun i x => x i)
    (fun bit => Or.inl ⟨bit, rfl⟩)
  have hcyclic := Synthesis.circuit (I := interpretation) (s := src) cyclic (fun i x => x i)
    (fun bit => Or.inl ⟨bit, rfl⟩)
  let s1 := src ∪ (wires (labels.eval interpretation) ∪
    wires (cyclic.eval interpretation))
  let ell : BitString n → BitVec (n + 3) := fun x => labelLength (labels.eval interpretation x)
  have he : wordWires ell ⊆ s1 := by
    rintro _ ⟨bit, rfl⟩
    simp only [ell, labelLength, getLsbD_word]
    exact Or.inr (Or.inl ⟨_, rfl⟩)
  have hw := wordWires_setWidth_subset (v := n + 1) (s := s1) he (Or.inl (Or.inr rfl))
  have hmux := Synthesis.word_mux (s := s1) (fun x => (ell x).setWidth (n + 1))
    (fun _ => (0 : BitVec (n + 1))) (fun x => cyclic.eval interpretation x 0)
    (Or.inr (Or.inr ⟨0, rfl⟩)) (fun i => hw ⟨i, rfl⟩)
    (fun i => by simpa using (show (fun _ : BitString n => false) ∈ s1 from Or.inl (Or.inr rfl)))
  obtain ⟨out, ho, hs⟩ := ((Synthesis.const (s := inputs n) false).trans
    ((hlabels.union hcyclic).trans hmux)).exists_circuit_outputs
  refine ⟨out, fun x => ?_, hs.trans ?_⟩
  · rw [ho x, word_getLsbD]
    by_cases hy : x ∈ Function.periodicPts f
    · have htrue := (hc x).mpr hy
      simp only [htrue, ite_true]
      have hperiod := cycleLength_eq_minimalPeriod_of_mem_periodicPts f hy
      have hbound : cycleLength f x < 2 ^ (n + 1) := by
        have hle := cycleLength_le_two_pow f x
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
        omega
      have hbound3 : cycleLength f x < 2 ^ (n + 3) := by
        have hle := cycleLength_le_two_pow f x
        have hpow : 2 ^ (n + 3) = 8 * 2 ^ n := by rw [pow_add]; ring
        omega
      dsimp only [ell]
      simp only [hl x, canonicalLabel, labelLength_labelBits, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat]
      change cycleLength f x % 2 ^ (n + 3) % 2 ^ (n + 1) = Function.minimalPeriod f x
      rw [Nat.mod_eq_of_lt hbound3, Nat.mod_eq_of_lt hbound, hperiod]
    · have hfalse : cyclic.eval interpretation x 0 = false :=
        Bool.eq_false_iff.mpr (fun h => hy ((hc x).mp h))
      simp only [hfalse, Bool.false_eq_true, ite_false]
      exact (Function.minimalPeriod_eq_zero_of_notMem_periodicPts hy).symm
  · have hb : n + 1 ≤ powerBudget n c.size (2 ^ n) L := by
      have hh := Nat.mul_le_mul_left ((n + 1) ^ 3)
        (show 1 ≤ L + 2 ^ n / L + 1 by lia)
      unfold powerBudget
      nlinarith [Nat.zero_le (n ^ 2)]
    lia

/-- One reachability bit, an `(n + 1)`-bit first visit time, and an `(n + 1)`-bit return period. -/
abbrev visitScheduleWidth (n : ℕ) := (1 + (n + 1)) + (n + 1)

/-- The `(n + 1)`-bit first hitting time field of a visit-schedule record. -/
def visitScheduleFirst (v : BitString (visitScheduleWidth n)) : BitVec (n + 1) :=
  word fun i => v (Fin.castAdd (n + 1) (Fin.natAdd 1 i))

/-- The `(n + 1)`-bit return period field of a visit-schedule record. -/
def visitSchedulePeriod (v : BitString (visitScheduleWidth n)) : BitVec (n + 1) :=
  word fun i => v (Fin.natAdd (1 + (n + 1)) i)

/-- Whether time `t` belongs to the arithmetic progression encoded by `v`. -/
def visitScheduleContains (v : BitString (visitScheduleWidth n)) (t : ℕ) : Prop :=
  v (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) = true ∧
    ∃ k, t = (visitScheduleFirst v).toNat + k * (visitSchedulePeriod v).toNat

/-- An arithmetic interpretation of a schedule; no additional-input gate bound is asserted. -/
def visitScheduleCount (v : BitString (visitScheduleWidth n)) (T : ℕ) : ℕ :=
  if v (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) then
    arithmeticProgressionCount (visitScheduleFirst v).toNat (visitSchedulePeriod v).toNat T
  else 0

/-- `visitScheduleCount v T` counts the times `t ≤ T` satisfying `visitScheduleContains v t`. -/
theorem visitScheduleCount_spec (v : BitString (visitScheduleWidth n)) (T : ℕ) :
    Set.ncard {t : ℕ | t ≤ T ∧ visitScheduleContains v t} = visitScheduleCount v T := by
  unfold visitScheduleCount visitScheduleContains
  split_ifs with hflag
  · simp only [hflag, true_and]
    exact arithmeticProgressionCount_spec _ _ _
  · have he : {t : ℕ | t ≤ T ∧
          v (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) = true ∧
          ∃ k, t = (visitScheduleFirst v).toNat + k * (visitSchedulePeriod v).toNat} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, hflag, Bool.false_eq_true, false_and, and_false,
        Set.mem_empty_iff_false]
    rw [he, Set.ncard_empty]

/-- **Visit-schedule circuit at spacing `L`.** The returned record describes every visit time, with
period zero encoding a singleton visit to a transient target. -/
theorem visit_schedule_circuit (c : Circuit signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + n) (visitScheduleWidth n),
      (∀ z t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z ↔
        visitScheduleContains (out.eval interpretation z) t) ∧
      out.size ≤ 5000000 * powerBudget n c.size (2 ^ n) L := by
  let f := c.eval interpretation
  obtain ⟨nav, hn, hns⟩ := navigation_circuit c L hL hLN
  obtain ⟨period, hp, hps⟩ := minimal_period_circuit c L hL hLN
  have hnav := Synthesis.circuit (I := interpretation) (s := inputs (n + n)) nav (fun i z => z i)
    (fun bit => ⟨bit, rfl⟩)
  have hperiod := Synthesis.circuit (I := interpretation) (s := inputs (n + n))
    period (fun i z => inputRight z i) (fun bit => ⟨Fin.natAdd n bit, rfl⟩)
  let output := fun z => Fin.append (nav.eval interpretation z)
    (period.eval interpretation (inputRight z))
  have hs := (hnav.union hperiod).mono Set.Subset.rfl
    (show wires output ⊆ wires (nav.eval interpretation) ∪
      wires (fun z => period.eval interpretation (inputRight z)) from by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp only [output, Fin.append_left]⟩
      | right i => exact Or.inr ⟨i, by simp only [output, Fin.append_right]⟩) le_rfl
  obtain ⟨out, ho, hsize⟩ := hs.exists_circuit_outputs
  refine ⟨out, fun z t => ?_, hsize.trans ?_⟩
  · rw [ho z]
    simp only [visitScheduleContains, visitScheduleFirst, visitSchedulePeriod, output,
      Fin.append_left, Fin.append_right, hp, hn z]
    have hflag := navigationBits_flag f (inputLeft z) (inputRight z)
    constructor
    · intro ht
      have hr : ∃ t, f^[t] (inputLeft z) = inputRight z := ⟨t, ht⟩
      have hd := navigationBits_time f (inputLeft z) (inputRight z) hr
      exact ⟨hflag.mpr hr, (visit_schedule_of_first f _ _ _ hd.1 hd.2.1 t).mp ht⟩
    · rintro ⟨hr, ht⟩
      have hd := navigationBits_time f (inputLeft z) (inputRight z) (hflag.mp hr)
      exact (visit_schedule_of_first f _ _ _ hd.1 hd.2.1 t).mpr ht
  · have hnB := hns.trans (navigationBudget_le n c.size L)
    lia

/-- **Square-root visit-schedule circuit.** Optimizing `L` gives a circuit of size at most
`15000000 * optimizedBudget n c.size (2 ^ n)` whose output record characterizes all visit times and
determines the exact visit count up to any deadline `T`. -/
theorem visit_schedule_optimized (c : Circuit signature n n) :
    ∃ out : Circuit signature (n + n) (visitScheduleWidth n),
      (∀ z t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z ↔
        visitScheduleContains (out.eval interpretation z) t) ∧
      (∀ z T, Set.ncard {t : ℕ | t ≤ T ∧
        (c.eval interpretation)^[t] (inputLeft z) = inputRight z} =
          visitScheduleCount (out.eval interpretation z) T) ∧
      (out.size : ℝ) ≤ 15000000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := visit_schedule_circuit c L hL hLN
  refine ⟨out, ho, fun z T => ?_, ?_⟩
  · rw [← visitScheduleCount_spec]
    congr 1
    ext t
    exact and_congr_right (fun _ => ho z t)
  · have hs' : (out.size : ℝ) ≤
      5000000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by exact_mod_cast hs
    linarith

end Cslib.Circuits.Boolean.Iteration
