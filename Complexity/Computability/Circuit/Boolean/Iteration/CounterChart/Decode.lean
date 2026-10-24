/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.CounterChart.Encode

/-! # Decoding sparse interval coordinates, including intervals crossing phase zero 
## Main definitions

* `CounterIntervalChart.negativePhase`, `CounterIntervalChart.phaseDistance`,
  `CounterIntervalChart.decodedRow`, `CounterIntervalChart.decodeFlag`: per-interval phase
  offset, decoded candidate word, and interval match test.
* `CounterIntervalChart.decode`: recover a state from its representative and phase.

## Main results

* `CounterIntervalChart.decode_spec`: decoding canonical coordinates recovers the state.

## References

* Adapted from lean/Proofs/CounterChartDecode.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration.CounterIntervalChart

attribute [local instance] counterChartWordOrder


open Cslib.FunctionalGraph

variable {n R : ℕ} {f : BitVec n → BitVec n} (chart : CounterIntervalChart f R)

/-- Additive inverse of the initial phase modulo the cycle length. -/
noncomputable def negativePhase (j : Fin R) : BitVec (chartWidth n) :=
  BitVec.ofNat (chartWidth n) ((cycleLength f (chart.first j) - phase f (chart.first j)) %
    cycleLength f (chart.first j))

/-- The natural-number value of `chart.negativePhase j` is the additive inverse of the initial
phase of interval `j` modulo its cycle length. -/
@[simp] theorem negativePhase_toNat (j : Fin R) :
    (chart.negativePhase j).toNat =
      (cycleLength f (chart.first j) - phase f (chart.first j)) %
        cycleLength f (chart.first j) :=
  chart_ofNat_toNat ((Nat.mod_lt _ (cycleLength_pos f _)).le.trans (cycleLength_le_words f _))

/-- Distance from the interval start, modulo its cycle length. -/
noncomputable def phaseDistance (j : Fin R) (p : BitVec (chartWidth n)) : BitVec (chartWidth n) :=
  addResidue (chart.period j) p (chart.negativePhase j)

private theorem phaseDistance_toNat (j : Fin R) (p : BitVec (chartWidth n))
    (hp : p.toNat < cycleLength f (chart.first j)) :
    (chart.phaseDistance j p).toNat =
      (p.toNat + cycleLength f (chart.first j) -
        phase f (chart.first j) % cycleLength f (chart.first j)) %
        cycleLength f (chart.first j) := by
  unfold phaseDistance
  rw [toNat_addResidue]
  · rw [period_toNat, negativePhase_toNat, Nat.add_mod_mod]
    rw [Nat.mod_eq_of_lt (phase_lt f _)]
    congr 1
    have := phase_lt f (chart.first j)
    lia
  · simpa only [period_toNat] using hp
  · simpa only [negativePhase_toNat, period_toNat] using Nat.mod_lt
      (cycleLength f (chart.first j) - phase f (chart.first j)) (cycleLength_pos f _)

/-- The decoded distance is exactly the numerical offset within a containing interval. -/
private theorem phaseDistance_of_contains (hf : Function.Injective f) (j : Fin R) (y : BitVec n)
    (hy : chart.contains j y = true) :
    (chart.phaseDistance j (BitVec.ofNat (chartWidth n) (phase f y))).toNat =
      y.toNat - chart.start j := by
  obtain ⟨hlo, hhi⟩ := (chart.contains_iff j y).mp hy
  have hpath := chart.point_eq j y hlo hhi
  have hd : y.toNat - chart.start j < cycleLength f (chart.first j) :=
    (show y.toNat - chart.start j < chart.stop j - chart.start j by lia).trans_le
      (chart.length_le_period hf j)
  have hl : cycleLength f y = cycleLength f (chart.first j) := by
    rw [← hpath, cycleLength_iterate]; rfl
  have hp := chart_ofNat_toNat ((phase_lt f y).le.trans (cycleLength_le_words f y))
  rw [chart.phaseDistance_toNat j _ (by rw [hp]; simpa only [← hl] using phase_lt f y), hp]
  apply add_sub_mod_mod_eq_of_modEq (cycleLength_pos f _) hd
  have hphase := phase_iterate f (chart.first j) (y.toNat - chart.start j)
  change phase f (f^[y.toNat - chart.start j] (BitVec.ofNat n (chart.start j))) = _ at hphase
  rw [hpath] at hphase
  simp only [Nat.ModEq, hphase, Nat.add_comm, Nat.mod_mod]

/-- On a matching cycle, the decoded distance really reaches the requested state. -/
private theorem phaseDistance_hit (hf : Function.Injective f) (j : Fin R) (y : BitVec n)
    (hc : canonicalCycle f (chart.first j) = canonicalCycle f y) :
    f^[(chart.phaseDistance j (BitVec.ofNat (chartWidth n) (phase f y))).toNat]
      (chart.first j) = y := by
  have hy := hf.mem_periodicPts y
  obtain ⟨t, ht⟩ := (exists_iterate_eq_iff_canonicalCycle_eq f (chart.first j) y hy).mpr hc
  have hl : cycleLength f y = cycleLength f (chart.first j) := by
    rw [← ht, cycleLength_iterate]
  have hp := chart_ofNat_toNat ((phase_lt f y).le.trans (cycleLength_le_words f y))
  have hz : transientDepth f (chart.first j) = 0 :=
    transientDepth_eq_zero_of_mem_periodicPts f (hf.mem_periodicPts _)
  have hd : (chart.phaseDistance j (BitVec.ofNat (chartWidth n) (phase f y))).toNat =
      cyclicDistance f (chart.first j) y := by
    rw [chart.phaseDistance_toNat j _ (by rw [hp, ← hl]; exact phase_lt f y), hp]
    simp only [cyclicDistance, hz, Nat.add_zero]
  have hhit := (cyclic_first_hit f (chart.first j) y hy hc).1
  simpa only [hz, Nat.zero_add, hd] using hhit

/-- Recover the word by adding the phase distance to the interval start. -/
noncomputable def decodedRow (j : Fin R) (p : BitVec (chartWidth n)) : BitVec n :=
  BitVec.ofNat n (chart.start j) + (chart.phaseDistance j p).setWidth n

private theorem decodedRow_eq (j : Fin R) (p : BitVec (chartWidth n)) :
    chart.decodedRow j p = BitVec.ofNat n (chart.start j + (chart.phaseDistance j p).toNat) := by
  simp only [decodedRow, BitVec.ofNat_add, BitVec.ofNat_toNat]

/-- Test the representative and whether the phase distance lies in the interval. -/
noncomputable def decodeFlag (j : Fin R) (rep : BitVec n) (p : BitVec (chartWidth n)) : Bool :=
  decide (rep = canonicalCycle f (chart.first j)) && (chart.phaseDistance j p).ult (chart.length j)

private theorem decodeFlag_of_contains (hf : Function.Injective f) (j : Fin R) (y : BitVec n)
    (hy : chart.contains j y = true) :
    chart.decodeFlag j (canonicalCycle f y) (BitVec.ofNat (chartWidth n) (phase f y)) = true := by
  obtain ⟨hlo, hhi⟩ := (chart.contains_iff j y).mp hy
  have hc : canonicalCycle f y = canonicalCycle f (chart.first j) := by
    rw [← chart.point_eq j y hlo hhi, canonicalCycle_iterate]; rfl
  simp only [decodeFlag, hc, decide_true, Bool.true_and, BitVec.ult, decide_eq_true_eq,
    chart.phaseDistance_of_contains hf j y hy, length_toNat]
  lia

private theorem decodedRow_spec (hf : Function.Injective f) (j : Fin R) (y : BitVec n)
    (hy : chart.decodeFlag j (canonicalCycle f y)
      (BitVec.ofNat (chartWidth n) (phase f y)) = true) :
    chart.decodedRow j (BitVec.ofNat (chartWidth n) (phase f y)) = y := by
  have hy' : canonicalCycle f y = canonicalCycle f (chart.first j) ∧
      (chart.phaseDistance j (BitVec.ofNat (chartWidth n) (phase f y))).toNat <
        chart.stop j - chart.start j := by
    simpa only [decodeFlag, Bool.and_eq_true, BitVec.ult, decide_eq_true_eq, length_toNat] using hy
  rw [chart.decodedRow_eq, ← chart.path j _ hy'.2]
  exact chart.phaseDistance_hit hf j y hy'.1.symm

/-- Select a matching interval and return its decoded word. -/
noncomputable def decode (rep : BitVec n) (p : BitVec (chartWidth n)) : BitString n :=
  chooseRecord (fun j => chart.decodeFlag j rep p)
    (fun j i => (chart.decodedRow j p).getLsbD i.val) (fun _ => false) R

/-- Decoding the canonical cycle representative and phase of `y` recovers the bits of `y`. -/
theorem decode_spec (hf : Function.Injective f) (y : BitVec n) :
    chart.decode (canonicalCycle f y) (BitVec.ofNat (chartWidth n) (phase f y)) =
      fun i => y.getLsbD i.val := by
  obtain ⟨j, hlo, hhi⟩ := chart.covers y
  have hj := chart.decodeFlag_of_contains hf j y ((chart.contains_iff j y).mpr ⟨hlo, hhi⟩)
  obtain ⟨k, _, hk, hout⟩ := chooseRecord_spec
    (fun j => chart.decodeFlag j (canonicalCycle f y) (BitVec.ofNat (chartWidth n) (phase f y)))
    (fun (j : Fin R) (i : Fin n) =>
      (chart.decodedRow j (BitVec.ofNat (chartWidth n) (phase f y))).getLsbD i.val)
    (fun _ => false) R ⟨j, j.isLt, hj⟩
  exact hout.trans (by rw [chart.decodedRow_spec hf k y hk])

end Cslib.Circuits.Boolean.Iteration.CounterIntervalChart
