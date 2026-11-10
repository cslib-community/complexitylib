/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Karger.Graph
public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.Randomized.Law
public import CslibFrontier.Computability.WordRAM.Time

/-!
# Compiled minimum-cut programs from an output law

The basic Karger and recursive Karger–Stein programs share the same final step: compile a
structured code whose observed word has a law supported on non-trivial cut weights. This module
transports that law to halted configurations, retaining supported-path halt and random-call
bounds, bounded data and the exact memory frame. Their amplification loops also share the update
of the best cut weight after each trial.

## Main results

* `Cslib.Algorithms.WordRAM.Karger.program_of_law`: compiled halt, call, cut and probability
  contracts from the existing `ExecRandLaw`.
* `Cslib.Algorithms.WordRAM.Karger.minUpdate_exec`: the running-minimum update on any registers,
  with its register frame.

## References

Extracted unchanged from the Karger word-RAM endpoint proof; the algorithm-specific mathematics
belongs to its specification law.
-/

public section

namespace Cslib.Algorithms.WordRAM.Karger

open Cslib.WeightedCut Cslib.WordRAM

/-- A compiled program whose output word has the law `μ`, supported on the weights of non-trivial
cuts of `W`, halts on every path with such a weight, and outputs `minCut W` with at least the
probability that `μ` gives it; it fails to do so with at most the probability that `μ` gives the
other values. -/
theorem program_of_law {r R T T' n w : ℕ} {c : Code .standard r} {out : Fin r}
    {input : List ℕ} {F : Finset ℕ} {W : Fin n → Fin n → ℕ} {μ : PMF ℕ}
    (h : ExecRandLaw w c (.init input) (fun y => Modifies F (Data.init (r := r) input).mem y.mem)
      T R (fun y => y.regs out) μ) (hT : T + 1 ≤ T') (hfit : InputFits w input)
    (hμ : ∀ v ∈ μ.support, ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ v = cutWeight W C) :
    RandHaltsWithin w (c.program out) (.init input) T' ∧
    RandCallsBounded w (c.program out) (.init input) T' R ∧
    (∀ cfg ∈ (runRand w (c.program out) T' (.running (.init input))).support,
      ∃ (y : Data r) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧ y.Bounded w ∧ IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧ Modifies F (Data.init (r := r) input).mem y.mem) ∧
    μ.toOuterMeasure {v | v = minCut W} ≤
      (evalRand w (c.program out) T' (.init input)).toOuterMeasure
        {cfg | ∃ y, cfg = .halted (minCut W) y} ∧
    (evalRand w (c.program out) T' (.init input)).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤ μ.toOuterMeasure {v | v ≠ minCut W} := by
  let output : RandCfg r → ℕ := fun | .halted v _ => v | _ => 0
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := h.program out hT output fun _ _ => rfl
  have hhalted : ∀ cfg ∈ (evalRand w (c.program out) T' (.init input)).support,
      ∃ y : Data r, cfg = .halted (y.regs out) y := fun cfg hcfg => by
    obtain ⟨y, rfl, -⟩ := hpost cfg (by rwa [support_evalRand] at hcfg)
    exact ⟨y, rfl⟩
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, ?_, ?_⟩
  · obtain ⟨y, rfl, hmod⟩ := hpost cfg hcfg
    obtain ⟨C, hC, hv⟩ := hμ (y.regs out) (by
      rw [← hlaw, PMF.mem_support_map_iff]
      exact ⟨_, by rwa [support_evalRand], rfl⟩)
    exact ⟨y, C, by rw [hv], (runRand_bounded_init hfit hcfg).2, hC, minCut_le_cutWeight W hC,
      hmod⟩
  · rw [← hlaw, PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ ?_
    rintro cfg ⟨hv, hcfg⟩
    obtain ⟨y, rfl⟩ := hhalted cfg hcfg
    change y.regs out = minCut W at hv
    exact ⟨y, by rw [hv]⟩
  · rw [← hlaw, PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ ?_
    rintro cfg ⟨hne, hcfg⟩ hv
    obtain ⟨y, rfl⟩ := hhalted cfg hcfg
    change y.regs out = minCut W at hv
    exact hne y (by rw [hv])

/-- The running-minimum update shared by the amplification loops, on any registers: on the first
trial (`trial` equal to the zero register) it records `val` in `best`, and afterwards the smaller
of `val` and `best`. It runs within five instructions and changes no other register or memory. -/
theorem minUpdate_exec {r w : ℕ} {trial zero val best : Fin r} (hbz : best ≠ zero)
    {x : Data r} (hz : x.regs zero = 0) :
    ∃ y, ExecWithin (B := .standard) w ram[
        if trial = zero then [ best ← val ] else [
          if val < best then [ best ← val ] else [ zero ← #0 ] ]] x y 5 ∧
      y.mem = x.mem ∧
      y.regs best = (if x.regs trial = 0 then x.regs val else min (x.regs val) (x.regs best)) ∧
      ∀ i, i ≠ best → y.regs i = x.regs i := by
  have hset (v : ℕ) : ∀ i, i ≠ best → (x.set best v).regs i = x.regs i := fun i hi => by
    simp only [Data.set_regs, Function.update_of_ne hi]
  have e_copy : ExecWithin (B := .standard) w ram[ best ← val ] x (x.set best (x.regs val)) 1 :=
    (Exec.copy (B := .standard) (w := w) (d := best) (s := val) (x := x)).within
  by_cases hi0 : x.regs trial = 0
  · have hc : (Cond.eq trial zero).Holds x := by simp [Cond.holds_eq, hz, hi0]
    exact ⟨_, (ExecWithin.branch_pos hc e_copy).mono (by omega), rfl, by simp [hi0], hset _⟩
  have hc : ¬(Cond.eq trial zero).Holds x := by simp [Cond.holds_eq, hz, hi0]
  by_cases hlt : x.regs val < x.regs best
  · have hc2 : (Cond.lt val best).Holds x := hlt
    exact ⟨_, (ExecWithin.branch_neg hc (ExecWithin.branch_pos hc2 e_copy)).mono (by omega), rfl,
      by simp [hi0, Nat.min_eq_left hlt.le], hset _⟩
  · have hc2 : ¬(Cond.lt val best).Holds x := hlt
    have e_zero : ExecWithin (B := .standard) w ram[ zero ← #0 ] x (x.set zero 0) 1 :=
      ExecWithin.const (fits_zero w)
    refine ⟨_, (ExecWithin.branch_neg hc (ExecWithin.branch_neg hc2 e_zero)).mono (by omega),
      rfl, ?_, fun i _ => ?_⟩
    · simp only [Data.set_regs, Function.update_of_ne hbz, hi0, ↓reduceIte]
      exact (Nat.min_eq_right (Nat.le_of_not_lt hlt)).symm
    · by_cases hiz : i = zero
      · subst hiz; simp [hz]
      · simp only [Data.set_regs, Function.update_of_ne hiz]

end Cslib.Algorithms.WordRAM.Karger
