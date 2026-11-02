/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.Computability.WordRAM.Heap
public import Complexity.Computability.WordRAM.Randomized.Law
public import Complexity.Computability.WordRAM.Time

/-!
# Compiled minimum-cut programs from an output law

The basic Karger and recursive Karger–Stein programs share the same final step: compile a
structured code whose observed word has a law supported on non-trivial cut weights. This module
transports that law to halted configurations, retaining supported-path halt and random-call
bounds, bounded data and the exact memory frame.

## Main results

* `Cslib.Algorithms.WordRAM.Karger.program_of_law`: compiled halt, call, cut and probability
  contracts from the existing `ExecRandLaw`.

## References

Extracted unchanged from the Karger word-RAM endpoint proof; the algorithm-specific mathematics
belongs to its specification law.
-/

public section

namespace Cslib.Algorithms.WordRAM.Karger

open Cslib.WeightedCut Cslib.WordRAM

/-- A compiled program whose output word has the law `μ`, supported on the weights of non-trivial
cuts of `W`, halts on every path with such a weight, and outputs `minCut W` with the probability
that `μ` gives it. -/
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

end Cslib.Algorithms.WordRAM.Karger
