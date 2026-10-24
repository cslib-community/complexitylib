/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Complexity.Computability.PCP.Encoded.GapTheorem

/-!
# MAX-2CSP is NP-hard to approximate

An instance of MAX-2CSP over a finite alphabet `α` is an executable constraint graph
(`Cslib.PCP.Encoded.Graph`): numbered vertices and a list of edges, each carrying the complete table
of a binary constraint on `α`. Its value is the largest proportion of the edges that a labelling of
the vertices satisfies, `1 - unsatVal`; the declared vertex count plays no role. `GapTwoCSP α s` is
the gap problem with perfect completeness: the yes-instances are the satisfiable ones and the
no-instances those of value at most `s`.

The PCP theorem in its hardness-of-approximation form [Arora and Barak, Chapter 11][AroraBarak09]
is Dinur's gap construction [Dinur2007]: composed with the Cook–Levin reduction, the concrete
executable SAT-to-gap pipeline `Cslib.PCP.Encoded.gapGraph` maps satisfiable formulas to
satisfiable constraint graphs and unsatisfiable ones to constraint graphs in which every labelling
violates at least the proportion `2 ^ (-61)` of the edges, over the alphabet
`Bool × (Fin 6 → Bool)` of `128` symbols. Hence MAX-2CSP over `128` symbols is NP-hard to
approximate within `1 - 2 ^ (-61)`. The constants are those of the landed construction, which was
not optimized for them.

## Main definitions

* `Cslib.Complexity.GapTwoCSP`: the gap problem of MAX-2CSP with perfect completeness.

## Main results

* `Cslib.Complexity.GapTwoCSP_npHard`: distinguishing satisfiable MAX-2CSP instances over `128`
  symbols from those of value at most `1 - 2 ^ (-61)` is NP-hard.
* `Cslib.Complexity.GapTwoCSP_notMem_PromiseP`: unless `P = NP`, no polynomial-time algorithm
  does so.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapters 11 and
  22][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- The gap problem of **MAX-2CSP** over the alphabet `α` with perfect completeness and soundness
`s`. Instances are executable constraint graphs whose edges carry constraint tables; their value
is the largest proportion of the edges satisfied by a labelling of the vertices. The yes-instances
have value one, the no-instances value at most `s`. -/
noncomputable def GapTwoCSP (α : Type) (s : ℝ) : PromiseProblem (Graph (α → α → Bool)) :=
  PromiseProblem.gapMax (fun g => 1 - (g.toGraph id).unsatVal) (fun _ => 1) (fun _ => s)

variable {α : Type} {s : ℝ} {g : Graph (α → α → Bool)}

/-- The yes-instances of `GapTwoCSP` are the satisfiable constraint graphs. -/
theorem mem_yes_GapTwoCSP [Nonempty α] : g ∈ (GapTwoCSP α s).yes ↔ (g.toGraph id).Satisfiable := by
  rw [GapTwoCSP, PromiseProblem.mem_yes_gapMax, ← ConstraintGraph.unsatVal_eq_zero_iff]
  have := (g.toGraph id).unsatVal_nonneg
  constructor <;> intro h <;> linarith

/-- For `s < 1`, the no-instances of `GapTwoCSP` are the constraint graphs in which every labelling
violates at least the proportion `1 - s` of the edges. -/
theorem mem_no_GapTwoCSP (hs : s < 1) :
    g ∈ (GapTwoCSP α s).no ↔ 1 - s ≤ (g.toGraph id).unsatVal := by
  rw [GapTwoCSP, PromiseProblem.mem_no_gapMax_of_lt hs]
  constructor <;> intro h <;> linarith

/-- **MAX-2CSP is NP-hard to approximate** [Dinur2007]: over the alphabet `Bool × (Fin 6 → Bool)`
of `128` symbols, distinguishing satisfiable constraint graphs from those in which every labelling
violates at least the proportion `2 ^ (-61)` of the edges is NP-hard. The reduction is Dinur's
gap construction `Cslib.PCP.Encoded.gapGraph` composed with the Cook–Levin reduction. -/
theorem GapTwoCSP_npHard :
    PromiseProblem.NPHard (Graph.encoding (encPi (encPi encBool)))
      (GapTwoCSP (Bool × (Fin 6 → Bool)) (1 - 1 / 2 ^ 61)) := by
  refine PromiseProblem.npHard_of_polyTimeReducible_SAT
    ⟨gapGraph, (isPolyTime_gapGraph (.of_tidy ComputableTidilyInPolyTime.id')), fun φ hφ => ?_,
      fun φ hφ => ?_⟩
  · exact mem_yes_GapTwoCSP.2 ((satisfiable_gapGraph_iff φ).2 hφ)
  · refine (mem_no_GapTwoCSP (by norm_num)).2 ?_
    have h := gap_le_unsatVal_gapGraph φ hφ
    rw [ConstraintGraph.Amplification.Arithmetic.gap] at h
    linarith

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes satisfiable MAX-2CSP instances over
`128` symbols from those of value at most `1 - 2 ^ (-61)`. -/
theorem GapTwoCSP_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapTwoCSP (Bool × (Fin 6 → Bool)) (1 - 1 / 2 ^ 61) ∉
      PromiseP (Graph.encoding (encPi (encPi encBool))) :=
  GapTwoCSP_npHard.notMem_PromiseP h

end Cslib.Complexity
