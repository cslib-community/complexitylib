/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Power
public import Complexity.Logics.FirstOrder.Ordered.FullTuple
public import Complexity.Logics.FirstOrder.Ordered.StrictOrder

/-!
# Canonical ordered power structures

The existing power interpretation exposes input truth tables on a polynomially enlarged universe.
This module adapts it to the canonical full-tuple interface, so that target order, BIT and numeric
constants are defined by the existing tuple formulas. Reversing each tuple block reconciles the
power interpretation's little-endian indexing with lexicographic ranking.

## Main definitions

* `Cslib.Logic.Vocabulary.orderedPowerInterpretation`: the full-tuple power interpretation.

## Main results

* `Cslib.Logic.Vocabulary.realize_orderedPower_rel`: exact numerical semantics of input relations.
* `Cslib.Logic.Vocabulary.inputStructure_orderedPowerInterpretation`: the interpreted input
  structure is the existing `powerStructure`, with no supplied numeric tables.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33.
-/

public section

namespace Cslib.Logic.Vocabulary

open FirstOrder Language Structure FO.Ordered

variable {L : Language} [L.IsRelational] (v : Vocabulary L) (k : ℕ)
    (har : ∀ i : Fin v.count, v.arity i ≤ k)

/-- Retain the original power-structure input predicates while using canonical lexicographic
tuple ranks. All target numeric predicates are supplied by the full-tuple interpretation. -/
noncomputable def orderedPowerInterpretation : FullTupleInterpretation L v.powerLanguage k where
  rel R := ((strictOrderInterpretation L).onFormula ((v.powerInterpretation k har).rel R)).relabel
    fun p => (p.1.1, p.1.2.rev)

/-- The original power predicates evaluated on lexicographically ranked tuples. -/
theorem realize_orderedPower_rel (hk : 1 ≤ k) (M : FO.Ordered.Structure L)
    {r : ℕ} (R : v.powerLanguage.Relations r) (x : Fin r → Fin k → M) :
    ((v.orderedPowerInterpretation k har).rel R).Realize (fun p => x p.1 p.2) ↔
      letI := v.powerStructure (FO.Ordered.encode v M) (M.size ^ k)
      RelMap R (fun i => lexEquiv (x i)) := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
    (ESO.orderRelOfEquiv (Equiv.refl M))
  let _ := v.powerStructure (FO.Ordered.encode v M) (M.size ^ k)
  rw [orderedPowerInterpretation, Formula.realize_relabel]
  change ((strictOrderInterpretation L).onFormula ((v.powerInterpretation k har).rel R)).Realize
    (fun p => x p.1.1 p.1.2.rev) ↔ _
  rw [realize_strictOrder_onFormula M ((v.powerInterpretation k har).rel R)
    (fun p => x p.1 p.2.rev)]
  let y : Fin r → (v.powerInterpretation k har).Model M :=
    fun i => ⟨fun j => x i j.rev, Formula.realize_top.mpr trivial⟩
  have h := (v.powerEquiv k hk har M (Equiv.refl M)).map_rel R y
  exact h.symm

/-- The input relations of the full-tuple interpretation agree exactly with the canonical
power structure of the native input encoding. -/
theorem inputStructure_orderedPowerInterpretation (hk : 1 ≤ k) (M : FO.Ordered.Structure L) :
    (v.orderedPowerInterpretation k har).inputStructure (n := M.size) =
      v.powerStructure (FO.Ordered.encode v M) (M.size ^ k) := by
  apply FirstOrder.Language.Structure.ext
  · funext r f
    exact isEmptyElim f
  · funext r R x
    apply propext
    change ((v.orderedPowerInterpretation k har).rel R).Realize
      (fun p => lexEquiv.symm (x p.1) p.2) ↔ _
    have h := v.realize_orderedPower_rel k har hk M R (fun i => lexEquiv.symm (x i))
    simpa only [Equiv.apply_symm_apply] using h

end Cslib.Logic.Vocabulary
