/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Simplex.Bland
import Mathlib.Data.Fintype.EquivFin

/-!
# The simplex method with Dantzig's rule

This module defines the simplex method with Dantzig's largest-coefficient rule
([Chvatal1983], Chapter 4) on the dictionaries of
`CslibFrontier.Algorithms.Lean.Simplex.Dictionary`,
and proves that it is sound: when it stops, its answer is correct.

## Algorithm

In a dictionary `D` (`dantzigStep`):

* if no nonbasic variable has a positive reduced cost, `D` is optimal;
* otherwise the entering variable `s` is a nonbasic variable of largest reduced cost, the
  smallest one in case of ties (`dantzigEntering`);
* the leaving variable is chosen by the ratio test as in Bland's rule (`blandLeaving`): the
  smallest basic variable among those with `coeff i s < 0` minimizing `rhs i / -coeff i s`; if
  there is none, the objective is unbounded along the edge of `s`.

`dantzigRun D fuel` iterates at most `fuel` pivots: it is `runWith` with Dantzig's rule, so its
soundness is that of `runWith`, applied to the step lemmas of this module.

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.Dictionary.dantzigEntering`: Dantzig's entering rule.
* `Cslib.Algorithms.Lean.Simplex.Dictionary.dantzigStep`: one step with Dantzig's rule.
* `Cslib.Algorithms.Lean.Simplex.Dictionary.dantzigRun`: the simplex method with Dantzig's rule
  and at most `fuel` pivots.

## Main results

* `Dictionary.dantzigRun_eq_optimal`, `Dictionary.dantzigRun_eq_unbounded`: soundness. A run
  that stops returns an equivalent feasible dictionary that is optimal, or certifies that the
  objective is unbounded.

## Limitations

Dantzig's rule can cycle on degenerate programs (Chvátal's cycling example, [Chvatal1983],
Chapter 3, is among the worked examples of the test suite), so no termination theorem holds in
general. On the Klee–Minty programs it takes `2 ^ n - 1` pivots
(`CslibFrontier.Algorithms.Lean.Simplex.KleeMinty`).

## References

* [V. Chvátal, *Linear Programming*][Chvatal1983]
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

namespace Dictionary

open Finset

variable {ι K : Type*} [Fintype ι] [LinearOrder ι] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] (D : Dictionary ι K)

/-- **Dantzig's entering rule** ([Chvatal1983], Chapter 4): a nonbasic variable with the
largest positive reduced cost, the smallest one in case of ties. -/
@[expose] def dantzigEntering : Option ι :=
  minOpt (D.enteringCandidates.filter fun j =>
    ∀ k ∈ D.enteringCandidates, D.objCoeff k ≤ D.objCoeff j)

/-- One step of the simplex method with Dantzig's entering rule and the smallest-index ratio
test. -/
@[expose] def dantzigStep : Step ι :=
  match D.dantzigEntering with
  | none => .optimal
  | some s =>
    match D.blandLeaving s with
    | none => .unbounded s
    | some r => .pivot r s

omit [IsStrictOrderedRing K] in
theorem dantzigEntering_eq_none_iff :
    D.dantzigEntering = none ↔ ∀ j ∉ D.basis, D.objCoeff j ≤ 0 := by
  rw [dantzigEntering, minOpt_eq_none_iff, ← blandEntering_eq_none_iff, blandEntering,
    minOpt_eq_none_iff]
  constructor
  · intro h
    by_contra hne
    obtain ⟨k, hk, hmax⟩ := D.enteringCandidates.exists_max_image D.objCoeff
      (Finset.nonempty_iff_ne_empty.2 hne)
    have : k ∈ D.enteringCandidates.filter fun j =>
        ∀ k ∈ D.enteringCandidates, D.objCoeff k ≤ D.objCoeff j :=
      Finset.mem_filter.2 ⟨hk, hmax⟩
    rw [h] at this
    exact Finset.notMem_empty k this
  · intro h
    rw [h, Finset.filter_empty]

omit [IsStrictOrderedRing K] in
theorem dantzigEntering_eq_some_iff {s : ι} : D.dantzigEntering = some s ↔
    s ∉ D.basis ∧ 0 < D.objCoeff s ∧ (∀ j ∉ D.basis, D.objCoeff j ≤ D.objCoeff s) ∧
      ∀ j ∉ D.basis, D.objCoeff j = D.objCoeff s → s ≤ j := by
  rw [dantzigEntering, minOpt_eq_some_iff]
  simp only [enteringCandidates, Finset.mem_filter, Finset.mem_compl, and_imp]
  constructor
  · rintro ⟨⟨⟨hs, hc⟩, hmax⟩, hle⟩
    refine ⟨hs, hc, fun j hj => ?_, fun j hj heq => hle j hj (heq ▸ hc) fun k hk hck => ?_⟩
    · rcases le_or_gt (D.objCoeff j) 0 with h | h
      · exact h.trans hc.le
      · exact hmax j hj h
    · exact heq ▸ hmax k hk hck
  · rintro ⟨hs, hc, hmax, hle⟩
    exact ⟨⟨⟨hs, hc⟩, fun k hk _ => hmax k hk⟩, fun j hj _ hj' =>
      hle j hj (le_antisymm (hmax j hj) (hj' s hs hc))⟩

omit [IsStrictOrderedRing K] in
theorem dantzigStep_eq_optimal_iff : D.dantzigStep = .optimal ↔ D.dantzigEntering = none := by
  rcases h1 : D.dantzigEntering with _ | s'
  · simp only [dantzigStep, h1]
  · rcases h2 : D.blandLeaving s' with _ | r' <;> simp only [dantzigStep, h1, h2, reduceCtorEq]

omit [IsStrictOrderedRing K] in
theorem dantzigStep_eq_unbounded_iff {s : ι} :
    D.dantzigStep = .unbounded s ↔ D.dantzigEntering = some s ∧ D.blandLeaving s = none := by
  unfold dantzigStep
  rcases D.dantzigEntering with _ | s'
  · simp
  · rcases h2 : D.blandLeaving s' with _ | r' <;> grind

omit [IsStrictOrderedRing K] in
theorem dantzigStep_eq_pivot_iff {r s : ι} :
    D.dantzigStep = .pivot r s ↔ D.dantzigEntering = some s ∧ D.blandLeaving s = some r := by
  unfold dantzigStep
  rcases D.dantzigEntering with _ | s'
  · simp
  · rcases h2 : D.blandLeaving s' with _ | r' <;> grind

/-- A pivot of Dantzig's rule preserves feasibility, equivalence and does not decrease the
objective. -/
theorem dantzigStep_eq_pivot_spec {r s : ι} (hD : D.Feasible) (h : D.dantzigStep = .pivot r s) :
    D.Equivalent (D.pivot r s) ∧ (D.pivot r s).Feasible ∧
      D.objConst ≤ (D.pivot r s).objConst := by
  obtain ⟨hs, hr⟩ := D.dantzigStep_eq_pivot_iff.1 h
  obtain ⟨hs, hc, -, -⟩ := D.dantzigEntering_eq_some_iff.1 hs
  obtain ⟨hr, har, hmin, -⟩ := D.blandLeaving_eq_some_iff.1 hr
  exact ⟨D.equivalent_pivot hr hs har.ne, D.feasible_pivot hD hr hs har hmin,
    D.objConst_le_pivot hD hr har hc.le⟩

/-! ### The simplex method with Dantzig's rule -/

/-- The simplex method with Dantzig's rule and at most `fuel` pivots. -/
@[expose] def dantzigRun : Dictionary ι K → ℕ → Outcome ι K := runWith dantzigStep

/-- **Soundness of Dantzig's rule, optimal case**: a run that stops at an optimal dictionary
`D'` returns an equivalent feasible dictionary with no positive reduced cost, so its basic
solution attains the maximum `D'.objConst` (`Dictionary.isGreatest_value`). -/
theorem dantzigRun_eq_optimal {fuel : ℕ} {D' : Dictionary ι K} (hD : D.Feasible)
    (h : D.dantzigRun fuel = .optimal D') :
    D.Equivalent D' ∧ D'.Feasible ∧ D.objConst ≤ D'.objConst ∧
      ∀ j ∉ D'.basis, D'.objCoeff j ≤ 0 :=
  D.runWith_eq_optimal
    (fun D h => D.dantzigEntering_eq_none_iff.1 (D.dantzigStep_eq_optimal_iff.1 h))
    dantzigStep_eq_pivot_spec hD h

/-- **Soundness of Dantzig's rule, unbounded case**: a run that stops with an unbounded entering
variable `s` returns an equivalent feasible dictionary in which `s` is nonbasic with a positive
reduced cost and no row bounds its increase, so the objective is unbounded
(`Dictionary.not_bddAbove_value`). -/
theorem dantzigRun_eq_unbounded {fuel : ℕ} {D' : Dictionary ι K} {s : ι} (hD : D.Feasible)
    (h : D.dantzigRun fuel = .unbounded D' s) :
    D.Equivalent D' ∧ D'.Feasible ∧ s ∉ D'.basis ∧ 0 < D'.objCoeff s ∧
      ∀ i ∈ D'.basis, 0 ≤ D'.coeff i s :=
  D.runWith_eq_unbounded
    (fun D _ h => by
      obtain ⟨h1, h2⟩ := D.dantzigStep_eq_unbounded_iff.1 h
      obtain ⟨hs, hc, -⟩ := D.dantzigEntering_eq_some_iff.1 h1
      exact ⟨hs, hc, D.blandLeaving_eq_none_iff.1 h2⟩)
    (fun D _ _ hD h => (D.dantzigStep_eq_pivot_spec hD h).imp_right And.left) hD h

end Dictionary

end Cslib.Algorithms.Lean.Simplex
