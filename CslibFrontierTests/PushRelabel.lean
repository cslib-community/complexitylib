/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.PushRelabel

/-!
# Push–Relabel Tests

Kernel-checked examples (without `native_decide`) for preflows, push and relabel, and
`pushRelabel`:

1. **CLRS 6-vertex network (as in `CslibFrontierTests.MaxFlow`; compare [CLRS2009], Figure 26.1):**
   `pushRelabel` finds a maximum flow of value `23` and the minimum cut `{0, 1, 2, 4}` after `29`
   operations (`13` relabels), within `maxOps clrsNet = 1384`; `pushRelabel_correct` certifies
   the output.
2. **Preconditions:** in the initial state of the CLRS network, vertex `1` can be relabelled but not
   push to `3`; after the relabel it can push to `3`, and a two-step run is checked.
3. **Edge cases:** antiparallel arcs, an unreachable sink, an arc `s → t` alone, and `N.s = N.t`
   (no operations, zero flow); the invariant `PushRelabel.State.Inv` holds initially and needs
   `N.s ≠ N.t`. On the arc `s → t` alone the empty run admits no operation, which instantiates
   `isMaxFlow_isMinCut_of_isRun`; `maxOps_le` is instantiated on the CLRS network.
-/

public section

namespace CslibFrontierTests.PushRelabel

open Cslib.Algorithms.Lean.MaxFlow Network.PushRelabel

/-! ### CLRS network -/

/-- The CLRS 6-vertex network of `CslibFrontierTests.MaxFlow`, with antiparallel arcs `(1, 2)` and
`(2, 1)`. -/
def clrsNet : Network (Fin 6) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 16
    | 0, 2 => 13
    | 1, 2 => 10
    | 2, 1 => 4
    | 1, 3 => 12
    | 3, 2 => 9
    | 2, 4 => 14
    | 4, 3 => 7
    | 3, 5 => 20
    | 4, 5 => 4
    | _, _ => 0
  s := 0
  t := 5

theorem clrsNet_st : clrsNet.s ≠ clrsNet.t := by decide

example : (pushRelabel clrsNet).flow.value = 23 := by decide +kernel

example : (pushRelabel clrsNet).ops.length = 29 := by decide +kernel

example : ((pushRelabel clrsNet).ops.filter fun o => decide o.IsRelabel).length = 13 := by
  decide +kernel

example : maxOps clrsNet = 1384 := by decide +kernel

example : (pushRelabel clrsNet).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide +kernel

example :
    (pushRelabel clrsNet).flow.IsMaxFlow ∧ clrsNet.IsMinCut (pushRelabel clrsNet).cut ∧
      (init clrsNet).IsRun (pushRelabel clrsNet).ops := by
  obtain ⟨hmax, hmin, _, hrun, _⟩ := pushRelabel_correct clrsNet_st
  exact ⟨hmax, hmin, hrun⟩

/-! ### Preconditions and a short run -/

example : (init clrsNet).flow.CanRelabel (init clrsNet).height 1 := by decide

example : ¬ (init clrsNet).flow.CanPush (init clrsNet).height 1 3 := by decide

example : ((init clrsNet).apply (.relabel 1)).flow.CanPush
    ((init clrsNet).apply (.relabel 1)).height 1 3 := by decide

example : (init clrsNet).IsRun [.relabel 1, .push 1 3] := by decide

example : (init clrsNet).Inv := inv_init clrsNet_st

/-! ### Edge cases -/

/-- Arcs `0 → 1`, `1 → 2`, `2 → 3` and `0 → 2`, `2 → 1`, `1 → 3`, with both `1 → 2` and `2 → 1`
present. -/
def antiNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 2
    | 0, 2 => 2
    | 1, 2 => 1
    | 2, 1 => 1
    | 1, 3 => 1
    | 2, 3 => 3
    | _, _ => 0
  s := 0
  t := 3

example : (pushRelabel antiNet).flow.value = 4 := by decide

/-- The sink `2` is unreachable from the source `0`. -/
def cutOffNet : Network (Fin 3) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 5
    | 2, 1 => 5
    | _, _ => 0
  s := 0
  t := 2

example : (pushRelabel cutOffNet).flow.value = 0 := by decide

example : cutOffNet.cutCapacity (pushRelabel cutOffNet).cut = 0 := by decide

/-- A single arc `s → t`: no operation is needed. -/
def directNet : Network (Fin 2) where
  cap u v := if u.1 = 0 ∧ v.1 = 1 then 7 else 0
  s := 0
  t := 1

example : (pushRelabel directNet).flow.value = 7 ∧ (pushRelabel directNet).ops = [] := by
  decide

/-- On `directNet` no operation is admissible initially, so the empty run already stops. -/
theorem directNet_stop : ∀ o, ¬ ((init directNet).run []).Admissible o := by
  have hp : ∀ u v : Fin 2, ¬ (init directNet).flow.CanPush (init directNet).height u v := by
    decide
  have hr : ∀ u : Fin 2, ¬ (init directNet).flow.CanRelabel (init directNet).height u := by
    decide
  rintro (⟨u, v⟩ | u)
  · exact hp u v
  · exact hr u

/-- `isMaxFlow_isMinCut_of_isRun` applies to the stopped empty run on `directNet`. -/
example : directNet.IsMinCut (Network.Preflow.gapCut ((init directNet).run []).height) :=
  (isMaxFlow_isMinCut_of_isRun (by decide) (os := []) trivial directNet_stop).choose_spec.2.1

example : maxOps clrsNet ≤ 4 * 6 ^ 2 * (1 + clrsNet.posArcs.card) := maxOps_le clrsNet

example : clrsNet.posArcs.card = 10 := by decide

/-- `N.s = N.t`: the algorithm does nothing and no state satisfies the invariant. -/
def loopNet : Network (Fin 2) where
  cap _ _ := 1
  s := 0
  t := 0

example : (pushRelabel loopNet).ops = [] ∧ (pushRelabel loopNet).flow.value = 0 := by decide

example (σ : State loopNet) : ¬ σ.Inv := fun h => h.valid.source_ne_sink rfl

end CslibFrontierTests.PushRelabel
