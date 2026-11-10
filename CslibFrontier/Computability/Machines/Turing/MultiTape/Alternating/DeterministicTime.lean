/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Marking
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ReachableViews
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Space-bounded alternation within exponential time

A space-bounded alternating machine is evaluated by listing the views reachable from its initial
view (`Turing.MultiTapeNTM.reachableViews`, breadth-first search until closed) and marking them
bottom-up (`Turing.MultiTapeATM.markAccepts`)
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]. Under a space bound `s` this decides acceptance
(`Turing.MultiTapeATM.reachableAccepts_iff`) within time and space `2 ^ O(log₂ n + s)`
(`Turing.MultiTapeATM.exists_computableInTimeAndSpace_reachableAccepts`).

Acceptance is the least fixed point of the labelling (`Turing.MultiTapeATM.Accepts`), so the
machine need not halt on every branch: a branch that runs forever within the space bound never
helps a view accept. The space bound need not be computable, since the search stops by itself.

## Main definitions

* `Turing.MultiTapeATM.reachableAccepts`: marking the reachable views.

## Main results

* `Turing.MultiTapeATM.reachableAccepts_iff`: under a space bound, marking the reachable views
  decides acceptance.
* `Turing.MultiTapeATM.exists_computableInTimeAndSpace_reachableAccepts`: under a space bound `s`,
  the decision is computable within time and space `2 ^ O(log₂ n + s)`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Section 3][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeATM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {atm : MultiTapeATM k Bool State}

variable (atm) in
/-- **Acceptance by marking the reachable views**: mark the views found by breadth-first search
until closed, and test the initial view. -/
noncomputable def reachableAccepts (input : List Bool) : Bool :=
  atm.markAccepts (atm.toPTM.toNTM.reachableViews input) (atm.toPTM.toNTM.initView input)

/-- **Marking the reachable views decides acceptance** under any space bound. -/
theorem reachableAccepts_iff {input : List Bool} {s : ℕ}
    (hs : atm.toPTM.toNTM.RunsInSpace input s) :
    atm.reachableAccepts input = true ↔ atm.Accepts input := by
  rw [accepts_iff_exists_viewAcceptsWithin, reachableAccepts]
  refine markAccepts_iff (fun v hv w hw => ?_)
    ((MultiTapeNTM.mem_reachableViews_iff hs).mpr .refl)
  rw [MultiTapeNTM.mem_reachableViews_iff hs] at hv ⊢
  exact hv.tail (MultiTapeNTM.viewStep_of_mem_viewSucc hw)

open scoped Classical in
/-- **Space-bounded alternation within exponential time**: if every computation prefix of `atm`
on every encoded instance stays within space `s a`, then marking the reachable views is computable
within time and space `2 ^ (c * (log₂ n + s a + 1))`. The space bound need not be computable. -/
theorem exists_computableInTimeAndSpace_reachableAccepts {α : Type} {enc : α ↪ List Bool}
    {s : α → ℕ} (hs : ∀ a, atm.toPTM.toNTM.RunsInSpace (enc a) (s a)) :
    ∃ c, ComputableInTimeAndSpace (fun a => atm.reachableAccepts (enc a)) enc encBool
      (fun a => 2 ^ (c * (Nat.log2 (enc a).length + s a + 1)))
      (fun a => 2 ^ (c * (Nat.log2 (enc a).length + s a + 1))) := by
  set ntm := atm.toPTM.toNTM
  -- the initial view is the first reachable view
  have hhead (input : List Bool) :
      (ntm.reachableViews input).headD (ntm.initView []) = ntm.initView input := by
    rw [List.headD_eq_head?_getD, MultiTapeNTM.head?_reachableViews, Option.getD_some]
  have hg : ComputableInPolyTime (fun found : List (FiniteCfg k Bool State) =>
      atm.markAccepts found (found.headD (ntm.initView []))) (encList encFiniteCfg) encBool :=
    computableInPolyTime_markAccepts.comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.headD _))
  obtain ⟨c, h⟩ := MultiTapeNTM.exists_computableInTimeAndSpace_reachableViews hs hg
  simp only [hhead] at h
  exact ⟨c, h⟩

end Turing.MultiTapeATM
