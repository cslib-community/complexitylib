/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Power
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk

/-!
# Executable constraints for killed-walk powering

The evaluator checks the original constraint at each used step against the two endpoint opinions.
It carries the runtime graph through rotation and relation calls, and obtains the reverse labels
from the same killed-power program used for the destination vertex. Agreement on valid encoded
vertices suffices to identify the result with the existing mathematical powered constraint.

## Main definitions

* `Cslib.PCP.RegularConstraintGraph.powerRelationWithInput`: the Boolean powered constraint.

## Main results

* `Cslib.PCP.RegularConstraintGraph.powerRelationWithInput_eq_true`: exact interpretation.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
-/

@[expose] public section

namespace Cslib.PCP.RegularConstraintGraph

open RotationMap

variable {P V W D α : Type*}

/-- Runtime graph input, a killed walk, and its two endpoint opinions. -/
abbrev PowerInput (P W D α : Type*) (T q : ℕ) :=
  P × ((W × ((Fin T → D) × (Fin T → Fin q))) ×
    ((WalkLabels D T → α) × (WalkLabels D T → α)))

/-- Check every used step. Unused steps accept, and each endpoint opinion is read at the exact
forward or reverse prefix specified by the mathematical powered constraint. -/
def powerRelationWithInput (rotate : P × (W × D) → W × D)
    (rel : P × ((W × D) × (α × α)) → Bool) (T q : ℕ) [NeZero q]
    (p : PowerInput P W D α T q) : Bool :=
  let returned := killedPowRotWithInput rotate T q (p.1, p.2.1)
  (List.finRange T).all fun i =>
    if i.val < killTime p.2.1.2.2 then
      rel (p.1, (walkAtWithInput rotate (p.1, p.2.1.1, p.2.1.2.1) i.val, p.2.1.2.1 i),
        p.2.2.1 (.take i.val i.isLt.le p.2.1.2.1),
        p.2.2.2 (.take (killTime p.2.1.2.2 - (i.val + 1))
          ((Nat.sub_le _ _).trans (killTime_le _)) returned.2.1))
    else true

/-- Valid encoded trajectories and original constraints give exactly the mathematical powered
constraint, including the reverse opinion queried at each step. -/
theorem powerRelationWithInput_eq_true
    (rotate : P × (W × D) → W × D) (rel : P × ((W × D) × (α × α)) → Bool)
    (input : P) (R : RegularConstraintGraph V D α) (encode : V → W)
    (hrotate : ∀ v d, rotate (input, encode v, d) =
      (encode (R.graph.rot (v, d)).1, (R.graph.rot (v, d)).2))
    (hrel : ∀ v d a b, rel (input, (encode v, d), a, b) = true ↔ R.rel (v, d) a b)
    (T q : ℕ) [NeZero q] (v : V) (k : Fin T → D) (c : Fin T → Fin q)
    (a b : WalkLabels D T → α) :
    powerRelationWithInput rotate rel T q (input, (encode v, k, c), a, b) = true ↔
      (R.power T q).rel (v, k, c) a b := by
  simp only [powerRelationWithInput, killedPowRotWithInput_eq rotate input R.graph encode hrotate,
    List.all_eq_true, List.mem_finRange, forall_const,
    walkAtWithInput_eq rotate input R.graph encode hrotate]
  constructor
  · intro h i hi
    have hstep := h ⟨i, hi.trans_le (killTime_le c)⟩
    simp only [ite_eq_left hi, hrel] at hstep
    exact hstep
  · intro h i
    split_ifs with hi
    · exact (hrel _ _ _ _).mpr (h i.val hi)
    · rfl

end Cslib.PCP.RegularConstraintGraph
