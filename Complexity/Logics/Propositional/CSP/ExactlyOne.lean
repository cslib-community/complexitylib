/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.PartitionFunction
import Complexity.Foundations.Data.List.Boole
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Exactly-one constraints

The exactly-one weighting `CSP.exactlyOneWeight` weighs a local assignment one when exactly one of
its values is `true`, and zero otherwise. Over `Bool`, the partition function of an instance with
these weights counts the sets `S` of occurring variables that meet every scope in exactly one
variable (`CSP.partitionFunction_exactlyOne`). With one variable per edge of a graph and one
constraint per vertex on its incident edges, these sets are the perfect matchings, so perfect
matchings and `0/1` permanents are such Holant instances.

## Main definitions

* `Cslib.Logic.PL.CSP.exactlyOneWeight`: the exactly-one weights.

## Main results

* `Cslib.Logic.PL.CSP.partitionFunction_exactlyOne`: the partition function counts the sets of
  variables that meet every scope exactly once.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- The exactly-one weights: one when exactly one entry of the local assignment is `true`, zero
otherwise. -/
@[expose] def exactlyOneWeight (_ : Unit) (w : List Bool) : ℕ :=
  if w.count true = 1 then 1 else 0

variable {V : Type*} [DecidableEq V]

/-- **Exactly-one partition functions count exact covers of the scopes**: the partition function
is the number of sets `S` of occurring variables such that every scope has exactly one entry in
`S`. -/
theorem partitionFunction_exactlyOne (F : CSP Unit V) :
    F.partitionFunction exactlyOneWeight =
      (F.vars.toFinset.powerset.filter fun S =>
        ∀ c ∈ F, (c.2.filter fun v => v ∈ S).length = 1).card := by
  rw [partitionFunction_eq_sum_powerset, Finset.card_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [weight, List.map_congr_left (g := fun c =>
      if (c.2.filter fun v => v ∈ S).length = 1 then 1 else 0) fun c _ => ?_, List.prod_map_boole]
  simp only [exactlyOneWeight, List.count_eq_countP, List.filter_map, List.length_map,
    List.countP_eq_length_filter, Function.comp_def, beq_true]

end Cslib.Logic.PL.CSP
