/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.DecisionTree.Prune

/-! # Checked clients for pruning repeated and fixed queries -/

set_option linter.privateModule false

open Cslib BitString

namespace Cslib.DecisionTree

private def repeatedQueryExample : DecisionTree Unit ℕ :=
  .node () (.leaf 12) (.node () (.leaf 999) (.leaf 37))

example : (repeatedQueryExample.prune PartialAssignment.empty).depth = 1 := rfl
example : repeatedQueryExample.weightedCost (fun _ => 5) (fun _ => true) = 10 := rfl
example : (repeatedQueryExample.prune PartialAssignment.empty).weightedCost
    (fun _ => 5) (fun _ => true) = 5 := rfl
example : (repeatedQueryExample.prune PartialAssignment.empty).weightedCost
    (fun _ => 0) (fun _ => true) = 0 := rfl
example : (repeatedQueryExample.prune (fun _ => some true)).eval (fun _ => true) = 37 := rfl
example : (repeatedQueryExample.prune (fun _ => some false)).eval (fun _ => false) = 12 := rfl
example : (repeatedQueryExample.prune (fun _ => some true)).depth = 0 := rfl
example : ((leaf 7 : DecisionTree Empty ℕ).prune PartialAssignment.empty).depth = 0 := rfl


end Cslib.DecisionTree

-- Recording an observed answer also works on an infinite coordinate type.
example (ρ : PartialAssignment ℕ) (x : ℕ → Bool) (hx : ρ.Agrees x) (i : ℕ) :
    PartialAssignment.Agrees (Function.update ρ i (some (x i))) x := hx.update rfl
