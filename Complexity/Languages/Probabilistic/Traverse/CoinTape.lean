/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Traverse
public import Complexity.Probability.BitString.List
import Complexity.Probability.PMF.Bind

/-!
# Flat saved tapes for probabilistic list traversal

A traversal can replay every call from its own fixed-width block of one uniform bit list.
The component realization law is required only at values occurring in the input list. Equal
input values still use distinct independent blocks, and zero-width blocks remain valid.

## Main results

* `Cslib.ProbComp.eval_mapM_of_uniformList`: replay the original traversal with exactly
  `list.length * width` allocated bits.
-/

public section

namespace Cslib.ProbComp

open Probability

/-- Independent fixed-width component seeds combine into one flat tape. The realization
premise concerns only the actual input values; it imposes no law outside the supplied list.
This is an exact distribution law and does not by itself assert computational efficiency. -/
theorem eval_mapM_of_uniformList {α β : Type} (program : α → ProbComp β)
    (evaluate : α → List Bool → β) (width : ℕ) (list : List α)
    (hlaw : ∀ a ∈ list,
      ProbComp.eval (program a) = (BitString.uniformList width).map (evaluate a)) :
    ProbComp.eval (list.mapM program) =
      (BitString.uniformList (list.length * width)).map
        (fun tape => List.zipWith evaluate list (BitString.listRows list.length width tape)) := by
  induction list with
  | nil => simp [BitString.listRows, ProbComp.eval_pure]
  | cons a list ih =>
    simp only [List.mapM_cons, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map]
    rw [hlaw a (List.mem_cons_self ..), ih (fun b hb => hlaw b (List.mem_cons_of_mem _ hb))]
    rw [show (a :: list).length * width = width + list.length * width by
      simp [Nat.add_mul, Nat.add_comm]]
    rw [BitString.uniformList_add, PMF.map_bind, PMF.bind_map]
    apply PMF.bind_congr_on_support
    intro front hfront
    have hlength := BitString.length_of_mem_support_uniformList hfront
    simp [PMF.map_comp, Function.comp_def, BitString.listRows_succ_append _ _ hlength]

end Cslib.ProbComp
