/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib Data/List/Basic)

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic
public import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Dense first-occurrence names under one-point identification

On occurring names, updating the dense name of `b` to that of `a` has exactly the kernel of
updating the original identity at `b` to `a`. The list may repeat elements; neither selected
point is required to occur. The explicit membership hypotheses apply only to the compared
names. This original identity supports actual incidence vertex-identification transport.
-/

public section

namespace List

/-- Dense and original one-point identifications equate precisely the same occurring names.
Repeated elements and arbitrary selected names outside the list are permitted. -/
theorem idxOf_update_id_eq_iff {α : Type*} [DecidableEq α] (l : List α) (a b x y : α)
    (hx : x ∈ l) (hy : y ∈ l) :
    Function.update id (l.idxOf b) (l.idxOf a) (l.idxOf x) =
        Function.update id (l.idxOf b) (l.idxOf a) (l.idxOf y) ↔
      Function.update id b a x = Function.update id b a y := by
  rw [Function.update_id_apply_eq_iff, Function.update_id_apply_eq_iff]
  simp only [List.idxOf_inj hx, List.idxOf_inj hy]

end List
