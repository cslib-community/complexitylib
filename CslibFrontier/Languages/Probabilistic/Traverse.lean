/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Data.List.Forall2

/-!
# Probabilistic list traversal

The support of ordinary `List.mapM` consists exactly of the lists whose entries are supported
by the corresponding calls. The relation also records the exact output length. These are
semantic laws; computational efficiency is provided separately in `Computability.Probabilistic`.

## Main results

* `Cslib.ProbComp.mem_support_mapM_iff`: pointwise support characterizes list traversal.
* `Cslib.ProbComp.eval_mapM_splice`: sample a designated coordinate before its surrounding
  traversal without changing the joint distribution.
-/

public section

namespace Cslib.ProbComp

/-- The support of list traversal is exactly the pointwise support of the individual calls. -/
theorem mem_support_mapM_iff {α β : Type} (program : α → ProbComp β)
    (inputs : List α) (outputs : List β) :
    outputs ∈ (eval (inputs.mapM program)).support ↔
      List.Forall₂ (fun a b => b ∈ (eval (program a)).support) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons a inputs ih =>
    cases outputs with
    | nil => simp [List.mapM_cons]
    | cons b outputs =>
      simp only [PMF.mem_support_iff] at ih
      simp [List.mapM_cons, ih, and_comm]

/-- Sampling a designated coordinate before its prefix and suffix preserves the full traversal
law. The three computations use independent randomness, and the returned order is unchanged. -/
theorem eval_mapM_splice {α β : Type} (program : α → ProbComp β)
    (before : List α) (middle : α) (after : List α) :
    eval (do
      let challenge ← program middle
      let front ← before.mapM program
      let back ← after.mapM program
      pure (front ++ challenge :: back)) =
        eval ((before ++ middle :: after).mapM program) := by
  simp only [List.mapM_append, List.mapM_cons, eval_bind, eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  exact PMF.bind_comm _ _ _

end Cslib.ProbComp
