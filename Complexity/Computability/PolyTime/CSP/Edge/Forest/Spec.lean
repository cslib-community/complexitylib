/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Forest.Agreement
public import Complexity.Computability.PolyTime.CSP.Edge.Forest.PolyTime
public import Complexity.Algorithms.Lean.EdgeCSP.Forest.Blossom
public import Complexity.Algorithms.Lean.EdgeCSP.Forest.Optimality

/-!
# Correctness of native fresh forest search

The native certificate and exact representation bridge compose with the three mathematical
fresh-search outcomes. Semantic correctness requires an edge instance, a valid initial labeling
and even delta-matroid constraints; the runtime certificate and width-only agreement do not.
This routine stops at its first event and does not implement contraction or recursive solving.
-/

public section

namespace Cslib.Complexity.CSP.EdgeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP

/-- A decoded native result has the corresponding fresh-search guarantee. Exhaustion means
optimality, augmentation removes two defects, and a blossom has valid count-preserving
preparation. The semantic hypotheses are additional to the exact-width representation guard. -/
theorem run_spec (input : Input)
    (hw : input.labels.length = (incidenceList input.body).length)
    (hF : EdgeInstance input.body)
    (hf : ValidLabeling Table.sem (EdgeAugmenting.labeling input.body input.labels))
    (hM : EdgeInstance.EvenConstraints Table.sem input.body) :
    let f := EdgeAugmenting.labeling input.body input.labels
    match (run input).bind (decode input.body) with
    | none => False
    | some (.exhausted _) => IsOptimalLabeling Table.sem f
    | some (.augment m) => m.walk.IsAugmenting Table.sem f ∧
        ValidLabeling Table.sem (m.walk.flip f) ∧
        (defects (m.walk.flip f)).card + 2 = (defects f).card
    | some (.blossom m) => ∃ b, m.blossomData = some b ∧
        b.cycle.IsBlossom Table.sem (b.prepare.flip f) ∧
        ValidLabeling Table.sem (b.prepare.flip f) ∧
        (defects (b.prepare.flip f)).card = (defects f).card := by
  dsimp only
  rw [decode_run input hw]
  cases hr : Forest.search Table.sem (EdgeAugmenting.labeling input.body input.labels) with
  | exhausted es => exact Forest.search_exhausted_isOptimalLabeling _ _ hF hf hM hr
  | augment m => exact Forest.search_augment_correct _ _ hF hf hM hr
  | blossom m => exact Forest.search_blossom_correct _ _ hF hf hM hr

end Cslib.Complexity.CSP.EdgeForest
