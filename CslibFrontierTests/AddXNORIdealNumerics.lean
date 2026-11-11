/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Cryptanalysis.AddXNORIdealCollisions
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Actual fresh-ledger collision and forest-covering clients

The examples distinguish cache hits from fresh collisions, include inverse queries and
coincident public roots, and instantiate the numerical bound with a private-coin observer.
The final bound concerns the proved analysis event, not the still-open security inequality.
-/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

namespace IdealNumericsClient

/-- A collision-free two-branch forest, with different independent permutation labels. -/
@[expose] def fork : List (Forest.Record (Label 1) (Fin 5)) :=
  [⟨(0, true), .forward 0, 2⟩, ⟨(0, false), .forward 0, 1⟩]

example : Forest.NoCollision {0, 4} fork := by
  norm_num [Forest.NoCollision, Forest.seen, Forest.Record.known, PermQuery.argument, fork]

example : Forest.paths 0 fork 1 = some [(0, false)] ∧
    Forest.paths 0 fork 2 = some [(0, true)] := by decide

example : (Forest.covered fork 0 (Forest.binaryLabels (fun i : Fin 1 => i))).card ≤ 2 := by
  exact Forest.covered_card_le {0, 4} 0 (by decide) fork (by
      norm_num [Forest.NoCollision, Forest.seen, Forest.Record.known,
      PermQuery.argument, fork])
    (Forest.binaryLabels _) (Forest.binaryLabels_injective _) (fun word => by
      intro heq
      have hlen := congrArg List.length heq
      simp [Forest.binaryLabels] at hlen)

example : Forest.Follows fork 0 [(0, true)] 2 :=
  Forest.paths_sound 0 fork (by simp [Forest.paths, fork])

/-- A new inverse answer creates a predecessor, not a path from the existing root. -/
example : Forest.NoCollision {0, 4}
    ([⟨(), .inverse 2, 1⟩] : List (Forest.Record Unit (Fin 5))) ∧
    Forest.paths 0 ([⟨(), .inverse 2, 1⟩] : List (Forest.Record Unit (Fin 5))) 1 = none := by
  norm_num [Forest.NoCollision, Forest.seen, Forest.Record.known, PermQuery.argument,
    Forest.paths]

/-- An inverse cache hit records nothing new and must not trigger the fresh-collision flag. -/
example : Ledger.update ((), .inverse (1 : Fin 5)) 0 [⟨(), .forward 0, 1⟩] =
    [⟨(), .forward 0, 1⟩] := by
  simp [Ledger.update, Ledger.tables, Forest.Record.entry, PermQuery.toCacheEntry,
    cachedAnswer, invLookup]

example : ¬Forest.NoCollision {0}
    ([⟨(), .forward 1, 0⟩] : List (Forest.Record Unit (Fin 5))) := by
  norm_num [Forest.NoCollision, Forest.seen, Forest.Record.known, PermQuery.argument]

example {Index Word : Type} [DecidableEq Word] (seed : Word)
    (rows : List (Forest.Record Index Word)) (hc : Forest.NoCollision {seed} rows)
    (labels : List Index) (hn : labels ≠ []) : ¬Forest.Follows rows seed labels seed :=
  Forest.no_nonempty_initial_path {seed} seed (Finset.mem_singleton_self _) rows hc
    (Finset.mem_singleton_self _) hn

/-- A fair private coin chooses a forward or inverse request to one real permutation. -/
@[expose] def observer : ProbOracleComp (Spec 9 (Fin 16384)) Bool := do
  let bit ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let reply ← ProbOracleComp.query
    ((0, false), if bit.val = 0 then .forward 0 else .inverse 1)
  return decide (reply = 1)

private theorem observer_budget : ProbOracleComp.IsQueryBounded observer 9 := by
  have hs := ProbOracleComp.IsQueryBounded.sample (spec := Spec 9 (Fin 16384))
    (ProbComp.unifFin 1)
  simpa only [observer, Nat.zero_add, Nat.add_zero] using hs.bind fun bit =>
    (ProbOracleComp.IsQueryBounded.query
      ((0, false), if bit.val = 0 then .forward 0 else .inverse (1 : Fin 16384))).bind
        fun reply => IsCostBounded.pure (decide (reply = (1 : Fin 16384))) 8

/-- Inside the source range `q=9`, `h=5`, `T=9`, `m=14`, the collision allowance is
`81/2048` and the combined allowance is `1809/2048`, both below one. -/
example : ((ProbOracleComp.runWith Ledger.answer observer []).toOuterMeasure
    {out | ¬Forest.NoCollision {0, 1} out.2}).toReal ≤ (81 / 2048 : ℝ) := by
  have h := Collisions.source_collision_le_eight 14 0 9 0 1 (by decide) (by decide)
    (by decide) observer (by simpa using observer_budget)
  norm_num at h ⊢
  exact h

example : ((Collisions.collisionOrCovered 0 1 (fun i : Fin 5 => i.castLE (by decide))
    (fun i : Fin 4 => (i.rev.natAdd 5 : Fin 9)) observer).toOuterMeasure {true}).toReal ≤
    1809 / 2048 := by
  have h := Collisions.source_forest_bound (q := 9) (h := 5) (d := 4) (by decide)
    (by decide) (Or.inr rfl) 14 9 0 1 (fun i => i.castLE (by decide)) (fun i => i.rev.natAdd 5)
    (by decide) (by decide) observer observer_budget
  norm_num at h ⊢
  exact h

end IdealNumericsClient
