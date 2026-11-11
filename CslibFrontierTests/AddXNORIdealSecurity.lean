/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Cryptanalysis.AddXNORIdealSecurity
import CslibFrontier.Languages.Probabilistic.Norm
import Mathlib.Tactic.NormNum

/-!
# Executed cut-reveal and numerical security clients

A guessed hidden prefix endpoint triggers the actual coupling although the old fresh ledger
has no collision and covers neither hidden side. The charged reveal detects its collision.
Separate private-coin input-dependent observers instantiate the whole source decision and
repaired search bounds, without enumerating the enormous permutation space.
-/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

namespace IdealSecurityClient

/-- The first two layers use a non-self-inverse cycle; the last exchanges the two other words. -/
@[expose] def perms : Label 3 → Equiv.Perm (Fin 5) := fun (i, _) =>
  if i.val = 2 then Equiv.swap 3 4 else Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def cut : Cut (Label 3) := sourceCut (fun _ => false) 1

/-- A single guessed request to the hidden middle input, with no preceding path queries. -/
@[expose] def guess : ProbOracleComp (Spec 3 (Fin 5)) (Fin 5) :=
  ProbOracleComp.query ((1, false), .forward 1)

/-- The actual one-query state before auxiliary observations. -/
@[expose] def before : Replay.State (Label 3) (Fin 5) :=
  ⟨[⟨(1, false), .forward 1, 2⟩], [⟨((1, false), .forward 1), 2⟩], perms⟩

private theorem before_support : (2, before) ∈
    (ProbOracleComp.runWith Replay.answer guess ⟨[], [], perms⟩).support := by
  rw [guess, ProbOracleComp.runWith_query, Replay.answer]
  have hv : Family.eval perms ((1, false), .forward 1) = 2 := by decide
  rw [hv]
  simp [Ledger.update, Ledger.tables, cachedAnswer, before]

example : Forest.NoCollision {0, 4} before.records := by
  norm_num [before, Forest.NoCollision, Forest.seen, Forest.Record.known, PermQuery.argument]

private theorem old_hit : ∃ entry ∈ before.trace, cut.affected perms 0 4 entry.1 := by
  refine ⟨⟨((1, false), .forward 1), 2⟩, by simp [before], ?_⟩
  unfold Cut.affected
  decide

private theorem no_path {Index Word : Type} (records : List (Forest.Record Index Word))
    (seed : Word) (hs : ∀ r ∈ records, r.source ≠ seed) (labels : List Index) (hne : labels ≠ []) :
    ¬∃ endpoint, Forest.Follows records seed labels endpoint := by
  rintro ⟨endpoint, hp⟩
  cases hp with
  | nil => exact hne rfl
  | cons r hr tail => exact hs r hr rfl

private theorem no_old_cover :
    ¬((∃ endpoint, Forest.Follows before.records 0 (cut.left ++ [cut.edge]) endpoint) ∨
      ∃ endpoint, Forest.Follows (before.records.map Forest.Record.reverse) 4
        cut.right.reverse endpoint) := by
  apply not_or.mpr
  constructor
  · apply no_path
    · intro r hr
      simp only [before, List.mem_singleton] at hr
      subst r
      decide
    · simp
  · apply no_path
    · intro r hr
      simp only [before, List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst r
      decide
    · decide

/-- The old collision flag alone cannot upper-bound the actual cut hit. -/
example : cut.affected perms 0 4 ((1, false), .forward 1) ∧
    Forest.NoCollision {0, 4} before.records := by
  constructor
  · unfold Cut.affected
    decide
  · norm_num [before, Forest.NoCollision, Forest.seen, Forest.Record.known, PermQuery.argument]

private theorem reveal_collision (result : Fin 5 × Fin 5)
    (last : Replay.State (Label 3) (Fin 5))
    (hout : (result, last) ∈
      (ProbOracleComp.runWith Replay.answer (Reveal.cutProgram cut 0 4) before).support) :
    ¬Forest.NoCollision {0, 4} last.records := by
  have h := Reveal.cutHit_bridge cut perms 0 4 guess 2 before before_support
    result last hout old_hit
  rcases h with hc | ⟨_, hf⟩
  · exact hc
  · exact (no_old_cover hf).elim

/-- The executed auxiliary path has a supported colliding continuation. -/
example : ∃ result last,
    (result, last) ∈
      (ProbOracleComp.runWith Replay.answer (Reveal.cutProgram cut 0 4) before).support ∧
      ¬Forest.NoCollision {0, 4} last.records := by
  obtain ⟨⟨result, last⟩, hout⟩ :=
    (ProbOracleComp.runWith Replay.answer (Reveal.cutProgram cut 0 4) before).support_nonempty
  exact ⟨result, last, hout, reveal_collision result last hout⟩

/-- A large alphabet is symbolic here: the proof never enumerates its permutation family. -/
abbrev W := Fin (2 ^ 30)

/-- Private randomness chooses the operator label and the direction using the public inputs. -/
@[expose] def observe (seed target : W) : ProbOracleComp (Spec 31 W) (Bool × W) := do
  let coin ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let bit := coin.val = 0
  let reply ← ProbOracleComp.query
    ((0, decide bit), if bit then .forward seed else .inverse target)
  return (decide bit, reply)

private theorem observe_budget (seed target : W) :
    ProbOracleComp.IsQueryBounded (observe seed target) 1 := by
  have hs := ProbOracleComp.IsQueryBounded.sample (spec := Spec 31 W) (ProbComp.unifFin 1)
  have hq (coin : Fin 2) : ProbOracleComp.IsQueryBounded
      ((do
        let reply ← ProbOracleComp.query (spec := Spec 31 W)
          ((0, decide (coin.val = 0)), if coin.val = 0 then .forward seed else .inverse target)
        return (decide (coin.val = 0), reply)) : ProbOracleComp (Spec 31 W) (Bool × W)) 1 := by
    exact (ProbOracleComp.IsQueryBounded.query (spec := Spec 31 W)
      ((0, decide (coin.val = 0)), if coin.val = 0 then .forward seed else .inverse target)).bind
        (fun reply => IsCostBounded.pure (decide (coin.val = 0), reply) 0)
  simpa only [observe, Nat.zero_add] using hs.bind hq

/-- Both the bit and reply affect the decision. -/
@[expose] def decider (seed target : W) : ProbOracleComp (Spec 31 W) Bool := do
  let (bit, reply) ← observe seed target
  return bit ^^ decide (reply = target)

/-- The candidate depends on the actual private-coin observation, rather than a supplied witness. -/
@[expose] def searcher (seed target : W) : ProbOracleComp (Spec 31 W) (Operators 31) := do
  let (bit, reply) ← observe seed target
  return fun i => bit ^^ decide (i.val = reply.val % 31)

private theorem decider_budget (seed target : W) :
    ProbOracleComp.IsQueryBounded (decider seed target) 31 := by
  simpa only [decider] using (observe_budget seed target).bind fun observation =>
    IsCostBounded.pure (observation.1 ^^ decide (observation.2 = target)) 30

private theorem searcher_budget (seed target : W) :
    ProbOracleComp.IsQueryBounded (searcher seed target) 31 := by
  simpa only [searcher] using (observe_budget seed target).bind fun observation =>
    IsCostBounded.pure
      (fun i : Fin 31 => observation.1 ^^ decide (i.val = observation.2.val % 31)) 30

/-- Literal source Corollary 4 yields a nontrivial bound below one percent for this observer. -/
example : (Crypto.Game.advantage (decision true decider) (decision false decider) : ℝ) <
    1 / 100 := by
  have h := Security.source_corollary_four (q := 31) (by decide) 30 31 decider decider_budget
    (by decide) (by decide)
  norm_num at h ⊢
  linarith

/-- The repaired search endpoint also rules out one-percent success at these source parameters. -/
example : ((plantedSearch searcher) true).toReal < 1 / 100 := by
  have h := Security.source_search_bound (q := 31) (by decide) 30 31 searcher searcher_budget
    (by decide) (by decide)
  norm_num at h ⊢
  linarith

end IdealSecurityClient
