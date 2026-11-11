/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Operations
import Mathlib.Tactic.FinCases

/-! Trail assembly, prefix closure, and the necessary positive-prefix hypothesis. -/

namespace CslibFrontierTests.EdgeCSPWalkOperations

open Cslib.Logic.PL Cslib.Logic.PL.CSP

private abbrev F : CSP Unit ℕ := [((), [0, 1]), ((), [0, 1])]
private abbrev a : F.Occurrence := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
private abbrev b : F.Occurrence := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
private abbrev c : F.Occurrence := ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
private abbrev d : F.Occurrence := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
private abbrev p : Walk F := ⟨0, [(a, b)]⟩
private abbrev q : Walk F := ⟨1, [(c, d)]⟩

private theorem p_walk : p.IsWalk := by
  constructor
  · simp only [Walk.Linked]; decide
  · decide

private theorem q_walk : q.IsWalk := by
  constructor
  · simp only [Walk.Linked]; decide
  · decide

private theorem pq_disjoint : List.Disjoint p.edges q.edges := by
  simp [Walk.edges, Walk.edgesOf, List.disjoint_left]

example : p.reverse.start = 1 := by decide
example : p.reverse.finish = 0 := by decide
example : p.reverse.edges = [b, a] := by decide
example : p.reverse.IsWalk := p_walk.reverse
example : (p.append q).IsWalk := p_walk.append q_walk (by decide) pq_disjoint
example : (p.append q).finish = 0 := by decide

-- Endpoint linkage alone is insufficient when the incidence lists overlap.
example : ¬ (p.append p.reverse).IsWalk := by
  intro h
  have hn : ¬ (p.append p.reverse).edges.Nodup := by decide
  exact hn h.2

private def sem (_ : Unit) : List Bool → Bool
  | [x, y] => x == y
  | _ => false

private def zeroLabels : F.OccurrenceLabeling Bool := fun _ => false
private def badLabels : F.OccurrenceLabeling Bool := fun o => o.1.val == 1

private theorem closed_prefix : (p.append q).IsFPrefix sem zeroLabels := by
  refine ⟨p_walk.append q_walk (by decide) pq_disjoint, ?_, ?_⟩
  · refine ⟨Or.inr ?_, Or.inl rfl, trivial⟩
    intro ⟨o, z, _, _, hne⟩
    exact hne rfl
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i; fin_cases i <;> decide

example : ((p.append q).take 1).IsFPrefix sem zeroLabels := closed_prefix.take 1

example : ¬ Inconsistent zeroLabels ((p.append q).take 1).finish :=
  closed_prefix.not_inconsistent_finish_take (by decide) (by decide)

example : p.IsFPrefix sem badLabels := by
  refine ⟨p_walk, ⟨Or.inl rfl, trivial⟩, ?_⟩
  constructor <;> intro i <;> fin_cases i <;> decide

-- A zero-length prefix ends at the possibly defective starting variable.
example : Inconsistent badLabels (p.take 0).finish :=
  ⟨a, d, rfl, rfl, by decide⟩

example (f : F.OccurrenceLabeling Bool) : p.reverse.flip f = p.flip f :=
  p.flip_reverse f

-- Even delta-matroid constraints do not make arbitrary f-walk reversal valid.
private def reversalSem (r : Fin 3) : List Bool → Bool
  | [a, b, c, d] => r == 0 &&
      ([[false, false, false, false], [true, true, false, false],
        [true, false, true, false], [false, true, false, true],
        [true, true, true, true]].contains [a, b, c, d])
  | [a, b] => r == 1 && a == b
  | [a] => r == 2 && a
  | _ => false

private abbrev reversalInstance : CSP (Fin 3) ℕ :=
  [(0, [0, 1, 2, 3]), (1, [1, 2]), (2, [0]), (2, [3])]

private def reversalLabels : reversalInstance.OccurrenceLabeling Bool :=
  fun o => decide (2 ≤ o.1.val)

private abbrev rp (j : Fin 4) : reversalInstance.Occurrence := ⟨0, j⟩
private abbrev rq (j : Fin 2) : reversalInstance.Occurrence := ⟨1, j⟩
private abbrev reversalWalk : Walk reversalInstance :=
  ⟨0, [(rp 0, rp 1), (rq 0, rq 1), (rp 2, rp 3)]⟩

example : EdgeInstance reversalInstance := by unfold EdgeInstance; decide

example : EdgeInstance.EvenConstraints reversalSem reversalInstance := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

example : reversalWalk.IsAugmenting reversalSem reversalLabels := by
  unfold Walk.IsAugmenting Walk.IsFWalk Walk.IsFPrefix Walk.IsWalk
  simp only [Walk.Linked, Walk.InternallyConsistent, Walk.PrefixValid]
  unfold ValidLabeling
  decide

example : reversalWalk.reverse.IsWalk := by
  apply Walk.IsWalk.reverse
  constructor
  · simp only [Walk.Linked]; decide
  · decide

-- The first reversed pair would produce 0011, which the four-port relation rejects.
example : ¬ reversalWalk.reverse.IsFWalk reversalSem reversalLabels := by
  intro h
  have hv := h.1.valid_take 1 (by decide)
  have hzero := hv (0 : Fin reversalInstance.length)
  have hbad : reversalSem 0
      (localTuple ((reversalWalk.reverse.take 1).flip reversalLabels) 0) = false := by decide
  change reversalSem 0
    (localTuple ((reversalWalk.reverse.take 1).flip reversalLabels) 0) = true at hzero
  rw [hbad] at hzero
  contradiction

end CslibFrontierTests.EdgeCSPWalkOperations
