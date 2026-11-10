/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedTransport
import all CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedTransport

/-!
# Global size and index budgets for shared-marker graph queries

The assembled width-three queries of [ChenJiangZhu2027], Appendix D.3 (PDF p.35), replace
rather than duplicate the old suffix clauses. Each additional predicate costs at most four
linking clauses beyond its old contribution. Literal indices are checked on the whole formula.

## Main results

* `query_indices`: every literal lies below the computed declaration.
* `query_length_le`: at most four extra clauses per original vertex.
* `query_cubic_budget`: at most `6004v³` clauses, including the actual size-test gates.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

open WeightedRow

/-- The fresh suffix blocks introduce no literal outside the actual enlarged declaration. -/
theorem block_indices (x : UpperDomination.Input) (β : Bool) (w : ℕ)
    (hw : w < IndependentDomination.order (graph x)) :
    ∀ c ∈ block (context x β w), ∀ l ∈ c,
      l.1 < oldDeclaration x + IndependentDomination.order (graph x) := by
  obtain ⟨hl, hr, _, hm⟩ := context_ports x β w hw
  intro c hc l hmem
  rcases List.mem_append.mp hc with hc | hc
  · by_cases ht : (context x β w).last = true
    · cases hb : (context x β w).boundary <;>
        simp_all [parity] <;> grind
    · have hf : (context x β w).last = false := Bool.eq_false_iff.mpr ht
      have hright := hr hf
      simp_all [parity]; grind
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨lit, hlt, rfl⟩ := List.mem_map.mp hmem
      exact ((context_terms x β w hw t ht).2 lit hlt).trans_le (Nat.le_add_right _ _)
    · obtain rfl := List.mem_singleton.mp hmem
      exact hm

/-- Complete literal-index validation, including the original gates and retained prefix. -/
theorem query_indices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    ∀ c ∈ query (ofGraph G k) β, ∀ l ∈ c,
      l.1 < oldDeclaration (ofGraph G k) + n := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · have ho : c ∈ TwoBoundary.BinaryFrontend.query (Unique.build (ofGraph G k)) β := by
      rw [old_query_split]
      exact List.mem_append_left _ hc
    exact (old_query_indices G k hn β c ho l hl).trans_le (Nat.le_add_right _ _)
  · obtain ⟨w, hw, hc⟩ := List.mem_flatMap.mp hc
    exact block_indices (ofGraph G k) β w (List.mem_range.mp hw) c hc l hl

/-- Refining the actual suffix adds at most four clauses per original vertex. -/
theorem query_length_le (x : UpperDomination.Input) (β : Bool) :
    (query x β).length ≤
      (TwoBoundary.BinaryFrontend.query (Unique.build x) β).length +
        4 * IndependentDomination.order (graph x) := by
  let f (w : ℕ) := ((complete (coreInput x)).getD w []).flatMap
    (BinaryQuery.termClauses (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
      ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
      ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w))
  have hw (w : ℕ) (hw : w < IndependentDomination.order (graph x)) :
      (block (context x β w)).length ≤ (f w).length + 4 := by
    have hj : (TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w ≠ 0 := by
      have := (layout x).2.1
      omega
    have ht (t : Term ℕ) : 1 ≤ (BinaryQuery.termClauses
        (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
        ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
        ((TwoBoundary.BinaryFrontend.conditions
          (UpperDomination.build x)).length + w) t).length := by
      simp only [BinaryQuery.termClauses, hj, ↓reduceIte]
      split_ifs <;> simp
    have hlen : ((complete (coreInput x)).getD w []).length ≤ (f w).length := by
      dsimp only [f]
      generalize (complete (coreInput x)).getD w [] = ts
      induction ts with
      | nil => simp
      | cons t ts ih =>
        have := ht t
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    exact (block_length _).trans (Nat.add_le_add_right hlen 4)
  have hs (ws : List ℕ) (hws : ∀ w ∈ ws, w < IndependentDomination.order (graph x)) :
      (ws.flatMap fun w => block (context x β w)).length ≤
        (ws.flatMap f).length + 4 * ws.length := by
    induction ws with
    | nil => simp
    | cons w ws ih =>
      have h := hw w (hws w (by simp))
      have hi := ih (fun u hu => hws u (by simp [hu]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have h := hs (List.range (IndependentDomination.order (graph x)))
    (fun w hw => List.mem_range.mp hw)
  rw [old_query_split]
  simp only [query, List.length_append, List.length_range] at h ⊢
  simpa only [Nat.add_assoc] using Nat.add_le_add_left h
    ((TwoBoundary.BinaryFrontend.side (UpperDomination.build x)).length +
      (prefixClauses x β).length)

/-- The actual refined formulas meet the source's cubic clause bound, uniformly in the signed
binary threshold; gate construction is included in the old source budget. -/
theorem query_cubic_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) : (query (ofGraph G k) β).length ≤ 6004 * n ^ 3 := by
  have h := query_length_le (ofGraph G k) β
  have ho := Unique.query_cubic_budget G k hn _ _ (old_query_mem G k hn β)
  have hn3 : n ≤ n ^ 3 := Nat.le_pow (by decide : 0 < 3)
  change (query (ofGraph G k) β).length ≤
    (TwoBoundary.BinaryFrontend.query (Unique.build (ofGraph G k)) β).length + 4 * n at h
  omega

/-- Source-wide budgets of both actually emitted queries on positive graphs. -/
theorem compile_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries (compile (ofGraph G k))) :
    N = 6 * n + (CardinalityInterval.circuit n k.toNat n).size - 1 ∧
      q.length ≤ 6004 * n ^ 3 ∧ ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  have ha : auxiliary (ofGraph G k) = (CardinalityInterval.circuit n k.toNat n).size :=
    IndependentDominationInterval.auxiliary_ofGraph G k.toNat n
  have he := declaration (ofGraph G k) hn
  change oldDeclaration (ofGraph G k) + n = 6 * n + auxiliary (ofGraph G k) - 1 at he
  rw [compile_queries (ofGraph G k) hn] at hq
  change (N, q) ∈ [(6 * n + auxiliary (ofGraph G k) - 1, query (ofGraph G k) false),
    (6 * n + auxiliary (ofGraph G k) - 1, query (ofGraph G k) true)] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨by rw [ha], query_cubic_budget G k hn _, fun c hc =>
      ⟨query_width _ _ c hc, ?_⟩⟩
    rw [← he]
    exact query_indices G k hn _ c hc

end Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers
