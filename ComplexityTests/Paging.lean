/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.Algorithms.Lean.Paging.LRU
public import Complexity.Algorithms.Lean.Paging.LowerBound
import Mathlib.Data.List.FinRange

/-!
# Tests for Online Competitive Analysis and Paging

Concrete evaluations, tight adversarial sequences, history-strategy instantiation, and non-vacuity
checks for `Complexity.Algorithms.Lean.Online.Basic`, `Complexity.Algorithms.Lean.Paging.Basic`,
`Complexity.Algorithms.Lean.Paging.LRU`, and `Complexity.Algorithms.Lean.Paging.LowerBound`.
-/

@[expose] public section

namespace ComplexityTests.Paging

open Cslib.Algorithms.Lean.Online Cslib.Algorithms.Lean.Paging

/-! ### Computable LRU recency-list execution and recency promotion -/

/-- Accessing page `1` on `[2, 1]` promotes `1` to MRU so the next miss on `3` evicts `2`, not
`1`. -/
example : lruRun 2 [2, 1] [1, 3] = [3, 1] := by decide

/-- Fault count on a textbook capacity-`3` trace from empty cache:
`[1, 2, 3]` (3 warmup misses), `2` (hit, promoted), `4` (miss, evicts `1`), `1` (miss, evicts `3`),
`2` (hit), `4` (hit) — total `5` faults. -/
example : lruFaults 3 ([] : List Nat) [1, 2, 3, 2, 4, 1, 2, 4] = 5 := by decide

/-- Final recency order `[4, 2, 1]` (most-recently-used first) on the same trace. -/
example : lruRun 3 ([] : List Nat) [1, 2, 3, 2, 4, 1, 2, 4] = [4, 2, 1] := by decide

/-! ### Concrete tight `k`-competitive witness (`lruFaults = k * optFaults`) -/

private def cyclicReqs : List Nat := [2, 0, 1, 2, 0, 1]

private def cyclicOffStates : List (Finset Nat) :=
  offlineLookahead 2 0 [0, 1, 2] ({0, 1} : Finset Nat) cyclicReqs

/-- Starting from warm recency list `[1, 0]` (`{0, 1}`, with `0` least recently used), cyclic
requests `[2, 0, 1, 2, 0, 1]` force LRU to fault on all `6` steps (`k * 3 = 6`). -/
example : lruFaults 2 [1, 0] cyclicReqs = 6 := by decide

/-- `offlineLookahead` produces a valid demand-paging schedule on `cyclicReqs`. -/
example : (problem Nat 2).ValidSchedule ({0, 1} : Finset Nat) cyclicReqs cyclicOffStates :=
  validSchedule_offlineLookahead (by omega) 0 (by decide) rfl cyclicReqs
    (by decide) (by decide) (by decide)

/-- Meanwhile, `offlineLookahead` starting from the identical cache `{0, 1}` incurs only `3`
faults (`6 = 2 * 3`, witnessing exact tightness of the `k`-competitive bound with zero additive
slack). -/
example : (problem Nat 2).scheduleCost ({0, 1} : Finset Nat) cyclicReqs cyclicOffStates = 3 := by
  decide

/-! ### Non-LRU deterministic strategy via `DetStrategy.ofHistory` -/

/-- A simple computable eviction rule over `Fin (k + 1)`: hits keep `s` unchanged, non-full misses
insert `p`, and full misses evict the least-index resident page via `List.find?`. -/
def minIndexNext (k : Nat) (s : Finset (Fin (k + 1))) (p : Fin (k + 1)) :
    Finset (Fin (k + 1)) :=
  if p ∈ s then s
  else if s.card < k then insert p s
  else
    match (List.finRange (k + 1)).find? (· ∈ s) with
    | some e => insert p (s.erase e)
    | none => insert p s

private theorem validStep_minIndexNext {k : Nat} (hk : 0 < k) {s : Finset (Fin (k + 1))}
    (hs : s.card ≤ k) (p : Fin (k + 1)) :
    ValidStep k s p (minIndexNext k s p) := by
  unfold minIndexNext
  split
  · next hp => exact validStep_hit hs hp
  · next hp =>
    split
    · next hlt => exact validStep_insert hlt hp
    · next hlt =>
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hne
      cases hfind : (List.finRange (k + 1)).find? (· ∈ s) with
      | some e =>
        have he : e ∈ s := by
          simpa only [decide_eq_true_eq] using List.find?_some hfind
        exact validStep_replace hs hp he
      | none =>
        have hfalse := List.find?_eq_none.mp hfind x (List.mem_finRange x)
        simp only [hx, decide_true, not_true_eq_false] at hfalse

/-- History-packaged deterministic strategy using `minIndexNext`. -/
def minIndexStrategy (k : Nat) (hk : 0 < k) : DetStrategy (problem (Fin (k + 1)) k) :=
  DetStrategy.ofHistory (fun _ _ s p => minIndexNext k s p)
    fun {s₀ _ s} r hs₀ ⟨states, hv, hf⟩ => by
      subst s
      exact validStep_minIndexNext hk (validCache_finalState hs₀ hv) r

/-- Computable adversarial witness against `minIndexStrategy 2`: over `6` requests from `∅`,
`adversaryRequests` forces all `6` steps to fault! -/
example :
    (minIndexStrategy 2 (by omega)).cost ∅
      (adversaryRequests 0 (List.finRange 3) (minIndexStrategy 2 (by omega)) ∅ 6) = 6 := by
  decide

/-- Refutation of `(1, b)`-competitiveness for `minIndexStrategy 2` from empty cache `∅`. -/
example (b : Nat) : ¬ (minIndexStrategy 2 (by omega)).IsCompetitiveFrom ∅ 1 b :=
  fin_not_isCompetitiveFrom_empty_of_lt (by omega) (minIndexStrategy 2 (by omega)) (by omega) b

/-! ### Tightness and non-vacuity synthesis for `lruStrategy` -/

/-- For every positive cache capacity `k`, `lruStrategy` over `Fin (k + 1)` simultaneously:
1. achieves exact `(k, 0)`-competitiveness from any common valid initial cache,
2. achieves `(k, k)`-competitiveness across arbitrary valid initial caches, and
3. cannot be `(k - 1, b)`-competitive (even from `∅`) for any additive constant `b`. -/
theorem lru_tight_competitive_ratio (k : Nat) (hk : 0 < k) (b : Nat) :
    (lruStrategy (α := Fin (k + 1)) k hk).IsCompetitive k 0 ∧
      (lruStrategy (α := Fin (k + 1)) k hk).IsCompetitiveAnyInit k k ∧
      ¬ (lruStrategy (α := Fin (k + 1)) k hk).IsCompetitiveFrom ∅ (k - 1) b :=
  ⟨lruStrategy_isCompetitive k hk,
    lruStrategy_isCompetitiveAnyInit k hk,
    fin_not_isCompetitiveFrom_empty_of_lt hk (lruStrategy k hk) (by omega) b⟩

/-- Even at `k = 1`, no deterministic online paging strategy over `Fin 2` can achieve competitive
ratio `99 / 100 < 1` from `∅`, for any additive constant `b`. -/
example (A : DetStrategy (problem (Fin 2) 1)) (b : Nat) :
    ∃ reqs offStates,
      (problem (Fin 2) 1).ValidSchedule ∅ reqs offStates ∧
        99 * (problem (Fin 2) 1).scheduleCost ∅ reqs offStates + b < 100 * A.cost ∅ reqs :=
  fin_exists_ratio_violation_empty_of_lt (by omega) A (by omega) b

end ComplexityTests.Paging
