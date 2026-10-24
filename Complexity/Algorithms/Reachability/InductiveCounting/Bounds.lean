/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting.Completeness
import Mathlib.Tactic.Ring

/-!
# Uniform bounds for the inductive-counting controller

Every branch halts in `O((N + 1)^4 * (width + 1))` instructions. Every register remains below
`N + 2^width + width + 2`, independently of the graph and the choices. A binary encoding of the
fixed register tuple therefore uses `O(log N + width)` bits when the width is chosen to encode
vertex identifiers.

## Main definitions

* `Cslib.InductiveCounting.budget`: the uniform polynomial instruction budget.

## Main results

* `Cslib.InductiveCounting.halted_replay_budget`: a uniform all-branch time bound.
* `Cslib.InductiveCounting.query_bounds`: legitimate queries use valid vertex identifiers.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Cslib.InductiveCounting

variable {N width source : ℕ} {edge : ℕ → ℕ → Bool} {bad : ℕ → Bool} {s : State} {q : Query}

/-- A uniform polynomial instruction budget. The width counts binary choices per vertex. -/
def budget (N width : ℕ) : ℕ := 16 * (N + 1) ^ 4 * (width + 1)

private theorem rank_initial (hsource : source < N) :
    rank N width (initial N source) = N * roundCost N width + 1 := by
  simp [initial, hsource, rank]

private theorem rank_initial_le_budget : rank N width (initial N source) ≤ budget N width := by
  by_cases hs : source < N
  · rw [rank_initial hs]
    calc
      N * roundCost N width + 1 ≤ N * roundCost N width + 1 +
          ((15 * N ^ 4 + 62 * N ^ 3 + 95 * N ^ 2 + 64 * N + 16) * width +
            13 * N ^ 4 + 54 * N ^ 3 + 79 * N ^ 2 + 52 * N + 15) := Nat.le_add_right _ _
      _ = budget N width := by
        simp only [budget, roundCost, targetCost, candidateCost]
        ring
  · simp [initial, hs, rank, reject]

/-- Every branch, including every dishonest branch, halts within the polynomial budget. -/
theorem halted_replay_budget (bs : List Bool) (hb : budget N width ≤ bs.length) :
    halted (replay N width source edge bad (initial N source) bs) = true :=
  halted_replay_of_rank_le bs (rank_initial_le_budget.trans hb)

/-- All registers of all choice prefixes satisfy the uniform bound. -/
theorem bounded_replay_initial (bs : List Bool) :
    Bounded N width (replay N width source edge bad (initial N source) bs) :=
  bounded_replay bounded_initial bs

/-- Honest acceptance needs no more choices than the all-branch instruction budget. -/
theorem accepts_complete_bounded (hsource : source < N) (hwidth : N ≤ 2 ^ width)
    (hsafe : Safe N source edge bad) :
    ∃ bs, bs.length ≤ budget N width ∧
      (replay N width source edge bad (initial N source) bs).phase = .accept := by
  obtain ⟨bs, hbs⟩ := accepts_complete hsource hwidth hsafe
  by_cases hlen : bs.length ≤ budget N width
  · exact ⟨bs, hlen, hbs⟩
  · have htlen : (bs.take (budget N width)).length = budget N width := by
      simp only [List.length_take]
      omega
    have hh := halted_replay_budget (N := N) (width := width) (source := source)
      (edge := edge) (bad := bad)
      (bs.take (budget N width)) (by omega)
    have he := replay_append (N := N) (width := width) (source := source) (edge := edge)
      (bad := bad) (s := initial N source) (bs.take (budget N width)) (bs.drop (budget N width))
    rw [List.take_append_drop, replay_halted hh] at he
    exact ⟨bs.take (budget N width), htlen.le, he ▸ hbs⟩

/-- Queries made along a semantically valid run use identifiers in the vertex interval. -/
theorem query_bounds (hsource : source < N) (hi : Invariant N edge bad source s)
    (hq : query s = some q) :
    match q with
    | .edge u v => u < N ∧ v < N
    | .bad u => u < N := by
  cases hp : s.phase <;> simp only [query, hp] at hq
  all_goals try contradiction
  case edge =>
    cases hq
    simp only [Invariant, hp] at hi
    exact ⟨within_lt hsource ((mem_roundSet hsource).mp hi.2.2.2.2.2.1), hi.2.2.2.2.2.2⟩
  case observe =>
    simp only [Invariant, hp] at hi
    obtain ⟨⟨_, hm⟩, _, hu, _⟩ := hi
    cases hf : s.finalScan <;> simp only [hf, Bool.false_eq_true, ↓reduceIte] at hq hm
    · cases hq
      exact ⟨hu, hm.2.1⟩
    · cases hq
      exact hu

end Cslib.InductiveCounting
