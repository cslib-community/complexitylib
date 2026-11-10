/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.List.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Bertsekas's auction algorithm for the assignment problem

This module implements the Gauss–Seidel auction algorithm of [Bertsekas1979] and [Bertsekas1988]
for the square, complete assignment problem with integer costs `c : Fin n × Fin n → ℤ`, and proves
its correctness: `ε`-complementary slackness is invariant, the algorithm terminates within an
explicit pseudo-polynomial number of bids, its output is within `n * ε` of optimal, and it is
exactly optimal when the costs are scaled by `n + 1` and `ε = 1`.

## Algorithm

The state (`AuctionState`) records the owner of each object, integer object prices, a stack of
unassigned persons and a bid counter. Starting from the empty assignment and zero prices
(`auctionInit`), each step (`bidStep`) lets the unassigned person `i` on top of the stack bid:

* `i` picks an object `j` of least reduced cost `v = c (i, j) + p j` (`bestObject`, the first
  minimiser), and the second least reduced cost `w` over the objects `k ≠ j` (`secondBest`);
* the price of `j` rises to `w - c (i, j) + ε`, i.e. by `w - v + ε ≥ ε` (`bidPrice`; if `n = 1`
  there is no second object and the price rises by `ε`);
* `j` is assigned to `i`, and its previous owner (if any) is pushed onto the stack.

This is the cost form (`c = -a`) of [Bertsekas1998], §7.1.1, (7.2)–(7.5), with bidding set `I` a
single unassigned person (the Gauss–Seidel version). Bertsekas sets `w = -∞` (in benefit form)
when the bidder has a single object; we raise the price by `ε` instead, which also preserves
`ε`-complementary slackness. The loop (`auctionLoop`) runs until the stack is empty, with fuel
`bidBound n (costSpread c) ε` computed from the data (`auction`).

## Cost model and limitations

* The resource measure is the **number of bids** (`AuctionState.bids`); each bid scans the `n`
  objects, which is not charged. There is no `TimeM` accounting here.
* The bid bound `bids_auction_le` is pseudo-polynomial: at most `n (C + ε) / ε + 1` bids when every
  row has cost range at most `C`; it comes from the measure `n (C + ε) - ∑ j, p j`, which every bid
  lowers by at least `ε` and which stays nonnegative while some person is unassigned. With an
  `O(n)` scan per bid this gives `O(n² C / ε)` operations, consistent with (and, on complete
  instances with `A = n²` arcs, sharper than) the pure (unscaled) auction's `O(n A C / ε)` running
  time of [Bertsekas1988], §1. There `C = max |a i j|`; here `C` bounds the row cost ranges, so
  `C = 2 max |c (i, j)|` is always admissible. The `ε`-scaling version and its
  `O(n A log (n C))` bound ([Bertsekas1998], Prop. 7.3) are not formalized.
* Integer costs and prices, complete bipartite instances (every person may take every object),
  and square instances (`n` persons, `n` objects) only. The Jacobi (parallel bidding), reverse and
  asymmetric auctions of [Bertsekas1998], §7.1–7.2 are not covered.

## Main definitions

* `AuctionState`, `bestObject`, `secondBest`, `bidPrice`, `bidStep`, `auctionInit`, `auctionLoop`:
  the auction as a Lean program.
* `bidBound`, `costSpread`, `auction`: the fuel bound and the complete algorithm.
* `auctionPerm c hε`: the computed assignment, as a permutation of `Fin n`.
* `scaledAuction c`, `scaledAuctionPerm c`: the exact auction, run on `(n + 1) • c` with `ε = 1`,
  and its assignment.
* `AuctionInv`: the invariant (partial matching, exact free list, unassigned objects at price `0`,
  `ε`-complementary slackness).

## Main results

* `AuctionInv.bidStep`: a bid preserves the invariant, in particular `ε`-complementary slackness
  ([Bertsekas1998], Prop. 7.1).
* `sum_price_bidStep`, `AuctionInv.price_le`: the termination measure.
* `auction_free`, `bids_auction_le`: termination with a complete assignment within
  `bidBound n C ε` bids ([Bertsekas1998], Prop. 7.2, with an explicit bound).
* `isEpsCompSlack_auctionPerm`, `sum_auctionPerm_le`, `sum_auctionPerm_le_rowPotential`: the output
  satisfies `ε`-complementary slackness with the final prices, costs at most `n * ε` more than every
  assignment, and the final prices give a dual certificate of this ([Bertsekas1998], Props. 1.4
  and 7.2).
* `sum_scaledAuctionPerm_le`, `bids_scaledAuction_le`: exact optimality for integer costs after
  scaling by `n + 1` with `ε = 1` ([Bertsekas1988], §3; [Bertsekas1998], §7.1.4), within
  `n ((n + 1) C + 1) + 1` bids.

## References

* [Bertsekas1979]
* [Bertsekas1988]
* [Bertsekas1998]
-/

public section

namespace Cslib.Algorithms.Lean.Assignment

open Finset

/-! ### The auction algorithm -/

/-- State of the Gauss–Seidel auction: the current owner of each object (if any), object
prices, the stack of unassigned persons (the next bidder first), and the number of bids so far. -/
structure AuctionState (n : ℕ) where
  /-- `owner j` is the person currently assigned object `j`, if any. -/
  owner : Fin n → Option (Fin n)
  /-- `price j` is the current price of object `j`. -/
  price : Fin n → ℤ
  /-- The unassigned persons; the head bids next. -/
  free : List (Fin n)
  /-- The number of bids made so far. -/
  bids : ℕ

variable {n : ℕ}

/-- Reduced cost `c (i, j) + p j` of object `j` for person `i` at prices `p`. -/
@[expose] def redCost (c : Fin n × Fin n → ℤ) (p : Fin n → ℤ) (i j : Fin n) : ℤ :=
  c (i, j) + p j

/-- A best object for person `i`: the first object of least reduced cost. -/
@[expose] def bestObject (c : Fin n × Fin n → ℤ) (p : Fin n → ℤ) (i : Fin n) : Option (Fin n) :=
  (List.finRange n).argmin (redCost c p i)

/-- The least reduced cost for person `i` among objects other than `j` (`none` if `n = 1`). -/
@[expose] def secondBest (c : Fin n × Fin n → ℤ) (p : Fin n → ℤ) (i j : Fin n) : Option ℤ :=
  (((List.finRange n).filter fun k => decide (k ≠ j)).map (redCost c p i)).min?

/-- The bid of person `i` for its best object `j`: the price `w - c (i, j) + ε` at which `j`'s
reduced cost becomes `ε` more than the second least reduced cost `w`, i.e. `p j + (w - v) + ε`
where `v` is the least reduced cost ([Bertsekas1998], (7.4)); `p j + ε` if `j` is the only
object. -/
@[expose] def bidPrice (c : Fin n × Fin n → ℤ) (ε : ℤ) (p : Fin n → ℤ) (i j : Fin n) : ℤ :=
  match secondBest c p i j with
  | some w => w - c (i, j) + ε
  | none => p j + ε

/-- One bid: the first unassigned person `i` bids for its best object `j`, raising its price to
`bidPrice`; `j` is assigned to `i` and its previous owner (if any) becomes unassigned. A state
with no unassigned person is fixed. -/
@[expose] def bidStep (c : Fin n × Fin n → ℤ) (ε : ℤ) (s : AuctionState n) : AuctionState n :=
  match s.free with
  | [] => s
  | i :: rest =>
    match bestObject c s.price i with
    | none => s
    | some j =>
      { owner := Function.update s.owner j (some i)
        price := Function.update s.price j (bidPrice c ε s.price i j)
        free := (s.owner j).toList ++ rest
        bids := s.bids + 1 }

/-- The initial state: nothing assigned, all prices `0`. -/
@[expose] def auctionInit (n : ℕ) : AuctionState n :=
  ⟨fun _ => none, fun _ => 0, List.finRange n, 0⟩

/-- Run at most `fuel` bids, stopping as soon as every person is assigned. -/
@[expose] def auctionLoop (c : Fin n × Fin n → ℤ) (ε : ℤ) : ℕ → AuctionState n → AuctionState n
  | 0, s => s
  | fuel + 1, s =>
    match s.free with
    | [] => s
    | _ :: _ => auctionLoop c ε fuel (bidStep c ε s)

/-- The bid bound `n (C + ε) / ε + 1` for a row cost range `C`. -/
@[expose] def bidBound (n : ℕ) (C ε : ℤ) : ℕ := n * (C + ε).toNat / ε.toNat + 1

/-- A computable bound on the row cost ranges: `2 ∑ᵢ ∑ⱼ |c (i, j)|` bounds every
`c (i, k) - c (i, j)` (`sub_le_costSpread`). -/
@[expose] def costSpread (c : Fin n × Fin n → ℤ) : ℤ := 2 * ∑ i, ∑ j, |c (i, j)|

/-- **The auction algorithm** with bidding increment `ε`, run for `bidBound n (costSpread c) ε`
bids, which suffices for termination when `0 < ε` (`auction_free`). -/
@[expose] def auction (c : Fin n × Fin n → ℤ) (ε : ℤ) : AuctionState n :=
  auctionLoop c ε (bidBound n (costSpread c) ε) (auctionInit n)

/-- The object of person `i` in a state (`i` itself if `i` is unassigned). -/
@[expose] def AuctionState.objectOf (s : AuctionState n) (i : Fin n) : Fin n :=
  ((List.finRange n).find? fun j => decide (s.owner j = some i)).getD i

/-- The owner of object `j` in a state (`j` itself if `j` is unassigned). -/
@[expose] def AuctionState.personOf (s : AuctionState n) (j : Fin n) : Fin n :=
  (s.owner j).getD j

/-! ### The invariant -/

/-- Invariant of the auction ([Bertsekas1998], §7.1.1): the owner table is a partial matching,
the stack of unassigned persons is exact and duplicate-free, unassigned objects keep price `0`,
and every assigned pair satisfies `ε`-complementary slackness (7.1). -/
structure AuctionInv (c : Fin n × Fin n → ℤ) (ε : ℤ) (s : AuctionState n) : Prop where
  /-- No person owns two objects. -/
  owner_inj : ∀ j j' i, s.owner j = some i → s.owner j' = some i → j = j'
  /-- The stack of unassigned persons has no duplicates. -/
  free_nodup : s.free.Nodup
  /-- The stack lists exactly the persons owning no object. -/
  mem_free : ∀ i, i ∈ s.free ↔ ∀ j, s.owner j ≠ some i
  /-- Objects never bid for keep their initial price `0`. -/
  price_unowned : ∀ j, s.owner j = none → s.price j = 0
  /-- `ε`-complementary slackness for every assigned pair. -/
  epsCS : ∀ j i, s.owner j = some i → ∀ k, c (i, j) + s.price j ≤ c (i, k) + s.price k + ε

variable {c : Fin n × Fin n → ℤ} {ε : ℤ}

/-- The initial state satisfies the invariant. -/
theorem auctionInv_init : AuctionInv c ε (auctionInit n) where
  owner_inj _ _ _ h := by simp [auctionInit] at h
  free_nodup := List.nodup_finRange n
  mem_free i := by simp [auctionInit]
  price_unowned _ _ := rfl
  epsCS _ _ h := by simp [auctionInit] at h

private theorem secondBest_some {p : Fin n → ℤ} {i j : Fin n} {w : ℤ}
    (h : secondBest c p i j = some w) :
    (∀ k, k ≠ j → w ≤ redCost c p i k) ∧ ∃ k, k ≠ j ∧ redCost c p i k = w := by
  rw [secondBest, List.min?_eq_some_iff] at h
  obtain ⟨hmem, hle⟩ := h
  refine ⟨fun k hk => hle _ ?_, ?_⟩
  · exact List.mem_map.2 ⟨k, List.mem_filter.2 ⟨List.mem_finRange k, by simpa using hk⟩, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hmem
    exact ⟨k, by simpa using (List.mem_filter.1 hk).2, rfl⟩

private theorem secondBest_none {p : Fin n → ℤ} {i j : Fin n}
    (h : secondBest c p i j = none) (k : Fin n) : k = j := by
  rw [secondBest, List.min?_eq_none_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  by_contra hk
  exact h k (List.mem_finRange k) (by simpa using hk)

/-- A bid raises the price of a best object by at least `ε`. -/
theorem le_bidPrice {p : Fin n → ℤ} {i j : Fin n} (hj : ∀ k, redCost c p i j ≤ redCost c p i k) :
    p j + ε ≤ bidPrice c ε p i j := by
  unfold bidPrice
  split
  · rename_i w hw
    obtain ⟨-, k, -, hk⟩ := secondBest_some hw
    have := hj k
    simp only [redCost] at this hk
    omega
  · exact le_rfl

/-- After the bid, the object bid for is within `ε` of every other object. -/
theorem bidPrice_epsCS {p : Fin n → ℤ} {i j : Fin n} (k : Fin n) (hk : k ≠ j) :
    c (i, j) + bidPrice c ε p i j ≤ c (i, k) + p k + ε := by
  unfold bidPrice
  split
  · rename_i w hw
    have := (secondBest_some hw).1 k hk
    simp only [redCost] at this
    omega
  · rename_i hw
    exact absurd (secondBest_none hw k) hk

/-- A state with no unassigned person is fixed by `bidStep`. -/
theorem bidStep_nil {s : AuctionState n} (hs : s.free = []) : bidStep c ε s = s := by
  unfold bidStep
  rw [hs]

/-- Unfolding one bid of the person `i` on top of the stack: it bids for a best object `j`. -/
theorem bidStep_cons {s : AuctionState n} {i : Fin n} {rest : List (Fin n)}
    (hs : s.free = i :: rest) :
    ∃ j, (∀ k, redCost c s.price i j ≤ redCost c s.price i k) ∧
      bidStep c ε s =
        { owner := Function.update s.owner j (some i)
          price := Function.update s.price j (bidPrice c ε s.price i j)
          free := (s.owner j).toList ++ rest
          bids := s.bids + 1 } := by
  have hne : List.finRange n ≠ [] := List.ne_nil_of_mem (List.mem_finRange i)
  obtain ⟨j, hj⟩ : ∃ j, bestObject c s.price i = some j :=
    Option.ne_none_iff_exists'.1 (by rw [Ne, bestObject, List.argmin_eq_none]; exact hne)
  refine ⟨j, fun k => List.le_of_mem_argmin (List.mem_finRange k) hj, ?_⟩
  unfold bidStep
  rw [hs]
  simp only [hj]

/-- A bid preserves the invariant; in particular it preserves `ε`-complementary slackness
([Bertsekas1998], Prop. 7.1). -/
theorem AuctionInv.bidStep {s : AuctionState n} (hε : 0 ≤ ε) (h : AuctionInv c ε s) :
    AuctionInv c ε (bidStep c ε s) := by
  rcases hs : s.free with _ | ⟨i, rest⟩
  · rw [bidStep_nil hs]; exact h
  obtain ⟨j, hj, heq⟩ := bidStep_cons (c := c) (ε := ε) hs
  rw [heq]
  have hi : ∀ j, s.owner j ≠ some i := (h.mem_free i).1 (hs ▸ List.mem_cons_self ..)
  have hnd := h.free_nodup
  rw [hs, List.nodup_cons] at hnd
  have hup : ∀ k, s.price k ≤ Function.update s.price j (bidPrice c ε s.price i j) k := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      have := le_bidPrice (ε := ε) hj
      omega
    · rw [Function.update_of_ne hk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro j₁ j₂ i' h₁ h₂
    by_cases e₁ : j₁ = j <;> by_cases e₂ : j₂ = j
    · rw [e₁, e₂]
    · rw [e₁, Function.update_self] at h₁
      rw [Function.update_of_ne e₂] at h₂
      cases h₁
      exact absurd h₂ (hi j₂)
    · rw [e₂, Function.update_self] at h₂
      rw [Function.update_of_ne e₁] at h₁
      cases h₂
      exact absurd h₁ (hi j₁)
    · rw [Function.update_of_ne e₁] at h₁
      rw [Function.update_of_ne e₂] at h₂
      exact h.owner_inj j₁ j₂ i' h₁ h₂
  · rcases ho : s.owner j with _ | i'
    · simpa using hnd.2
    · simp only [Option.toList_some, List.singleton_append, List.nodup_cons]
      refine ⟨fun hmem => ?_, hnd.2⟩
      have : i' ∈ s.free := hs ▸ List.mem_cons_of_mem _ hmem
      exact (h.mem_free i').1 this j ho
  · intro x
    simp only [List.mem_append, Option.mem_toList]
    constructor
    · rintro (hx | hx) j'
      · -- `x` was the previous owner of `j`
        have hxi : x ≠ i := fun e => hi j (e ▸ hx)
        by_cases e : j' = j
        · rw [e, Function.update_self]
          exact fun h' => hxi (Option.some_injective _ h').symm
        · rw [Function.update_of_ne e]
          exact fun h' => e (h.owner_inj j' j x h' hx)
      · have hxi : x ≠ i := fun e => hnd.1 (e ▸ hx)
        have hfree : ∀ j, s.owner j ≠ some x := (h.mem_free x).1 (hs ▸ List.mem_cons_of_mem _ hx)
        by_cases e : j' = j
        · rw [e, Function.update_self]
          exact fun h' => hxi (Option.some_injective _ h').symm
        · rw [Function.update_of_ne e]
          exact hfree j'
    · intro hx
      have hxi : x ≠ i := fun e => hx j (by rw [Function.update_self, e])
      by_cases ho : s.owner j = some x
      · exact Or.inl ho
      · right
        have : ∀ j', s.owner j' ≠ some x := by
          intro j'
          by_cases e : j' = j
          · exact e ▸ ho
          · have := hx j'
            rwa [Function.update_of_ne e] at this
        have hmem := (h.mem_free x).2 this
        rw [hs] at hmem
        exact (List.mem_cons.1 hmem).resolve_left hxi
  · intro j' hj'
    by_cases e : j' = j
    · rw [e, Function.update_self] at hj'
      cases hj'
    · rw [Function.update_of_ne e] at hj'
      rw [Function.update_of_ne e]
      exact h.price_unowned j' hj'
  · intro j' i' hj' k
    by_cases e : j' = j
    · subst e
      rw [Function.update_self] at hj'
      cases hj'
      rw [Function.update_self]
      by_cases hk : k = j'
      · subst hk
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hk]
        exact bidPrice_epsCS k hk
    · rw [Function.update_of_ne e] at hj'
      rw [Function.update_of_ne e]
      have := h.epsCS j' i' hj' k
      have := hup k
      omega

/-- A bid raises the total price by at least `ε`: the termination measure. -/
theorem sum_price_bidStep {s : AuctionState n} {i : Fin n} {rest : List (Fin n)}
    (hs : s.free = i :: rest) :
    ∑ j, s.price j + ε ≤ ∑ j, (bidStep c ε s).price j := by
  obtain ⟨j, hj, heq⟩ := bidStep_cons (c := c) (ε := ε) hs
  rw [heq]
  dsimp only
  rw [Finset.sum_update_of_mem (mem_univ j), sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ j)]
  have := le_bidPrice (ε := ε) hj
  omega

/-- A bid by an unassigned person increments the bid counter. -/
theorem bids_bidStep {s : AuctionState n} {i : Fin n} {rest : List (Fin n)}
    (hs : s.free = i :: rest) : (bidStep c ε s).bids = s.bids + 1 := by
  obtain ⟨j, -, heq⟩ := bidStep_cons (c := c) (ε := ε) hs
  rw [heq]

/-- While some person is unassigned, some object is unassigned. -/
theorem AuctionInv.exists_owner_eq_none {s : AuctionState n} (h : AuctionInv c ε s)
    (hs : s.free ≠ []) : ∃ k, s.owner k = none := by
  obtain ⟨i, rest, hir⟩ := List.exists_cons_of_ne_nil hs
  by_contra hall
  simp only [not_exists, ← ne_eq] at hall
  let f : Fin n → Fin n := fun k => (s.owner k).get (Option.isSome_iff_ne_none.2 (hall k))
  have hf : ∀ k, s.owner k = some (f k) := fun k => (Option.some_get _).symm
  have hinj : Function.Injective f := fun k k' e => h.owner_inj k k' (f k) (hf k) (e ▸ hf k')
  obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.1 hinj i
  exact (h.mem_free i).1 (hir ▸ List.mem_cons_self ..) k (hk ▸ hf k)

/-- While some person is unassigned, every price is at most `C + ε`, where `C` bounds the row
cost ranges: the owner of an object prefers it, up to `ε`, to an unassigned object of price `0`
(cf. [Bertsekas1998], §7.1.1, observation (a)). -/
theorem AuctionInv.price_le {s : AuctionState n} (h : AuctionInv c ε s) (hs : s.free ≠ [])
    {C : ℤ} (hC : ∀ i j k, c (i, k) - c (i, j) ≤ C) (hε : 0 ≤ ε) (j : Fin n) :
    s.price j ≤ C + ε := by
  obtain ⟨k, hk⟩ := h.exists_owner_eq_none hs
  rcases ho : s.owner j with _ | i
  · rw [h.price_unowned j ho]
    have := hC j j j
    omega
  · have h1 := h.epsCS j i ho k
    have h2 := hC i j k
    rw [h.price_unowned k hk] at h1
    omega

/-- **Termination** by the measure `n (C + ε) - ∑ j, p j`, which every bid lowers by at least `ε`
and which is nonnegative while some person is unassigned: if the measure is below `fuel * ε`,
then `fuel` bids complete the assignment. -/
theorem auctionLoop_spec (hε : 0 < ε) {C : ℤ} (hC : ∀ i j k, c (i, k) - c (i, j) ≤ C) :
    ∀ (fuel : ℕ) (s : AuctionState n), AuctionInv c ε s →
      (n : ℤ) * (C + ε) - ∑ j, s.price j < fuel * ε →
      AuctionInv c ε (auctionLoop c ε fuel s) ∧ (auctionLoop c ε fuel s).free = [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro s h hlt
    refine ⟨h, ?_⟩
    by_contra hs
    have hsum : ∑ j, s.price j ≤ ∑ _j : Fin n, (C + ε) :=
      sum_le_sum fun j _ => h.price_le hs hC hε.le j
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    simp only [Nat.cast_zero, zero_mul] at hlt
    omega
  | succ fuel ih =>
    intro s h hlt
    rcases hs : s.free with _ | ⟨i, rest⟩
    · rw [auctionLoop, hs]
      exact ⟨h, hs⟩
    · rw [auctionLoop, hs]
      apply ih _ (h.bidStep hε.le)
      have := sum_price_bidStep (c := c) (ε := ε) hs
      push_cast at hlt
      linarith

/-- Extra fuel does not change a completed run. -/
theorem auctionLoop_add {s : AuctionState n} {fuel : ℕ} (h : (auctionLoop c ε fuel s).free = [])
    (m : ℕ) : auctionLoop c ε (fuel + m) s = auctionLoop c ε fuel s := by
  induction fuel generalizing s with
  | zero =>
    rw [auctionLoop] at h
    cases m <;> simp [auctionLoop, h]
  | succ fuel ih =>
    rw [Nat.add_right_comm]
    rcases hs : s.free with _ | ⟨i, rest⟩
    · simp [auctionLoop, hs]
    · rw [auctionLoop, hs] at h
      rw [auctionLoop, hs, auctionLoop, hs]
      exact ih h

/-- A run with `fuel` makes at most `fuel` bids. -/
theorem bids_auctionLoop_le (fuel : ℕ) (s : AuctionState n) :
    (auctionLoop c ε fuel s).bids ≤ s.bids + fuel := by
  induction fuel generalizing s with
  | zero => simp [auctionLoop]
  | succ fuel ih =>
    rcases hs : s.free with _ | ⟨i, rest⟩
    · simp [auctionLoop, hs]
    · simp only [auctionLoop, hs]
      have := ih (bidStep c ε s)
      rw [bids_bidStep hs] at this
      omega

/-- The fuel `bidBound n C ε` exceeds the initial measure `n (C + ε)` divided by `ε`. -/
theorem lt_bidBound_mul (hε : 0 < ε) (C : ℤ) :
    (n : ℤ) * (C + ε) < (bidBound n C ε : ℤ) * ε := by
  have hεn : ((ε.toNat : ℕ) : ℤ) = ε := Int.toNat_of_nonneg hε.le
  have hpos : 0 < ε.toNat := by omega
  have key : n * (C + ε).toNat < (n * (C + ε).toNat / ε.toNat + 1) * ε.toNat := by
    rw [Nat.add_mul, one_mul]
    exact Nat.lt_div_mul_add hpos
  have h1 : (n : ℤ) * (C + ε) ≤ ((n * (C + ε).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Int.self_le_toNat _) (Nat.cast_nonneg n)
  have h2 : ((n * (C + ε).toNat : ℕ) : ℤ) < ((bidBound n C ε * ε.toNat : ℕ) : ℤ) :=
    Nat.cast_lt.2 key
  rw [Nat.cast_mul (bidBound n C ε), hεn] at h2
  exact lt_of_le_of_lt h1 h2

/-- `costSpread c` bounds every row cost range. -/
theorem sub_le_costSpread (i j k : Fin n) : c (i, k) - c (i, j) ≤ costSpread c := by
  have hrow : ∀ j, |c (i, j)| ≤ ∑ i, ∑ j, |c (i, j)| := fun j =>
    (single_le_sum (fun j _ => abs_nonneg (c (i, j))) (mem_univ j)).trans
      (single_le_sum (f := fun i => ∑ j, |c (i, j)|)
        (fun i _ => sum_nonneg fun j _ => abs_nonneg _) (mem_univ i))
  have h1 := hrow k
  have h2 := hrow j
  have h3 := le_abs_self (c (i, k))
  have h4 := neg_abs_le (c (i, j))
  unfold costSpread
  linarith

/-- With fuel `bidBound n C ε` for any bound `C` on the row cost ranges, the auction completes the
assignment and maintains the invariant. -/
theorem auctionLoop_bidBound (hε : 0 < ε) {C : ℤ} (hC : ∀ i j k, c (i, k) - c (i, j) ≤ C) :
    AuctionInv c ε (auctionLoop c ε (bidBound n C ε) (auctionInit n)) ∧
      (auctionLoop c ε (bidBound n C ε) (auctionInit n)).free = [] :=
  auctionLoop_spec hε hC _ _ auctionInv_init (by
    simp only [auctionInit, sum_const_zero, sub_zero]
    exact lt_bidBound_mul hε C)

/-- The final state of the auction satisfies the invariant. -/
theorem auctionInv_auction (hε : 0 < ε) : AuctionInv c ε (auction c ε) :=
  (auctionLoop_bidBound hε sub_le_costSpread).1

/-- **Termination** ([Bertsekas1998], Prop. 7.2): the auction ends with every person assigned. -/
theorem auction_free (hε : 0 < ε) : (auction c ε).free = [] :=
  (auctionLoop_bidBound hε sub_le_costSpread).2

/-- **Bid bound**: if `c (i, k) - c (i, j) ≤ C` for all `i, j, k`, the auction makes at most
`n (C + ε) / ε + 1` bids. This is pseudo-polynomial: it is linear in `C / ε`. -/
theorem bids_auction_le (hε : 0 < ε) {C : ℤ} (hC : ∀ i j k, c (i, k) - c (i, j) ≤ C) :
    (auction c ε).bids ≤ bidBound n C ε := by
  unfold auction
  rcases le_total (bidBound n C ε) (bidBound n (costSpread c) ε) with hle | hle
  · rw [← Nat.add_sub_cancel' hle, auctionLoop_add (auctionLoop_bidBound hε hC).2]
    have := bids_auctionLoop_le (c := c) (ε := ε) (bidBound n C ε) (auctionInit n)
    rwa [show (auctionInit n).bids = 0 from rfl, zero_add] at this
  · have := bids_auctionLoop_le (c := c) (ε := ε) (bidBound n (costSpread c) ε) (auctionInit n)
    rw [show (auctionInit n).bids = 0 from rfl, zero_add] at this
    omega

/-! ### The output permutation -/

section Final

variable {s : AuctionState n}

/-- In a complete state, person `i` owns `s.objectOf i`. -/
theorem AuctionInv.owner_objectOf (h : AuctionInv c ε s) (hs : s.free = []) (i : Fin n) :
    s.owner (s.objectOf i) = some i := by
  have hex : ∃ j, s.owner j = some i := by
    have := (h.mem_free i).not.1 (by rw [hs]; exact List.not_mem_nil)
    simpa only [not_forall, not_not] using this
  obtain ⟨j₀, hj₀⟩ := hex
  have hsome : ((List.finRange n).find? fun j => decide (s.owner j = some i)).isSome :=
    List.find?_isSome.2 ⟨j₀, List.mem_finRange j₀, by simpa using hj₀⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hsome
  have := List.find?_some hj
  simp only [decide_eq_true_eq] at this
  simp only [AuctionState.objectOf, hj, Option.getD_some]
  exact this

/-- In a complete state, `personOf` is a left inverse of `objectOf`. -/
theorem AuctionInv.personOf_objectOf (h : AuctionInv c ε s) (hs : s.free = []) (i : Fin n) :
    s.personOf (s.objectOf i) = i := by
  simp only [AuctionState.personOf, h.owner_objectOf hs i, Option.getD_some]

/-- In a complete state, `personOf` is a right inverse of `objectOf`. -/
theorem AuctionInv.objectOf_personOf (h : AuctionInv c ε s) (hs : s.free = []) (j : Fin n) :
    s.objectOf (s.personOf j) = j := by
  have hinj : Function.Injective s.objectOf := fun i i' e =>
    Option.some_injective _ ((h.owner_objectOf hs i).symm.trans (e ▸ h.owner_objectOf hs i'))
  obtain ⟨i, rfl⟩ := Finite.injective_iff_surjective.1 hinj j
  rw [h.personOf_objectOf hs]

end Final

/-- The assignment computed by the auction with increment `ε > 0`: person `i` is assigned object
`auctionPerm c hε i`. -/
@[expose] def auctionPerm (c : Fin n × Fin n → ℤ) {ε : ℤ} (hε : 0 < ε) : Equiv.Perm (Fin n) where
  toFun := (auction c ε).objectOf
  invFun := (auction c ε).personOf
  left_inv := (auctionInv_auction hε).personOf_objectOf (auction_free hε)
  right_inv := (auctionInv_auction hε).objectOf_personOf (auction_free hε)

/-- The output and the final prices satisfy `ε`-complementary slackness. -/
theorem isEpsCompSlack_auctionPerm (hε : 0 < ε) :
    IsEpsCompSlack c ε (auctionPerm c hε) (auction c ε).price := fun i k =>
  (auctionInv_auction hε).epsCS _ i
    ((auctionInv_auction hε).owner_objectOf (auction_free hε) i) k

/-- **`nε`-optimality of the auction** ([Bertsekas1998], Prop. 7.2): the computed assignment costs
at most `n * ε` more than every assignment. -/
theorem sum_auctionPerm_le (hε : 0 < ε) (τ : Equiv.Perm (Fin n)) :
    ∑ i, c (i, auctionPerm c hε i) ≤ ∑ i, c (i, τ i) + n * ε := by
  have := (isEpsCompSlack_auctionPerm (c := c) hε).sum_le_sum_add τ
  rwa [Fintype.card_fin, nsmul_eq_mul] at this

/-- **Dual certificate**: the final prices `p` give feasible dual potentials
`(rowPotential c p, -p)` (`rowPotential_add_neg_le`) whose total is within `n * ε` of the cost of
the computed assignment. -/
theorem sum_auctionPerm_le_rowPotential (hε : 0 < ε) :
    ∑ i, c (i, auctionPerm c hε i) ≤
      ∑ i, rowPotential c (auction c ε).price i + ∑ j, -(auction c ε).price j + n * ε := by
  have := (isEpsCompSlack_auctionPerm (c := c) hε).sum_le_rowPotential
  rwa [Fintype.card_fin, nsmul_eq_mul] at this

/-- The exact auction: the auction on the costs scaled by `n + 1`, with `ε = 1`. -/
@[expose] def scaledAuction (c : Fin n × Fin n → ℤ) : AuctionState n :=
  auction (fun e => ((n : ℤ) + 1) * c e) 1

/-- The assignment computed by the exact auction `scaledAuction`. -/
@[expose] def scaledAuctionPerm (c : Fin n × Fin n → ℤ) : Equiv.Perm (Fin n) :=
  auctionPerm (fun e => ((n : ℤ) + 1) * c e) one_pos

/-- `scaledAuctionPerm c` reads the assignment off the final state `scaledAuction c`. -/
theorem scaledAuctionPerm_apply (c : Fin n × Fin n → ℤ) (i : Fin n) :
    scaledAuctionPerm c i = (scaledAuction c).objectOf i := rfl

/-- **Exact optimality** for integer costs ([Bertsekas1998], Prop. 7.2 with integer data and
`ε < 1 / n`; scaling by `n + 1` as in [Bertsekas1988], §3): on the costs scaled by `n + 1` and with
`ε = 1`, the auction returns a minimum-cost assignment. -/
theorem sum_scaledAuctionPerm_le (τ : Equiv.Perm (Fin n)) :
    ∑ i, c (i, scaledAuctionPerm c i) ≤ ∑ i, c (i, τ i) := by
  have h := sum_auctionPerm_le (c := fun e => ((n : ℤ) + 1) * c e) one_pos τ
  rw [← mul_sum, ← mul_sum, mul_one] at h
  change ((n : ℤ) + 1) * ∑ i, c (i, scaledAuctionPerm c i) ≤ _ at h
  by_contra hlt
  have hlt' : ∑ i, c (i, τ i) + 1 ≤ ∑ i, c (i, scaledAuctionPerm c i) := by omega
  have := mul_le_mul_of_nonneg_left hlt' (by positivity : (0 : ℤ) ≤ n + 1)
  linarith

/-- **Bid bound for the exact algorithm**: if every row cost range is at most `C`, the exact
auction `scaledAuction` makes at most `n ((n + 1) C + 1) + 1` bids. -/
theorem bids_scaledAuction_le {C : ℤ} (hC : ∀ i j k, c (i, k) - c (i, j) ≤ C) :
    (scaledAuction c).bids ≤ n * (((n : ℤ) + 1) * C + 1).toNat + 1 := by
  have hC' : ∀ i j k, ((n : ℤ) + 1) * c (i, k) - ((n : ℤ) + 1) * c (i, j) ≤ ((n : ℤ) + 1) * C :=
    fun i j k => by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (hC i j k) (by positivity)
  have := bids_auction_le (c := fun e => ((n : ℤ) + 1) * c e) one_pos hC'
  simpa only [scaledAuction, bidBound, Int.toNat_one, Nat.div_one] using this

end Cslib.Algorithms.Lean.Assignment
