/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Strategic.Potential
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Atomic congestion games and Rosenthal's potential

In an atomic congestion game there are finitely many players and a set `E` of resources. A
strategy of player `i` is a strategy `a : S i` that determines a finite set of resources
`resources i a`, for instance the edges of a path in a network. Given a profile `s`, the **load**
`load s e` of a resource `e` is the number of players whose chosen resource set contains `e`, and
player `i` pays the sum of the latencies `latency e (load s e)` of its resources. This is the model
of [Rosenthal1973]; see also [MondererShapley1996], Section 3, and [Roughgarden2015], Example 2.5.

Rosenthal [Rosenthal1973] observed that
`Φ s = ∑ e, ∑ k ∈ Finset.range (load s e), latency e (k + 1)` is an exact potential: when player
`i` changes its strategy, the change in its cost equals the change in `Φ`. Hence every congestion
game with finitely many strategies has a pure Nash equilibrium and the finite improvement property
([MondererShapley1996], Theorem 3.1).

## Main definitions

* `Cslib.GameTheory.CongestionGame`: an atomic congestion game with real-valued latencies.
* `Cslib.GameTheory.CongestionGame.load`: the number of players using a resource.
* `Cslib.GameTheory.CongestionGame.toCostGame`: the strategic game it defines.
* `Cslib.GameTheory.CongestionGame.rosenthalPotential`: Rosenthal's potential.

## Main results

* `Cslib.GameTheory.CongestionGame.isExactPotential_rosenthalPotential` ([Rosenthal1973];
  [MondererShapley1996], Theorem 3.1): Rosenthal's function is an exact potential.
* `Cslib.GameTheory.CongestionGame.exists_isPureNash` ([Rosenthal1973]): a congestion game with
  finitely many strategies has a pure Nash equilibrium.
* `Cslib.GameTheory.CongestionGame.hasFIP`: it has the finite improvement property, so
  better-response dynamics reach a pure Nash equilibrium.
* `Cslib.GameTheory.CongestionGame.socialCost_toCostGame`: the social cost is
  `∑ e, load s e * latency e (load s e)`.
* `Cslib.GameTheory.CongestionGame.load_update_le`: a unilateral deviation raises a load by at
  most one.

## References

* [MondererShapley1996]
* [Rosenthal1973]
* [Roughgarden2015]
-/

public section

namespace Cslib.GameTheory

/-- An **atomic congestion game** on the resources `E`: player `i` chooses a strategy `a : S i`,
which uses the finite set of resources `resources i a`, and `latency e k` is the cost to each user
of resource `e` when exactly `k` players use it. -/
structure CongestionGame (ι : Type*) (S : ι → Type*) (E : Type*) where
  /-- The resources used by player `i` when it plays the strategy `a`. -/
  resources : ∀ i, S i → Finset E
  /-- The per-user cost of resource `e` when its load is `k`. -/
  latency : E → ℕ → ℝ

namespace CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq E]
  (C : CongestionGame ι S E)

/-- The **load** of resource `e` at the profile `s`: the number of players whose resource set
contains `e`. -/
@[expose] def load (s : ∀ i, S i) (e : E) : ℕ :=
  (Finset.univ.filter fun i => e ∈ C.resources i (s i)).card

/-- The strategic game defined by a congestion game: player `i` pays the sum of the latencies of
its resources at their current loads. -/
@[expose] def toCostGame : CostGame ι S where
  cost i s := ∑ e ∈ C.resources i (s i), C.latency e (C.load s e)

theorem toCostGame_cost (i : ι) (s : ∀ i, S i) :
    C.toCostGame.cost i s = ∑ e ∈ C.resources i (s i), C.latency e (C.load s e) := rfl

/-- **Rosenthal's potential** [Rosenthal1973]:
`∑ e, (latency e 1 + latency e 2 + ⋯ + latency e (load s e))`. -/
def rosenthalPotential [Fintype E] (s : ∀ i, S i) : ℝ :=
  ∑ e, ∑ k ∈ Finset.range (C.load s e), C.latency e (k + 1)

/-- Exchanging the sums over players and resources: summing `f e` over every player's resources
counts each resource `e` with multiplicity `load s e`. -/
theorem sum_sum_resources_eq_sum_load_mul [Fintype E] (s : ∀ i, S i) (f : E → ℝ) :
    ∑ i, ∑ e ∈ C.resources i (s i), f e = ∑ e, (C.load s e : ℝ) * f e := by
  simp only [load, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The social cost of a congestion game is `∑ e, load s e * latency e (load s e)`. -/
theorem socialCost_toCostGame [Fintype E] (s : ∀ i, S i) :
    C.toCostGame.socialCost s = ∑ e, (C.load s e : ℝ) * C.latency e (C.load s e) :=
  C.sum_sum_resources_eq_sum_load_mul s fun e => C.latency e (C.load s e)

variable [DecidableEq ι]

/-- The number of players other than `i` that use `e`. -/
private def loadExcept (s : ∀ i, S i) (i : ι) (e : E) : ℕ :=
  ((Finset.univ.erase i).filter fun j => e ∈ C.resources j (s j)).card

private theorem loadExcept_update (s : ∀ i, S i) (i : ι) (a : S i) (e : E) :
    C.loadExcept (Function.update s i a) i e = C.loadExcept s i e := by
  unfold loadExcept
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem load_eq (s : ∀ i, S i) (i : ι) (e : E) :
    C.load s e = C.loadExcept s i e + if e ∈ C.resources i (s i) then 1 else 0 := by
  unfold load loadExcept
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- A unilateral deviation raises the load of each resource by at most one. -/
theorem load_update_le (s : ∀ i, S i) (i : ι) (a : S i) (e : E) :
    C.load (Function.update s i a) e ≤ C.load s e + 1 := by
  rw [C.load_eq (Function.update s i a) i e, loadExcept_update, C.load_eq s i e]
  split_ifs <;> omega

private theorem rosenthalPotential_sub_cost [Fintype E] (s : ∀ i, S i) (i : ι) :
    C.rosenthalPotential s - C.toCostGame.cost i s
      = ∑ e, ∑ k ∈ Finset.range (C.loadExcept s i e), C.latency e (k + 1) := by
  have hcost : C.toCostGame.cost i s
      = ∑ e, if e ∈ C.resources i (s i) then C.latency e (C.load s e) else 0 := by
    rw [toCostGame_cost, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hcost, rosenthalPotential, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [C.load_eq s i e]
  split_ifs
  · rw [Finset.sum_range_succ]
    ring
  · rw [add_zero, sub_zero]

/-- **Rosenthal's theorem** ([Rosenthal1973]; [MondererShapley1996], Theorem 3.1): Rosenthal's
function is an exact potential for every atomic congestion game with finitely many resources. -/
theorem isExactPotential_rosenthalPotential [Fintype E] :
    C.toCostGame.IsExactPotential C.rosenthalPotential := by
  intro s i a
  have h1 := C.rosenthalPotential_sub_cost s i
  have h2 := C.rosenthalPotential_sub_cost (Function.update s i a) i
  simp only [loadExcept_update] at h2
  linarith

/-- An atomic congestion game with finitely many players, strategies and resources has the finite
improvement property: every sequence of strictly improving unilateral deviations is finite. -/
theorem hasFIP [Finite E] [∀ i, Finite (S i)] : C.toCostGame.HasFIP := by
  have := Fintype.ofFinite E
  exact C.isExactPotential_rosenthalPotential.isGeneralizedOrdinalPotential.hasFIP

/-- **Every atomic congestion game has a pure Nash equilibrium** [Rosenthal1973], when there are
finitely many players, strategies and resources and every player has a strategy. -/
theorem exists_isPureNash [Finite E] [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] :
    ∃ s, C.toCostGame.IsPureNash s :=
  C.hasFIP.exists_isPureNash

end CongestionGame

end Cslib.GameTheory
