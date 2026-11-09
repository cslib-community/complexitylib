/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Online.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The `k`-server problem

This file defines the `k`-server problem of [Manasse, McGeoch and Sleator, *Competitive
algorithms for server problems*][ManasseMcGeochSleator1990] (see also [Borodin and El-Yaniv,
*Online Computation and Competitive Analysis*, Chapter 10][BorodinElYaniv1998]) as an instance of
the online framework `Cslib.DataStructure.Online.Problem`, together with the matching distance
between configurations used by potential-function analyses.

`k` servers occupy points of a metric space. Each request is a point, and to serve it some server
must move onto it. Serving a request costs the total distance moved by all servers.

## Model

* Distances are natural numbers (`NatMetric`), so step costs fit `Online.Problem.stepCost : Nat`.
  `NatMetric.line` is the line `ℤ` with `|x - y|`, and `NatMetric.uniform` the uniform metric,
  where the problem is paging with `k` cache slots up to the cost of an eviction.
* A configuration is a labeled tuple `Fin k → α`, so coincident servers are allowed. A transition
  is any configuration with a server on the request, and it costs `moveCost`, the summed
  per-label distance. Relabeling is free: a schedule may pass to `s' ∘ σ` for any permutation `σ`.
  The cheapest such move from `s` to the multiset of `s'` is therefore `matchCost s s'`, the
  minimum-cost perfect matching (`matchCostAlong_eq_moveCost`). So the labeled model has the
  same offline optimum as the multiset formulation of the source.
* Online algorithms are `Online.DetStrategy`s and competitiveness is `Online.IsCompetitiveFrom`.

## Main definitions

* `Cslib.DataStructure.KServer.NatMetric`: a metric with natural-number distances, with the
  instances `NatMetric.line` and `NatMetric.uniform`.
* `Cslib.DataStructure.KServer.moveCost`: total server movement between two configurations.
* `Cslib.DataStructure.KServer.problem`: the `k`-server `Online.Problem` on a metric.
* `Cslib.DataStructure.KServer.matchCost`: minimum-cost perfect matching between configurations.
* `Cslib.DataStructure.KServer.pairSum`: summed pairwise distance within a configuration.

## Main results

* `matchCost_le_add_moveCost`: moving the second configuration changes the matching distance by
  at most the movement.
* `matchCostAlong_swap_le`: uncrossing a matching along a geodesic does not increase its cost.
* `matchCostAlong_update_toward`: moving a server toward its partner lowers the cost by the
  distance moved.

## References

* [M. S. Manasse, L. A. McGeoch and D. D. Sleator, *Competitive algorithms for server
  problems*][ManasseMcGeochSleator1990]
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
-/

public section

namespace Cslib.DataStructure.KServer

open Cslib.DataStructure.Online

/-- A metric on `α` with natural-number distances. -/
structure NatMetric (α : Type) where
  /-- The distance between two points. -/
  dist : α → α → Nat
  dist_self : ∀ x, dist x x = 0
  eq_of_dist_eq_zero : ∀ {x y}, dist x y = 0 → x = y
  dist_comm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

namespace NatMetric

/-- The line metric on `ℤ`, `dist x y = |x - y|`. -/
@[expose]
def line : NatMetric Int where
  dist x y := (x - y).natAbs
  dist_self x := by simp only [sub_self, Int.natAbs_zero]
  eq_of_dist_eq_zero h := by omega
  dist_comm x y := by omega
  dist_triangle x y z := by omega

@[simp]
theorem line_dist (x y : Int) : line.dist x y = (x - y).natAbs := rfl

/-- The uniform metric: distinct points are at distance `1`. -/
@[expose]
def uniform (α : Type) [DecidableEq α] : NatMetric α where
  dist x y := if x = y then 0 else 1
  dist_self x := ite_eq_left rfl
  eq_of_dist_eq_zero {x y} h := by
    by_contra hxy
    rw [ite_eq_right hxy] at h
    exact Nat.one_ne_zero h
  dist_comm x y := by
    by_cases h : x = y
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  dist_triangle x y z := by
    by_cases hxz : x = z
    · rw [ite_eq_left hxz]
      exact Nat.zero_le _
    · rw [ite_eq_right hxz]
      by_cases hxy : x = y
      · rw [ite_eq_right (hxy ▸ hxz : y ≠ z)]
        omega
      · rw [ite_eq_right hxy]
        omega

end NatMetric

variable {α : Type} (M : NatMetric α) {k : Nat}

theorem NatMetric.dist_pos_of_ne {x y : α} (h : x ≠ y) : 0 < M.dist x y :=
  Nat.pos_of_ne_zero fun h0 => h (M.eq_of_dist_eq_zero h0)

/-! ### Server movement -/

/-- Total distance moved when every server `i` goes from `s i` to `s' i`. -/
@[expose]
def moveCost (s s' : Fin k → α) : Nat :=
  ∑ i, M.dist (s i) (s' i)

@[simp]
theorem moveCost_self (s : Fin k → α) : moveCost M s s = 0 :=
  Finset.sum_eq_zero fun i _ => M.dist_self (s i)

theorem moveCost_triangle (s t u : Fin k → α) :
    moveCost M s u ≤ moveCost M s t + moveCost M t u := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => M.dist_triangle _ _ _

/-- Relabeling both configurations by the same permutation does not change the movement. -/
theorem moveCost_comp_perm (s s' : Fin k → α) (π : Equiv.Perm (Fin k)) :
    moveCost M (s ∘ π) (s' ∘ π) = moveCost M s s' :=
  Equiv.sum_comp π fun i => M.dist (s i) (s' i)

/-- Moving one server costs its distance. -/
theorem moveCost_update (s : Fin k → α) (a : Fin k) (x : α) :
    moveCost M s (Function.update s a x) = M.dist (s a) x := by
  unfold moveCost
  rw [Fintype.sum_eq_single a fun i hi => by rw [Function.update_of_ne hi, M.dist_self],
    Function.update_self]

/-- Moving two distinct servers costs the sum of their distances. -/
theorem moveCost_update_update (s : Fin k → α) {a b : Fin k} (hab : a ≠ b) (x y : α) :
    moveCost M s (Function.update (Function.update s a x) b y) =
      M.dist (s a) x + M.dist (s b) y := by
  unfold moveCost
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [← Finset.add_sum_erase _ _ hb]
  have hrest : ∑ i ∈ (Finset.univ.erase a).erase b,
      M.dist (s i) (Function.update (Function.update s a x) b y i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
        Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)), M.dist_self]
  rw [hrest, Function.update_of_ne hab, Function.update_self, Function.update_self, Nat.add_zero]

/-! ### The problem -/

/-- The `k`-server problem on the metric `M`: configurations are labeled server positions, any
initial configuration is admissible, serving `r` means reaching a configuration with a server at
`r`, and a step costs the total server movement. -/
abbrev problem (M : NatMetric α) (k : Nat) : Problem where
  State := Fin k → α
  Req := α
  ValidInit _ := True
  ValidStep _ r s' := ∃ i, s' i = r
  stepCost s _ s' := moveCost M s s'

/-! ### Minimum-cost matching between configurations -/

/-- Cost of matching server `i` of `s` to server `σ i` of `t`. -/
@[expose]
def matchCostAlong (s t : Fin k → α) (σ : Equiv.Perm (Fin k)) : Nat :=
  ∑ i, M.dist (s i) (t (σ i))

/-- Matching along `σ` is the movement to the relabeled configuration `t ∘ σ`. -/
theorem matchCostAlong_eq_moveCost (s t : Fin k → α) (σ : Equiv.Perm (Fin k)) :
    matchCostAlong M s t σ = moveCost M s (t ∘ σ) := rfl

/-- Minimum-cost perfect matching distance between two configurations, i.e. the transport
distance between the multisets of server positions. -/
def matchCost (s t : Fin k → α) : Nat :=
  Finset.univ.inf' Finset.univ_nonempty (matchCostAlong M s t)

theorem matchCost_le (s t : Fin k → α) (σ : Equiv.Perm (Fin k)) :
    matchCost M s t ≤ matchCostAlong M s t σ :=
  Finset.inf'_le _ (Finset.mem_univ σ)

theorem exists_matchCost_eq (s t : Fin k → α) :
    ∃ σ, matchCost M s t = matchCostAlong M s t σ := by
  obtain ⟨σ, _, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (matchCostAlong M s t)
  exact ⟨σ, by rw [matchCost, h]⟩

theorem matchCost_le_moveCost (s t : Fin k → α) : matchCost M s t ≤ moveCost M s t :=
  matchCost_le M s t (Equiv.refl _)

@[simp]
theorem matchCost_self (s : Fin k → α) : matchCost M s s = 0 :=
  Nat.eq_zero_of_le_zero ((matchCost_le_moveCost M s s).trans (moveCost_self M s).le)

/-- Moving the second configuration changes the matching distance by at most the movement. -/
theorem matchCost_le_add_moveCost (s t t' : Fin k → α) :
    matchCost M s t' ≤ matchCost M s t + moveCost M t t' := by
  obtain ⟨σ, hσ⟩ := exists_matchCost_eq M s t
  rw [hσ]
  refine (matchCost_le M s t' σ).trans ?_
  unfold matchCostAlong moveCost
  rw [← Equiv.sum_comp σ (fun i => M.dist (t i) (t' i)), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => M.dist_triangle _ _ _

/-- Relabeling the first configuration does not change the matching distance. -/
theorem matchCost_comp_perm (s t : Fin k → α) (π : Equiv.Perm (Fin k)) :
    matchCost M (s ∘ π) t = matchCost M s t := by
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := exists_matchCost_eq M s t
    rw [hσ]
    refine (matchCost_le M (s ∘ π) t (π.trans σ)).trans (le_of_eq ?_)
    unfold matchCostAlong
    exact Equiv.sum_comp π (fun i => M.dist (s i) (t (σ i)))
  · obtain ⟨σ, hσ⟩ := exists_matchCost_eq M (s ∘ π) t
    rw [hσ]
    refine (matchCost_le M s t (π.symm.trans σ)).trans (le_of_eq ?_)
    unfold matchCostAlong
    rw [← Equiv.sum_comp π]
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Summed distance over ordered pairs of servers; each unordered pair is counted twice. -/
@[expose]
def pairSum (s : Fin k → α) : Nat :=
  ∑ i, ∑ j, M.dist (s i) (s j)

theorem pairSum_comp_perm (s : Fin k → α) (π : Equiv.Perm (Fin k)) :
    pairSum M (s ∘ π) = pairSum M s := by
  unfold pairSum
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp π (fun i => ∑ j, M.dist (s i) (s (π j)))]
  exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp π (fun j => M.dist (s i) (s j))

/-- Sums of two functions agreeing off `{a, b}` compare as their values on `{a, b}`. -/
private theorem sum_le_sum_of_eq_off_pair {f g : Fin k → Nat} {a b : Fin k} (hab : a ≠ b)
    (hfg : ∀ i, i ≠ a → i ≠ b → f i = g i) (h : f a + f b ≤ g a + g b) :
    ∑ i, f i ≤ ∑ i, g i := by
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ a),
    ← Finset.add_sum_erase _ g (Finset.mem_univ a), ← Finset.add_sum_erase _ f hb,
    ← Finset.add_sum_erase _ g hb]
  have hrest : ∑ i ∈ (Finset.univ.erase a).erase b, f i =
      ∑ i ∈ (Finset.univ.erase a).erase b, g i :=
    Finset.sum_congr rfl fun i hi =>
      hfg i (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)
  omega

/-- Uncrossing: if `s b` lies on a geodesic from `t (σ a)` to `s a`, swapping the partners of
`a` and `b` does not increase the matching cost. -/
theorem matchCostAlong_swap_le (s t : Fin k → α) (σ : Equiv.Perm (Fin k)) {a b : Fin k}
    (hbtw : M.dist (t (σ a)) (s a) = M.dist (t (σ a)) (s b) + M.dist (s b) (s a)) :
    matchCostAlong M s t (σ * Equiv.swap a b) ≤ matchCostAlong M s t σ := by
  by_cases hab : a = b
  · rw [hab, Equiv.swap_self, Equiv.Perm.mul_def, Equiv.refl_trans]
  unfold matchCostAlong
  refine sum_le_sum_of_eq_off_pair hab (fun i ha hb => ?_) ?_
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ha hb]
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have h1 := M.dist_triangle (s a) (s b) (t (σ b))
    have h2 := M.dist_comm (s b) (t (σ a))
    have h3 := M.dist_comm (s a) (t (σ a))
    have h4 := M.dist_comm (s b) (s a)
    omega

/-- Moving one server changes a fixed matching's cost by at most the distance moved. -/
theorem matchCostAlong_update_le (s t : Fin k → α) (σ : Equiv.Perm (Fin k)) (i : Fin k) (y : α) :
    matchCostAlong M (Function.update s i y) t σ ≤ matchCostAlong M s t σ + M.dist (s i) y := by
  unfold matchCostAlong
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  have hrest : ∑ j ∈ Finset.univ.erase i, M.dist (Function.update s i y j) (t (σ j)) =
      ∑ j ∈ Finset.univ.erase i, M.dist (s j) (t (σ j)) :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have htri := M.dist_triangle y (s i) (t (σ i))
  have hc := M.dist_comm y (s i)
  omega

/-- Moving one server along a geodesic toward its partner lowers the cost by the distance moved. -/
theorem matchCostAlong_update_toward (s t : Fin k → α) (σ : Equiv.Perm (Fin k)) (i : Fin k) (y : α)
    (hy : M.dist (s i) (t (σ i)) = M.dist (s i) y + M.dist y (t (σ i))) :
    matchCostAlong M (Function.update s i y) t σ + M.dist (s i) y = matchCostAlong M s t σ := by
  unfold matchCostAlong
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  have hrest : ∑ j ∈ Finset.univ.erase i, M.dist (Function.update s i y j) (t (σ j)) =
      ∑ j ∈ Finset.univ.erase i, M.dist (s j) (t (σ j)) :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  omega

end Cslib.DataStructure.KServer
