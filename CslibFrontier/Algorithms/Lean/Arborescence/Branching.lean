/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Table
public import CslibFrontier.Foundations.Combinatorics.Digraph.Branching
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Optimum branchings via Chu–Liu/Edmonds

A **branching** in a directed graph `G` (`Digraph.IsBranching`) is a directed forest of disjoint
out-arborescences (`Edmonds1967Branchings`, Section 1). Using the `Option V` super-root
correspondence from `CslibFrontier.Foundations.Combinatorics.Digraph.Branching`
(`Digraph.superRootDigraph`, `Digraph.superRootExtend`, `Digraph.restrictOption`), this module
reduces maximum-weight branching on `(G, w)` to minimum-cost spanning in-arborescence on
`(G.superRootDigraph, superRootCost w, none)` (`optimumBranching`, `optimumBranchingM`).

Because every vertex `some v` has an arc to the super-root `none` of cost `0` while real arcs
`some v → some u` carry negated cost `-w u v`, the super-root reduction preserves exact weights up
to negation (`arcCost_superRootExtend`), always succeeds without a separate shift constant, runs
in `O(n³)` time (`time_optimumBranchingM_le`), and also yields minimum-weight branchings via `-w`
(`minBranching`). We also formalize Edmonds' weight-shift reductions from
[Edmonds1967Branchings, Section 2] (`edmonds_shift_weight_branching`,
`edmonds_rooted_outArborescence_of_shift`) characterizing maximum-cardinality branchings and
rooted spanning out-arborescences under weight shift `h > ∑ |w_e|`.

## Main definitions

* `Cslib.Algorithms.Lean.Arborescence.optionFinEnum`: `FinEnum (Option V)` of cardinality
  `FinEnum.card V + 1`.
* `Cslib.Algorithms.Lean.Arborescence.superRootCost`: negated-weight cost function on `Option V`.
* `Cslib.Algorithms.Lean.Arborescence.optimumBranchingParent`,
  `Cslib.Algorithms.Lean.Arborescence.optimumBranching`: exact maximum-weight branching solver
  via `edmonds`.
* `Cslib.Algorithms.Lean.Arborescence.optimumBranchingM`: `O(n³)` materialized-table solver in
  `TimeM ℕ`.
* `Cslib.Algorithms.Lean.Arborescence.minBranching`: minimum-weight branching via negated weights.
* `Cslib.Algorithms.Lean.Arborescence.rootedDigraph`: subgraph removing arcs entering a designated
  root `r₀`.

## Main results

* `Cslib.Algorithms.Lean.Arborescence.arcCost_superRootExtend`: exact cost correspondence between
  `B` and `B.superRootExtend`.
* `Cslib.Algorithms.Lean.Arborescence.optimumBranching_isBranching`,
  `Cslib.Algorithms.Lean.Arborescence.optimumBranching_le`,
  `Cslib.Algorithms.Lean.Arborescence.optimumBranching_optimal`: correctness and global
  maximum-weight optimality over all branchings `B ≤ G`.
* `Cslib.Algorithms.Lean.Arborescence.optimumBranchingM_ret_eq`,
  `Cslib.Algorithms.Lean.Arborescence.time_optimumBranchingM_le`: equivalence with
  `optimumBranchingParent` and `≤ 15 * (n + 1) ^ 3` (`O(n³)`) step bound.
* `Cslib.Algorithms.Lean.Arborescence.minBranching_optimal`: global minimum-weight optimality.
* `Cslib.Algorithms.Lean.Arborescence.edmonds_shift_weight_branching`,
  `Cslib.Algorithms.Lean.Arborescence.edmonds_rooted_outArborescence_of_shift`: Edmonds'
  weight-shift theorems connecting optimum branchings to maximum-cardinality branchings and
  spanning out-arborescences.

## References

* [J. Edmonds, *Optimum Branchings*][Edmonds1967Branchings], Sections 1–4
-/

public section

namespace Cslib.Algorithms.Lean.Arborescence

open Cslib.Algorithms.Lean

/-! ### `FinEnum (Option V)` and super-root costs -/

/-- Equivalence identifying `Option V` with `Fin (FinEnum.card V + 1)` while keeping `none` at the
last index. -/
@[expose] def optionFinEquiv (V : Type*) [FinEnum V] :
    Option V ≃ Fin (FinEnum.card V + 1) where
  toFun
    | none => ⟨FinEnum.card V, Nat.lt_succ_self _⟩
    | some v => ⟨((@FinEnum.equiv V _) v).1, Nat.lt_succ_of_lt ((@FinEnum.equiv V _) v).isLt⟩
  invFun i :=
    if h : i.1 < FinEnum.card V then some ((@FinEnum.equiv V _).symm ⟨i.1, h⟩) else none
  left_inv
    | none => by simp
    | some v => by
      have hv : ((@FinEnum.equiv V _) v).1 < FinEnum.card V := ((@FinEnum.equiv V _) v).isLt
      simp [hv]
  right_inv i := by
    by_cases h : i.1 < FinEnum.card V
    · ext
      simp [h]
    · have hi : i.1 = FinEnum.card V := by omega
      ext
      simp [hi]

/-- Explicit `FinEnum (Option V)` with `.card = FinEnum.card V + 1` definitionally. -/
@[instance_reducible, expose]
def optionFinEnum (V : Type*) [FinEnum V] : FinEnum (Option V) where
  card := FinEnum.card V + 1
  equiv := optionFinEquiv V

/-- Super-root arc cost on `Option V`: real reversed arcs `some v → some u` carry negated weight
`-w u v`, while fallback arcs to `none` carry cost `0`. -/
@[expose] def superRootCost {V β : Type*} [Zero β] [Neg β] (w : V → V → β) :
    Option V → Option V → β
  | some v, some u => -w u v
  | _, _ => 0

/-- Extending a branching `B` to `Option V` negates its total arc weight under `superRootCost w`. -/
theorem arcCost_superRootExtend {V β : Type*} [Fintype V] [AddCommGroup β]
    (B : Digraph V) [DecidableRel B.Adj] [DecidableRel B.superRootExtend.Adj]
    (w : V → V → β) :
    arcCost B.superRootExtend (superRootCost w) = -arcCost B w := by
  unfold arcCost
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_option]
  have hnone : ∑ y : Option V,
      (if B.superRootExtend.Adj none y then superRootCost w none y else 0) = 0 := by
    simp [Digraph.superRootExtend]
  rw [hnone, zero_add]
  simp only [Fintype.sum_option, Digraph.superRootExtend_some_none, superRootCost,
    ite_self, zero_add, Digraph.superRootExtend_some_some]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

/-- Negating all arc weights negates `arcCost`. -/
theorem arcCost_neg {V β : Type*} [Fintype V] [AddCommGroup β]
    (B : Digraph V) [DecidableRel B.Adj] (w : V → V → β) :
    arcCost B (fun u v => -w u v) = -arcCost B w := by
  unfold arcCost
  rw [Finset.sum_neg_distrib]

/-- Congruence of `arcCost` across `Fintype`, `DecidableRel`, and equal digraphs. -/
theorem arcCost_congr {V β : Type*} (inst₁ inst₂ : Fintype V) [m : AddCommMonoid β]
    {T₁ T₂ : Digraph V} (d₁ : DecidableRel T₁.Adj) (d₂ : DecidableRel T₂.Adj)
    (h : T₁ = T₂) (c : V → V → β) :
    @arcCost V β inst₁ m T₁ d₁ c = @arcCost V β inst₂ m T₂ d₂ c := by
  subst h
  cases Subsingleton.elim inst₁ inst₂
  cases Subsingleton.elim d₁ d₂
  rfl

/-! ### Restricting `Option V` parent maps and super-root feasibility -/

/-- Project an `Option V → Option V` parent map to `V → V`, turning `none` parents into fixed
points (branching roots). -/
@[expose] def restrictParent {V : Type*} (p : Option V → Option V) (v : V) : V :=
  (p (some v)).getD v

/-- When `parentDigraph none p` is a spanning in-arborescence on `Option V` rooted at `none`,
`branchingDigraph (restrictParent p)` coincides with
`Digraph.restrictOption (parentDigraph none p)`. -/
theorem branchingDigraph_restrictParent {V : Type*} [Finite V] {p : Option V → Option V}
    (hT : (Digraph.parentDigraph none p).IsInArborescence none) :
    Digraph.branchingDigraph (restrictParent p) =
      Digraph.restrictOption (Digraph.parentDigraph none p) := by
  ext u v
  simp only [Digraph.branchingDigraph_adj, Digraph.restrictOption_adj,
    Digraph.parentDigraph_adj, ne_eq, Option.some_ne_none, restrictParent]
  cases hp : p (some v) with
  | none => simp
  | some w =>
    simp only [Option.getD_some, not_false_eq_true, true_and, Option.some.injEq]
    refine ⟨fun h => h.2, fun hwu => ⟨fun hwv => ?_, hwu⟩⟩
    exact (Digraph.restrictOption_spec hT).1.loopless v ⟨Option.some_ne_none v, hwv ▸ hp⟩

section Solvers

variable {β : Type*} [LinearOrder β] [AddCommGroup β] [IsOrderedAddMonoid β]

/-- Running `edmonds` on `(G.superRootDigraph, superRootCost w, none)` always returns `some p`
because `fun _ => none` is always a feasible spanning in-arborescence parent map. -/
theorem edmonds_superRootDigraph_isSome {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    let _ := optionFinEnum V
    ∃ p, edmonds G.superRootDigraph (superRootCost w) none = some p := by
  let _ := optionFinEnum V
  have hfeas : IsInArborescenceParent G.superRootDigraph.Adj none (fun _ => none) :=
    ⟨rfl, fun x hx => by
      cases x with
      | none => exact absurd rfl hx
      | some v => trivial,
      fun _ => ⟨1, rfl⟩⟩
  dsimp only
  by_cases hnone : edmonds G.superRootDigraph (superRootCost w) none = none
  · exact absurd hfeas (edmonds_spec.2 hnone _)
  · exact Option.ne_none_iff_exists'.mp hnone

/-- Parent-towards-root map returned by the super-root Chu–Liu/Edmonds reduction for an optimum
(maximum-weight) branching of `(G, w)`. -/
@[expose] def optimumBranchingParent {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) : V → V :=
  letI := optionFinEnum V
  match edmonds G.superRootDigraph (superRootCost w) none with
  | none => id
  | some p => restrictParent p

/-- Maximum-weight branching digraph of `(G, w)` computed via the `Option V` super-root
reduction to `edmonds`. -/
@[expose] def optimumBranching {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) : Digraph V :=
  Digraph.branchingDigraph (optimumBranchingParent G w)

instance {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    DecidableRel (optimumBranching G w).Adj :=
  inferInstanceAs (DecidableRel (Digraph.branchingDigraph (optimumBranchingParent G w)).Adj)

/-- Materialized-table `TimeM ℕ` solver returning the optimum branching parent map in `O(n³)`
charged steps. -/
@[expose] def optimumBranchingM {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) : TimeM ℕ (V → V) :=
  letI := optionFinEnum V
  let res := edmondsTableM G.superRootDigraph (superRootCost w) none
  ⟨match res.ret with | none => id | some p => restrictParent p, res.time⟩

omit [IsOrderedAddMonoid β] in
/-- `optimumBranchingM` computes the exact same parent map as `optimumBranchingParent`. -/
theorem optimumBranchingM_ret_eq {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    (optimumBranchingM G w).ret = optimumBranchingParent G w := by
  let _ := optionFinEnum V
  dsimp only [optimumBranchingM, optimumBranchingParent]
  rw [edmondsTableM_ret_eq_edmonds]

omit [IsOrderedAddMonoid β] in
/-- **`O(n³)` charged step bound for `optimumBranchingM`**: at most `15 * (n + 1) ^ 3` ticks on an
`n`-vertex digraph. -/
theorem time_optimumBranchingM_le {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    (optimumBranchingM G w).time ≤ 15 * (FinEnum.card V + 1) ^ 3 := by
  let _ := optionFinEnum V
  exact time_edmondsTableM_le G.superRootDigraph (superRootCost w) none

/-- **Correctness and optimality of `optimumBranching`**: `optimumBranching G w` is a branching
contained in `G`, and maximizes `arcCost B w` over all branchings `B ≤ G`. -/
theorem optimumBranching_spec {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    (optimumBranching G w).IsBranching ∧ optimumBranching G w ≤ G ∧
      ∀ (B : Digraph V) [DecidableRel B.Adj], B.IsBranching → B ≤ G →
        arcCost B w ≤ arcCost (optimumBranching G w) w := by
  classical
  let _ := optionFinEnum V
  obtain ⟨p, hp⟩ := edmonds_superRootDigraph_isSome G w
  have hparent : optimumBranchingParent G w = restrictParent p := by
    simp [optimumBranchingParent, hp]
  have hB_eq : optimumBranching G w = Digraph.restrictOption (Digraph.parentDigraph none p) := by
    rw [optimumBranching, hparent]
    exact branchingDigraph_restrictParent (edmonds_optimal hp).1
  obtain ⟨hT, hTG, hoptT⟩ := edmonds_optimal hp
  obtain ⟨hB, hBext, hBG⟩ := Digraph.restrictOption_spec hT
  have hB_branch : (optimumBranching G w).IsBranching := hB_eq ▸ hB
  have hB_le : optimumBranching G w ≤ G := hB_eq ▸ hBG G hTG
  refine ⟨hB_branch, hB_le, fun B _ hB' hBG' => ?_⟩
  have hB'_arb : B.superRootExtend.IsInArborescence none :=
    Digraph.isBranching_iff_isInArborescence_superRootExtend.mp hB'
  have hB'_le : B.superRootExtend ≤ G.superRootDigraph :=
    Digraph.superRootExtend_le_superRootDigraph hBG'
  have hcmp := hoptT B.superRootExtend hB'_arb hB'_le
  have hext : (optimumBranching G w).superRootExtend = Digraph.parentDigraph none p := by
    rw [hB_eq]
    exact hBext
  refine neg_le_neg_iff.mp ?_
  calc -arcCost (optimumBranching G w) w
      = arcCost (optimumBranching G w).superRootExtend (superRootCost w) :=
        (arcCost_superRootExtend (optimumBranching G w) w).symm
    _ = _ := arcCost_congr _ _ _ _ hext (superRootCost w)
    _ ≤ _ := hcmp
    _ = arcCost B.superRootExtend (superRootCost w) :=
        arcCost_congr _ _ _ _ rfl (superRootCost w)
    _ = -arcCost B w := arcCost_superRootExtend B w

theorem optimumBranching_isBranching {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    (optimumBranching G w).IsBranching :=
  (optimumBranching_spec G w).1

theorem optimumBranching_le {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    optimumBranching G w ≤ G :=
  (optimumBranching_spec G w).2.1

theorem optimumBranching_optimal {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β)
    (B : Digraph V) [DecidableRel B.Adj] (hB : B.IsBranching) (hBG : B ≤ G) :
    arcCost B w ≤ arcCost (optimumBranching G w) w :=
  (optimumBranching_spec G w).2.2 B hB hBG

/-- Minimum-weight branching of `(G, w)` via negated weights. -/
@[expose] def minBranching {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) : Digraph V :=
  optimumBranching G (fun u v => -w u v)

instance {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    DecidableRel (minBranching G w).Adj :=
  inferInstanceAs (DecidableRel (optimumBranching G (fun u v => -w u v)).Adj)

theorem minBranching_isBranching {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    (minBranching G w).IsBranching :=
  optimumBranching_isBranching G (fun u v => -w u v)

theorem minBranching_le {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) :
    minBranching G w ≤ G :=
  optimumBranching_le G (fun u v => -w u v)

theorem minBranching_optimal {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β)
    (B : Digraph V) [DecidableRel B.Adj] (hB : B.IsBranching) (hBG : B ≤ G) :
    arcCost (minBranching G w) w ≤ arcCost B w := by
  classical
  have h := optimumBranching_optimal G (fun u v => -w u v) B hB hBG
  have hM : arcCost (optimumBranching G (fun u v => -w u v)) (fun u v => -w u v) =
      -arcCost (minBranching G w) w := by
    rw [arcCost_neg]
    congr 1
  rw [arcCost_neg, hM] at h
  exact neg_le_neg_iff.mp h

/-! ### Edmonds (1967, Section 2) weight-shift and rooted reductions -/

section EdmondsSection2

/-- Adding a uniform constant `h` to every arc shifts `arcCost` by `card_arcs * h`. -/
theorem arcCost_add_const {V β : Type*} [Fintype V] [AddCommMonoid β]
    (T : Digraph V) [DecidableRel T.Adj] (w : V → V → β) (h : β) :
    arcCost T (fun u v => w u v + h) =
      arcCost T w + (Finset.univ.filter fun e : V × V => T.Adj e.1 e.2).card • h := by
  unfold arcCost
  rw [Finset.sum_add_distrib, Finset.sum_const]

private theorem arcCost_eq_sum_arcs_of_le {V β : Type*} [Fintype V] [AddCommMonoid β]
    {B G : Digraph V} [DecidableRel B.Adj] [DecidableRel G.Adj] (hBG : B ≤ G) (w : V → V → β) :
    arcCost B w =
      ∑ e ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2),
        if B.Adj e.1 e.2 then w e.1 e.2 else 0 := by
  unfold arcCost
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hG : G.Adj e.1 e.2
  · simp [hG]
  · have hB : ¬B.Adj e.1 e.2 := fun h => hG (hBG h)
    simp [hG, hB]

/-- For any two subdigraphs `B₁, B₂ ≤ G`, the weight difference `arcCost B₁ w - arcCost B₂ w` is
bounded above by the sum of `max (w e) (-w e)` over all arcs of `G`. -/
theorem arcCost_sub_arcCost_le {V : Type*} [Fintype V]
    {B₁ B₂ G : Digraph V} [DecidableRel B₁.Adj] [DecidableRel B₂.Adj] [DecidableRel G.Adj]
    (h1 : B₁ ≤ G) (h2 : B₂ ≤ G) (w : V → V → β) :
    arcCost B₁ w - arcCost B₂ w ≤
      ∑ e ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2),
        max (w e.1 e.2) (-w e.1 e.2) := by
  have hmax_nonneg : ∀ x : β, 0 ≤ max x (-x) := fun x => by
    rcases le_total (0 : β) x with hx | hx
    · exact hx.trans (le_max_left _ _)
    · exact (neg_nonneg.mpr hx).trans (le_max_right _ _)
  rw [arcCost_eq_sum_arcs_of_le h1, arcCost_eq_sum_arcs_of_le h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases hB1 : B₁.Adj e.1 e.2 <;> by_cases hB2 : B₂.Adj e.1 e.2
  · simp only [hB1, hB2, ite_true, sub_self]
    exact hmax_nonneg _
  · simp only [hB1, hB2, ite_true, ite_false, sub_zero]
    exact le_max_left _ _
  · simp only [hB1, hB2, ite_false, ite_true, zero_sub]
    exact le_max_right _ _
  · simp only [hB1, hB2, ite_false, sub_zero]
    exact hmax_nonneg _

/-- **Edmonds (1967, Section 2) weight-shift reduction:** Adding `h > ∑_{e ∈ G} |w_e|` to every
arc weight makes an optimum branching maximize the number of arcs across all branchings `B ≤ G`,
and break ties by `arcCost · w`. When `G` contains a spanning out-arborescence, the shifted
optimum branching is a maximum-weight spanning out-arborescence of `(G, w)`. -/
theorem edmonds_shift_weight_branching {V : Type*} [FinEnum V]
    (G : Digraph V) [DecidableRel G.Adj] (w : V → V → β) (h : β)
    (hh : ∑ e ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2),
        max (w e.1 e.2) (-w e.1 e.2) < h) :
    let Bstar := optimumBranching G (fun u v => w u v + h)
    Bstar.IsBranching ∧ Bstar ≤ G ∧
      (∀ (B : Digraph V) [DecidableRel B.Adj], B.IsBranching → B ≤ G →
        (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card ≤
          (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card ∧
        ((Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card =
            (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card →
          arcCost B w ≤ arcCost Bstar w)) ∧
      (Nonempty V →
        (∃ r, ∃ T : Digraph V, T.IsOutArborescence r ∧ T ≤ G) →
        (∃ r, Bstar.IsOutArborescence r) ∧
          ∀ r (T : Digraph V) [DecidableRel T.Adj], T.IsOutArborescence r → T ≤ G →
            arcCost T w ≤ arcCost Bstar w) := by
  classical
  dsimp only
  set Bstar := optimumBranching G (fun u v => w u v + h)
  let _ : DecidableRel Bstar.Adj := inferInstanceAs
    (DecidableRel (optimumBranching G (fun u v => w u v + h)).Adj)
  have hBstar := optimumBranching_isBranching G (fun u v => w u v + h)
  have hBstar_le := optimumBranching_le G (fun u v => w u v + h)
  have hsum_nonneg : 0 ≤ ∑ e ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2),
      max (w e.1 e.2) (-w e.1 e.2) := by
    refine Finset.sum_nonneg fun e _ => ?_
    rcases le_total (0 : β) (w e.1 e.2) with hx | hx
    · exact hx.trans (le_max_left _ _)
    · exact (neg_nonneg.mpr hx).trans (le_max_right _ _)
  have hh_pos : 0 < h := lt_of_le_of_lt hsum_nonneg hh
  have hmax : ∀ (B : Digraph V) [DecidableRel B.Adj], B.IsBranching → B ≤ G →
      (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card ≤
        (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card ∧
      ((Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card =
          (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card →
        arcCost B w ≤ arcCost Bstar w) := by
    intro B _ hB hBG
    set kB := (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card
    set kS := (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card
    have hopt := optimumBranching_optimal G (fun u v => w u v + h) B hB hBG
    rw [arcCost_add_const, arcCost_add_const] at hopt
    change arcCost B w + kB • h ≤ arcCost Bstar w + kS • h at hopt
    have hk_le : kB ≤ kS := by
      by_contra hlt
      have hk_gt : 1 + kS ≤ kB := by omega
      have hmul : h + kS • h ≤ kB • h := by
        calc h + kS • h = (1 : ℕ) • h + kS • h := by rw [one_nsmul]
          _ = (1 + kS) • h := (add_nsmul h 1 kS).symm
          _ ≤ kB • h := nsmul_le_nsmul_left hh_pos.le hk_gt
      have hcmp : h + arcCost B w + kS • h ≤ arcCost Bstar w + kS • h := by
        calc h + arcCost B w + kS • h
            = h + (arcCost B w + kS • h) := add_assoc h _ _
          _ = arcCost B w + (h + kS • h) := add_left_comm h _ _
          _ ≤ arcCost B w + kB • h := add_le_add_right hmul _
          _ ≤ arcCost Bstar w + kS • h := hopt
      have hdiff : h ≤ arcCost Bstar w - arcCost B w := by
        rw [le_sub_iff_add_le]
        exact le_of_add_le_add_right hcmp
      have hbound := arcCost_sub_arcCost_le hBstar_le hBG w
      exact absurd (lt_of_le_of_lt (hdiff.trans hbound) hh) (lt_irrefl _)
    refine ⟨hk_le, fun heq => ?_⟩
    rw [heq] at hopt
    exact le_of_add_le_add_right hopt
  refine ⟨hBstar, hBstar_le, hmax, fun _ ⟨r₀, T₀, hT₀, hT₀G⟩ => ?_⟩
  let _ := T₀.Adj
  have hT₀_branch := Digraph.IsBranching.of_isOutArborescence hT₀
  have hT₀_card : (Finset.univ.filter fun e : V × V => T₀.Adj e.1 e.2).card =
      Fintype.card V - 1 :=
    (Digraph.IsBranching.isOutArborescence_iff_card_arcs hT₀_branch).mp ⟨r₀, hT₀⟩
  have hS_ge : Fintype.card V - 1 ≤
      (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card :=
    hT₀_card ▸ (hmax T₀ hT₀_branch hT₀G).1
  have hS_le :
      (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card ≤ Fintype.card V - 1 :=
    hBstar.card_arcs_le
  have hS_card :
      (Finset.univ.filter fun e : V × V => Bstar.Adj e.1 e.2).card = Fintype.card V - 1 :=
    le_antisymm hS_le hS_ge
  refine ⟨(Digraph.IsBranching.isOutArborescence_iff_card_arcs hBstar).mpr hS_card, ?_⟩
  intro r T _ hT hTG
  have hT_branch := Digraph.IsBranching.of_isOutArborescence hT
  have hT_card : (Finset.univ.filter fun e : V × V => T.Adj e.1 e.2).card =
      Fintype.card V - 1 :=
    (Digraph.IsBranching.isOutArborescence_iff_card_arcs hT_branch).mp ⟨r, hT⟩
  exact (hmax T hT_branch hTG).2 (hT_card.trans hS_card.symm)

/-- Subgraph obtained from `G` by deleting all arcs entering a designated root `r₀`. -/
@[expose] def rootedDigraph {V : Type*} (G : Digraph V) (r₀ : V) : Digraph V where
  Adj u v := v ≠ r₀ ∧ G.Adj u v

instance {V : Type*} [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (r₀ : V) :
    DecidableRel (rootedDigraph G r₀).Adj :=
  fun u v => inferInstanceAs (Decidable (v ≠ r₀ ∧ G.Adj u v))

@[simp]
theorem rootedDigraph_adj {V : Type*} {G : Digraph V} {r₀ u v : V} :
    (rootedDigraph G r₀).Adj u v ↔ v ≠ r₀ ∧ G.Adj u v := Iff.rfl

theorem rootedDigraph_le {V : Type*} (G : Digraph V) (r₀ : V) : rootedDigraph G r₀ ≤ G :=
  fun _ _ h => h.2

/-- **Edmonds (1967, Section 2) rooted spanning out-arborescence reduction:** Deleting incoming
arcs of `r₀` and shifting remaining arc weights by `h > ∑ |w_e|` reduces maximum-weight
`r₀`-rooted spanning out-arborescences to optimum branchings. -/
theorem edmonds_rooted_outArborescence_of_shift {V : Type*} [FinEnum V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.Adj] (r₀ : V) (w : V → V → β) (h : β)
    (hh : ∑ e ∈ Finset.univ.filter (fun e : V × V => (rootedDigraph G r₀).Adj e.1 e.2),
        max (w e.1 e.2) (-w e.1 e.2) < h)
    (hexists : ∃ T : Digraph V, T.IsOutArborescence r₀ ∧ T ≤ G) :
    let Bstar := optimumBranching (rootedDigraph G r₀) (fun u v => w u v + h)
    Bstar.IsOutArborescence r₀ ∧ Bstar ≤ G ∧
      ∀ (T : Digraph V) [DecidableRel T.Adj], T.IsOutArborescence r₀ → T ≤ G →
        arcCost T w ≤ arcCost Bstar w := by
  classical
  dsimp only
  set Gr := rootedDigraph G r₀
  set Bstar := optimumBranching Gr (fun u v => w u v + h)
  let _ : DecidableRel Bstar.Adj := inferInstanceAs
    (DecidableRel (optimumBranching Gr (fun u v => w u v + h)).Adj)
  obtain ⟨T₀, hT₀, hT₀G⟩ := hexists
  have hT₀r : T₀ ≤ Gr := fun u v huv =>
    ⟨fun hvr => (Digraph.isOutArborescence_iff.mp hT₀).1 u (hvr ▸ huv), hT₀G huv⟩
  have hres := edmonds_shift_weight_branching Gr w h hh
  have hBr : Bstar ≤ Gr := hres.2.1
  obtain ⟨⟨r, hBstar⟩, hopt⟩ := hres.2.2.2 ‹Nonempty V› ⟨r₀, T₀, hT₀, hT₀r⟩
  have hr_eq : r = r₀ := by
    by_contra hne
    obtain ⟨u, hu, -⟩ := (Digraph.isOutArborescence_iff.mp hBstar).2.1 r₀ (Ne.symm hne)
    exact (hBr hu).1 rfl
  rw [hr_eq] at hBstar
  refine ⟨hBstar, hBr.trans (rootedDigraph_le G r₀), fun T _ hT hTG => ?_⟩
  have hTr : T ≤ Gr := fun u v huv =>
    ⟨fun hvr => (Digraph.isOutArborescence_iff.mp hT).1 u (hvr ▸ huv), hTG huv⟩
  exact hopt r₀ T hT hTr

end EdmondsSection2

end Solvers

end Cslib.Algorithms.Lean.Arborescence
