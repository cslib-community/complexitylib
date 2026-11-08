/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.HopcroftKarp
public import Complexity.Algorithms.Lean.MaxFlow.WeightedMatching
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Ring

/-!
# The Hungarian Method for the Assignment Problem

An executable `TimeM ℕ` implementation of the **Hungarian method** for the `n × n` assignment
problem with integer costs `c : Fin n × Fin n → ℤ` ([Kuhn1955]; [Munkres1957]; [CLRS2022], §25.3),
in the `O(n³)` form that grows one alternating tree per row and keeps a slack array (the
reduced-cost technique of [EdmondsKarp1972]). It is proved to return a minimum-cost perfect matching
together with integral feasible potentials whose total equals the cost, which is Egerváry's
min–max theorem for the assignment problem ([Schrijver2003], Ch. 17), in at most
`6 n³ + 6 n² + 3 n` charged steps.

## Algorithm and source mapping

Costs are minimized. Row potentials `y`, column potentials `z` and the matching (a column-indexed
mate table `mate`, as in `Complexity.Algorithms.Lean.MaxFlow.HopcroftKarp`) are kept with every
reduced cost `hgRed c y z u v = c (u, v) - y u - z v` nonnegative and every matched edge tight
(reduced cost `0`).

1. **Row reduction:** `y u = min_v c (u, v)` and `z = 0` give feasible potentials.
2. **One phase per row `r` (`hgPhaseM`):** the alternating tree is grown from the free row `r`.
   `minv j` is the least reduced cost from a tree row to the non-tree column `j`, and `path j` is
   the alternating path from `r` to `j` that attains it. Each round of `hgLoopM` picks the
   non-tree column `j₁` of least slack `δ`, then raises the tree rows and lowers the tree columns
   by `δ` (`hgDualM`), which keeps feasibility and makes the last edge to `j₁` tight. If `j₁` is
   free, the matching is augmented along `path j₁`. This is an augmenting path in the sense of
   `Complexity.Algorithms.Lean.MaxFlow.AugmentingPath`, so `r` becomes matched. Otherwise `j₁` and
   its mate join the tree and the slacks are relaxed through the new row (`hgExtendM`). A round
   that does not augment adds a matched column to the tree, so the phase augments within `n`
   rounds.
3. **Certificate:** after `n` phases the matching is perfect and tight for feasible potentials, so
   weak duality and complementary slackness (`Complexity.Algorithms.Lean.MaxFlow.WeightedMatching`)
   show that it has minimum cost and that its cost is `∑ y + ∑ z`.

## Cost model and limitations

* **Charged (`TimeM ℕ` ticks):** `n` ticks for each row minimum during row reduction (`n²`), and
  `2 n` ticks to allocate the potential and mate tables. Each phase costs `4 n` ticks to
  initialise the tree, slack and path tables. Each round costs `n` ticks for the argmin scan,
  `3 n` for the dual adjustment, and then either `1 + 2 n` to extend the tree and relax, or
  `1` tick per rematched column (`≤ n`) to augment. Extracting the matching costs `n` ticks.
  There are at most `n` rounds per phase and `n` phases, giving the bound of `hungarianM_time_le`.
* **Abstract unit-cost primitives:** `Vector` indexing and update (`vget`, `vset`), list cons
  (paths are stored as persistent lists that share tails, in place of a predecessor array),
  `Finset.insert`, comparisons and arithmetic on `ℤ`, and evaluating `c (u, v)` are `O(1)` within
  each charged step, as in `Complexity.Algorithms.Lean.MaxFlow.EdmondsKarp` and
  `Complexity.Algorithms.Lean.MaxFlow.HopcroftKarp`. This is an abstract RAM-style step count with
  unit-cost integers, not Turing-machine time.
* **Scope:** square instances of the complete bipartite graph with integer costs. Rectangular
  instances and forbidden edges have to be encoded by padding and by large costs. Maximum-weight
  assignment is obtained by negating costs.

## Main definitions

* `hgRed`: reduced costs; `HgState`: the state of a phase.
* `hgArgminM`, `hgDualM`, `hgRelaxM`, `hgExtendM`, `hgInitM`, `hgLoopM`, `hgPhaseM`, `hgRowsM`:
  the steps of one phase and the loop over rows.
* `ofFnTickM`, `ofFnM`: vectors built entry by entry, with one tick per entry, or by running a
  charged program per entry.
* `HungarianOutput`, `hungarianM`: the full algorithm.

## Main results

* `hungarianM_correct`: the output matching is a minimum-cost perfect matching
  (`IsMinCostPerfectMatching`), the output potentials are feasible (`IsFeasiblePotential`), and
  the matching cost equals the total potential.
* `hungarianM_time_le`: at most `6 n³ + 6 n² + 3 n` charged steps.
* `exists_isMinCostPerfectMatching_potential_eq` (**Egerváry's theorem**, integral form), and
  `isMinCostPerfectMatching_iff_exists_potential` (min–max form): a perfect matching has minimum
  cost iff some integral feasible potentials have total equal to its cost.
* `exists_perm_assignment`: the permutation form `min_σ ∑ u, c (u, σ u) = max (∑ y + ∑ z)`.

## References

* [H. W. Kuhn, *The Hungarian Method for the Assignment Problem*][Kuhn1955]
* [J. Munkres, *Algorithms for the Assignment and Transportation Problems*][Munkres1957]
* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, 4th ed.][CLRS2022]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean.TimeM

/-! ### Charged vector construction -/

/-- Build a vector entry by entry, charging one step per entry. -/
@[expose] def ofFnTickM {α : Type*} : (n : ℕ) → (Fin n → α) → TimeM ℕ (Vector α n)
  | 0, _ => pure #v[]
  | n + 1, f => do
    ✓
    let rest ← ofFnTickM n fun i => f i.castSucc
    pure (rest.push (f (Fin.last n)))

@[simp] theorem vget_ofFnTickM_ret {α : Type*} (n : ℕ) (f : Fin n → α) (i : Fin n) :
    vget (ofFnTickM n f).ret i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [ofFnTickM, TimeM.ret_bind, TimeM.ret_pure, vget]
    by_cases hi : i.1 < n
    · rw [Vector.getElem_push_lt hi]
      exact ih (fun j => f j.castSucc) ⟨i.1, hi⟩
    · have : i = Fin.last n := Fin.ext (by have := i.2; simp; omega)
      subst this
      simp

@[simp] theorem ofFnTickM_time {α : Type*} (n : ℕ) (f : Fin n → α) :
    (ofFnTickM n f).time = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ofFnTickM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih]
    omega

/-- Build a vector by running a charged program for each entry, in index order. -/
@[expose] def ofFnM {α : Type*} : (n : ℕ) → (Fin n → TimeM ℕ α) → TimeM ℕ (Vector α n)
  | 0, _ => pure #v[]
  | n + 1, f => do
    let rest ← ofFnM n fun i => f i.castSucc
    let a ← f (Fin.last n)
    pure (rest.push a)

@[simp] theorem vget_ofFnM_ret {α : Type*} (n : ℕ) (f : Fin n → TimeM ℕ α) (i : Fin n) :
    vget (ofFnM n f).ret i = (f i).ret := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [ofFnM, TimeM.ret_bind, TimeM.ret_pure, vget]
    by_cases hi : i.1 < n
    · rw [Vector.getElem_push_lt hi]
      exact ih (fun j => f j.castSucc) ⟨i.1, hi⟩
    · have : i = Fin.last n := Fin.ext (by have := i.2; simp; omega)
      subst this
      simp

theorem ofFnM_time_le {α : Type*} (n : ℕ) (f : Fin n → TimeM ℕ α) {t : ℕ}
    (h : ∀ i, (f i).time ≤ t) : (ofFnM n f).time ≤ n * t := by
  induction n with
  | zero => simp [ofFnM]
  | succ n ih =>
    simp only [ofFnM, TimeM.time_bind, TimeM.time_pure]
    have h1 := ih (fun i => f i.castSucc) (fun i => h _)
    have h2 := h (Fin.last n)
    rw [Nat.succ_mul]
    omega

/-! ### Algorithm -/

section Algorithm

variable {n : ℕ}

/-- Minimum of row `u` of `c`, scanning all `n` columns with one step each. -/
@[expose] def hgRowMinM (c : Fin n × Fin n → ℤ) (u : Fin n) : TimeM ℕ ℤ :=
  foldlTickM (fun a v => min a (c (u, v))) (List.finRange n) (c (u, u))

/-- Reduced cost `c (u, v) - y u - z v`. -/
@[expose] def hgRed (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n) (u v : Fin n) : ℤ :=
  c (u, v) - vget y u - vget z v

/-- State of one phase of the Hungarian method (growing an alternating tree from one root). -/
structure HgState (n : ℕ) where
  /-- Row potentials. -/
  y : Vector ℤ n
  /-- Column potentials. -/
  z : Vector ℤ n
  /-- Matched row of each column. -/
  mate : Vector (Option (Fin n)) n
  /-- Columns already in the tree. -/
  used : Vector Bool n
  /-- Rows in the tree. -/
  tree : Vector Bool n
  /-- Slack of each column not in the tree: its minimum reduced cost from a tree row. -/
  minv : Vector ℤ n
  /-- For each column, the tree path reaching it, as `(row, column)` edges, last edge first. -/
  path : Vector (List (Fin n × Fin n)) n

/-- One argmin scan step: keep the unused column of smaller slack. -/
@[expose] def hgArgminStep (s : HgState n) (b : Option (Fin n)) (j : Fin n) : Option (Fin n) :=
  if vget s.used j then b
  else match b with
    | none => some j
    | some k => if vget s.minv j < vget s.minv k then some j else some k

/-- Unused column of minimum slack (`n` steps). -/
@[expose] def hgArgminM (s : HgState n) : TimeM ℕ (Option (Fin n)) :=
  foldlTickM (hgArgminStep s) (List.finRange n) none

/-- Dual adjustment by `δ`: raise tree rows, lower tree columns, reduce the slack of the other
columns (`3 n` steps). -/
@[expose] def hgDualM (s : HgState n) (δ : ℤ) : TimeM ℕ (HgState n) := do
  let y ← ofFnTickM n fun i => if vget s.tree i then vget s.y i + δ else vget s.y i
  let z ← ofFnTickM n fun j => if vget s.used j then vget s.z j - δ else vget s.z j
  let minv ← ofFnTickM n fun j => if vget s.used j then vget s.minv j else vget s.minv j - δ
  pure { s with y, z, minv }

/-- Relax the slacks of the unused columns through the new tree row `i`, the mate of the column
`j₁` just added to the tree (`2 n` steps). -/
@[expose] def hgRelaxM (s : HgState n) (c : Fin n × Fin n → ℤ) (i j₁ : Fin n) :
    TimeM ℕ (HgState n) := do
  let minv ← ofFnTickM n fun j =>
    if vget s.used j then vget s.minv j else min (vget s.minv j) (hgRed c s.y s.z i j)
  let path ← ofFnTickM n fun j =>
    if !vget s.used j && decide (hgRed c s.y s.z i j < vget s.minv j) then
      (i, j) :: vget s.path j₁
    else vget s.path j
  pure { s with minv, path }

/-- Initial state of the phase rooted at the free row `r` (`4 n` steps). -/
@[expose] def hgInitM (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n)
    (r : Fin n) : TimeM ℕ (HgState n) := do
  let used ← ofFnTickM n fun _ => false
  let tree ← ofFnTickM n fun i => decide (i = r)
  let minv ← ofFnTickM n fun j => hgRed c y z r j
  let path ← ofFnTickM n fun j => [(r, j)]
  pure ⟨y, z, mate, used, tree, minv, path⟩

/-- Add the column `j₁` and its mate `i₀` to the tree, then relax through `i₀` (`2 n + 1` steps). -/
@[expose] def hgExtendM (c : Fin n × Fin n → ℤ) (s : HgState n) (j₁ i₀ : Fin n) :
    TimeM ℕ (HgState n) := do
  ✓
  hgRelaxM { s with used := vset s.used j₁ true, tree := vset s.tree i₀ true } c i₀ j₁

/-- The tree-growing loop of one phase: pick the unused column `j₁` of minimum slack `δ`, adjust
the potentials by `δ`, then augment along the tree path of `j₁` if it is free, or add `j₁` and its
mate to the tree and relax. -/
@[expose] def hgLoopM (c : Fin n × Fin n → ℤ) : ℕ → HgState n → TimeM ℕ (HgState n)
  | 0, s => pure s
  | fuel + 1, s => do
    match ← hgArgminM s with
    | none => pure s
    | some j₁ =>
      let s ← hgDualM s (vget s.minv j₁)
      match vget s.mate j₁ with
      | none =>
        let mate ← hkApplyEdgesM s.mate (vget s.path j₁)
        pure { s with mate }
      | some i₀ =>
        let s' ← hgExtendM c s j₁ i₀
        hgLoopM c fuel s'

/-- One phase: augment the matching by one edge from the free row `r`. -/
@[expose] def hgPhaseM (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (r : Fin n) : TimeM ℕ (HgState n) := do
  let s ← hgInitM c y z mate r
  hgLoopM c n s

/-- Run one phase per row of the list. -/
@[expose] def hgRowsM (c : Fin n × Fin n → ℤ) :
    List (Fin n) → HgState n → TimeM ℕ (HgState n)
  | [], s => pure s
  | r :: rs, s => do
    let s' ← hgPhaseM c s.y s.z s.mate r
    hgRowsM c rs s'

/-- Phase state before the first phase: potentials `y`, `z` and matching `mate`, with an empty
tree. -/
@[expose] def hgStartState (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) : HgState n :=
  ⟨y, z, mate, mate.map fun _ => false, mate.map fun _ => false, z, mate.map fun _ => []⟩

end Algorithm

/-- Output of the Hungarian method: a perfect matching and potentials certifying its optimality. -/
structure HungarianOutput (n : ℕ) where
  /-- The perfect matching. -/
  matching : Finset (Fin n × Fin n)
  /-- Row potentials. -/
  y : Fin n → ℤ
  /-- Column potentials. -/
  z : Fin n → ℤ

/-- **The Hungarian method** for the `n × n` assignment problem with integer costs `c`: row
reduction, then one alternating-tree phase per row, then extraction of the matching. -/
@[expose] def hungarianM {n : ℕ} (c : Fin n × Fin n → ℤ) : TimeM ℕ (HungarianOutput n) := do
  let y ← ofFnM n (hgRowMinM c)
  let z ← replicateM n 0
  let mate ← replicateM n none
  let s ← hgRowsM c (List.finRange n) (hgStartState y z mate)
  let matching ← foldlTickM (hkMatchingStep s.mate) (List.finRange n) ∅
  pure ⟨matching, vget s.y, vget s.z⟩

/-! ### Specification of the phase steps -/

section Spec

variable {n : ℕ} {c : Fin n × Fin n → ℤ}

/-- Invariant of the argmin scan after the columns `S`. -/
private def HgArgminOK (s : HgState n) (S : List (Fin n)) (b : Option (Fin n)) : Prop :=
  (b = none → ∀ j ∈ S, vget s.used j = true) ∧
    ∀ k, b = some k → vget s.used k = false ∧ ∀ j ∈ S, vget s.used j = false →
      vget s.minv k ≤ vget s.minv j

private theorem hgArgminOK_nil (s : HgState n) : HgArgminOK s [] none := by
  unfold HgArgminOK
  simp

private theorem hgArgmin_foldl (s : HgState n) (l : List (Fin n)) :
    ∀ (S : List (Fin n)) (b : Option (Fin n)), HgArgminOK s S b →
      HgArgminOK s (S ++ l) (l.foldl (hgArgminStep s) b) := by
  induction l with
  | nil => intro S b h; simpa using h
  | cons x l ih =>
    intro S b h
    rw [List.foldl_cons, show S ++ x :: l = (S ++ [x]) ++ l by simp]
    apply ih
    unfold HgArgminOK at h ⊢
    unfold hgArgminStep
    by_cases hx : vget s.used x = true
    · rw [ite_eq_left hx]
      refine ⟨fun hb j hj => ?_, fun k hk => ?_⟩
      · rcases List.mem_append.mp hj with hj | hj
        · exact h.1 hb j hj
        · rw [List.mem_singleton.mp hj]
          exact hx
      · obtain ⟨hk1, hk2⟩ := h.2 k hk
        refine ⟨hk1, fun j hj hju => ?_⟩
        rcases List.mem_append.mp hj with hj | hj
        · exact hk2 j hj hju
        · rw [List.mem_singleton.mp hj] at hju
          rw [hx] at hju
          exact absurd hju Bool.noConfusion
    · rw [ite_eq_right hx]
      have hx' : vget s.used x = false := Bool.eq_false_iff.mpr hx
      cases b with
      | none =>
        refine ⟨fun hb => (nomatch hb), fun k hk => ?_⟩
        have hkx : x = k := Option.some.inj hk
        subst hkx
        refine ⟨hx', fun j hj hju => ?_⟩
        rcases List.mem_append.mp hj with hj | hj
        · rw [h.1 rfl j hj] at hju
          exact absurd hju Bool.noConfusion
        · rw [List.mem_singleton.mp hj]
      | some k₀ =>
        obtain ⟨hk1, hk2⟩ := h.2 k₀ rfl
        refine ⟨fun hb => ?_, fun k hk => ?_⟩
        · dsimp only at hb
          split_ifs at hb
        · dsimp only at hk
          split_ifs at hk with hlt
          · have hkx : x = k := Option.some.inj hk
            subst hkx
            refine ⟨hx', fun j hj hju => ?_⟩
            rcases List.mem_append.mp hj with hj | hj
            · exact hlt.le.trans (hk2 j hj hju)
            · rw [List.mem_singleton.mp hj]
          · have hkx : k₀ = k := Option.some.inj hk
            subst hkx
            refine ⟨hk1, fun j hj hju => ?_⟩
            rcases List.mem_append.mp hj with hj | hj
            · exact hk2 j hj hju
            · rw [List.mem_singleton.mp hj]
              exact not_lt.mp hlt

private theorem hgArgminM_none {s : HgState n} (h : (hgArgminM s).ret = none) :
    ∀ j, vget s.used j = true := by
  have := hgArgmin_foldl s (List.finRange n) [] none (hgArgminOK_nil s)
  rw [hgArgminM, foldlTickM_ret] at h
  rw [h] at this
  intro j
  exact this.1 rfl j (by simp)

private theorem hgArgminM_some {s : HgState n} {k : Fin n} (h : (hgArgminM s).ret = some k) :
    vget s.used k = false ∧ ∀ j, vget s.used j = false → vget s.minv k ≤ vget s.minv j := by
  have := hgArgmin_foldl s (List.finRange n) [] none (hgArgminOK_nil s)
  rw [hgArgminM, foldlTickM_ret] at h
  rw [h] at this
  obtain ⟨h1, h2⟩ := this.2 k rfl
  exact ⟨h1, fun j hj => h2 j (by simp) hj⟩

private theorem hgArgminM_time (s : HgState n) : (hgArgminM s).time = n := by
  simp [hgArgminM]

/-! #### Field lemmas -/

private theorem hgDualM_mate (s : HgState n) (δ : ℤ) : (hgDualM s δ).ret.mate = s.mate := rfl
private theorem hgDualM_used (s : HgState n) (δ : ℤ) : (hgDualM s δ).ret.used = s.used := rfl
private theorem hgDualM_tree (s : HgState n) (δ : ℤ) : (hgDualM s δ).ret.tree = s.tree := rfl
private theorem hgDualM_path (s : HgState n) (δ : ℤ) : (hgDualM s δ).ret.path = s.path := rfl

private theorem hgDualM_y (s : HgState n) (δ : ℤ) (i : Fin n) :
    vget (hgDualM s δ).ret.y i = if vget s.tree i = true then vget s.y i + δ else vget s.y i := by
  simp [hgDualM]

private theorem hgDualM_z (s : HgState n) (δ : ℤ) (j : Fin n) :
    vget (hgDualM s δ).ret.z j = if vget s.used j = true then vget s.z j - δ else vget s.z j := by
  simp [hgDualM]

private theorem hgDualM_minv (s : HgState n) (δ : ℤ) (j : Fin n) :
    vget (hgDualM s δ).ret.minv j =
      if vget s.used j = true then vget s.minv j else vget s.minv j - δ := by
  simp [hgDualM]

private theorem hgDualM_time (s : HgState n) (δ : ℤ) : (hgDualM s δ).time = 3 * n := by
  simp only [hgDualM, TimeM.time_bind, ofFnTickM_time, TimeM.time_pure]
  omega

private theorem hgRelaxM_y (s : HgState n) (i j₁ : Fin n) : (hgRelaxM s c i j₁).ret.y = s.y := rfl
private theorem hgRelaxM_z (s : HgState n) (i j₁ : Fin n) : (hgRelaxM s c i j₁).ret.z = s.z := rfl
private theorem hgRelaxM_mate (s : HgState n) (i j₁ : Fin n) :
    (hgRelaxM s c i j₁).ret.mate = s.mate := rfl
private theorem hgRelaxM_used (s : HgState n) (i j₁ : Fin n) :
    (hgRelaxM s c i j₁).ret.used = s.used := rfl
private theorem hgRelaxM_tree (s : HgState n) (i j₁ : Fin n) :
    (hgRelaxM s c i j₁).ret.tree = s.tree := rfl

private theorem hgRelaxM_minv (s : HgState n) (i j₁ j : Fin n) :
    vget (hgRelaxM s c i j₁).ret.minv j =
      if vget s.used j = true then vget s.minv j
      else min (vget s.minv j) (hgRed c s.y s.z i j) := by
  simp [hgRelaxM]

private theorem hgRelaxM_path (s : HgState n) (i j₁ j : Fin n) :
    vget (hgRelaxM s c i j₁).ret.path j =
      if vget s.used j = false ∧ hgRed c s.y s.z i j < vget s.minv j then
        (i, j) :: vget s.path j₁
      else vget s.path j := by
  simp only [hgRelaxM, TimeM.ret_bind, TimeM.ret_pure, vget_ofFnTickM_ret]
  by_cases h1 : vget s.used j = false <;> by_cases h2 : hgRed c s.y s.z i j < vget s.minv j <;>
    simp [h1, h2]

private theorem hgRelaxM_time (s : HgState n) (i j₁ : Fin n) :
    (hgRelaxM s c i j₁).time = 2 * n := by
  simp only [hgRelaxM, TimeM.time_bind, ofFnTickM_time, TimeM.time_pure]
  omega

private theorem hgInitM_y (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInitM c y z mate r).ret.y = y := rfl
private theorem hgInitM_z (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInitM c y z mate r).ret.z = z := rfl
private theorem hgInitM_mate (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInitM c y z mate r).ret.mate = mate := rfl

private theorem hgInitM_used (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r j : Fin n) :
    vget (hgInitM c y z mate r).ret.used j = false := by
  simp [hgInitM]

private theorem hgInitM_tree (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r i : Fin n) :
    vget (hgInitM c y z mate r).ret.tree i = decide (i = r) := by
  simp [hgInitM]

private theorem hgInitM_minv (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r j : Fin n) :
    vget (hgInitM c y z mate r).ret.minv j = hgRed c y z r j := by
  simp [hgInitM]

private theorem hgInitM_path (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r j : Fin n) :
    vget (hgInitM c y z mate r).ret.path j = [(r, j)] := by
  simp [hgInitM]

private theorem hgInitM_time (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInitM c y z mate r).time = 4 * n := by
  simp only [hgInitM, TimeM.time_bind, ofFnTickM_time, TimeM.time_pure]
  omega

/-! #### Invariants -/

/-- `q` is the stored tree path of column `j` (last edge first): it starts at the root `r`, ends
at `j`, alternates through matched edges, has tight tail edges inside the tree, and its last edge
has reduced cost `0` if `j` is in the tree and `minv j` otherwise. -/
private structure HgPath (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (used tree : Vector Bool n) (minv : Vector ℤ n)
    (r j : Fin n) (q : List (Fin n × Fin n)) : Prop where
  ne_nil : q ≠ []
  head : ∀ e ∈ q.head?, e.2 = j ∧
    hgRed c y z e.1 e.2 = if vget used j = true then 0 else vget minv j
  last : ∀ e ∈ q.getLast?, e.1 = r
  chain : q.IsChain fun a b => vget mate b.2 = some a.1
  nodup_fst : (q.map Prod.fst).Nodup
  nodup_snd : (q.map Prod.snd).Nodup
  tail : ∀ e ∈ q.tail, hgRed c y z e.1 e.2 = 0 ∧ vget used e.2 = true
  tree : ∀ e ∈ q, vget tree e.1 = true

/-- Invariant of the tree-growing loop of the phase rooted at `r`. -/
private structure HgInv (c : Fin n × Fin n → ℤ) (r : Fin n) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (used tree : Vector Bool n) (minv : Vector ℤ n)
    (path : Vector (List (Fin n × Fin n)) n) : Prop where
  matching : IsMatching (fun _ => true) (mateMatching mate)
  feas : ∀ i j, 0 ≤ hgRed c y z i j
  tight : ∀ i j, vget mate j = some i → hgRed c y z i j = 0
  root_free : ∀ j, vget mate j ≠ some r
  used_mate : ∀ j, vget used j = true → ∃ i, vget mate j = some i
  tree_iff : ∀ i, vget tree i = true ↔ i = r ∨ ∃ j, vget used j = true ∧ vget mate j = some i
  minv_le : ∀ i j, vget tree i = true → vget used j = false → vget minv j ≤ hgRed c y z i j
  path_ok : ∀ j, HgPath c y z mate used tree minv r j (vget path j)

/-- Invariant between phases. -/
private structure HgOuter (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) : Prop where
  matching : IsMatching (fun _ => true) (mateMatching mate)
  feas : ∀ i j, 0 ≤ hgRed c y z i j
  tight : ∀ i j, vget mate j = some i → hgRed c y z i j = 0

private theorem mate_inj {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) {i : Fin n} {j j' : Fin n}
    (h : vget mate j = some i) (h' : vget mate j' = some i) : j = j' :=
  hM.2.1 i j j' (mem_mateMatching.mpr h) (mem_mateMatching.mpr h')

section InvLemmas

variable {r : Fin n} {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n}
  {used tree : Vector Bool n} {minv : Vector ℤ n} {path : Vector (List (Fin n × Fin n)) n}

private theorem HgInv.tree_iff_used (h : HgInv c r y z mate used tree minv path) {i j : Fin n}
    (hm : vget mate j = some i) : vget tree i = true ↔ vget used j = true := by
  rw [h.tree_iff]
  constructor
  · rintro (rfl | ⟨j', hj', hm'⟩)
    · exact absurd hm (h.root_free j)
    · rwa [mate_inj h.matching hm hm']
  · intro hj
    exact .inr ⟨j, hj, hm⟩

private theorem HgInv.minv_nonneg (h : HgInv c r y z mate used tree minv path) {j : Fin n}
    (hj : vget used j = false) : 0 ≤ vget minv j := by
  have hp := h.path_ok j
  obtain ⟨e, l, hq⟩ := List.exists_cons_of_ne_nil hp.ne_nil
  have he : e ∈ (vget path j).head? := by simp [hq]
  obtain ⟨h1, h2⟩ := hp.head e he
  rw [hj, ite_eq_right Bool.false_ne_true] at h2
  rw [← h2]
  exact h.feas _ _

private theorem HgPath.mem_cases {used tree : Vector Bool n} {minv : Vector ℤ n} {j : Fin n}
    {q : List (Fin n × Fin n)} (hp : HgPath c y z mate used tree minv r j q) {e : Fin n × Fin n}
    (he : e ∈ q) : e.2 = j ∨ vget used e.2 = true := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.ne_nil
  rcases List.mem_cons.mp he with rfl | he
  · exact .inl (hp.head e rfl).1
  · exact .inr (hp.tail e he).2

end InvLemmas

/-! #### The dual adjustment -/

private theorem hgRed_dual (s : HgState n) (δ : ℤ) (i j : Fin n) :
    hgRed c (hgDualM s δ).ret.y (hgDualM s δ).ret.z i j =
      hgRed c s.y s.z i j - (if vget s.tree i = true then δ else 0) +
        (if vget s.used j = true then δ else 0) := by
  unfold hgRed
  rw [hgDualM_y, hgDualM_z]
  split_ifs <;> omega

private theorem hgInv_dual {r : Fin n} {s : HgState n}
    (h : HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path) {j₁ : Fin n}
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j) :
    HgInv c r (hgDualM s (vget s.minv j₁)).ret.y (hgDualM s (vget s.minv j₁)).ret.z s.mate s.used
      s.tree (hgDualM s (vget s.minv j₁)).ret.minv s.path := by
  have hδ : 0 ≤ vget s.minv j₁ := h.minv_nonneg hj₁
  refine ⟨h.matching, fun i j => ?_, fun i j hm => ?_, h.root_free, h.used_mate, h.tree_iff,
    fun i j hi hj => ?_, fun j => ?_⟩
  · rw [hgRed_dual]
    have := h.feas i j
    by_cases hi : vget s.tree i = true <;> by_cases hj : vget s.used j = true
    · rw [ite_eq_left hi, ite_eq_left hj]; omega
    · rw [ite_eq_left hi, ite_eq_right hj]
      have h1 := h.minv_le i j hi (Bool.eq_false_iff.mpr hj)
      have h2 := hmin j (Bool.eq_false_iff.mpr hj)
      omega
    · rw [ite_eq_right hi, ite_eq_left hj]; omega
    · rw [ite_eq_right hi, ite_eq_right hj]; omega
  · rw [hgRed_dual, h.tight i j hm]
    have hiff := h.tree_iff_used hm
    by_cases hj : vget s.used j = true
    · rw [ite_eq_left (hiff.mpr hj), ite_eq_left hj]; omega
    · rw [ite_eq_right (fun hi => hj (hiff.mp hi)), ite_eq_right hj]; omega
  · rw [hgDualM_minv, hgRed_dual, ite_eq_left hi, hj, ite_eq_right Bool.false_ne_true,
      ite_eq_right Bool.false_ne_true]
    have := h.minv_le i j hi hj
    omega
  · have hp := h.path_ok j
    refine ⟨hp.ne_nil, fun e he => ?_, hp.last, hp.chain, hp.nodup_fst, hp.nodup_snd,
      fun e he => ?_, hp.tree⟩
    · obtain ⟨h1, h2⟩ := hp.head e he
      refine ⟨h1, ?_⟩
      have het := hp.tree e (List.mem_of_mem_head? he)
      rw [hgRed_dual, h2, ite_eq_left het, hgDualM_minv, h1]
      split_ifs <;> omega
    · obtain ⟨h1, h2⟩ := hp.tail e he
      have het := hp.tree e (List.mem_of_mem_tail he)
      refine ⟨?_, h2⟩
      rw [hgRed_dual, h1, ite_eq_left het, ite_eq_left h2]
      omega

private theorem minv_dual_self (s : HgState n) {j₁ : Fin n} (hj₁ : vget s.used j₁ = false) :
    vget (hgDualM s (vget s.minv j₁)).ret.minv j₁ = 0 := by
  rw [hgDualM_minv, hj₁, ite_eq_right Bool.false_ne_true, sub_self]

/-! #### Augmenting along a tree path -/

private theorem hgAugment {r : Fin n} {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n}
    {used tree : Vector Bool n} {minv : Vector ℤ n} {path : Vector (List (Fin n × Fin n)) n}
    (h : HgInv c r y z mate used tree minv path) {j₁ : Fin n} (hj₁ : vget used j₁ = false)
    (hz : vget minv j₁ = 0) (hfree : vget mate j₁ = none) :
    HgOuter c y z (hkApplyEdgesM mate (vget path j₁)).ret ∧
      matchedLeft (mateMatching (hkApplyEdgesM mate (vget path j₁)).ret) =
        insert r (matchedLeft (mateMatching mate)) ∧
      (hkApplyEdgesM mate (vget path j₁)).time ≤ n := by
  have hq := h.path_ok j₁
  have hret : (hkApplyEdgesM mate (vget path j₁)).ret =
      (vget path j₁).foldl (fun mt e => vset mt e.2 (some e.1)) mate := by
    rw [hkApplyEdgesM, foldlTickM_ret]
  have hp : IsAugmentingPath (fun _ => true) (mateMatching mate) (vget path j₁).reverse := by
    refine ⟨List.reverse_ne_nil_iff.mpr hq.ne_nil, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_reverse, List.nodup_reverse]
      exact hq.nodup_fst
    · rw [List.map_reverse, List.nodup_reverse]
      exact hq.nodup_snd
    · intro e he
      rw [List.head?_reverse] at he
      rw [hq.last e he]
      intro hr
      obtain ⟨v, hv⟩ := mem_matchedLeft.mp hr
      exact h.root_free v (mem_mateMatching.mp hv)
    · intro e he
      rw [List.getLast?_reverse] at he
      rw [(hq.head e he).1]
      intro hv
      obtain ⟨u, hu⟩ := mem_matchedRight.mp hv
      rw [mem_mateMatching, hfree] at hu
      exact absurd hu (by simp)
    · rw [List.isChain_reverse]
      refine hq.chain.imp ?_
      intro a b hab
      exact mem_mateMatching.mpr hab
  have hcompat : ∀ u v, (u, v) ∈ mateMatching mate →
      (u ∈ matchedLeft (vget path j₁).toFinset ↔ v ∈ matchedRight (vget path j₁).toFinset) := by
    have := hp.compat_iff h.matching
    rwa [List.toFinset_reverse] at this
  have hmatch : mateMatching (hkApplyEdgesM mate (vget path j₁)).ret =
      augment (mateMatching mate) (vget path j₁).toFinset := by
    rw [hret]
    exact mateMatching_applyEdges mate _ hq.nodup_snd hcompat
  have hM' : IsMatching (fun _ => true) (augment (mateMatching mate) (vget path j₁).toFinset) := by
    have := hp.isMatching_augment h.matching
    rwa [List.toFinset_reverse] at this
  refine ⟨⟨hmatch ▸ hM', h.feas, fun i j hm => ?_⟩, ?_, ?_⟩
  · rw [hret, vget_foldl_apply mate _ hq.nodup_snd] at hm
    rcases hm with hm | ⟨_, hm⟩
    · obtain ⟨e, l, hql⟩ := List.exists_cons_of_ne_nil hq.ne_nil
      rw [hql] at hm
      rcases List.mem_cons.mp hm with he | he
      · have hhead := hq.head e (by simp [hql])
        rw [hj₁, hz] at hhead
        have h2 := hhead.2
        simp only [Bool.false_eq_true, ite_false] at h2
        rw [← he] at h2
        exact h2
      · have htl := hq.tail (i, j) (by simp [hql, he])
        exact htl.1
    · exact h.tight i j hm
  · rw [hmatch, matchedLeft_augment]
    ext u
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (hu | hu)
      · have hu' : u ∈ matchedLeft (vget path j₁).reverse.toFinset := by
          rwa [List.toFinset_reverse]
        rcases hp.matchedLeft_toFinset_subset u hu' with ⟨e, he, hue⟩ | hu''
        · rw [List.head?_reverse] at he
          exact .inl (hue.symm.trans (hq.last e he))
        · exact .inr hu''
      · exact .inr hu
    · rintro (hu | hu)
      · rw [hu]
        obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp
          (mt List.getLast?_eq_none_iff.mp hq.ne_nil)
        have h1 := hq.last e he
        refine .inl (mem_matchedLeft.mpr ⟨e.2, List.mem_toFinset.mpr ?_⟩)
        rw [← h1]
        exact List.mem_of_getLast? he
      · exact .inr hu
  · rw [hkApplyEdgesM, foldlTickM_time]
    simpa using hq.nodup_snd.length_le_card

/-! #### Growing the tree -/

private theorem hgInv_extend {r : Fin n} {s : HgState n}
    (h : HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path) {j₁ i₀ : Fin n}
    (hj₁ : vget s.used j₁ = false) (hz : vget s.minv j₁ = 0) (hm : vget s.mate j₁ = some i₀) :
    HgInv c r s.y s.z s.mate (vset s.used j₁ true) (vset s.tree i₀ true)
      (hgRelaxM { s with used := vset s.used j₁ true, tree := vset s.tree i₀ true } c i₀
        j₁).ret.minv
      (hgRelaxM { s with used := vset s.used j₁ true, tree := vset s.tree i₀ true } c i₀
        j₁).ret.path := by
  have hi₀ : vget s.tree i₀ = false := by
    have := h.tree_iff_used hm
    rw [hj₁] at this
    exact Bool.eq_false_iff.mpr fun h' => Bool.false_ne_true (this.mp h')
  have hU : ∀ j, vget (vset s.used j₁ true) j = true ↔ j = j₁ ∨ vget s.used j = true := by
    intro j
    by_cases hj : j = j₁
    · subst hj
      simp
    · rw [vget_vset_ne _ _ (Ne.symm hj)]
      simp [hj]
  have hT : ∀ i, vget (vset s.tree i₀ true) i = true ↔ i = i₀ ∨ vget s.tree i = true := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp
    · rw [vget_vset_ne _ _ (Ne.symm hi)]
      simp [hi]
  have hU' : ∀ j, j ≠ j₁ → vget (vset s.used j₁ true) j = vget s.used j := fun j hj =>
    vget_vset_ne _ _ (Ne.symm hj)
  refine ⟨h.matching, h.feas, h.tight, h.root_free, fun j hj => ?_, fun i => ?_,
    fun i j hi hj => ?_, fun j => ?_⟩
  · rcases (hU j).mp hj with rfl | hj
    · exact ⟨i₀, hm⟩
    · exact h.used_mate j hj
  · rw [hT, h.tree_iff]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, hmj⟩)
      · exact .inr ⟨j₁, (hU j₁).mpr (.inl rfl), hm⟩
      · exact .inl rfl
      · exact .inr ⟨j, (hU j).mpr (.inr hj), hmj⟩
    · rintro (rfl | ⟨j, hj, hmj⟩)
      · exact .inr (.inl rfl)
      · rcases (hU j).mp hj with rfl | hj
        · exact .inl (Option.some.inj (hmj.symm.trans hm))
        · exact .inr (.inr ⟨j, hj, hmj⟩)
  · have hjj : j ≠ j₁ := by
      rintro rfl
      simp at hj
    have hjs : vget s.used j = false := by rw [← hU' j hjj]; exact hj
    rw [hgRelaxM_minv]
    dsimp only
    rw [hj, ite_eq_right Bool.false_ne_true]
    rcases (hT i).mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h.minv_le i j hi hjs)
  · rw [hgRelaxM_path]
    dsimp only
    have hp₁ := h.path_ok j₁
    split_ifs with hc
    · have hjj : j ≠ j₁ := by
        rintro rfl
        simp at hc
      have hjs : vget s.used j = false := by rw [← hU' j hjj]; exact hc.1
      obtain ⟨b, l, hql⟩ := List.exists_cons_of_ne_nil hp₁.ne_nil
      have hb := hp₁.head b (by simp [hql])
      refine ⟨List.cons_ne_nil _ _, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
        fun e he => ?_, fun e he => ?_⟩
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
        subst he
        refine ⟨rfl, ?_⟩
        rw [hgRelaxM_minv]
        dsimp only
        rw [hc.1, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
        exact (min_eq_right hc.2.le).symm
      · rw [hql, List.getLast?_cons_cons, ← hql] at he
        exact hp₁.last e he
      · rw [hql]
        refine List.IsChain.cons_cons ?_ (hql ▸ hp₁.chain)
        rw [hb.1]
        exact hm
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hp₁.nodup_fst⟩
        obtain ⟨e, he, hei⟩ := List.mem_map.mp hmem
        have := hp₁.tree e he
        rw [hei, hi₀] at this
        exact Bool.false_ne_true this
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hp₁.nodup_snd⟩
        obtain ⟨e, he, hej⟩ := List.mem_map.mp hmem
        rcases hp₁.mem_cases he with h1 | h1
        · exact hjj (hej.symm.trans h1)
        · rw [hej, hjs] at h1
          exact Bool.false_ne_true h1
      · simp only [List.tail_cons] at he
        rcases hp₁.mem_cases he with h1 | h1
        · rw [hql] at he
          rcases List.mem_cons.mp he with rfl | he'
          · refine ⟨?_, ?_⟩
            · have h2 := hb.2
              rw [hj₁, hz, ite_eq_right Bool.false_ne_true] at h2
              exact h2
            · rw [h1]
              exact (hU j₁).mpr (.inl rfl)
          · have := (hp₁.tail e (by rw [hql]; exact he')).2
            rw [h1, hj₁] at this
            exact absurd this Bool.false_ne_true
        · refine ⟨?_, (hU e.2).mpr (.inr h1)⟩
          obtain ⟨b', l', hql'⟩ := List.exists_cons_of_ne_nil hp₁.ne_nil
          rw [hql'] at he
          rcases List.mem_cons.mp he with rfl | he'
          · have h2 := (hp₁.head e (by simp [hql'])).2
            rw [hj₁, hz, ite_eq_right Bool.false_ne_true] at h2
            exact h2
          · exact (hp₁.tail e (by rw [hql']; exact he')).1
      · rcases List.mem_cons.mp he with rfl | he'
        · exact (hT i₀).mpr (.inl rfl)
        · exact (hT e.1).mpr (.inr (hp₁.tree e he'))
    · have hp := h.path_ok j
      refine ⟨hp.ne_nil, fun e he => ?_, hp.last, hp.chain, hp.nodup_fst, hp.nodup_snd,
        fun e he => ?_, fun e he => (hT e.1).mpr (.inr (hp.tree e he))⟩
      · obtain ⟨h1, h2⟩ := hp.head e he
        refine ⟨h1, ?_⟩
        rw [hgRelaxM_minv]
        dsimp only
        by_cases hjj : j = j₁
        · subst hjj
          rw [vget_vset_self, ite_eq_left rfl]
          rw [hj₁, hz, ite_eq_right Bool.false_ne_true] at h2
          exact h2
        · rw [hU' j hjj] at hc ⊢
          by_cases hju : vget s.used j = true
          · simp only [hju, ite_true] at h2 ⊢
            exact h2
          · have hjf : vget s.used j = false := Bool.eq_false_iff.mpr hju
            simp only [hjf, Bool.false_eq_true, ite_false, true_and, not_lt] at h2 hc ⊢
            rw [h2]
            exact (min_eq_left hc).symm
      · obtain ⟨h1, h2⟩ := hp.tail e he
        exact ⟨h1, (hU e.2).mpr (.inr h2)⟩

private theorem hgInv_extendM {r : Fin n} {s : HgState n}
    (h : HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path) {j₁ i₀ : Fin n}
    (hj₁ : vget s.used j₁ = false) (hz : vget s.minv j₁ = 0) (hm : vget s.mate j₁ = some i₀) :
    HgInv c r (hgExtendM c s j₁ i₀).ret.y (hgExtendM c s j₁ i₀).ret.z
      (hgExtendM c s j₁ i₀).ret.mate (hgExtendM c s j₁ i₀).ret.used
      (hgExtendM c s j₁ i₀).ret.tree (hgExtendM c s j₁ i₀).ret.minv
      (hgExtendM c s j₁ i₀).ret.path :=
  hgInv_extend h hj₁ hz hm

private theorem hgExtendM_mate (s : HgState n) (j₁ i₀ : Fin n) :
    (hgExtendM c s j₁ i₀).ret.mate = s.mate := rfl

private theorem hgExtendM_used (s : HgState n) (j₁ i₀ : Fin n) :
    (hgExtendM c s j₁ i₀).ret.used = vset s.used j₁ true := rfl

private theorem hgExtendM_time (s : HgState n) (j₁ i₀ : Fin n) :
    (hgExtendM c s j₁ i₀).time = 2 * n + 1 := by
  simp only [hgExtendM, TimeM.time_bind, TimeM.time_tick, hgRelaxM_time]
  omega

/-! #### Counting tree columns -/

/-- Number of columns in the tree. -/
private def usedCount (used : Vector Bool n) : ℕ :=
  (Finset.univ.filter fun j => vget used j = true).card

private theorem usedCount_le {mate : Vector (Option (Fin n)) n} {used : Vector Bool n}
    (hM : IsMatching (fun _ => true) (mateMatching mate))
    (hu : ∀ j, vget used j = true → ∃ i, vget mate j = some i) :
    usedCount used ≤ (mateMatching mate).card := by
  rw [← card_matchedRight hM]
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨i, hi⟩ := hu j (Finset.mem_filter.mp hj).2
  exact mem_matchedRight.mpr ⟨i, mem_mateMatching.mpr hi⟩

private theorem usedCount_vset {used : Vector Bool n} {j₁ : Fin n}
    (hj₁ : vget used j₁ = false) : usedCount (vset used j₁ true) = usedCount used + 1 := by
  unfold usedCount
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j => vget used j = true)
    (a := j₁) (by simp [hj₁])]
  congr 1
  ext j
  by_cases hj : j = j₁
  · subst hj
    simp
  · rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, vget_vset_ne _ _ (Ne.symm hj)]
    simp [hj]

private theorem usedCount_all {used : Vector Bool n} (h : ∀ j, vget used j = true) :
    usedCount used = n := by
  unfold usedCount
  rw [Finset.filter_true_of_mem fun j _ => h j]
  simp

private theorem card_lt_of_root_free {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) {r : Fin n}
    (hr : ∀ j, vget mate j ≠ some r) : (mateMatching mate).card < n := by
  rw [← card_matchedLeft hM]
  have : r ∉ matchedLeft (mateMatching mate) := by
    intro h
    obtain ⟨v, hv⟩ := mem_matchedLeft.mp h
    exact hr v (mem_mateMatching.mp hv)
  simpa using Finset.card_lt_univ_of_notMem this

/-! #### The loop, the phase and the rows -/

private theorem hgLoopM_spec {r : Fin n} :
    ∀ (fuel : ℕ) (s : HgState n), HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path →
      (mateMatching s.mate).card < fuel + usedCount s.used →
      HgOuter c (hgLoopM c fuel s).ret.y (hgLoopM c fuel s).ret.z (hgLoopM c fuel s).ret.mate ∧
        matchedLeft (mateMatching (hgLoopM c fuel s).ret.mate) =
          insert r (matchedLeft (mateMatching s.mate)) ∧
        (hgLoopM c fuel s).time ≤ fuel * (6 * n + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s h hfuel
    have := usedCount_le h.matching h.used_mate
    omega
  | succ fuel ih =>
    intro s h hfuel
    simp only [hgLoopM, TimeM.ret_bind, TimeM.time_bind]
    cases ha : (hgArgminM s).ret with
    | none =>
      have hall := hgArgminM_none ha
      have h1 := usedCount_all hall
      have h2 := usedCount_le h.matching h.used_mate
      have h3 := card_lt_of_root_free h.matching h.root_free
      omega
    | some j₁ =>
      obtain ⟨hj₁, hmin⟩ := hgArgminM_some ha
      have hD := hgInv_dual h hj₁ hmin
      have hz := minv_dual_self s hj₁
      simp only [TimeM.ret_bind, TimeM.time_bind, hgDualM_mate, hgDualM_path, hgArgminM_time,
        hgDualM_time]
      cases hm : vget s.mate j₁ with
      | none =>
        obtain ⟨hO, hL, hT⟩ := hgAugment hD hj₁ hz hm
        simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.ret_pure, TimeM.time_pure]
        refine ⟨hO, hL, ?_⟩
        have : (fuel + 1) * (6 * n + 1) = fuel * (6 * n + 1) + (6 * n + 1) := Nat.succ_mul _ _
        omega
      | some i₀ =>
        have hE := hgInv_extendM (s := hgDualM s (vget s.minv j₁) |>.ret) hD hj₁ hz hm
        have hcnt : usedCount (hgExtendM c (hgDualM s (vget s.minv j₁)).ret j₁ i₀).ret.used =
            usedCount s.used + 1 := by
          rw [hgExtendM_used]
          exact usedCount_vset hj₁
        obtain ⟨hO, hL, hT⟩ := ih _ hE (by
          rw [hcnt]
          change (mateMatching s.mate).card < fuel + (usedCount s.used + 1)
          omega)
        simp only [TimeM.ret_bind, TimeM.time_bind, hgExtendM_time]
        refine ⟨hO, hL, ?_⟩
        have : (fuel + 1) * (6 * n + 1) = fuel * (6 * n + 1) + (6 * n + 1) := Nat.succ_mul _ _
        omega

private theorem hgInv_init {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n} {r : Fin n}
    (h : HgOuter c y z mate) (hr : r ∉ matchedLeft (mateMatching mate)) :
    HgInv c r (hgInitM c y z mate r).ret.y (hgInitM c y z mate r).ret.z
      (hgInitM c y z mate r).ret.mate (hgInitM c y z mate r).ret.used
      (hgInitM c y z mate r).ret.tree (hgInitM c y z mate r).ret.minv
      (hgInitM c y z mate r).ret.path := by
  rw [hgInitM_y, hgInitM_z, hgInitM_mate]
  refine ⟨h.matching, h.feas, h.tight, fun j hj => hr ?_, fun j hj => ?_, fun i => ?_,
    fun i j hi _ => ?_, fun j => ?_⟩
  · exact mem_matchedLeft.mpr ⟨j, mem_mateMatching.mpr hj⟩
  · rw [hgInitM_used] at hj
    exact absurd hj Bool.false_ne_true
  · simp [hgInitM_tree, hgInitM_used]
  · rw [hgInitM_tree, decide_eq_true_eq] at hi
    subst hi
    rw [hgInitM_minv]
  · rw [hgInitM_path]
    refine ⟨List.cons_ne_nil _ _, fun e he => ?_, fun e he => ?_, List.isChain_singleton _,
      by simp, by simp, fun e he => ?_, fun e he => ?_⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
      subst he
      simp [hgInitM_used, hgInitM_minv]
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at he
      subst he
      rfl
    · simp at he
    · simp only [List.mem_singleton] at he
      subst he
      simp [hgInitM_tree]

private theorem hgPhaseM_spec {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n} {r : Fin n}
    (h : HgOuter c y z mate) (hr : r ∉ matchedLeft (mateMatching mate)) :
    HgOuter c (hgPhaseM c y z mate r).ret.y (hgPhaseM c y z mate r).ret.z
        (hgPhaseM c y z mate r).ret.mate ∧
      matchedLeft (mateMatching (hgPhaseM c y z mate r).ret.mate) =
        insert r (matchedLeft (mateMatching mate)) ∧
      (hgPhaseM c y z mate r).time ≤ 4 * n + n * (6 * n + 1) := by
  have hI := hgInv_init h hr
  have hlt := card_lt_of_root_free h.matching (r := r) (fun j hj => hr
    (mem_matchedLeft.mpr ⟨j, mem_mateMatching.mpr hj⟩))
  have h0 : usedCount (hgInitM c y z mate r).ret.used = 0 := by
    unfold usedCount
    simp [hgInitM_used]
  obtain ⟨hO, hL, hT⟩ := hgLoopM_spec n _ hI (by rw [h0, hgInitM_mate]; omega)
  simp only [hgPhaseM, TimeM.ret_bind, TimeM.time_bind, hgInitM_time]
  exact ⟨hO, hL, by omega⟩

private theorem hgRowsM_spec :
    ∀ (rows : List (Fin n)) (s : HgState n), rows.Nodup → HgOuter c s.y s.z s.mate →
      (∀ r ∈ rows, r ∉ matchedLeft (mateMatching s.mate)) →
      HgOuter c (hgRowsM c rows s).ret.y (hgRowsM c rows s).ret.z (hgRowsM c rows s).ret.mate ∧
        matchedLeft (mateMatching (hgRowsM c rows s).ret.mate) =
          rows.toFinset ∪ matchedLeft (mateMatching s.mate) ∧
        (hgRowsM c rows s).time ≤ rows.length * (4 * n + n * (6 * n + 1)) := by
  intro rows
  induction rows with
  | nil =>
    intro s _ h _
    simp only [hgRowsM, TimeM.ret_pure, TimeM.time_pure, List.toFinset_nil, Finset.empty_union,
      List.length_nil, Nat.zero_mul, le_refl, and_true]
    exact h
  | cons r rs ih =>
    intro s hnd h hfree
    rw [List.nodup_cons] at hnd
    obtain ⟨hO, hL, hT⟩ := hgPhaseM_spec h (hfree r List.mem_cons_self)
    obtain ⟨hO', hL', hT'⟩ := ih (hgPhaseM c s.y s.z s.mate r).ret hnd.2 hO (by
      intro r' hr' hmem
      rw [hL, Finset.mem_insert] at hmem
      rcases hmem with rfl | hmem
      · exact hnd.1 hr'
      · exact hfree r' (List.mem_cons_of_mem _ hr') hmem)
    simp only [hgRowsM, TimeM.ret_bind, TimeM.time_bind]
    refine ⟨hO', ?_, ?_⟩
    · rw [hL', hL]
      ext u
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h)
        · exact .inr h
      · rintro ((h | h) | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Spec

/-! ### Correctness and running time -/

section Main

variable {n : ℕ}

private theorem foldl_min_le (c : Fin n × Fin n → ℤ) (u : Fin n) :
    ∀ (l : List (Fin n)) (a : ℤ),
      l.foldl (fun a v => min a (c (u, v))) a ≤ a ∧
        ∀ v ∈ l, l.foldl (fun a v => min a (c (u, v))) a ≤ c (u, v) := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
    intro a
    obtain ⟨h1, h2⟩ := ih (min a (c (u, x)))
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨h1.trans (min_le_left _ _), fun v hv => ?_⟩
    rcases hv with rfl | hv
    · exact h1.trans (min_le_right _ _)
    · exact h2 v hv

private theorem hgRowMinM_le (c : Fin n × Fin n → ℤ) (u v : Fin n) :
    (hgRowMinM c u).ret ≤ c (u, v) := by
  rw [hgRowMinM, foldlTickM_ret]
  exact (foldl_min_le c u _ _).2 v (List.mem_finRange v)

private theorem hgOuter_start (c : Fin n × Fin n → ℤ) :
    HgOuter c (ofFnM n (hgRowMinM c)).ret (replicateM n 0).ret (replicateM n none).ret := by
  refine ⟨⟨fun _ _ => rfl, fun u v₁ v₂ h₁ _ => ?_, fun u₁ u₂ v h₁ _ => ?_⟩,
    fun i j => ?_, fun i j hm => ?_⟩
  · simp [replicateM_ret, vget_replicate] at h₁
  · simp [replicateM_ret, vget_replicate] at h₁
  · have := hgRowMinM_le c i j
    simp only [hgRed, vget_ofFnM_ret, replicateM_ret, vget_replicate]
    omega
  · simp [replicateM_ret, vget_replicate] at hm

private theorem hg_final {c : Fin n × Fin n → ℤ} {s : HgState n}
    (h : HgOuter c s.y s.z s.mate) (hL : matchedLeft (mateMatching s.mate) = Finset.univ) :
    IsMinCostPerfectMatching (fun _ => true) c
        ((List.finRange n).foldl (hkMatchingStep s.mate) ∅) ∧
      IsFeasiblePotential (fun _ => true) c (vget s.y) (vget s.z) ∧
      matchingCost c ((List.finRange n).foldl (hkMatchingStep s.mate) ∅) =
        ∑ u, vget s.y u + ∑ v, vget s.z v := by
  have hM : (List.finRange n).foldl (hkMatchingStep s.mate) ∅ = mateMatching s.mate := by
    ext ⟨u, v⟩
    rw [mem_foldl_hkMatchingStep, mem_mateMatching]
    simp
  rw [hM]
  have hR : matchedRight (mateMatching s.mate) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [card_matchedRight h.matching, ← card_matchedLeft h.matching, hL, Finset.card_univ]
  have hP : IsPerfectMatching (fun _ => true) (mateMatching s.mate) := ⟨h.matching, hL, hR⟩
  have hf : IsFeasiblePotential (fun _ => true) c (vget s.y) (vget s.z) := by
    intro u v _
    have := h.feas u v
    unfold hgRed at this
    omega
  have ht : ∀ e ∈ mateMatching s.mate, vget s.y e.1 + vget s.z e.2 = c e := by
    rintro ⟨u, v⟩ he
    have := h.tight u v (mem_mateMatching.mp he)
    unfold hgRed at this
    dsimp only
    omega
  exact ⟨hP.isMinCostPerfectMatching_of_tight hf ht, hf,
    ((hP.potential_eq_cost_iff hf).mpr ht).symm⟩

private theorem hungarianM_rows (c : Fin n × Fin n → ℤ) :
    HgOuter c (hgRowsM c (List.finRange n) (hgStartState (ofFnM n (hgRowMinM c)).ret
        (replicateM n 0).ret (replicateM n none).ret)).ret.y
      (hgRowsM c (List.finRange n) (hgStartState (ofFnM n (hgRowMinM c)).ret
        (replicateM n 0).ret (replicateM n none).ret)).ret.z
      (hgRowsM c (List.finRange n) (hgStartState (ofFnM n (hgRowMinM c)).ret
        (replicateM n 0).ret (replicateM n none).ret)).ret.mate ∧
    matchedLeft (mateMatching (hgRowsM c (List.finRange n) (hgStartState
        (ofFnM n (hgRowMinM c)).ret (replicateM n 0).ret (replicateM n none).ret)).ret.mate) =
      Finset.univ ∧
    (hgRowsM c (List.finRange n) (hgStartState (ofFnM n (hgRowMinM c)).ret
        (replicateM n 0).ret (replicateM n none).ret)).time ≤
      n * (4 * n + n * (6 * n + 1)) := by
  obtain ⟨hO, hL, hT⟩ := hgRowsM_spec (c := c) (List.finRange n) (hgStartState
    (ofFnM n (hgRowMinM c)).ret (replicateM n 0).ret (replicateM n none).ret)
    (List.nodup_finRange n) (hgOuter_start c)
    (fun r _ hr => by
      obtain ⟨v, hv⟩ := mem_matchedLeft.mp hr
      simp [hgStartState, mem_mateMatching, replicateM_ret, vget_replicate] at hv)
  refine ⟨hO, ?_, by simpa using hT⟩
  rw [hL]
  exact Finset.eq_univ_of_forall fun u => Finset.mem_union_left _ (by simp)

/-- **Correctness of the Hungarian method.** The output is a minimum-cost perfect matching of the
complete bipartite graph on `Fin n × Fin n`, the output potentials are feasible, and the cost of
the matching equals the total potential (Egerváry's certificate of optimality). -/
theorem hungarianM_correct (c : Fin n × Fin n → ℤ) :
    IsMinCostPerfectMatching (fun _ => true) c (hungarianM c).ret.matching ∧
      IsFeasiblePotential (fun _ => true) c (hungarianM c).ret.y (hungarianM c).ret.z ∧
      matchingCost c (hungarianM c).ret.matching =
        ∑ u, (hungarianM c).ret.y u + ∑ v, (hungarianM c).ret.z v := by
  obtain ⟨hO, hL, -⟩ := hungarianM_rows c
  have := hg_final hO hL
  simpa only [hungarianM, TimeM.ret_bind, TimeM.ret_pure, foldlTickM_ret] using this

/-- **Running time of the Hungarian method**: at most `6 n³ + 6 n² + 3 n` charged steps, i.e.
`O(n³)`. -/
theorem hungarianM_time_le (c : Fin n × Fin n → ℤ) :
    (hungarianM c).time ≤ 6 * n ^ 3 + 6 * n ^ 2 + 3 * n := by
  obtain ⟨-, -, hT⟩ := hungarianM_rows c
  have hy : (ofFnM n (hgRowMinM c)).time ≤ n * n :=
    ofFnM_time_le n _ fun u => by simp [hgRowMinM]
  simp only [hungarianM, TimeM.time_bind, TimeM.time_pure, foldlTickM_time, replicateM_time,
    List.length_finRange]
  have h1 : n * (4 * n + n * (6 * n + 1)) = 6 * n ^ 3 + 5 * n ^ 2 := by ring
  have h2 : n * n = n ^ 2 := by ring
  omega

/-- **Egerváry's theorem** for the integral assignment problem: there is a perfect matching of the
complete bipartite graph on `Fin n × Fin n` and integral feasible potentials whose total equals
its cost; in particular the matching has minimum cost. -/
theorem exists_isMinCostPerfectMatching_potential_eq (c : Fin n × Fin n → ℤ) :
    ∃ (M : Finset (Fin n × Fin n)) (y z : Fin n → ℤ),
      IsMinCostPerfectMatching (fun _ => true) c M ∧ IsFeasiblePotential (fun _ => true) c y z ∧
        matchingCost c M = ∑ u, y u + ∑ v, z v :=
  ⟨_, _, _, hungarianM_correct c⟩

/-- **Min–max form of Egerváry's theorem**: a perfect matching `M` has minimum cost iff some
integral feasible potentials have total equal to its cost, and then every feasible potential has
total at most `matchingCost c M`. -/
theorem isMinCostPerfectMatching_iff_exists_potential (c : Fin n × Fin n → ℤ)
    {M : Finset (Fin n × Fin n)} (hM : IsPerfectMatching (fun _ => true) M) :
    IsMinCostPerfectMatching (fun _ => true) c M ↔
      ∃ y z : Fin n → ℤ, IsFeasiblePotential (fun _ => true) c y z ∧
        matchingCost c M = ∑ u, y u + ∑ v, z v := by
  constructor
  · intro hmin
    obtain ⟨M', y, z, hM', hf, heq⟩ := exists_isMinCostPerfectMatching_potential_eq c
    refine ⟨y, z, hf, le_antisymm ?_ (hM.potential_le_cost hf)⟩
    rw [← heq]
    exact hmin.2 M' hM'.1
  · rintro ⟨y, z, hf, heq⟩
    refine ⟨hM, fun M' hM' => ?_⟩
    rw [heq]
    exact hM'.potential_le_cost hf

/-- **Assignment problem, permutation form**: some permutation `σ` minimizes `∑ u, c (u, σ u)`
over all permutations, certified by integral feasible potentials with equal total. -/
theorem exists_perm_assignment (c : Fin n × Fin n → ℤ) :
    ∃ (σ : Equiv.Perm (Fin n)) (y z : Fin n → ℤ),
      (∀ τ : Equiv.Perm (Fin n), ∑ u, c (u, σ u) ≤ ∑ u, c (u, τ u)) ∧
        (∀ u v, y u + z v ≤ c (u, v)) ∧ ∑ u, c (u, σ u) = ∑ u, y u + ∑ v, z v := by
  obtain ⟨M, y, z, hmin, hf, heq⟩ := exists_isMinCostPerfectMatching_potential_eq c
  obtain ⟨σ, rfl⟩ := exists_eq_permMatching hmin.1
  refine ⟨σ, y, z, fun τ => ?_, fun u v => hf u v rfl, ?_⟩
  · have := hmin.2 _ (isPerfectMatching_permMatching τ)
    rwa [matchingCost_permMatching, matchingCost_permMatching] at this
  · rwa [matchingCost_permMatching] at heq

end Main

end Cslib.Algorithms.Lean.MaxFlow
