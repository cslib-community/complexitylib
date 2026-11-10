/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt

/-!
# Hopcroft–Karp Maximum Bipartite Matching

An executable `TimeM ℕ` implementation of the **Hopcroft–Karp algorithm** ([HopcroftKarp1973];
[CLRS2009], Problem 26-6) on `G : Fin m × Fin r → Bool` with candidate neighbour lists
`adj : Fin m → List (Fin r)`, proved to return a maximum matching together with a minimum König
vertex cover after at most `2⌊√ν⌋` augmenting phases (`ν` the maximum matching size), in
`O((m + r + |adj|) √ν)` charged steps, where `|adj| = bipAdjSteps adj` is the total candidate list
length (`|E|` for exact adjacency lists).

## Algorithm and source mapping

The matching is stored as a right-indexed mate table `mate : Vector (Option (Fin m)) r`
(`mateMatching`). Each round of `hkLoopM` is:

1. **Breadth-first layering (`hkBfsM`):** computes the exact alternating layers `IsLayer` of
   `CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath` up to the first layer `k` adjacent to a
   free
   right vertex (`hkBfsM_spec`). If there is none, the layers have closed up and the unreached left
   vertices together with the reached right vertices form a König cover certifying maximality
   (`isMaxMatching_isMinVertexCover_of_stable`).
2. **Depth-first phase (`hkPhaseM`):** a depth-first search from every free left vertex along
   the layers, sharing one visited table over right vertices, collects vertex-disjoint shortest
   augmenting paths (`hkDfsRootsM`). The collected edge list is an `IsLayeredFamily` admitting
   no further layered path, hence an `IsMaximalLayeredAugmentation` (`hkDfsRootsM_maximal`); the
   mate table is then rematched along it (`hkPhaseM_spec`). The phase lemma
   `IsMaximalLayeredAugmentation.noShortAug_augment` and the phase bound
   `IsPhaseRun.le_two_mul_sqrt` give at most `2⌊√ν⌋` rounds that augment. This is slightly
   sharper than the `2⌊√s⌋ + 2` bound of [HopcroftKarp1973], Theorem 3, which counts distinct
   shortest augmenting path lengths.

The phase bound and Berge's theorem are proved through the layered counting lemma
`card_mul_le_of_noShortAug` rather than the textbook decomposition of `M ⊕ M*` into
vertex-disjoint augmenting paths; see `CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath`.

## Cost model and limitations

* **Charged (`TimeM ℕ` ticks), per round (`≤ 7 m + 3 r + 1 + 4 |adj|`):**
  * `hkBfsM` (`hkBfsM_time_le`, `≤ 6 m + r + 1 + 2 |adj|`): `m + r` ticks to mark matched left
    vertices, `m` ticks to allocate the layer table, `m` ticks to seed layer `0`, `1` tick per
    expanded layer (`≤ m + 1`), and `1` tick per expanded left vertex and per candidate edge
    inspected (every left vertex is expanded at most once);
  * `hkPhaseM` (`hkPhaseM_time_le`, `≤ 2 r + m + 2 |adj|`): `r` ticks to allocate the visited
    table, `1` tick per left vertex considered as a root, `1` tick per candidate edge scanned
    (a free left vertex scans its candidates as a root, a matched left vertex at most once, when it
    is entered through its then unvisited mate edge), and `1` tick per rematched right vertex
    (`≤ r`).
* **Charged, once:** `r` ticks to allocate the empty mate table and `m + 2 r` ticks to extract the
  matching and the cover (`hopcroftKarpM_time_le`).
* **Abstract unit-cost primitives:** `Vector` indexing and update (`vget`, `vset`), list cons,
  `Finset.insert`, `ℕ` and `Option` comparisons, and evaluating `G (u, v)` are `O(1)` within each
  charged step, as in `CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp`. This is an abstract
  RAM-style step count, not Turing-machine time.
* **Input:** `adj` must contain every edge (`BipAdjValid G adj`); extra candidates are allowed
  and only cost time. `hopcroftKarpDenseM` uses `denseBipAdj m r` (`|adj| = m r`), giving
  `O(m r √(min m r))`, i.e. the `O(n^{5/2})` bound of [HopcroftKarp1973] for `n = m = r`.

## Main definitions

* `BipAdjValid`, `bipAdjSteps`, `denseBipAdj`: candidate neighbour lists and their total length.
* `mateMatching`: the matching encoded by a mate table.
* `hkBfsM`, `hkDfsM`, `hkDfsRootsM`, `hkPhaseM`, `hkLoopM`: layering, depth-first search, one
  phase, and the phase loop.
* `HopcroftKarpOutput`, `hopcroftKarpM`, `hopcroftKarpDenseM`, `decidePerfectMatchingHKM`.

## Main results

* `hopcroftKarpM_correct`: maximum matching, minimum vertex cover, equal sizes (König), and at
  most `2⌊√ν⌋` phases.
* `hopcroftKarpM_time_le`: `(2⌊√ν⌋ + 1) (7 m + 3 r + 1 + 4 |adj|) + m + 3 r` charged steps;
  `hopcroftKarpM_time_le_sqrt_min` with `√(min m r)` in place of `√ν`.
* `hopcroftKarpDenseM_correct`, `hopcroftKarpDenseM_time_le`: the dense instance.
* `card_hopcroftKarpM_matching`: same matching size as `bipartiteMatchingM` (Edmonds–Karp), so
  clients can switch solvers.
* `decidePerfectMatchingHKM_eq_true_iff`, `decidePerfectMatchingHKM_time_le`: perfect-matching
  decision in `O((n + |adj|) √n)` charged steps.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean
open scoped TimeM

/-! ### Charged folds and graph inputs -/

/-- Left fold of `step` over `xs`, charging `1` tick per element. -/
@[expose] def foldlTickM {α β : Type*} (step : β → α → β) : List α → β → TimeM ℕ β
  | [], b => pure b
  | x :: xs, b => do
    ✓
    foldlTickM step xs (step b x)

@[simp]
theorem foldlTickM_ret {α β : Type*} (step : β → α → β) (xs : List α) (b : β) :
    (foldlTickM step xs b).ret = xs.foldl step b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp [foldlTickM, ih]

@[simp]
theorem foldlTickM_time {α β : Type*} (step : β → α → β) (xs : List α) (b : β) :
    (foldlTickM step xs b).time = xs.length := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldlTickM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

variable {m r : ℕ}

/-- Candidate neighbour lists `adj` cover every edge of `G`. -/
@[expose] def BipAdjValid (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r)) : Prop :=
  ∀ u v, G (u, v) = true → v ∈ adj u

/-- Total length of the candidate neighbour lists (`|E|` for exact adjacency lists). -/
@[expose] def bipAdjSteps (adj : Fin m → List (Fin r)) : ℕ := ∑ u, (adj u).length

/-- Dense candidate neighbour lists enumerating every right vertex. -/
@[expose] def denseBipAdj (m r : ℕ) : Fin m → List (Fin r) := fun _ => List.finRange r

theorem bipAdjValid_denseBipAdj (G : Fin m × Fin r → Bool) : BipAdjValid G (denseBipAdj m r) :=
  fun _ v _ => List.mem_finRange v

@[simp]
theorem bipAdjSteps_denseBipAdj : bipAdjSteps (denseBipAdj m r) = m * r := by
  simp [bipAdjSteps, denseBipAdj, Finset.sum_const]

/-- Matching encoded by a right-vertex mate table: `(u, v)` is matched iff `mate[v] = some u`. -/
@[expose] def mateMatching (mate : Vector (Option (Fin m)) r) : Finset (Fin m × Fin r) :=
  Finset.univ.filter fun e => vget mate e.2 = some e.1

@[simp]
theorem mem_mateMatching {mate : Vector (Option (Fin m)) r} {e : Fin m × Fin r} :
    e ∈ mateMatching mate ↔ vget mate e.2 = some e.1 := by
  simp [mateMatching]

/-! ### Breadth-first layering -/

/-- Mark the mate of the right vertex `v`. -/
@[expose] def hkMarkStep (mate : Vector (Option (Fin m)) r) (b : Vector Bool m) (v : Fin r) :
    Vector Bool m :=
  match vget mate v with
  | some u => vset b u true
  | none => b

/-- Mark the left vertices matched by `mate` (`m + r` ticks). -/
@[expose] def hkMatchedLeftM (mate : Vector (Option (Fin m)) r) : TimeM ℕ (Vector Bool m) := do
  let b ← replicateM m false
  foldlTickM (hkMarkStep mate) (List.finRange r) b

/-- State of the expansion of one breadth-first layer. -/
structure HKBfsState (m : ℕ) where
  /-- Layer index of each discovered left vertex. -/
  dist : Vector (Option ℕ) m
  /-- Left vertices discovered for the next layer. -/
  next : List (Fin m)
  /-- Whether a free right vertex is adjacent to the current layer. -/
  found : Bool

/-- Inspect the candidate edge `(u, v)` from layer `j`: a free `v` sets `found`; the mate `w` of a
matched `v` is discovered in layer `j + 1` unless already discovered. -/
@[expose] def hkBfsStep (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) (j : ℕ)
    (u : Fin m) (s : HKBfsState m) (v : Fin r) : HKBfsState m :=
  if G (u, v) = true then
    match vget mate v with
    | none => { s with found := true }
    | some w =>
      if vget s.dist w = none then
        { s with dist := vset s.dist w (some (j + 1)), next := w :: s.next }
      else s
  else s

/-- Expand the frontier `us` of layer `j`: `1` tick per frontier vertex and per candidate edge. -/
@[expose] def hkBfsLayerM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (j : ℕ) :
    List (Fin m) → HKBfsState m → TimeM ℕ (HKBfsState m)
  | [], s => pure s
  | u :: us, s => do
    ✓
    let s' ← foldlTickM (hkBfsStep G mate j u) (adj u) s
    hkBfsLayerM G adj mate j us s'

/-- Result of a breadth-first layering: layer indices, the last layer `k`, and whether a free right
vertex is adjacent to layer `k`. -/
structure HKBfsResult (m : ℕ) where
  /-- Layer index of each reached left vertex. -/
  dist : Vector (Option ℕ) m
  /-- Index of the last expanded layer. -/
  k : ℕ
  /-- Whether layer `k` reaches a free right vertex. -/
  found : Bool

/-- Expand layers `j, j + 1, …` until a free right vertex is found or no new vertex appears. -/
@[expose] def hkBfsLoopM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) :
    ℕ → ℕ → Vector (Option ℕ) m → List (Fin m) → TimeM ℕ (HKBfsResult m)
  | 0, j, dist, _ => pure ⟨dist, j, false⟩
  | fuel + 1, j, dist, frontier => do
    ✓
    let s ← hkBfsLayerM G adj mate j frontier ⟨dist, [], false⟩
    if s.found then pure ⟨s.dist, j, true⟩
    else if s.next.isEmpty then pure ⟨s.dist, j, false⟩
    else hkBfsLoopM G adj mate fuel (j + 1) s.dist s.next

/-- Put a free left vertex into layer `0`. -/
@[expose] def hkBfsInitStep (ml : Vector Bool m) (p : Vector (Option ℕ) m × List (Fin m))
    (u : Fin m) : Vector (Option ℕ) m × List (Fin m) :=
  if vget ml u = true then p else (vset p.1 u (some 0), u :: p.2)

/-- Breadth-first layering of the alternating graph of the matching encoded by `mate`. -/
@[expose] def hkBfsM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) : TimeM ℕ (HKBfsResult m) := do
  let ml ← hkMatchedLeftM mate
  let dist₀ ← replicateM m none
  let p ← foldlTickM (hkBfsInitStep ml) (List.finRange m) (dist₀, [])
  hkBfsLoopM G adj mate (m + 1) 0 p.1 p.2

/-! ### Depth-first search for vertex-disjoint shortest augmenting paths -/

/-- Scan the candidates `vs` of `u` in layer `i`. With `accept`, take a free unvisited `v`;
otherwise descend through an unvisited matched `v` whose mate lies in layer `i + 1` using
`next`. Visited right vertices are never revisited. Returns the visited table and, on success,
the found path's non-matching edges prepended to `acc`. -/
@[expose] def hkDfsLevelM (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (accept : Bool) (i : ℕ)
    (next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      TimeM ℕ (Vector Bool r × Option (List (Fin m × Fin r))))
    (u : Fin m) : List (Fin r) → Vector Bool r → List (Fin m × Fin r) →
      TimeM ℕ (Vector Bool r × Option (List (Fin m × Fin r)))
  | [], vis, _ => pure (vis, none)
  | v :: vs, vis, acc => do
    ✓
    if G (u, v) = true ∧ vget vis v = false then
      match vget mate v with
      | none =>
        if accept = true then pure (vset vis v true, some ((u, v) :: acc))
        else hkDfsLevelM G mate dist accept i next u vs vis acc
      | some w =>
        if accept = false ∧ vget dist w = some (i + 1) then do
          let res ← next w (vset vis v true) acc
          match res.2 with
          | some q => pure (res.1, some ((u, v) :: q))
          | none => hkDfsLevelM G mate dist accept i next u vs res.1 acc
        else hkDfsLevelM G mate dist accept i next u vs vis acc
    else hkDfsLevelM G mate dist accept i next u vs vis acc

/-- Depth-first search from `u` in layer `i` with `f` layers remaining. -/
@[expose] def hkDfsM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) :
    ℕ → ℕ → Fin m → Vector Bool r → List (Fin m × Fin r) →
      TimeM ℕ (Vector Bool r × Option (List (Fin m × Fin r)))
  | 0, i, u, vis, acc =>
    hkDfsLevelM G mate dist true i (fun _ vis _ => pure (vis, none)) u (adj u) vis acc
  | f + 1, i, u, vis, acc =>
    hkDfsLevelM G mate dist false i (hkDfsM G adj mate dist f (i + 1)) u (adj u) vis acc

/-- Run the depth-first search from every layer-`0` vertex of `us`, sharing the visited table. -/
@[expose] def hkDfsRootsM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) (k : ℕ) :
    List (Fin m) → Vector Bool r → List (Fin m × Fin r) → TimeM ℕ (List (Fin m × Fin r))
  | [], _, acc => pure acc
  | u :: us, vis, acc => do
    ✓
    if vget dist u = some 0 then do
      let res ← hkDfsM G adj mate dist k 0 u vis acc
      hkDfsRootsM G adj mate dist k us res.1 (res.2.getD acc)
    else hkDfsRootsM G adj mate dist k us vis acc

/-- Rematch the right end of every edge of `es` to its left end (`1` tick per edge). -/
@[expose] def hkApplyEdgesM (mate : Vector (Option (Fin m)) r) (es : List (Fin m × Fin r)) :
    TimeM ℕ (Vector (Option (Fin m)) r) :=
  foldlTickM (fun mt e => vset mt e.2 (some e.1)) es mate

/-- One augmenting phase for the layering `dist` with shortest augmenting parameter `k`. -/
@[expose] def hkPhaseM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) (k : ℕ) :
    TimeM ℕ (Vector (Option (Fin m)) r) := do
  let vis ← replicateM r false
  let es ← hkDfsRootsM G adj mate dist k (List.finRange m) vis []
  hkApplyEdgesM mate es

/-- Final state of the phase loop. -/
structure HKLoopResult (m r : ℕ) where
  /-- Final mate table. -/
  mate : Vector (Option (Fin m)) r
  /-- Final (closed) layering. -/
  dist : Vector (Option ℕ) m
  /-- Number of augmenting phases performed. -/
  phases : ℕ

/-- Alternate breadth-first layering and augmenting phases until no augmenting path remains. -/
@[expose] def hkLoopM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r)) :
    ℕ → ℕ → Vector (Option (Fin m)) r → TimeM ℕ (HKLoopResult m r)
  | 0, n, mate => pure ⟨mate, Vector.replicate m none, n⟩
  | fuel + 1, n, mate => do
    let b ← hkBfsM G adj mate
    if b.found then do
      let mate' ← hkPhaseM G adj mate b.dist b.k
      hkLoopM G adj fuel (n + 1) mate'
    else pure ⟨mate, b.dist, n⟩

/-- Collect the matched edge at the right vertex `v`. -/
@[expose] def hkMatchingStep (mate : Vector (Option (Fin m)) r) (a : Finset (Fin m × Fin r))
    (v : Fin r) : Finset (Fin m × Fin r) :=
  match vget mate v with
  | some u => insert (u, v) a
  | none => a

/-- Collect the left vertex `u` into the cover when it is unreached. -/
@[expose] def hkCoverLeftStep (dist : Vector (Option ℕ) m) (a : Finset (Fin m)) (u : Fin m) :
    Finset (Fin m) :=
  if vget dist u = none then insert u a else a

/-- Collect the right vertex `v` into the cover when its mate is reached. -/
@[expose] def hkCoverRightStep (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m)
    (a : Finset (Fin r)) (v : Fin r) : Finset (Fin r) :=
  match vget mate v with
  | some w => if vget dist w = none then a else insert v a
  | none => a

/-- Output of `hopcroftKarpM`. -/
structure HopcroftKarpOutput (m r : ℕ) where
  /-- Maximum-cardinality matching. -/
  matching : Finset (Fin m × Fin r)
  /-- Minimum-cardinality König vertex cover. -/
  cover : VertexCover (Fin m) (Fin r)
  /-- Number of augmenting phases. -/
  phases : ℕ

/-- **Hopcroft–Karp** on `G : Fin m × Fin r → Bool` with candidate neighbour lists `adj`. -/
@[expose] def hopcroftKarpM (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r)) :
    TimeM ℕ (HopcroftKarpOutput m r) := do
  let mate₀ ← replicateM r none
  let st ← hkLoopM G adj (m + 1) 0 mate₀
  let matching ← foldlTickM (hkMatchingStep st.mate) (List.finRange r) ∅
  let left ← foldlTickM (hkCoverLeftStep st.dist) (List.finRange m) ∅
  let right ← foldlTickM (hkCoverRightStep st.mate st.dist) (List.finRange r) ∅
  pure ⟨matching, ⟨left, right⟩, st.phases⟩

/-- Hopcroft–Karp with dense candidate lists `denseBipAdj m r`. -/
@[expose] def hopcroftKarpDenseM (G : Fin m × Fin r → Bool) : TimeM ℕ (HopcroftKarpOutput m r) :=
  hopcroftKarpM G (denseBipAdj m r)

/-! ### Potentials -/

/-- Total cost of the entries of `t` satisfying `p`. -/
private def vecPotential {α : Type*} {n : ℕ} (p : α → Prop) [DecidablePred p] (c : Fin n → ℕ)
    (t : Vector α n) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => p (vget t u)), c u

private theorem vecPotential_vset_add {α : Type*} {n : ℕ} {p : α → Prop} [DecidablePred p]
    {c : Fin n → ℕ} {t : Vector α n} {w : Fin n} {x : α} (hw : p (vget t w)) (hx : ¬ p x) :
    vecPotential p c (vset t w x) + c w = vecPotential p c t := by
  have hset : Finset.univ.filter (fun u => p (vget (vset t w x) u)) =
      (Finset.univ.filter (fun u => p (vget t u))).erase w := by
    ext u
    by_cases huw : u = w
    · subst huw
      simp [hx]
    · simp [huw, vget_vset_ne t x (Ne.symm huw)]
  rw [vecPotential, hset, Finset.sum_erase_add _ _ (by simpa using hw)]
  rfl

private theorem vecPotential_vset_le {α : Type*} {n : ℕ} {p : α → Prop} [DecidablePred p]
    {c : Fin n → ℕ} (t : Vector α n) (w : Fin n) {x : α} (hx : ¬ p x) :
    vecPotential p c (vset t w x) ≤ vecPotential p c t := by
  refine Finset.sum_le_sum_of_subset fun u hu => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  by_cases huw : u = w
  · subst huw
    rw [vget_vset_self] at hu
    exact absurd hu hx
  · rwa [vget_vset_ne t x (Ne.symm huw)] at hu

private theorem vecPotential_le_sum {α : Type*} {n : ℕ} {p : α → Prop} [DecidablePred p]
    (c : Fin n → ℕ) (t : Vector α n) : vecPotential p c t ≤ ∑ u, c u :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-! ### Matched left vertices -/

private theorem matchedLeft_foldl (mate : Vector (Option (Fin m)) r) (l : List (Fin r))
    (b : Vector Bool m) (u : Fin m) :
    vget (l.foldl (hkMarkStep mate) b) u = true ↔
      vget b u = true ∨ ∃ v ∈ l, vget mate v = some u := by
  induction l generalizing b with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih]
    rcases hv : vget mate v with _ | w
    · simp only [hkMarkStep, hv, List.mem_cons, exists_eq_or_imp, reduceCtorEq, false_or]
    · simp only [hkMarkStep, hv, List.mem_cons, exists_eq_or_imp, Option.some.injEq]
      by_cases huw : w = u
      · subst huw
        simp
      · rw [vget_vset_ne b true huw]
        simp [huw]

theorem hkMatchedLeftM_ret (mate : Vector (Option (Fin m)) r) (u : Fin m) :
    vget (hkMatchedLeftM mate).ret u = true ↔ u ∈ matchedLeft (mateMatching mate) := by
  simp only [hkMatchedLeftM, TimeM.ret_bind, foldlTickM_ret, replicateM_ret]
  rw [matchedLeft_foldl]
  simp

theorem hkMatchedLeftM_time (mate : Vector (Option (Fin m)) r) :
    (hkMatchedLeftM mate).time = m + r := by
  simp [hkMatchedLeftM, replicateM_time]

/-! ### Layer `0` -/

private theorem bfsInit_foldl (ml : Vector Bool m) (l : List (Fin m))
    (p : Vector (Option ℕ) m × List (Fin m)) :
    (∀ u, vget (l.foldl (hkBfsInitStep ml) p).1 u =
      if u ∈ l ∧ vget ml u = false then some 0 else vget p.1 u) ∧
    (∀ u, u ∈ (l.foldl (hkBfsInitStep ml) p).2 ↔ u ∈ p.2 ∨ (u ∈ l ∧ vget ml u = false)) := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := ih (hkBfsInitStep ml p x)
    refine ⟨fun u => ?_, fun u => ?_⟩
    · rw [ih1]
      by_cases hx : vget ml x = true
      · have : hkBfsInitStep ml p x = p := by simp [hkBfsInitStep, hx]
        rw [this]
        by_cases hux : u = x
        · subst hux
          simp [hx]
        · simp [hux]
      · have hx' : vget ml x = false := by simpa using hx
        have : hkBfsInitStep ml p x = (vset p.1 x (some 0), x :: p.2) := by
          simp [hkBfsInitStep, hx']
        rw [this]
        by_cases hux : u = x
        · subst hux
          simp [hx']
        · simp [hux, vget_vset_ne p.1 (some 0) (Ne.symm hux)]
    · rw [ih2]
      by_cases hx : vget ml x = true
      · have : hkBfsInitStep ml p x = p := by simp [hkBfsInitStep, hx]
        rw [this]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl h
          · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl h
          · rcases List.mem_cons.mp h1 with rfl | h1
            · simp [hx] at h2
            · exact .inr ⟨h1, h2⟩
      · have hx' : vget ml x = false := by simpa using hx
        have : hkBfsInitStep ml p x = (vset p.1 x (some 0), x :: p.2) := by
          simp [hkBfsInitStep, hx']
        rw [this]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · rcases List.mem_cons.mp h with rfl | h
            · exact .inr ⟨List.mem_cons_self, hx'⟩
            · exact .inl h
          · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.mp h1 with rfl | h1
            · exact .inl List.mem_cons_self
            · exact .inr ⟨h1, h2⟩

private theorem bfsInit_nodup (ml : Vector Bool m) (l : List (Fin m))
    (p : Vector (Option ℕ) m × List (Fin m)) (hl : l.Nodup) (hp : p.2.Nodup)
    (hdisj : ∀ x ∈ l, x ∉ p.2) : (l.foldl (hkBfsInitStep ml) p).2.Nodup := by
  induction l generalizing p with
  | nil => exact hp
  | cons x l ih =>
    rw [List.foldl_cons]
    obtain ⟨hxl, hl⟩ := List.nodup_cons.mp hl
    by_cases hx : vget ml x = true
    · have : hkBfsInitStep ml p x = p := by simp [hkBfsInitStep, hx]
      rw [this]
      exact ih p hl hp fun y hy => hdisj y (List.mem_cons_of_mem _ hy)
    · have : hkBfsInitStep ml p x = (vset p.1 x (some 0), x :: p.2) := by
        simp [hkBfsInitStep, hx]
      rw [this]
      refine ih _ hl (List.nodup_cons.mpr ⟨hdisj x List.mem_cons_self, hp⟩) fun y hy h => ?_
      rcases List.mem_cons.mp h with rfl | h
      · exact hxl hy
      · exact hdisj y (List.mem_cons_of_mem _ hy) h

private theorem bfsInit_potential (ml : Vector Bool m) (c : Fin m → ℕ) (l : List (Fin m))
    (p : Vector (Option ℕ) m × List (Fin m)) :
    vecPotential (· = none) c (l.foldl (hkBfsInitStep ml) p).1 +
        ((l.foldl (hkBfsInitStep ml) p).2.map c).sum ≤
      vecPotential (· = none) c p.1 + (p.2.map c).sum + (l.map c).sum := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    by_cases hx : vget ml x = true
    · have : hkBfsInitStep ml p x = p := by simp [hkBfsInitStep, hx]
      rw [this, List.map_cons, List.sum_cons]
      omega
    · have : hkBfsInitStep ml p x = (vset p.1 x (some 0), x :: p.2) := by
        simp [hkBfsInitStep, hx]
      rw [this]
      have := vecPotential_vset_le (p := (· = none)) (c := c) p.1 x (x := some 0) (by simp)
      simp only [List.map_cons, List.sum_cons]
      omega


/-! ### Breadth-first search: one layer -/

section BfsLayer

variable {G : Fin m × Fin r → Bool} {mate : Vector (Option (Fin m)) r}

private theorem vget_mate_eq_none_iff {v : Fin r} :
    vget mate v = none ↔ v ∉ matchedRight (mateMatching mate) := by
  simp only [mem_matchedRight, mem_mateMatching, not_exists]
  constructor
  · intro h u hu
    rw [h] at hu
    exact nomatch hu
  · intro h
    cases hv : vget mate v with
    | none => rfl
    | some u => exact absurd hv (h u)

/-- Invariant while expanding layer `j`. -/
private structure HKStepInv (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (j : ℕ)
    (s : HKBfsState m) : Prop where
  exact : ∀ u i, i ≤ j → (vget s.dist u = some i ↔ IsLayer G M u i)
  bound : ∀ u i, vget s.dist u = some i → i ≤ j + 1
  next_iff : ∀ u, vget s.dist u = some (j + 1) ↔ u ∈ s.next
  next_layer : ∀ u ∈ s.next, IsLayer G M u (j + 1)
  nodup : s.next.Nodup
  found : s.found = true → ∃ t ∈ altRight G M j, t ∉ matchedRight M

private theorem hkBfsStep_inv {j : ℕ} {u : Fin m} (hu : u ∈ altLeft G (mateMatching mate) j)
    {s : HKBfsState m} (hs : HKStepInv G (mateMatching mate) j s) (v : Fin r) :
    HKStepInv G (mateMatching mate) j (hkBfsStep G mate j u s v) := by
  unfold hkBfsStep
  by_cases hG : G (u, v) = true
  · rw [ite_eq_left hG]
    cases hm : vget mate v with
    | none =>
      exact ⟨hs.exact, hs.bound, hs.next_iff, hs.next_layer, hs.nodup, fun _ =>
        ⟨v, mem_altRight.mpr ⟨u, hu, hG⟩, vget_mate_eq_none_iff.mp hm⟩⟩
    | some w =>
      simp only
      by_cases hd : vget s.dist w = none
      · rw [ite_eq_left hd]
        have hwM : (w, v) ∈ mateMatching mate := mem_mateMatching.mpr hm
        have hwl : IsLayer G (mateMatching mate) w (j + 1) := by
          obtain ⟨i, hi, hwi⟩ := exists_isLayer
            (mem_altLeft_succ_of_mem hwM (mem_altRight.mpr ⟨u, hu, hG⟩))
          rcases Nat.lt_or_eq_of_le hi with hlt | rfl
          · have := (hs.exact w i (by omega)).mpr hwi
            rw [hd] at this
            exact absurd this (by simp)
          · exact hwi
        refine ⟨fun x i hi => ?_, fun x i hx => ?_, fun x => ?_, fun x hx => ?_, ?_, hs.found⟩
        · by_cases hxw : x = w
          · subst hxw
            rw [vget_vset_self]
            constructor
            · intro h
              simp only [Option.some.injEq] at h
              omega
            · intro h
              have := (hs.exact x i hi).mpr h
              rw [hd] at this
              exact absurd this (by simp)
          · rw [vget_vset_ne _ _ (Ne.symm hxw)]
            exact hs.exact x i hi
        · by_cases hxw : x = w
          · subst hxw
            rw [vget_vset_self, Option.some.injEq] at hx
            omega
          · rw [vget_vset_ne _ _ (Ne.symm hxw)] at hx
            exact hs.bound x i hx
        · by_cases hxw : x = w
          · subst hxw
            simp
          · rw [vget_vset_ne _ _ (Ne.symm hxw), hs.next_iff]
            simp [hxw]
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hwl
          · exact hs.next_layer x hx
        · refine List.nodup_cons.mpr ⟨fun h => ?_, hs.nodup⟩
          have := (hs.next_iff w).mpr h
          rw [hd] at this
          exact absurd this (by simp)
      · rw [ite_eq_right hd]
        exact hs
  · rw [ite_eq_right hG]
    exact hs

private theorem foldl_hkBfsStep_inv {j : ℕ} {u : Fin m} (hu : u ∈ altLeft G (mateMatching mate) j)
    (l : List (Fin r)) {s : HKBfsState m} (hs : HKStepInv G (mateMatching mate) j s) :
    HKStepInv G (mateMatching mate) j (l.foldl (hkBfsStep G mate j u) s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons v l ih => exact ih (hkBfsStep_inv hu hs v)

/-- Later states keep `found` and all discovered layers. -/
private def HKStateLe (s s' : HKBfsState m) : Prop :=
  (s.found = true → s'.found = true) ∧ ∀ u i, vget s.dist u = some i → vget s'.dist u = some i

private theorem HKStateLe.refl (s : HKBfsState m) : HKStateLe s s := ⟨id, fun _ _ => id⟩

private theorem HKStateLe.trans {s₁ s₂ s₃ : HKBfsState m} (h₁ : HKStateLe s₁ s₂)
    (h₂ : HKStateLe s₂ s₃) : HKStateLe s₁ s₃ :=
  ⟨fun h => h₂.1 (h₁.1 h), fun u i h => h₂.2 u i (h₁.2 u i h)⟩

private theorem hkBfsStep_le (j : ℕ) (u : Fin m) (s : HKBfsState m) (v : Fin r) :
    HKStateLe s (hkBfsStep G mate j u s v) := by
  unfold hkBfsStep
  by_cases hG : G (u, v) = true
  · rw [ite_eq_left hG]
    cases hm : vget mate v with
    | none => exact ⟨fun _ => rfl, fun _ _ h => h⟩
    | some w =>
      simp only
      by_cases hd : vget s.dist w = none
      · rw [ite_eq_left hd]
        refine ⟨id, fun x i hx => ?_⟩
        have hxw : x ≠ w := fun h => by rw [h, hd] at hx; exact nomatch hx
        simpa [vget_vset_ne _ _ (Ne.symm hxw)] using hx
      · rw [ite_eq_right hd]
        exact HKStateLe.refl s
  · rw [ite_eq_right hG]
    exact HKStateLe.refl s

private theorem foldl_hkBfsStep_le (j : ℕ) (u : Fin m) (l : List (Fin r)) (s : HKBfsState m) :
    HKStateLe s (l.foldl (hkBfsStep G mate j u) s) := by
  induction l generalizing s with
  | nil => exact HKStateLe.refl s
  | cons v l ih => exact (hkBfsStep_le j u s v).trans (ih _)

/-- Every candidate edge of `u` has been processed in `s`. -/
private def HKStepDone (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) (u : Fin m)
    (s : HKBfsState m) (l : List (Fin r)) : Prop :=
  ∀ v ∈ l, G (u, v) = true → (vget mate v = none → s.found = true) ∧
    ∀ w, vget mate v = some w → vget s.dist w ≠ none

private theorem HKStepDone.mono {u : Fin m} {s s' : HKBfsState m} {l : List (Fin r)}
    (h : HKStepDone G mate u s l) (hle : HKStateLe s s') : HKStepDone G mate u s' l := by
  intro v hv hG
  refine ⟨fun hm => hle.1 ((h v hv hG).1 hm), fun w hw hd => ?_⟩
  cases hs : vget s.dist w with
  | none => exact (h v hv hG).2 w hw hs
  | some i => rw [hle.2 w i hs] at hd; exact nomatch hd

private theorem foldl_hkBfsStep_done (j : ℕ) (u : Fin m) (l : List (Fin r)) (s : HKBfsState m) :
    HKStepDone G mate u (l.foldl (hkBfsStep G mate j u) s) l := by
  induction l generalizing s with
  | nil => intro v hv; simp at hv
  | cons v l ih =>
    intro x hx hG
    rcases List.mem_cons.mp hx with rfl | hx
    · refine HKStepDone.mono (l := [x]) ?_ (foldl_hkBfsStep_le j u l _) x
        List.mem_cons_self hG
      intro y hy hGy
      rw [List.mem_singleton] at hy
      subst hy
      unfold hkBfsStep
      rw [ite_eq_left hGy]
      refine ⟨fun hm => by simp [hm], fun w hw => ?_⟩
      simp only [hw]
      by_cases hd : vget s.dist w = none
      · simp [hd]
      · simp [hd]
    · exact ih _ x hx hG

end BfsLayer


/-! ### Breadth-first search: correctness -/

section BfsSpec

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)} {mate : Vector (Option (Fin m)) r}

theorem hkBfsLayerM_ret (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    (hkBfsLayerM G adj mate j us s).ret =
      us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih => simp [hkBfsLayerM, ih]

theorem hkBfsLayerM_time (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    (hkBfsLayerM G adj mate j us s).time = (us.map fun u => (adj u).length + 1).sum := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih =>
    simp only [hkBfsLayerM, TimeM.time_bind, TimeM.time_tick, foldlTickM_time, ih,
      List.map_cons, List.sum_cons]
    omega

private theorem layerFold_inv {j : ℕ} (us : List (Fin m))
    (hus : ∀ u ∈ us, u ∈ altLeft G (mateMatching mate) j) {s : HKBfsState m}
    (hs : HKStepInv G (mateMatching mate) j s) :
    HKStepInv G (mateMatching mate) j
      (us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s) := by
  induction us generalizing s with
  | nil => exact hs
  | cons u us ih =>
    exact ih (fun x hx => hus x (List.mem_cons_of_mem _ hx))
      (foldl_hkBfsStep_inv (hus u List.mem_cons_self) (adj u) hs)

private theorem layerFold_le (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    HKStateLe s (us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s) := by
  induction us generalizing s with
  | nil => exact HKStateLe.refl s
  | cons u us ih => exact (foldl_hkBfsStep_le j u (adj u) s).trans (ih _)

private theorem layerFold_done (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    ∀ u ∈ us, HKStepDone G mate u
      (us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s) (adj u) := by
  induction us generalizing s with
  | nil => intro u hu; simp at hu
  | cons x us ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact (foldl_hkBfsStep_done j u (adj u) s).mono (layerFold_le j us _)
    · exact ih _ u hu

/-- After expanding the full layer-`j` frontier, every vertex of layer `j + 1` is discovered and
a free right vertex adjacent to layer `j` sets `found`. -/
private theorem layer_complete (hadj : BipAdjValid G adj) {j : ℕ} {frontier : List (Fin m)}
    (hfront : ∀ u, u ∈ frontier ↔ IsLayer G (mateMatching mate) u j)
    (hN : NoShortAug G (mateMatching mate) j) {s : HKBfsState m}
    (hs : HKStepInv G (mateMatching mate) j s)
    (hdone : ∀ u ∈ frontier, HKStepDone G mate u s (adj u)) :
    (∀ w, IsLayer G (mateMatching mate) w (j + 1) → w ∈ s.next) ∧
    (∀ t ∈ altRight G (mateMatching mate) j, t ∉ matchedRight (mateMatching mate) →
      s.found = true) := by
  refine ⟨fun w hw => ?_, fun t ht hfree => ?_⟩
  · rcases mem_altLeft_succ.mp hw.1 with h | ⟨v, hwv, hv⟩
    · exact absurd h (hw.2 j (Nat.lt_succ_self j))
    obtain ⟨u, hu, hG⟩ := mem_altRight.mp hv
    obtain ⟨i, hij, hui⟩ := exists_isLayer hu
    have hi : i = j := by
      by_contra hne
      have := mem_altLeft_succ_of_mem hwv (mem_altRight_of_isLayer hui le_rfl hG)
      exact hw.2 (i + 1) (by omega) this
    rw [hi] at hui
    have hd := (hdone u ((hfront u).mpr hui) v (hadj u v hG) hG).2 w (mem_mateMatching.mp hwv)
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hd
    have hb := hs.bound w i' hi'
    rcases Nat.lt_or_eq_of_le hb with hlt | heq
    · have := hw.unique ((hs.exact w i' (by omega)).mp hi')
      omega
    · exact (hs.next_iff w).mp (heq ▸ hi')
  · obtain ⟨u, hu, hG⟩ := mem_altRight.mp ht
    obtain ⟨i, hij, hui⟩ := exists_isLayer hu
    have hi : i = j := by
      by_contra hne
      exact hfree (hN i (by omega) (mem_altRight_of_isLayer hui le_rfl hG))
    rw [hi] at hui
    exact (hdone u ((hfront u).mpr hui) t (hadj u t hG) hG).1 (vget_mate_eq_none_iff.mpr hfree)

/-- Specification of a breadth-first layering result. -/
structure HKBfsSpec (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r))
    (b : HKBfsResult m) : Prop where
  noShort : NoShortAug G M b.k
  exact : ∀ u i, i ≤ b.k → (vget b.dist u = some i ↔ IsLayer G M u i)
  found_true : b.found = true → ∃ t ∈ altRight G M b.k, t ∉ matchedRight M
  found_false : b.found = false → altLeft G M (b.k + 1) = altLeft G M b.k ∧
    altRight G M b.k ⊆ matchedRight M ∧ ∀ u, vget b.dist u = none ↔ u ∉ altLeft G M b.k

end BfsSpec


section BfsLoop

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)} {mate : Vector (Option (Fin m)) r}

private theorem hkBfsLoopM_spec (hadj : BipAdjValid G adj) (fuel : ℕ) {j : ℕ}
    {dist : Vector (Option ℕ) m} {frontier : List (Fin m)}
    (hex : ∀ u i, i ≤ j → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i))
    (hbd : ∀ u i, vget dist u = some i → i ≤ j)
    (hfront : ∀ u, u ∈ frontier ↔ IsLayer G (mateMatching mate) u j) (hnd : frontier.Nodup)
    (hN : NoShortAug G (mateMatching mate) j)
    (hfuel : m < fuel + (altLeft G (mateMatching mate) j).card) :
    HKBfsSpec G (mateMatching mate) (hkBfsLoopM G adj mate fuel j dist frontier).ret := by
  induction fuel generalizing j dist frontier with
  | zero =>
    have := Finset.card_le_univ (altLeft G (mateMatching mate) j)
    simp only [Fintype.card_fin] at this
    omega
  | succ fuel ih =>
    have hs0 : HKStepInv G (mateMatching mate) j ⟨dist, [], false⟩ :=
      ⟨hex, fun u i h => by have := hbd u i h; omega,
        fun u => by
          simp only [List.not_mem_nil, iff_false]
          intro h
          have := hbd u _ h
          omega,
        fun u hu => by simp at hu, List.nodup_nil, fun h => by simp at h⟩
    have hfrontL : ∀ u ∈ frontier, u ∈ altLeft G (mateMatching mate) j :=
      fun u hu => ((hfront u).mp hu).1
    set s := frontier.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s)
      (⟨dist, [], false⟩ : HKBfsState m) with hsdef
    have hs : HKStepInv G (mateMatching mate) j s := layerFold_inv frontier hfrontL hs0
    obtain ⟨hcomp, hfound⟩ := layer_complete hadj hfront hN hs (layerFold_done j frontier _)
    simp only [hkBfsLoopM, TimeM.ret_bind, hkBfsLayerM_ret, ← hsdef]
    by_cases hf : s.found = true
    · rw [ite_eq_left hf, TimeM.ret_pure]
      exact ⟨hN, hs.exact, fun _ => hs.found hf, fun h => by simp at h⟩
    rw [ite_eq_right hf]
    by_cases hne : s.next.isEmpty = true
    · rw [ite_eq_left hne, TimeM.ret_pure]
      have hnil : s.next = [] := List.isEmpty_iff.mp hne
      have hstable : altLeft G (mateMatching mate) (j + 1) = altLeft G (mateMatching mate) j := by
        refine Finset.Subset.antisymm (fun w hw => ?_) (altLeft_mono (Nat.le_succ j))
        obtain ⟨i, hij, hwi⟩ := exists_isLayer hw
        rcases Nat.lt_or_eq_of_le hij with hlt | rfl
        · exact altLeft_mono (by omega) hwi.1
        · have := hcomp w hwi
          rw [hnil] at this
          simp at this
      have hmatched : altRight G (mateMatching mate) j ⊆ matchedRight (mateMatching mate) := by
        intro t ht
        by_contra hfree
        exact hf (hfound t ht hfree)
      refine ⟨hN, hs.exact, fun h => by simp at h, fun _ => ⟨hstable, hmatched, fun u => ?_⟩⟩
      dsimp only
      constructor
      · intro hd hu
        obtain ⟨i, hij, hui⟩ := exists_isLayer hu
        rw [(hs.exact u i hij).mpr hui] at hd
        exact nomatch hd
      · intro hu
        cases hd : vget s.dist u with
        | none => rfl
        | some i =>
          exfalso
          have hb := hs.bound u i hd
          rcases Nat.lt_or_eq_of_le hb with hlt | heq
          · exact hu (altLeft_mono (by omega) ((hs.exact u i (by omega)).mp hd).1)
          · have := (hs.next_iff u).mp (heq ▸ hd)
            rw [hnil] at this
            simp at this
    rw [ite_eq_right hne]
    have hne' : s.next ≠ [] := fun h => hne (by simp [h])
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil s.next hne'
    refine ih (fun u i hi => ?_) (fun u i h => hs.bound u i h) (fun u => ?_) hs.nodup ?_ ?_
    · rcases Nat.lt_or_eq_of_le hi with hlt | rfl
      · exact hs.exact u i (by omega)
      · exact ⟨fun h => hs.next_layer u ((hs.next_iff u).mp h),
          fun h => (hs.next_iff u).mpr (hcomp u h)⟩
    · exact ⟨hs.next_layer u, hcomp u⟩
    · intro j' hj' t ht
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hlt | rfl
      · exact hN j' hlt ht
      · by_contra hfree
        exact hf (hfound t ht hfree)
    · have hwl := hs.next_layer w hw
      have hsub : altLeft G (mateMatching mate) j ⊂ altLeft G (mateMatching mate) (j + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨altLeft_mono (Nat.le_succ j), fun h =>
          hwl.2 j (Nat.lt_succ_self j) (h ▸ hwl.1)⟩
      have := Finset.card_lt_card hsub
      omega

theorem hkBfsM_spec (hadj : BipAdjValid G adj) :
    HKBfsSpec G (mateMatching mate) (hkBfsM G adj mate).ret := by
  simp only [hkBfsM, TimeM.ret_bind, foldlTickM_ret, replicateM_ret]
  set ml := (hkMatchedLeftM mate).ret
  set p := (List.finRange m).foldl (hkBfsInitStep ml) (Vector.replicate m none, [])
  obtain ⟨h1, h2⟩ := bfsInit_foldl ml (List.finRange m) (Vector.replicate m none, [])
  have hml : ∀ u, vget ml u = false ↔ IsLayer G (mateMatching mate) u 0 := by
    intro u
    rw [isLayer_zero, ← hkMatchedLeftM_ret mate u]
    simp [ml]
  refine hkBfsLoopM_spec hadj (m + 1) (fun u i hi => ?_) (fun u i h => ?_) (fun u => ?_)
    (bfsInit_nodup ml _ _ (List.nodup_finRange m) List.nodup_nil (by simp))
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (by omega)
  · have hi0 : i = 0 := by omega
    subst hi0
    rw [h1 u, ← hml u]
    simp
  · rw [h1 u] at h
    by_cases hc : u ∈ List.finRange m ∧ vget ml u = false
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      omega
    · rw [ite_eq_right hc, vget_replicate] at h
      exact nomatch h
  · rw [h2 u, ← hml u]
    simp

end BfsLoop


/-! ### Breadth-first search: cost -/

section BfsTime

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)} {mate : Vector (Option (Fin m)) r}

/-- Cost of expanding a left vertex: one frontier tick plus its candidate edges. -/
private def hkBfsCost (adj : Fin m → List (Fin r)) (u : Fin m) : ℕ := (adj u).length + 1

private theorem hkBfsStep_potential (j : ℕ) (u : Fin m) (s : HKBfsState m) (v : Fin r) :
    vecPotential (· = none) (hkBfsCost adj) (hkBfsStep G mate j u s v).dist +
        ((hkBfsStep G mate j u s v).next.map (hkBfsCost adj)).sum =
      vecPotential (· = none) (hkBfsCost adj) s.dist + (s.next.map (hkBfsCost adj)).sum := by
  unfold hkBfsStep
  by_cases hG : G (u, v) = true
  · rw [ite_eq_left hG]
    cases hm : vget mate v with
    | none => rfl
    | some w =>
      simp only
      by_cases hd : vget s.dist w = none
      · rw [ite_eq_left hd]
        have := vecPotential_vset_add (c := hkBfsCost adj) (p := (· = none)) (t := s.dist)
          (x := some (j + 1)) hd (by simp)
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [ite_eq_right hd]
  · rw [ite_eq_right hG]

private theorem layerFold_potential (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    vecPotential (· = none) (hkBfsCost adj)
        (us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s).dist +
      ((us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s).next.map
        (hkBfsCost adj)).sum =
      vecPotential (· = none) (hkBfsCost adj) s.dist + (s.next.map (hkBfsCost adj)).sum := by
  have step : ∀ (u : Fin m) (l : List (Fin r)) (s : HKBfsState m),
      vecPotential (· = none) (hkBfsCost adj) (l.foldl (hkBfsStep G mate j u) s).dist +
        ((l.foldl (hkBfsStep G mate j u) s).next.map (hkBfsCost adj)).sum =
      vecPotential (· = none) (hkBfsCost adj) s.dist + (s.next.map (hkBfsCost adj)).sum := by
    intro u l
    induction l with
    | nil => intro s; rfl
    | cons v l ih => intro s; rw [List.foldl_cons, ih, hkBfsStep_potential]
  induction us generalizing s with
  | nil => rfl
  | cons u us ih => rw [List.foldl_cons, ih, step]

private theorem hkBfsLoopM_time_le (fuel j : ℕ) (dist : Vector (Option ℕ) m)
    (frontier : List (Fin m)) :
    (hkBfsLoopM G adj mate fuel j dist frontier).time ≤
      fuel + (frontier.map (hkBfsCost adj)).sum + vecPotential (· = none) (hkBfsCost adj) dist := by
  induction fuel generalizing j dist frontier with
  | zero => simp [hkBfsLoopM]
  | succ fuel ih =>
    have hlayer : (hkBfsLayerM G adj mate j frontier ⟨dist, [], false⟩).time =
        (frontier.map (hkBfsCost adj)).sum := by
      rw [hkBfsLayerM_time]
      rfl
    have hpot := layerFold_potential (G := G) (mate := mate) (adj := adj) j frontier
      ⟨dist, [], false⟩
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hpot
    simp only [hkBfsLoopM, TimeM.time_bind, TimeM.time_tick, hlayer, hkBfsLayerM_ret]
    set s := frontier.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s)
      (⟨dist, [], false⟩ : HKBfsState m)
    split_ifs
    · simp only [TimeM.time_pure]
      omega
    · simp only [TimeM.time_pure]
      omega
    · have := ih (j + 1) s.dist s.next
      omega

private theorem sum_hkBfsCost (adj : Fin m → List (Fin r)) :
    ∑ u, hkBfsCost adj u = bipAdjSteps adj + m := by
  simp [hkBfsCost, bipAdjSteps, Finset.sum_add_distrib, Finset.sum_const]

theorem hkBfsM_time_le (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) :
    (hkBfsM G adj mate).time ≤ 6 * m + r + 1 + 2 * bipAdjSteps adj := by
  simp only [hkBfsM, TimeM.time_bind, hkMatchedLeftM_time, replicateM_time, foldlTickM_time,
    List.length_finRange, foldlTickM_ret, replicateM_ret]
  have hinit := bfsInit_potential (hkMatchedLeftM mate).ret (hkBfsCost adj) (List.finRange m)
    (Vector.replicate m none, [])
  set p := (List.finRange m).foldl (hkBfsInitStep (hkMatchedLeftM mate).ret)
    (Vector.replicate m none, [])
  have hloop := hkBfsLoopM_time_le (G := G) (adj := adj) (mate := mate) (m + 1) 0 p.1 p.2
  have h0 := vecPotential_le_sum (p := (· = none)) (hkBfsCost adj)
    (Vector.replicate m (none : Option ℕ))
  have hsum : ((List.finRange m).map (hkBfsCost adj)).sum = bipAdjSteps adj + m := by
    rw [← List.sum_toFinset _ (List.nodup_finRange m), ← sum_hkBfsCost adj]
    simp
  simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hinit
  rw [sum_hkBfsCost] at h0
  omega

end BfsTime

/-! ### Depth-first search: correctness -/

section DfsSpec

variable {G : Fin m × Fin r → Bool} {M : Finset (Fin m × Fin r)} {k : ℕ}

private theorem mate_unique {mate : Vector (Option (Fin m)) r} {w w' : Fin m} {v : Fin r}
    (h : (w, v) ∈ mateMatching mate) (h' : (w', v) ∈ mateMatching mate) : w = w' := by
  rw [mem_mateMatching] at h h'
  rw [h] at h'
  exact Option.some.inj h'

private theorem mem_matchedRight_cons {e : Fin m × Fin r} {l : List (Fin m × Fin r)} {v : Fin r} :
    v ∈ matchedRight (e :: l).toFinset ↔ v = e.2 ∨ v ∈ matchedRight l.toFinset := by
  simp only [mem_matchedRight, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
  constructor
  · rintro ⟨u, rfl | h⟩
    · exact .inl rfl
    · exact .inr ⟨u, h⟩
  · rintro (rfl | ⟨u, h⟩)
    · exact ⟨e.1, .inl rfl⟩
    · exact ⟨u, .inr h⟩

private theorem matchedRight_subset_append (p l : List (Fin m × Fin r)) :
    matchedRight l.toFinset ⊆ matchedRight (p ++ l).toFinset := by
  intro v hv
  obtain ⟨u, hu⟩ := mem_matchedRight.mp hv
  exact mem_matchedRight.mpr ⟨u, by
    simp only [List.toFinset_append, Finset.mem_union]
    exact .inr hu⟩

private theorem matchedRight_subset_cons (e : Fin m × Fin r) (l : List (Fin m × Fin r)) :
    matchedRight l.toFinset ⊆ matchedRight (e :: l).toFinset :=
  matchedRight_subset_append [e] l

/-- A layered path through the candidate edge `(u, v)`. -/
private theorem IsLayeredPath.cons_cases {U : Finset (Fin r)} {u : Fin m} {v : Fin r} {i : ℕ}
    {q : List (Fin m × Fin r)} (h : IsLayeredPath G M U k u i ((u, v) :: q)) :
    G (u, v) = true ∧ v ∉ U ∧ ((i = k ∧ v ∉ matchedRight M) ∨
      ∃ w, (w, v) ∈ M ∧ IsLayeredPath G M U k w (i + 1) q) := by
  cases h with
  | last _ hG hv hU => exact ⟨hG, hU, .inl ⟨rfl, hv⟩⟩
  | cons _ hG hM hU hp => exact ⟨hG, hU, .inr ⟨_, hM, hp⟩⟩

/-- The right vertex `v` is matched to a left vertex from which no layered path avoids `U`. -/
private def HKDead (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (U : Finset (Fin r))
    (k : ℕ) (v : Fin r) : Prop :=
  ∃ w, (w, v) ∈ M ∧ ∀ i q, ¬ IsLayeredPath G M U k w i q

private theorem HKDead.mono {U U' : Finset (Fin r)} (hU : U ⊆ U') {v : Fin r}
    (h : HKDead G M U k v) : HKDead G M U' k v := by
  obtain ⟨w, hw, h⟩ := h
  exact ⟨w, hw, fun i q hq => h i q (hq.mono hU)⟩

/-- Visited-table invariant of the depth-first search for accumulated paths `acc` and the right
vertices `S` on the current search stack. -/
private structure HKVisInv (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (k : ℕ)
    (acc : List (Fin m × Fin r)) (S : Finset (Fin r)) (vis : Vector Bool r) : Prop where
  acc_vis : ∀ v ∈ matchedRight acc.toFinset, vget vis v = true
  vis_cases : ∀ v, vget vis v = true →
    v ∈ matchedRight acc.toFinset ∨ v ∈ S ∨ HKDead G M (matchedRight acc.toFinset) k v

/-- Visited tables only grow. -/
private def HKVisLe (vis vis' : Vector Bool r) : Prop := ∀ v, vget vis v = true → vget vis' v = true

private theorem HKVisLe.refl (vis : Vector Bool r) : HKVisLe vis vis := fun _ => id

private theorem HKVisLe.trans {a b c : Vector Bool r} (h₁ : HKVisLe a b) (h₂ : HKVisLe b c) :
    HKVisLe a c := fun v h => h₂ v (h₁ v h)

private theorem HKVisLe.vset (vis : Vector Bool r) (v : Fin r) : HKVisLe vis (vset vis v true) := by
  intro x hx
  by_cases hxv : x = v
  · subst hxv
    exact vget_vset_self vis x true
  · rw [vget_vset_ne vis true (Ne.symm hxv)]
    exact hx

/-- Postcondition of a depth-first scan from `u` in layer `i`. On success the found path is
prepended to `acc`; on failure `blocked` holds. -/
private structure HKDfsPost (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (k : ℕ)
    (u : Fin m) (i : ℕ) (acc : List (Fin m × Fin r)) (S : Finset (Fin r)) (vis : Vector Bool r)
    (blocked : Prop) (res : Vector Bool r × Option (List (Fin m × Fin r))) : Prop where
  le : HKVisLe vis res.1
  found : ∀ p, res.2 = some p → ∃ q, p = q ++ acc ∧
    IsLayeredPath G M (matchedRight acc.toFinset) k u i q ∧ HKVisInv G M k p S res.1
  fail : res.2 = none → HKVisInv G M k acc S res.1 ∧ blocked

/-- Right vertices on the search stack are matched to left vertices of layers `≤ i`. -/
private def HKStackOK (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (S : Finset (Fin r))
    (i : ℕ) : Prop :=
  ∀ v ∈ S, ∃ w j, (w, v) ∈ M ∧ IsLayer G M w j ∧ j ≤ i

/-- Specification of a depth-first search procedure from layer `i`. -/
private def HKDfsSpec (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (k i : ℕ)
    (dfs : Fin m → Vector Bool r → List (Fin m × Fin r) →
      TimeM ℕ (Vector Bool r × Option (List (Fin m × Fin r)))) : Prop :=
  ∀ u vis acc S, IsLayer G M u i → HKStackOK G M S i → HKVisInv G M k acc S vis →
    HKDfsPost G M k u i acc S vis (∀ q, ¬ IsLayeredPath G M (matchedRight acc.toFinset) k u i q)
      (dfs u vis acc).ret

end DfsSpec

section DfsLevel

variable {G : Fin m × Fin r → Bool} {mate : Vector (Option (Fin m)) r}
  {dist : Vector (Option ℕ) m} {k : ℕ}

private theorem hkDfsLevelM_post
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i))
    {accept : Bool} {i : ℕ} (hik : i ≤ k) (hacc : accept = true ↔ i = k)
    {next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      TimeM ℕ (Vector Bool r × Option (List (Fin m × Fin r)))}
    (hnext : accept = false → HKDfsSpec G (mateMatching mate) k (i + 1) next)
    {u : Fin m} (hu : IsLayer G (mateMatching mate) u i) {acc : List (Fin m × Fin r)}
    {S : Finset (Fin r)} (hS : HKStackOK G (mateMatching mate) S i) (vs : List (Fin r)) :
    ∀ vis, HKVisInv G (mateMatching mate) k acc S vis →
    HKDfsPost G (mateMatching mate) k u i acc S vis
      (∀ v ∈ vs, ∀ q, ¬ IsLayeredPath G (mateMatching mate) (matchedRight acc.toFinset) k u i
        ((u, v) :: q))
      (hkDfsLevelM G mate dist accept i next u vs vis acc).ret := by
  induction vs with
  | nil =>
    intro vis hinv
    exact ⟨HKVisLe.refl vis, fun p hp => (nomatch hp),
      fun _ => ⟨hinv, fun v hv => absurd hv List.not_mem_nil⟩⟩
  | cons v vs ih =>
    intro vis hinv
    have skip : ∀ vis', HKVisLe vis vis' → HKVisInv G (mateMatching mate) k acc S vis' →
        (∀ q, ¬ IsLayeredPath G (mateMatching mate) (matchedRight acc.toFinset) k u i
          ((u, v) :: q)) →
        HKDfsPost G (mateMatching mate) k u i acc S vis
          (∀ v' ∈ v :: vs, ∀ q, ¬ IsLayeredPath G (mateMatching mate)
            (matchedRight acc.toFinset) k u i ((u, v') :: q))
          (hkDfsLevelM G mate dist accept i next u vs vis' acc).ret := by
      intro vis' hle hinv' hblk
      have h := ih vis' hinv'
      refine ⟨hle.trans h.le, h.found, fun hn => ⟨(h.fail hn).1, fun v' hv' => ?_⟩⟩
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hblk
      · exact (h.fail hn).2 v' hv'
    simp only [hkDfsLevelM, TimeM.ret_bind]
    by_cases hc : G (u, v) = true ∧ vget vis v = false
    · rw [ite_eq_left hc]
      have hvU : v ∉ matchedRight acc.toFinset := fun h => by
        have := hinv.acc_vis v h
        rw [hc.2] at this
        exact nomatch this
      cases hm : vget mate v with
      | none =>
        simp only
        by_cases ha : accept = true
        · rw [ite_eq_left ha, TimeM.ret_pure]
          have hik' : i = k := hacc.mp ha
          subst hik'
          refine ⟨HKVisLe.vset vis v, fun p hp => ?_, fun hp => (nomatch hp)⟩
          have hp' : p = (u, v) :: acc := (Option.some.inj hp).symm
          subst hp'
          refine ⟨[(u, v)], rfl,
            .last hu hc.1 (vget_mate_eq_none_iff.mp hm) hvU, ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
          · rcases mem_matchedRight_cons.mp hx with rfl | hx
            · exact vget_vset_self vis _ true
            · exact HKVisLe.vset vis v x (hinv.acc_vis x hx)
          · by_cases hxv : x = v
            · subst hxv
              exact .inl (mem_matchedRight_cons.mpr (.inl rfl))
            · rw [vget_vset_ne vis true (Ne.symm hxv)] at hx
              rcases hinv.vis_cases x hx with h | h | h
              · exact .inl (matchedRight_subset_cons _ _ h)
              · exact .inr (.inl h)
              · exact .inr (.inr (h.mono (matchedRight_subset_cons _ _)))
        · rw [ite_eq_right ha]
          refine skip vis (HKVisLe.refl vis) hinv fun q hq => ?_
          rcases hq.cons_cases.2.2 with ⟨hik', _⟩ | ⟨w, hw, _⟩
          · exact ha (hacc.mpr hik')
          · rw [mem_mateMatching, hm] at hw
            exact nomatch hw
      | some w =>
        simp only
        have hwM : (w, v) ∈ mateMatching mate := mem_mateMatching.mpr hm
        have hvM : v ∈ matchedRight (mateMatching mate) := mem_matchedRight.mpr ⟨w, hwM⟩
        by_cases hb : accept = false ∧ vget dist w = some (i + 1)
        · rw [ite_eq_left hb]
          simp only [TimeM.ret_bind]
          have hik1 : i + 1 ≤ k := by
            rcases Nat.lt_or_eq_of_le hik with h | h
            · omega
            · have := hacc.mpr h
              rw [hb.1] at this
              exact nomatch this
          have hwl : IsLayer G (mateMatching mate) w (i + 1) := (hex w (i + 1) hik1).mp hb.2
          have hS' : HKStackOK G (mateMatching mate) (insert v S) (i + 1) := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ⟨w, i + 1, hwM, hwl, le_rfl⟩
            · obtain ⟨w', j, h1, h2, h3⟩ := hS x hx
              exact ⟨w', j, h1, h2, by omega⟩
          have hinv' : HKVisInv G (mateMatching mate) k acc (insert v S) (vset vis v true) := by
            refine ⟨fun x hx => HKVisLe.vset vis v x (hinv.acc_vis x hx), fun x hx => ?_⟩
            by_cases hxv : x = v
            · subst hxv
              exact .inr (.inl (Finset.mem_insert_self _ _))
            · rw [vget_vset_ne vis true (Ne.symm hxv)] at hx
              rcases hinv.vis_cases x hx with h | h | h
              · exact .inl h
              · exact .inr (.inl (Finset.mem_insert_of_mem h))
              · exact .inr (.inr h)
          have hspec := hnext hb.1 w (vset vis v true) acc (insert v S) hwl hS' hinv'
          generalize (next w (vset vis v true) acc).ret = res at hspec ⊢
          obtain ⟨vis', o⟩ := res
          have hle : HKVisLe vis vis' := (HKVisLe.vset vis v).trans hspec.le
          cases o with
          | some p' =>
            simp only [TimeM.ret_pure]
            obtain ⟨q, hq_eq, hqpath, hqinv⟩ := hspec.found p' rfl
            refine ⟨hle, fun p hp => ?_, fun hp => (nomatch hp)⟩
            have hp' : p = (u, v) :: p' := (Option.some.inj hp).symm
            subst hp'
            refine ⟨(u, v) :: q, by rw [hq_eq]; rfl, .cons hu hc.1 hwM hvU hqpath,
              ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
            · rcases mem_matchedRight_cons.mp hx with rfl | hx
              · exact hspec.le _ (vget_vset_self vis _ true)
              · exact hqinv.acc_vis x hx
            · rcases hqinv.vis_cases x hx with h | h | h
              · exact .inl (matchedRight_subset_cons _ _ h)
              · rcases Finset.mem_insert.mp h with rfl | h
                · exact .inl (mem_matchedRight_cons.mpr (.inl rfl))
                · exact .inr (.inl h)
              · exact .inr (.inr (h.mono (matchedRight_subset_cons _ _)))
          | none =>
            simp only
            obtain ⟨hinv1, hblk⟩ := hspec.fail rfl
            refine skip vis' hle ⟨hinv1.acc_vis, fun x hx => ?_⟩ fun q hq => ?_
            · rcases hinv1.vis_cases x hx with h | h | h
              · exact .inl h
              · rcases Finset.mem_insert.mp h with rfl | h
                · refine .inr (.inr ⟨w, hwM, fun i' q hq => ?_⟩)
                  have := hwl.unique hq.isLayer
                  subst this
                  exact hblk q hq
                · exact .inr (.inl h)
              · exact .inr (.inr h)
            · rcases hq.cons_cases.2.2 with ⟨_, hfree⟩ | ⟨w', hw', hp⟩
              · exact hfree hvM
              · rw [← mate_unique hwM hw'] at hp
                exact hblk q hp
        · rw [ite_eq_right hb]
          refine skip vis (HKVisLe.refl vis) hinv fun q hq => ?_
          rcases hq.cons_cases.2.2 with ⟨_, hfree⟩ | ⟨w', hw', hp⟩
          · exact hfree hvM
          · rw [← mate_unique hwM hw'] at hp
            refine hb ⟨?_, (hex w (i + 1) hp.le).mpr hp.isLayer⟩
            cases ha : accept with
            | false => rfl
            | true =>
              have := hacc.mp ha
              have := hp.le
              omega
    · rw [ite_eq_right hc]
      refine skip vis (HKVisLe.refl vis) hinv fun q hq => ?_
      obtain ⟨hG, hU, hcase⟩ := hq.cons_cases
      have hvis : vget vis v = true := by
        cases h : vget vis v with
        | true => rfl
        | false => exact absurd ⟨hG, h⟩ hc
      rcases hinv.vis_cases v hvis with h | h | ⟨w, hw, hdead⟩
      · exact hU h
      · obtain ⟨w, j, hw, hwl, hj⟩ := hS v h
        rcases hcase with ⟨_, hfree⟩ | ⟨w', hw', hp⟩
        · exact hfree (mem_matchedRight.mpr ⟨w, hw⟩)
        · rw [← mate_unique hw hw'] at hp
          have := hwl.unique hp.isLayer
          omega
      · rcases hcase with ⟨_, hfree⟩ | ⟨w', hw', hp⟩
        · exact hfree (mem_matchedRight.mpr ⟨w, hw⟩)
        · rw [← mate_unique hw hw'] at hp
          exact hdead _ q hp

end DfsLevel

section DfsDriver

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}
  {mate : Vector (Option (Fin m)) r} {dist : Vector (Option ℕ) m} {k : ℕ}

private theorem HKDfsPost.weaken {M : Finset (Fin m × Fin r)} {u : Fin m} {i : ℕ}
    {acc : List (Fin m × Fin r)} {S : Finset (Fin r)} {vis : Vector Bool r} {P Q : Prop}
    {res : Vector Bool r × Option (List (Fin m × Fin r))}
    (h : HKDfsPost G M k u i acc S vis P res) (hPQ : P → Q) :
    HKDfsPost G M k u i acc S vis Q res :=
  ⟨h.le, h.found, fun hn => ⟨(h.fail hn).1, hPQ (h.fail hn).2⟩⟩

private theorem hkDfsM_spec (hadj : BipAdjValid G adj)
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    ∀ f i, f + i = k → HKDfsSpec G (mateMatching mate) k i (hkDfsM G adj mate dist f i) := by
  have blocked : ∀ {u : Fin m} {i : ℕ} {U : Finset (Fin r)},
      (∀ v ∈ adj u, ∀ q, ¬ IsLayeredPath G (mateMatching mate) U k u i ((u, v) :: q)) →
      ∀ q, ¬ IsLayeredPath G (mateMatching mate) U k u i q := by
    intro u i U h q hq
    obtain ⟨v, l, rfl⟩ := hq.head
    exact h v (hadj u v hq.cons_cases.1) l hq
  intro f
  induction f with
  | zero =>
    intro i hi u vis acc S hu hS hinv
    simp only [hkDfsM]
    exact (hkDfsLevelM_post (accept := true) hex (by omega) (by simp; omega)
      (fun h => nomatch h) hu hS (adj u) vis hinv).weaken blocked
  | succ f ih =>
    intro i hi u vis acc S hu hS hinv
    simp only [hkDfsM]
    exact (hkDfsLevelM_post (accept := false) hex (by omega) (by simp; omega)
      (fun _ => ih (i + 1) (by omega)) hu hS (adj u) vis hinv).weaken blocked

private theorem mem_matchedLeft_iff_mem_map {l : List (Fin m × Fin r)} {x : Fin m} :
    x ∈ matchedLeft l.toFinset ↔ x ∈ l.map Prod.fst := by
  simp only [mem_matchedLeft, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(x, v), hv, rfl⟩
  · rintro ⟨⟨a, b⟩, h, rfl⟩
    exact ⟨b, h⟩

private theorem matchedLeft_subset_append (p l : List (Fin m × Fin r)) :
    matchedLeft l.toFinset ⊆ matchedLeft (p ++ l).toFinset := by
  intro v hv
  obtain ⟨u, hu⟩ := mem_matchedLeft.mp hv
  exact mem_matchedLeft.mpr ⟨u, by
    simp only [List.toFinset_append, Finset.mem_union]
    exact .inr hu⟩

private theorem hkDfsRootsM_spec (hadj : BipAdjValid G adj)
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i))
    (us : List (Fin m)) (hnd : us.Nodup) :
    ∀ vis acc, IsLayeredFamily G (mateMatching mate) k acc →
    HKVisInv G (mateMatching mate) k acc ∅ vis →
    (∀ y ∈ us, IsLayer G (mateMatching mate) y 0 → y ∉ matchedLeft acc.toFinset) →
    (∀ y, y ∉ us → y ∉ matchedLeft acc.toFinset →
      ∀ q, ¬ IsLayeredPath G (mateMatching mate) (matchedRight acc.toFinset) k y 0 q) →
    IsLayeredFamily G (mateMatching mate) k (hkDfsRootsM G adj mate dist k us vis acc).ret ∧
    ∀ y, y ∉ matchedLeft (hkDfsRootsM G adj mate dist k us vis acc).ret.toFinset →
      ∀ q, ¬ IsLayeredPath G (mateMatching mate)
        (matchedRight (hkDfsRootsM G adj mate dist k us vis acc).ret.toFinset) k y 0 q := by
  induction us with
  | nil =>
    intro vis acc hfam _ _ hmax
    exact ⟨hfam, fun y hy => hmax y List.not_mem_nil hy⟩
  | cons x us ih =>
    intro vis acc hfam hinv hroots hmax
    obtain ⟨hxus, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [hkDfsRootsM, TimeM.ret_bind]
    by_cases hd : vget dist x = some 0
    · rw [ite_eq_left hd]
      simp only [TimeM.ret_bind]
      have hx0 : IsLayer G (mateMatching mate) x 0 := (hex x 0 (Nat.zero_le _)).mp hd
      have hS : HKStackOK G (mateMatching mate) ∅ 0 := fun v hv => absurd hv (Finset.notMem_empty v)
      have hspec := hkDfsM_spec hadj hex k 0 (by omega) x vis acc ∅ hx0 hS hinv
      generalize (hkDfsM G adj mate dist k 0 x vis acc).ret = res at hspec ⊢
      obtain ⟨vis', o⟩ := res
      cases o with
      | none =>
        obtain ⟨hinv', hblk⟩ := hspec.fail rfl
        refine ih hnd' vis' acc hfam hinv' (fun y hy => hroots y (List.mem_cons_of_mem _ hy))
          fun y hy hyacc => ?_
        by_cases hyx : y = x
        · subst hyx
          exact hblk
        · exact hmax y (fun h => (List.mem_cons.mp h).elim hyx hy) hyacc
      | some p =>
        obtain ⟨q, rfl, hq, hinv'⟩ := hspec.found p rfl
        have hxacc : x ∉ acc.map Prod.fst := fun h =>
          hroots x List.mem_cons_self hx0 (mem_matchedLeft_iff_mem_map.mpr h)
        refine ih hnd' vis' (q ++ acc) (.cons hfam hxacc hq) hinv' (fun y hy hy0 hyacc => ?_)
          fun y hy hyacc => ?_
        · rw [mem_matchedLeft_iff_mem_map, List.map_append, List.mem_append] at hyacc
          rcases hyacc with hyq | hyacc
          · obtain ⟨e, he, hfst⟩ := List.mem_map.mp hyq
            rcases hq.mem_left e he with hex' | ⟨e', _, hM'⟩
            · rw [← hfst, hex'] at hy
              exact hxus hy
            · rw [hfst] at hM'
              exact (isLayer_zero.mp hy0) (mem_matchedLeft.mpr ⟨_, hM'⟩)
          · exact hroots y (List.mem_cons_of_mem _ hy) hy0 (mem_matchedLeft_iff_mem_map.mpr hyacc)
        · by_cases hyx : y = x
          · subst hyx
            obtain ⟨v, l, rfl⟩ := hq.head
            exact absurd (mem_matchedLeft.mpr ⟨v, by simp⟩) hyacc
          · intro p hp
            exact hmax y (fun h => (List.mem_cons.mp h).elim hyx hy)
              (fun h => hyacc (matchedLeft_subset_append q acc h)) p
              (hp.mono (matchedRight_subset_append q acc))
    · rw [ite_eq_right hd]
      refine ih hnd' vis acc hfam hinv (fun y hy => hroots y (List.mem_cons_of_mem _ hy))
        fun y hy hyacc => ?_
      by_cases hyx : y = x
      · subst hyx
        intro q hq
        exact hd ((hex y 0 (Nat.zero_le _)).mpr hq.isLayer)
      · exact hmax y (fun h => (List.mem_cons.mp h).elim hyx hy) hyacc

/-- The edge list found by one phase is a maximal layered augmentation. -/
theorem hkDfsRootsM_maximal (hadj : BipAdjValid G adj)
    (hM : IsMatching G (mateMatching mate))
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    IsLayeredFamily G (mateMatching mate) k
      (hkDfsRootsM G adj mate dist k (List.finRange m) (Vector.replicate r false) []).ret ∧
    IsMaximalLayeredAugmentation G (mateMatching mate)
      (hkDfsRootsM G adj mate dist k (List.finRange m) (Vector.replicate r false) []).ret.toFinset
      k := by
  have h := hkDfsRootsM_spec hadj hex (List.finRange m) (List.nodup_finRange m)
    (Vector.replicate r false) [] .nil
    ⟨fun v hv => by simp [matchedRight] at hv, fun v hv => by
      rw [vget_replicate] at hv
      exact nomatch hv⟩
    (fun y _ _ => by simp [matchedLeft]) (fun y hy => absurd (List.mem_finRange y) hy)
  exact ⟨h.1, h.1.isMaximalLayeredAugmentation hM h.2⟩

end DfsDriver

section ApplyEdges

/-- Rematching along an edge list with distinct right ends: `v` is matched to `u` afterwards iff
`(u, v)` is in the list, or `v` is not rematched and was matched to `u` before. -/
theorem vget_foldl_apply (mate : Vector (Option (Fin m)) r) (es : List (Fin m × Fin r))
    (hnd : (es.map Prod.snd).Nodup) (u : Fin m) (v : Fin r) :
    vget (es.foldl (fun mt e => vset mt e.2 (some e.1)) mate) v = some u ↔
      (u, v) ∈ es ∨ (v ∉ es.map Prod.snd ∧ vget mate v = some u) := by
  induction es generalizing mate with
  | nil => simp
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons, ih _ hnd.2]
    by_cases hvb : v = b
    · subst hvb
      simp only [vget_vset_self, Option.some.injEq, List.mem_cons, Prod.mk.injEq, and_true,
        List.map_cons, true_or, not_true_eq_false, false_and, or_false]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact .inr (by
            have : (u, v) ∈ es := h
            exact absurd (List.mem_map.mpr ⟨(u, v), this, rfl⟩) hnd.1)
        · exact .inl h.symm
      · rintro (h | h)
        · exact .inr ⟨hnd.1, h.symm⟩
        · exact absurd (List.mem_map.mpr ⟨(u, v), h, rfl⟩) hnd.1
    · rw [vget_vset_ne mate _ (Ne.symm hvb)]
      simp only [List.mem_cons, Prod.mk.injEq, hvb, and_false, false_or, List.map_cons]

/-- Rematching a mate table along a compatible edge list realizes `augment`. -/
theorem mateMatching_applyEdges (mate : Vector (Option (Fin m)) r)
    (es : List (Fin m × Fin r))
    (hnd : (es.map Prod.snd).Nodup)
    (hcompat : ∀ u v, (u, v) ∈ mateMatching mate →
      (u ∈ matchedLeft es.toFinset ↔ v ∈ matchedRight es.toFinset)) :
    mateMatching (es.foldl (fun mt e => vset mt e.2 (some e.1)) mate) =
      augment (mateMatching mate) es.toFinset := by
  ext ⟨u, v⟩
  rw [mem_mateMatching, vget_foldl_apply mate es hnd, mem_augment, List.mem_toFinset,
    mem_mateMatching]
  have hv : v ∈ es.map Prod.snd ↔ v ∈ matchedRight es.toFinset := by
    simp only [List.mem_map, mem_matchedRight, List.mem_toFinset]
    constructor
    · rintro ⟨⟨a, b⟩, h, rfl⟩
      exact ⟨a, h⟩
    · rintro ⟨a, h⟩
      exact ⟨(a, v), h, rfl⟩
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact .inl h
    · refine .inr ⟨h2, fun hu => h1 (hv.mpr ((hcompat u v (mem_mateMatching.mpr h2)).mp hu))⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact .inl h
    · exact .inr ⟨fun h => h2 ((hcompat u v (mem_mateMatching.mpr h1)).mpr (hv.mp h)), h1⟩

end ApplyEdges

/-! ### Depth-first search: cost -/


section DfsTime

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}
  {mate : Vector (Option (Fin m)) r} {dist : Vector (Option ℕ) m}

/-- Cost charged to a right vertex: the candidate list length of its mate. -/
private def hkDfsCost (adj : Fin m → List (Fin r)) (mate : Vector (Option (Fin m)) r)
    (v : Fin r) : ℕ :=
  match vget mate v with
  | some w => (adj w).length
  | none => 0

private theorem hkDfsLevelM_time_le {accept : Bool} {i : ℕ}
    {next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      TimeM ℕ (Vector Bool r × Option (List (Fin m × Fin r)))}
    (hnext : ∀ w vis acc, (next w vis acc).time +
        vecPotential (· = false) (hkDfsCost adj mate) (next w vis acc).ret.1 ≤
      (adj w).length + vecPotential (· = false) (hkDfsCost adj mate) vis)
    (u : Fin m) (acc : List (Fin m × Fin r)) (vs : List (Fin r)) :
    ∀ vis, (hkDfsLevelM G mate dist accept i next u vs vis acc).time +
        vecPotential (· = false) (hkDfsCost adj mate)
          (hkDfsLevelM G mate dist accept i next u vs vis acc).ret.1 ≤
      vs.length + vecPotential (· = false) (hkDfsCost adj mate) vis := by
  induction vs with
  | nil => intro vis; simp [hkDfsLevelM]
  | cons v vs ih =>
    intro vis
    have skip : ∀ vis', vecPotential (· = false) (hkDfsCost adj mate) vis' ≤
        vecPotential (· = false) (hkDfsCost adj mate) vis →
        1 + (hkDfsLevelM G mate dist accept i next u vs vis' acc).time +
          vecPotential (· = false) (hkDfsCost adj mate)
            (hkDfsLevelM G mate dist accept i next u vs vis' acc).ret.1 ≤
        (v :: vs).length + vecPotential (· = false) (hkDfsCost adj mate) vis := by
      intro vis' hvis'
      have := ih vis'
      simp only [List.length_cons]
      omega
    simp only [hkDfsLevelM, TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind]
    by_cases hc : G (u, v) = true ∧ vget vis v = false
    · rw [ite_eq_left hc]
      have hpot : ∀ w, vget mate v = some w →
          vecPotential (· = false) (hkDfsCost adj mate) (vset vis v true) + (adj w).length =
            vecPotential (· = false) (hkDfsCost adj mate) vis := by
        intro w hw
        have := vecPotential_vset_add (p := (· = false)) (c := hkDfsCost adj mate) (t := vis)
          (w := v) (x := true) hc.2 (by simp)
        simpa [hkDfsCost, hw] using this
      cases hm : vget mate v with
      | none =>
        simp only
        by_cases ha : accept = true
        · rw [ite_eq_left ha, TimeM.time_pure, TimeM.ret_pure]
          have := vecPotential_vset_le (p := (· = false)) (c := hkDfsCost adj mate) vis v
            (x := true) (by simp)
          simp only [List.length_cons]
          omega
        · rw [ite_eq_right ha]
          exact skip vis le_rfl
      | some w =>
        simp only
        by_cases hb : accept = false ∧ vget dist w = some (i + 1)
        · rw [ite_eq_left hb]
          simp only [TimeM.time_bind, TimeM.ret_bind]
          have hp := hpot w hm
          have hn := hnext w (vset vis v true) acc
          generalize next w (vset vis v true) acc = R at hn ⊢
          rcases R with ⟨⟨vis', o⟩, t⟩
          simp only at hn
          cases o with
          | some q =>
            simp only [TimeM.time_pure, TimeM.ret_pure, List.length_cons]
            omega
          | none =>
            simp only [List.length_cons]
            have := ih vis'
            omega
        · rw [ite_eq_right hb]
          exact skip vis le_rfl
    · rw [ite_eq_right hc]
      exact skip vis le_rfl

private theorem hkDfsM_time_le (f : ℕ) : ∀ i u vis acc,
    (hkDfsM G adj mate dist f i u vis acc).time +
        vecPotential (· = false) (hkDfsCost adj mate) (hkDfsM G adj mate dist f i u vis acc).ret.1 ≤
      (adj u).length + vecPotential (· = false) (hkDfsCost adj mate) vis := by
  induction f with
  | zero =>
    intro i u vis acc
    simp only [hkDfsM]
    exact hkDfsLevelM_time_le (fun w vis acc => by simp) u acc (adj u) vis
  | succ f ih =>
    intro i u vis acc
    simp only [hkDfsM]
    exact hkDfsLevelM_time_le (fun w vis acc => ih (i + 1) w vis acc) u acc (adj u) vis

private theorem hkDfsRootsM_time_le (k : ℕ) (us : List (Fin m)) :
    ∀ vis acc, (hkDfsRootsM G adj mate dist k us vis acc).time ≤
      us.length + (us.map fun u => (adj u).length).sum +
        vecPotential (· = false) (hkDfsCost adj mate) vis := by
  induction us with
  | nil => intro vis acc; simp [hkDfsRootsM]
  | cons u us ih =>
    intro vis acc
    simp only [hkDfsRootsM, TimeM.time_bind, TimeM.time_tick, List.length_cons, List.map_cons,
      List.sum_cons]
    split_ifs
    · simp only [TimeM.time_bind]
      have h1 := hkDfsM_time_le (G := G) (adj := adj) (mate := mate) (dist := dist) k 0 u vis acc
      have h2 := ih (hkDfsM G adj mate dist k 0 u vis acc).ret.1
        ((hkDfsM G adj mate dist k 0 u vis acc).ret.2.getD acc)
      omega
    · have := ih vis acc
      omega

/-- The initial potential is at most the total candidate list length, as `mate` is a matching. -/
private theorem vecPotential_replicate_le (hM : IsMatching G (mateMatching mate)) :
    vecPotential (· = false) (hkDfsCost adj mate) (Vector.replicate r false) ≤ bipAdjSteps adj := by
  refine (vecPotential_le_sum _ _).trans ?_
  have hc : ∀ v, hkDfsCost adj mate v =
      ∑ u, if vget mate v = some u then (adj u).length else 0 := by
    intro v
    unfold hkDfsCost
    cases hv : vget mate v with
    | none => simp
    | some w => simp [Finset.sum_ite_eq]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hcard : (Finset.univ.filter fun v => vget mate v = some u).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hM.2.1 u a b (mem_mateMatching.mpr ha) (mem_mateMatching.mpr hb)
  calc _ ≤ 1 * (adj u).length := Nat.mul_le_mul_right _ hcard
    _ = (adj u).length := Nat.one_mul _

private theorem sum_finRange_length (adj : Fin m → List (Fin r)) :
    ((List.finRange m).map fun u => (adj u).length).sum = bipAdjSteps adj := by
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  simp [bipAdjSteps]

end DfsTime

/-! ### One phase -/

section Phase

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}
  {mate : Vector (Option (Fin m)) r} {dist : Vector (Option ℕ) m} {k : ℕ}

theorem hkPhaseM_spec (hadj : BipAdjValid G adj) (hM : IsMatching G (mateMatching mate))
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    ∃ N, IsMaximalLayeredAugmentation G (mateMatching mate) N k ∧
      mateMatching (hkPhaseM G adj mate dist k).ret = augment (mateMatching mate) N := by
  obtain ⟨hfam, hmax⟩ := hkDfsRootsM_maximal (dist := dist) hadj hM hex
  refine ⟨_, hmax, ?_⟩
  simp only [hkPhaseM, TimeM.ret_bind, replicateM_ret, hkApplyEdgesM, foldlTickM_ret]
  exact mateMatching_applyEdges mate _ (hfam.nodup_right hM) hmax.compat

theorem hkPhaseM_time_le (hadj : BipAdjValid G adj) (hM : IsMatching G (mateMatching mate))
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    (hkPhaseM G adj mate dist k).time ≤ 2 * r + m + 2 * bipAdjSteps adj := by
  obtain ⟨hfam, -⟩ := hkDfsRootsM_maximal (dist := dist) hadj hM hex
  simp only [hkPhaseM, TimeM.time_bind, replicateM_time, replicateM_ret, hkApplyEdgesM,
    foldlTickM_time]
  have h1 := hkDfsRootsM_time_le (G := G) (adj := adj) (mate := mate) (dist := dist) k
    (List.finRange m) (Vector.replicate r false) []
  have h2 := vecPotential_replicate_le (G := G) (adj := adj) (mate := mate) hM
  rw [sum_finRange_length, List.length_finRange] at h1
  have h3 := (hfam.nodup_right hM).length_le_card
  rw [List.length_map, Fintype.card_fin] at h3
  omega

end Phase

/-! ### Phase loop -/

section Loop

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}

/-- Postcondition of the phase loop started with phase counter `n` from `mate`. -/
private structure HKLoopPost (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) (n : ℕ)
    (res : HKLoopResult m r) : Prop where
  isMatching : IsMatching G (mateMatching res.mate)
  le_phases : n ≤ res.phases
  run : IsPhaseRun G (mateMatching mate) (res.phases - n)
  closed : ∃ k, altLeft G (mateMatching res.mate) (k + 1) = altLeft G (mateMatching res.mate) k ∧
    altRight G (mateMatching res.mate) k ⊆ matchedRight (mateMatching res.mate) ∧
    ∀ u, vget res.dist u = none ↔ u ∉ altLeft G (mateMatching res.mate) k

private theorem hkLoopM_spec (hadj : BipAdjValid G adj) {C : ℕ}
    (hC : 6 * m + r + 1 + 2 * bipAdjSteps adj + (2 * r + m + 2 * bipAdjSteps adj) ≤ C) :
    ∀ fuel n (mate : Vector (Option (Fin m)) r), IsMatching G (mateMatching mate) →
      m < fuel + (mateMatching mate).card →
      HKLoopPost G mate n (hkLoopM G adj fuel n mate).ret ∧
        (hkLoopM G adj fuel n mate).time ≤
          ((hkLoopM G adj fuel n mate).ret.phases - n + 1) * C := by
  intro fuel
  induction fuel with
  | zero =>
    intro n mate hM hfuel
    have h := hM.card_le_card_left
    simp only [Fintype.card_fin] at h
    omega
  | succ fuel ih =>
    intro n mate hM hfuel
    have hb := hkBfsM_spec (G := G) (adj := adj) (mate := mate) hadj
    have hbt := hkBfsM_time_le G adj mate
    simp only [hkLoopM, TimeM.ret_bind, TimeM.time_bind]
    set b := (hkBfsM G adj mate).ret with hbdef
    by_cases hf : b.found = true
    · rw [ite_eq_left hf]
      simp only [TimeM.ret_bind, TimeM.time_bind]
      have hex := hb.exact
      obtain ⟨N, hN, hmate'⟩ := hkPhaseM_spec (dist := b.dist) hadj hM hex
      have hpt := hkPhaseM_time_le (dist := b.dist) (k := b.k) hadj hM hex
      obtain ⟨t, ht, hfree⟩ := hb.found_true hf
      have hM' : IsMatching G (mateMatching (hkPhaseM G adj mate b.dist b.k).ret) := by
        rw [hmate']
        exact hN.isMatching_augment hM
      have hlt : (mateMatching mate).card <
          (mateMatching (hkPhaseM G adj mate b.dist b.k).ret).card := by
        rw [hmate']
        exact hN.card_lt_card_augment_of_mem_altRight hM hb.noShort ht hfree
      obtain ⟨hpost, htime⟩ := ih (n + 1) _ hM' (by omega)
      refine ⟨⟨hpost.isMatching, by have := hpost.le_phases; omega, ?_, hpost.closed⟩, ?_⟩
      · have hrun := hpost.run
        rw [hmate'] at hrun
        have heq : (hkLoopM G adj fuel (n + 1) (hkPhaseM G adj mate b.dist b.k).ret).ret.phases -
            n = (hkLoopM G adj fuel (n + 1) (hkPhaseM G adj mate b.dist b.k).ret).ret.phases -
              (n + 1) + 1 := by
          have := hpost.le_phases
          omega
        rw [heq]
        exact .step hb.noShort ht hfree hN hrun
      · have hle := hpost.le_phases
        set P := (hkLoopM G adj fuel (n + 1) (hkPhaseM G adj mate b.dist b.k).ret).ret.phases
        have heq : P - n + 1 = (P - (n + 1) + 1) + 1 := by omega
        rw [heq, Nat.succ_mul]
        omega
    · have hf' : b.found = false := by simpa using hf
      rw [ite_eq_right hf]
      simp only [TimeM.ret_pure, TimeM.time_pure]
      obtain ⟨hstable, hsub, hdist⟩ := hb.found_false hf'
      refine ⟨⟨hM, le_rfl, by rw [Nat.sub_self]; exact .done, b.k, hstable, hsub, hdist⟩, ?_⟩
      simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul]
      omega

end Loop

/-! ### Extraction -/

section Extract

/-- Membership in the matching extracted from a mate table. -/
theorem mem_foldl_hkMatchingStep (mate : Vector (Option (Fin m)) r) (l : List (Fin r))
    (a : Finset (Fin m × Fin r)) (u : Fin m) (v : Fin r) :
    (u, v) ∈ l.foldl (hkMatchingStep mate) a ↔ (u, v) ∈ a ∨ (v ∈ l ∧ vget mate v = some u) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    unfold hkMatchingStep
    cases hx : vget mate x with
    | none =>
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl h
        · rw [hx] at h2
          exact nomatch h2
        · exact .inr ⟨h1, h2⟩
    | some w =>
      simp only [Finset.mem_insert, Prod.mk.injEq, List.mem_cons]
      constructor
      · rintro ((⟨rfl, rfl⟩ | h) | ⟨h1, h2⟩)
        · exact .inr ⟨.inl rfl, hx⟩
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl (.inr h)
        · rw [hx] at h2
          exact .inl (.inl ⟨(Option.some.inj h2).symm, rfl⟩)
        · exact .inr ⟨h1, h2⟩

private theorem mem_foldl_hkCoverLeftStep (dist : Vector (Option ℕ) m) (l : List (Fin m))
    (a : Finset (Fin m)) (u : Fin m) :
    u ∈ l.foldl (hkCoverLeftStep dist) a ↔ u ∈ a ∨ (u ∈ l ∧ vget dist u = none) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    unfold hkCoverLeftStep
    by_cases hx : vget dist x = none
    · rw [ite_eq_left hx]
      simp only [Finset.mem_insert, List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h1, h2⟩)
        · exact .inr ⟨.inl rfl, hx⟩
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr ⟨h1, h2⟩
    · rw [ite_eq_right hx]
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl h
        · exact absurd h2 hx
        · exact .inr ⟨h1, h2⟩

private theorem mem_foldl_hkCoverRightStep (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (l : List (Fin r)) (a : Finset (Fin r)) (v : Fin r) :
    v ∈ l.foldl (hkCoverRightStep mate dist) a ↔
      v ∈ a ∨ (v ∈ l ∧ ∃ w, vget mate v = some w ∧ vget dist w ≠ none) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    unfold hkCoverRightStep
    cases hx : vget mate x with
    | none =>
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact .inl h
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact .inl h
        · obtain ⟨w, hw, _⟩ := h2
          rw [hx] at hw
          exact nomatch hw
        · exact .inr ⟨h1, h2⟩
    | some w =>
      simp only
      by_cases hd : vget dist w = none
      · rw [ite_eq_left hd]
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl h
          · exact .inr ⟨.inr h1, h2⟩
        · rintro (h | ⟨rfl | h1, h2⟩)
          · exact .inl h
          · obtain ⟨w', hw', hd'⟩ := h2
            rw [hx] at hw'
            rw [← Option.some.inj hw'] at hd'
            exact absurd hd hd'
          · exact .inr ⟨h1, h2⟩
      · rw [ite_eq_right hd]
        simp only [Finset.mem_insert, List.mem_cons]
        constructor
        · rintro ((rfl | h) | ⟨h1, h2⟩)
          · exact .inr ⟨.inl rfl, w, hx, hd⟩
          · exact .inl h
          · exact .inr ⟨.inr h1, h2⟩
        · rintro (h | ⟨rfl | h1, h2⟩)
          · exact .inl (.inr h)
          · exact .inl (.inl rfl)
          · exact .inr ⟨h1, h2⟩

end Extract

/-! ### Main theorems -/

section Main

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}

/-- Per-round cost bound used in `hopcroftKarpM_time_le`. -/
private theorem hk_round_cost (adj : Fin m → List (Fin r)) :
    6 * m + r + 1 + 2 * bipAdjSteps adj + (2 * r + m + 2 * bipAdjSteps adj) ≤
      7 * m + 3 * r + 1 + 4 * bipAdjSteps adj := by
  omega

private theorem hkLoop_start (hadj : BipAdjValid G adj) :
    HKLoopPost G (Vector.replicate r none) 0
        (hkLoopM G adj (m + 1) 0 (Vector.replicate r none)).ret ∧
      (hkLoopM G adj (m + 1) 0 (Vector.replicate r none)).time ≤
        ((hkLoopM G adj (m + 1) 0 (Vector.replicate r none)).ret.phases - 0 + 1) *
          (7 * m + 3 * r + 1 + 4 * bipAdjSteps adj) := by
  have h0 : mateMatching (Vector.replicate r (none : Option (Fin m))) = ∅ := by
    ext e
    simp [vget_replicate]
  refine hkLoopM_spec hadj (hk_round_cost adj) (m + 1) 0 _ ?_ (by omega)
  rw [h0]
  exact ⟨by simp, by simp, by simp⟩

/-- **Correctness of Hopcroft–Karp.** `hopcroftKarpM G adj` returns a maximum matching and a
minimum König vertex cover of equal size, after at most `2⌊√ν⌋` augmenting phases, where `ν` is
the maximum matching size. -/
theorem hopcroftKarpM_correct (hadj : BipAdjValid G adj) :
    IsMaxMatching G (hopcroftKarpM G adj).ret.matching ∧
      IsMinVertexCover G (hopcroftKarpM G adj).ret.cover ∧
      (hopcroftKarpM G adj).ret.matching.card = (hopcroftKarpM G adj).ret.cover.size ∧
      (hopcroftKarpM G adj).ret.phases ≤ 2 * Nat.sqrt (hopcroftKarpM G adj).ret.matching.card := by
  obtain ⟨hpost, -⟩ := hkLoop_start (G := G) hadj
  have h0 : mateMatching (Vector.replicate r (none : Option (Fin m))) = ∅ := by
    ext e
    simp [vget_replicate]
  simp only [hopcroftKarpM, TimeM.ret_bind, replicateM_ret, foldlTickM_ret, TimeM.ret_pure]
  set st := (hkLoopM G adj (m + 1) 0 (Vector.replicate r none)).ret
  obtain ⟨k, hstable, hsub, hdist⟩ := hpost.closed
  have hM := hpost.isMatching
  have hmatch : (List.finRange r).foldl (hkMatchingStep st.mate) ∅ = mateMatching st.mate := by
    ext ⟨u, v⟩
    rw [mem_foldl_hkMatchingStep, mem_mateMatching]
    simp
  have hcover : (⟨(List.finRange m).foldl (hkCoverLeftStep st.dist) ∅,
      (List.finRange r).foldl (hkCoverRightStep st.mate st.dist) ∅⟩ : VertexCover (Fin m) (Fin r))
      = layerCover G (mateMatching st.mate) k := by
    simp only [layerCover, VertexCover.mk.injEq]
    constructor
    · ext u
      rw [mem_foldl_hkCoverLeftStep, Finset.mem_sdiff, ← hdist u]
      simp
    · ext v
      rw [mem_foldl_hkCoverRightStep, mem_altRight_iff_of_stable hM hstable hsub]
      simp only [Finset.notMem_empty, List.mem_finRange, true_and, false_or, mem_mateMatching]
      constructor
      · rintro ⟨w, hw, hd⟩
        exact ⟨w, hw, by_contra fun h => hd ((hdist w).mpr h)⟩
      · rintro ⟨w, hw, hwk⟩
        exact ⟨w, hw, fun h => (hdist w).mp h hwk⟩
  rw [hmatch, hcover]
  obtain ⟨hmax, hmin⟩ := isMaxMatching_isMinVertexCover_of_stable hM hstable hsub
  refine ⟨hmax, hmin, (size_layerCover_of_stable hM hstable hsub).symm, ?_⟩
  have hrun := hpost.run
  rw [h0, Nat.sub_zero] at hrun
  exact hrun.le_two_mul_sqrt hmax

end Main

section Main2

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}

/-- **Running time of Hopcroft–Karp.** At most `2⌊√ν⌋ + 1` rounds of breadth-first layering and
depth-first augmentation, each costing `O(m + r + |adj|)` charged steps, where `ν` is the maximum
matching size and `|adj| = bipAdjSteps adj` is the total candidate list length. -/
theorem hopcroftKarpM_time_le (hadj : BipAdjValid G adj) :
    (hopcroftKarpM G adj).time ≤
      (2 * Nat.sqrt (hopcroftKarpM G adj).ret.matching.card + 1) *
        (7 * m + 3 * r + 1 + 4 * bipAdjSteps adj) + m + 3 * r := by
  obtain ⟨-, htime⟩ := hkLoop_start (G := G) hadj
  have hph := (hopcroftKarpM_correct hadj).2.2.2
  have hphase : (hopcroftKarpM G adj).ret.phases =
      (hkLoopM G adj (m + 1) 0 (Vector.replicate r none)).ret.phases := by
    simp [hopcroftKarpM, replicateM_ret]
  rw [hphase] at hph
  generalize (hopcroftKarpM G adj).ret.matching.card = ν at hph ⊢
  simp only [hopcroftKarpM, TimeM.time_bind, replicateM_time, replicateM_ret, foldlTickM_time,
    List.length_finRange, TimeM.time_pure]
  have := Nat.mul_le_mul_right (7 * m + 3 * r + 1 + 4 * bipAdjSteps adj)
    (show (hkLoopM G adj (m + 1) 0 (Vector.replicate r none)).ret.phases - 0 + 1 ≤
      2 * Nat.sqrt ν + 1 by omega)
  omega

/-- `O((m + r + |adj|) √(min m r))` form of `hopcroftKarpM_time_le`. -/
theorem hopcroftKarpM_time_le_sqrt_min (hadj : BipAdjValid G adj) :
    (hopcroftKarpM G adj).time ≤
      (2 * Nat.sqrt (min m r) + 1) * (7 * m + 3 * r + 1 + 4 * bipAdjSteps adj) + m + 3 * r := by
  have h := hopcroftKarpM_time_le hadj
  have hM := (hopcroftKarpM_correct hadj).1.1
  have hs := Nat.sqrt_le_sqrt (le_min (hM.card_le_card_left.trans_eq (Fintype.card_fin m))
    (hM.card_le_card_right.trans_eq (Fintype.card_fin r)))
  have := Nat.mul_le_mul_right (7 * m + 3 * r + 1 + 4 * bipAdjSteps adj)
    (show 2 * Nat.sqrt (hopcroftKarpM G adj).ret.matching.card + 1 ≤
      2 * Nat.sqrt (min m r) + 1 by omega)
  omega

/-- Correctness of `hopcroftKarpDenseM`. -/
theorem hopcroftKarpDenseM_correct (G : Fin m × Fin r → Bool) :
    IsMaxMatching G (hopcroftKarpDenseM G).ret.matching ∧
      IsMinVertexCover G (hopcroftKarpDenseM G).ret.cover ∧
      (hopcroftKarpDenseM G).ret.matching.card = (hopcroftKarpDenseM G).ret.cover.size ∧
      (hopcroftKarpDenseM G).ret.phases ≤
        2 * Nat.sqrt (hopcroftKarpDenseM G).ret.matching.card :=
  hopcroftKarpM_correct (bipAdjValid_denseBipAdj G)

/-- `O(m r √(min m r))` running time of `hopcroftKarpDenseM`. -/
theorem hopcroftKarpDenseM_time_le (G : Fin m × Fin r → Bool) :
    (hopcroftKarpDenseM G).time ≤
      (2 * Nat.sqrt (min m r) + 1) * (7 * m + 3 * r + 1 + 4 * (m * r)) + m + 3 * r := by
  have h := hopcroftKarpM_time_le_sqrt_min (bipAdjValid_denseBipAdj G)
  rw [bipAdjSteps_denseBipAdj] at h
  exact h

/-- Hopcroft–Karp and the Edmonds–Karp reduction `bipartiteMatchingM` find matchings of the same
(maximum) size. -/
theorem card_hopcroftKarpM_matching (hadj : BipAdjValid G adj) :
    (hopcroftKarpM G adj).ret.matching.card = (bipartiteMatchingM G).ret.matching.card := by
  have h1 := (hopcroftKarpM_correct hadj).1
  have h2 := (bipartiteMatchingM_correct G).1
  exact le_antisymm (h2.2 _ h1.1) (h1.2 _ h2.1)

end Main2

section Perfect

/-- Decide whether `G : Fin n × Fin n → Bool` has a perfect matching using Hopcroft–Karp. -/
@[expose] def decidePerfectMatchingHKM {n : ℕ} (G : Fin n × Fin n → Bool)
    (adj : Fin n → List (Fin n)) : TimeM ℕ Bool := do
  let res ← hopcroftKarpM G adj
  ✓
  pure (decide (res.matching.card = n))

variable {n : ℕ} {G : Fin n × Fin n → Bool} {adj : Fin n → List (Fin n)}

theorem decidePerfectMatchingHKM_eq_true_iff (hadj : BipAdjValid G adj) :
    (decidePerfectMatchingHKM G adj).ret = true ↔
      Cslib.Circuits.BipartiteMatching.HasPerfectMatching G := by
  simp only [decidePerfectMatchingHKM, TimeM.ret_bind, TimeM.ret_pure, decide_eq_true_iff]
  rw [card_hopcroftKarpM_matching hadj, ← decidePerfectMatchingM_eq_true_iff]
  simp [decidePerfectMatchingM]

theorem decidePerfectMatchingHKM_time_le (hadj : BipAdjValid G adj) :
    (decidePerfectMatchingHKM G adj).time ≤
      (2 * Nat.sqrt n + 1) * (10 * n + 1 + 4 * bipAdjSteps adj) + 4 * n + 1 := by
  simp only [decidePerfectMatchingHKM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
  have h := hopcroftKarpM_time_le_sqrt_min hadj
  rw [Nat.min_self] at h
  have : 7 * n + 3 * n + 1 + 4 * bipAdjSteps adj = 10 * n + 1 + 4 * bipAdjSteps adj := by omega
  rw [this] at h
  omega

end Perfect

end Cslib.Algorithms.Lean.MaxFlow
