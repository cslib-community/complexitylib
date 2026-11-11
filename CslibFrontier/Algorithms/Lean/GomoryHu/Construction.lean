/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield
public import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut
public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp

/-!
# Gomory–Hu trees with `n - 1` maximum flow computations

An executable `TimeM` construction of a Gomory–Hu tree of a weighted multigraph
`W : Fin n → Fin n → ℕ`, following Gusfield's contraction-free algorithm ([Gusfield1990]): one
Edmonds–Karp maximum flow computation ([EdmondsKarp1972]) per non-root vertex, so `n - 1` in total,
all on the original graph, plus `O(n)` bookkeeping per vertex on a parent array and edge-weight
array `fl`. Correctness is transferred from the abstract algorithm
`Cslib.Algorithms.Lean.GomoryHu.gusfieldWithWeights` of
`CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield`, with the Edmonds–Karp minimum cut and maximum
flow value as the oracle.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.Output`: parent array `parent` and edge-weight array `weight`
  returned by Gusfield's algorithm.
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM`: Gusfield's algorithm over `Fin n` in `TimeM ℕ`,
  returning the parent array and edge weights of the tree.
* `Cslib.Algorithms.Lean.GomoryHu.ekCut`, `Cslib.Algorithms.Lean.GomoryHu.ekValue`: the minimum
  cut and maximum flow value returned by `edmondsKarpM`.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gomoryHuM`: the parent graph of the output is a
  Gomory–Hu tree of `cutWeight W` (cut-equivalent: the side of each tree edge `uv` containing `u`
  is a minimum `u`–`v` cut of `W`).
* `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHuM_weight_eq_minCutBetween`: for every vertex
  `u : Fin n`, the recorded weight `vget (gomoryHuM W adj r).ret.weight u` equals
  `minCutBetween W u (vget (gomoryHuM W adj r).ret.parent u)` (`0` at the root `r`,
  `vget_gomoryHuM_weight_root`).
* `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHuM`,
  `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHuM_parent`,
  `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHuM_weight`: the output agrees with the abstract
  `gusfieldParent` and `gusfieldWithWeights` run with `ekCut` and `ekValue`.
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM_time_le_of_forall`: the charged time is at most `3 n`
  plus `n - 1` times (any bound on one Edmonds–Karp computation, plus `n + 3`).
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM_time_le`: the same with the Edmonds–Karp bound
  `edmondsKarpM_time_le`, `O(n m²)` per computation for `m` edges, so `O(n² m²)` in total.
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM_time_le_dense`: `O(n ^ 6)` with dense adjacency lists.

## Cost model

The unit-cost model of `Cslib.Algorithms.Lean.MaxFlow.edmondsKarpM`, extended with `Finset`
membership on the returned cut and reading `out.flow.value` (`netOut N.s`, an `O(n)` sum over
`Fin n`) as free primitives: `Vector` reads and writes, those membership tests, that `Flow.value`
sum, equality tests on `Fin n`, and evaluating `W u v` count as `O(1)` primitives inside charged
steps. (Computing `out.flow.value` once per step would add `O(n²)` in total, subsumed by the
re-hanging scan; `O(n)` `Finset` membership tests inside each `n`-vertex scan would add `O(n³)` in
total.) Charged: `n` ticks to allocate the parent array `p`, `n` ticks to allocate the edge-weight
array `fl`, `1` tick per vertex for the loop test `s = r`, and for each non-root vertex `s`: `1`
tick to read its parent, the full Edmonds–Karp cost, `n` ticks for the re-hanging scan over all
vertices, `1` tick for the final swap test and its parent writes, and `1` tick to record the edge
weight in `fl`.

## Limitations

The weights of `W` are natural numbers, and only Edmonds–Karp is instantiated as the maximum flow
oracle (`gomoryHuM_time_le_of_forall` accepts any per-call bound).

## References

* [EdmondsKarp1972]
* [GomoryHu1961]
* [Gusfield1990]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut
open SimpleGraph (parentGraph)

variable {n : ℕ}

/-- Output of Gusfield's Gomory–Hu tree construction on `Fin n`: the parent array `parent` rooted
at `r` and the edge-weight array `weight` storing `λ(u, parent[u])` for every non-root `u` (`0` at
the root `r`). -/
structure Output (n : ℕ) where
  /-- Parent array of the tree (`vget parent r = r`). -/
  parent : Vector (Fin n) n
  /-- Edge weight `λ(u, vget parent u)` for every non-root vertex `u` (`0` at `r`). -/
  weight : Vector ℕ n
  deriving DecidableEq

/-- Re-hang below `s` every vertex `z ∈ zs` whose parent in `p` is `t` and which lies in `X`,
writing into `acc` and charging `1` tick per scanned vertex. -/
@[expose] def rehangM (p : Vector (Fin n) n) (s t : Fin n) (X : Finset (Fin n)) :
    List (Fin n) → Vector (Fin n) n → TimeM ℕ (Vector (Fin n) n)
  | [], acc => pure acc
  | z :: zs, acc => do
    ✓
    rehangM p s t X zs (if vget p z = t ∧ z ∈ X then vset acc z s else acc)

@[simp]
theorem rehangM_time (p : Vector (Fin n) n) (s t : Fin n) (X : Finset (Fin n)) :
    ∀ (zs : List (Fin n)) (acc : Vector (Fin n) n), (rehangM p s t X zs acc).time = zs.length
  | [], _ => rfl
  | z :: zs, acc => by
    simp only [rehangM, TimeM.time_bind, TimeM.time_tick, rehangM_time p s t X zs,
      List.length_cons]
    omega

theorem vget_rehangM (p : Vector (Fin n) n) (s t : Fin n) (X : Finset (Fin n)) :
    ∀ (zs : List (Fin n)) (acc : Vector (Fin n) n) (z : Fin n),
      vget (rehangM p s t X zs acc).ret z =
        if z ∈ zs ∧ vget p z = t ∧ z ∈ X then s else vget acc z
  | [], acc, z => by simp [rehangM]
  | x :: zs, acc, z => by
    simp only [rehangM, TimeM.ret_bind, vget_rehangM p s t X zs, List.mem_cons]
    by_cases hzx : z = x
    · subst hzx
      split_ifs <;> simp_all
    · split_ifs <;> simp_all [vget_vset_ne _ _ (Ne.symm hzx)]

/-- The minimum cut returned by the Edmonds–Karp solver on the network with capacities `W`,
source `s` and sink `t`. -/
@[expose] def ekCut (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (s t : Fin n) :
    Finset (Fin n) :=
  (edmondsKarpM (Network.mk W s t) adj).ret.cut

/-- The maximum flow value returned by the Edmonds–Karp solver on the network with capacities `W`,
source `s` and sink `t`. -/
@[expose] def ekValue (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (s t : Fin n) : ℕ :=
  (edmondsKarpM (Network.mk W s t) adj).ret.flow.value.toNat

/-- The Edmonds–Karp cut is a minimum `s`–`t` cut of the cut function of `W`, for adjacency lists
covering the edges of `W`. -/
theorem isMinCutBetween_ekCut {W : Fin n → Fin n → ℕ} {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u) {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (ekCut W adj s t) := by
  obtain ⟨-, hmin, -⟩ := edmondsKarpM_correct (N := Network.mk W s t) (adj := adj) hadj hst
  exact hmin.isMinCutBetween

/-- The Edmonds–Karp maximum flow value equals the weight of `ekCut W adj s t`, for adjacency lists
covering the edges of `W`. -/
theorem ekValue_eq_cutWeight {W : Fin n → Fin n → ℕ} {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u) {s t : Fin n} (hst : s ≠ t) :
    ekValue W adj s t = cutWeight W (ekCut W adj s t) := by
  obtain ⟨-, -, hval, -⟩ := edmondsKarpM_correct (N := Network.mk W s t) (adj := adj) hadj hst
  unfold ekValue ekCut
  rw [hval]
  rfl

/-- One step of Gusfield's algorithm on the parent array `p` and weight array `fl` for vertex `s`:
one Edmonds–Karp computation between `s` and its parent `t`, a scan re-hanging the vertices on the
`s`-side below `s`, the swap of `s` and `t` when the parent of `t` is on the `s`-side, and the
weight update from the maximum flow value (`fl[s] := val`, or on a swap `fl[s] := fl[t]` and
`fl[t] := val`). -/
@[expose] def gusfieldStepM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) : TimeM ℕ (Output n) := do
  ✓
  let t := vget p s
  let out ← edmondsKarpM (Network.mk W s t) adj
  let q ← rehangM p s t out.cut (List.finRange n) p
  ✓
  let val := out.flow.value.toNat
  ✓
  if vget p t ∈ out.cut then
    let flt := vget fl t
    pure { parent := vset (vset q t s) s (vget p t), weight := vset (vset fl t val) s flt }
  else
    pure { parent := vset (vset q t (vget p t)) s t, weight := vset fl s val }

theorem gusfieldStepM_time (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) :
    (gusfieldStepM W adj p fl s).time =
      (edmondsKarpM (Network.mk W s (vget p s)) adj).time + n + 3 := by
  simp only [gusfieldStepM, TimeM.time_bind, TimeM.time_tick, rehangM_time, List.length_finRange]
  split_ifs <;> simp only [TimeM.time_pure] <;> omega

theorem vget_gusfieldStepM_parent (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) (z : Fin n) :
    vget (gusfieldStepM W adj p fl s).ret.parent z =
      gusfieldStep (vget p) s (ekCut W adj s (vget p s)) z := by
  unfold ekCut
  simp only [gusfieldStepM, TimeM.ret_bind, gusfieldStep]
  generalize (edmondsKarpM (Network.mk W s (vget p s)) adj).ret.cut = X
  have hq : ∀ z, vget (rehangM p s (vget p s) X (List.finRange n) p).ret z =
      if vget p z = vget p s ∧ z ∈ X then s else vget p z := fun z => by
    simp only [vget_rehangM, List.mem_finRange, true_and]
  generalize (rehangM p s (vget p s) X (List.finRange n) p).ret = q at hq ⊢
  by_cases hzs : z = s
  · subst hzs
    by_cases hX : vget p (vget p z) ∈ X <;> simp only [hX, ↓reduceIte, TimeM.ret_pure,
      vget_vset_self]
  by_cases hzt : z = vget p s
  · subst hzt
    by_cases hX : vget p (vget p s) ∈ X <;>
      simp only [hX, hzs, ↓reduceIte, TimeM.ret_pure, vget_vset_ne _ _ (Ne.symm hzs),
        vget_vset_self]
  by_cases hX : vget p (vget p s) ∈ X <;>
    simp only [hX, hzs, hzt, ↓reduceIte, TimeM.ret_pure, vget_vset_ne _ _ (Ne.symm hzs),
      vget_vset_ne _ _ (Ne.symm hzt), hq]

/-- The weight array computed by `gusfieldStepM` agrees pointwise with `gusfieldStepWeight`. -/
theorem vget_gusfieldStepM_weight (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) (z : Fin n) :
    vget (gusfieldStepM W adj p fl s).ret.weight z =
      gusfieldStepWeight (vget p) (vget fl) s (ekCut W adj s (vget p s))
        (ekValue W adj s (vget p s)) z := by
  unfold ekCut ekValue
  simp only [gusfieldStepM, TimeM.ret_bind, gusfieldStepWeight]
  generalize (edmondsKarpM (Network.mk W s (vget p s)) adj).ret = out
  by_cases hX : vget p (vget p s) ∈ out.cut
  · simp only [hX, ↓reduceIte, TimeM.ret_pure]
    by_cases hzs : z = s
    · subst hzs
      simp only [vget_vset_self, ↓reduceIte]
    · simp only [hzs, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzs)]
      by_cases hzt : z = vget p s
      · subst hzt
        simp only [vget_vset_self, ↓reduceIte]
      · simp only [hzt, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzt)]
  · simp only [hX, ↓reduceIte, TimeM.ret_pure]
    by_cases hzs : z = s
    · subst hzs
      simp only [vget_vset_self, ↓reduceIte]
    · simp only [hzs, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzs)]

/-- Gusfield's loop over the vertices `l`, skipping the root `r` and tracking both parent and
edge-weight arrays. -/
@[expose] def gomoryHuLoopM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    List (Fin n) → Vector (Fin n) n → Vector ℕ n → TimeM ℕ (Output n)
  | [], p, fl => pure { parent := p, weight := fl }
  | s :: l, p, fl => do
    ✓
    if s = r then gomoryHuLoopM W adj r l p fl
    else
      let step ← gusfieldStepM W adj p fl s
      gomoryHuLoopM W adj r l step.parent step.weight

theorem vget_gomoryHuLoopM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    ∀ (l : List (Fin n)) (p : Vector (Fin n) n) (fl : Vector ℕ n),
      vget (gomoryHuLoopM W adj r l p fl).ret.parent =
          (gusfieldWeightLoop (ekCut W adj) (ekValue W adj) r l (vget p) (vget fl)).1 ∧
        vget (gomoryHuLoopM W adj r l p fl).ret.weight =
          (gusfieldWeightLoop (ekCut W adj) (ekValue W adj) r l (vget p) (vget fl)).2
  | [], p, fl => ⟨rfl, rfl⟩
  | s :: l, p, fl => by
    by_cases hsr : s = r
    · simp only [gomoryHuLoopM, TimeM.ret_bind, hsr, ↓reduceIte, gusfieldWeightLoop]
      exact vget_gomoryHuLoopM W adj r l p fl
    · simp only [gomoryHuLoopM, TimeM.ret_bind, hsr, ↓reduceIte, gusfieldWeightLoop]
      obtain ⟨hpar, hwt⟩ := vget_gomoryHuLoopM W adj r l (gusfieldStepM W adj p fl s).ret.parent
        (gusfieldStepM W adj p fl s).ret.weight
      have hp : vget (gusfieldStepM W adj p fl s).ret.parent =
          gusfieldStep (vget p) s (ekCut W adj s (vget p s)) :=
        funext (vget_gusfieldStepM_parent W adj p fl s)
      have hw : vget (gusfieldStepM W adj p fl s).ret.weight =
          gusfieldStepWeight (vget p) (vget fl) s (ekCut W adj s (vget p s))
            (ekValue W adj s (vget p s)) :=
        funext (vget_gusfieldStepM_weight W adj p fl s)
      rw [hp, hw] at hpar hwt
      exact ⟨hpar, hwt⟩

/-- **Gusfield's Gomory–Hu tree algorithm** ([Gusfield1990]) over `Fin n` in `TimeM ℕ`: start
from the star centred at the root `r` with `0` initial weights, and process the other vertices in
order with one Edmonds–Karp computation each. Returns both the parent array `parent` and the tree
edge weights `weight`. -/
@[expose] def gomoryHuM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    TimeM ℕ (Output n) := do
  let p ← replicateM n r
  let fl ← replicateM n 0
  gomoryHuLoopM W adj r (List.finRange n) p fl

private theorem vget_gomoryHuM_spec (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (r : Fin n) :
    vget (gomoryHuM W adj r).ret.parent =
        (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).1 ∧
      vget (gomoryHuM W adj r).ret.weight =
        (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).2 := by
  simp only [gomoryHuM, TimeM.ret_bind, replicateM_ret, gusfieldWithWeights]
  obtain ⟨hpar, hwt⟩ :=
    vget_gomoryHuLoopM W adj r (List.finRange n) (Vector.replicate n r) (Vector.replicate n 0)
  have hp : vget (Vector.replicate n r) = fun _ => r := funext (vget_replicate r)
  have hw : vget (Vector.replicate n 0) = fun _ => 0 := funext (vget_replicate 0)
  rw [hp, hw] at hpar hwt
  exact ⟨hpar, hwt⟩

/-- The parent array returned by `gomoryHuM` agrees pointwise with the first component of
`gusfieldWithWeights`. -/
theorem vget_gomoryHuM_parent (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHuM W adj r).ret.parent =
      (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).1 :=
  (vget_gomoryHuM_spec W adj r).1

/-- The parent array returned by `gomoryHuM` agrees pointwise with `gusfieldParent`. -/
theorem vget_gomoryHuM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHuM W adj r).ret.parent = gusfieldParent (ekCut W adj) r (List.finRange n) := by
  rw [vget_gomoryHuM_parent, fst_gusfieldWithWeights]

/-- The weight array returned by `gomoryHuM` agrees pointwise with the second component of
`gusfieldWithWeights`. -/
theorem vget_gomoryHuM_weight (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHuM W adj r).ret.weight =
      (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).2 :=
  (vget_gomoryHuM_spec W adj r).2

private theorem gomoryHuM_pure_spec {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) :
    let res := gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)
    IsGomoryHuTree (cutWeight W) (parentGraph res.1) ∧ res.1 r = r ∧ res.2 r = 0 ∧
      ∀ u, u ≠ r →
        IsMinCutBetween (cutWeight W) u (res.1 u)
            (SimpleGraph.edgeSide (parentGraph res.1) u (res.1 u)) ∧
          res.2 u = cutWeight W (SimpleGraph.edgeSide (parentGraph res.1) u (res.1 u)) :=
  gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W)
    (fun _ _ hst => isMinCutBetween_ekCut hadj hst)
    (fun _ _ hst => ekValue_eq_cutWeight hadj hst) r 0 (List.nodup_finRange n)
    fun x _ => List.mem_finRange x

/-- **Correctness of Gusfield's algorithm with Edmonds–Karp** ([Gusfield1990]): for a weighted
multigraph `W` on `Fin n` and adjacency lists `adj` covering its edges, the parent array computed
by `gomoryHuM` is a Gomory–Hu tree of `W`: for every tree edge `uv`, the side of `T - uv`
containing `u` is a minimum `u`–`v` cut of `W`. -/
theorem isGomoryHuTree_gomoryHuM {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (parentGraph (vget (gomoryHuM W adj r).ret.parent)) := by
  rw [vget_gomoryHuM_parent]
  exact (gomoryHuM_pure_spec hW hadj r).1

/-- The recorded root weight is `0`. -/
theorem vget_gomoryHuM_weight_root {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) :
    vget (gomoryHuM W adj r).ret.weight r = 0 := by
  rw [vget_gomoryHuM_weight]
  exact (gomoryHuM_pure_spec hW hadj r).2.2.1

/-- **Correctness of the edge weights returned by `gomoryHuM`** ([Gusfield1990]): for every vertex
`u : Fin n`, the weight `vget (gomoryHuM W adj r).ret.weight u` equals the minimum cut weight
`minCutBetween W u (vget (gomoryHuM W adj r).ret.parent u)` between `u` and its parent (`0` at the
root `r`). -/
theorem vget_gomoryHuM_weight_eq_minCutBetween {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r u : Fin n) :
    vget (gomoryHuM W adj r).ret.weight u =
      minCutBetween W u (vget (gomoryHuM W adj r).ret.parent u) := by
  have hspec := gomoryHuM_pure_spec hW hadj r
  rw [vget_gomoryHuM_weight, vget_gomoryHuM_parent]
  by_cases hur : u = r
  · subst hur
    rw [hspec.2.1, hspec.2.2.1, minCutBetween_self]
  · obtain ⟨hcut, hw⟩ := hspec.2.2.2 u hur
    exact hw.trans ((isMinCutBetween_cutWeight_iff W).mp hcut).2.2

theorem gomoryHuLoopM_time_le (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n)
    {B : ℕ} (hB : ∀ s t, (edmondsKarpM (Network.mk W s t) adj).time ≤ B) :
    ∀ (l : List (Fin n)) (p : Vector (Fin n) n) (fl : Vector ℕ n),
      (gomoryHuLoopM W adj r l p fl).time ≤ l.length + (l.filter (· ≠ r)).length * (B + n + 3)
  | [], _, _ => by simp [gomoryHuLoopM]
  | s :: l, p, fl => by
    have ih := gomoryHuLoopM_time_le W adj r hB l
    by_cases hsr : s = r
    · rw [List.filter_cons_of_neg (by simp [hsr])]
      simp only [gomoryHuLoopM, TimeM.time_bind, TimeM.time_tick, hsr, ↓reduceIte,
        List.length_cons]
      have := ih p fl
      omega
    · rw [List.filter_cons_of_pos (by simp [hsr])]
      simp only [gomoryHuLoopM, TimeM.time_bind, TimeM.time_tick, hsr, ↓reduceIte,
        List.length_cons, gusfieldStepM_time]
      have h1 := ih (gusfieldStepM W adj p fl s).ret.parent (gusfieldStepM W adj p fl s).ret.weight
      have h2 := hB s (vget p s)
      rw [Nat.add_mul, Nat.one_mul]
      omega

private theorem length_filter_finRange_ne (r : Fin n) :
    ((List.finRange n).filter (· ≠ r)).length = n - 1 := by
  have h : (List.finRange n).filter (· ≠ r) = (List.finRange n).erase r := by
    rw [(List.nodup_finRange n).erase_eq_filter]
    refine List.filter_congr fun x _ => ?_
    by_cases hx : x = r <;> simp [hx]
  rw [h, List.length_erase_of_mem (List.mem_finRange r), List.length_finRange]

/-- **Running time of Gusfield's algorithm.** If every Edmonds–Karp computation on the
capacities `W` takes at most `B` charged steps, `gomoryHuM W adj r` takes at most
`3 n + (n - 1) (B + n + 3)`: `2 n` to allocate the parent and weight arrays, `1` per vertex for
the loop, and for each of the `n - 1` non-root vertices one maximum flow computation, the `n`-step
re-hanging scan and `3` steps of pointer and weight updates. -/
theorem gomoryHuM_time_le_of_forall (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (r : Fin n) {B : ℕ} (hB : ∀ s t, (edmondsKarpM (Network.mk W s t) adj).time ≤ B) :
    (gomoryHuM W adj r).time ≤ 3 * n + (n - 1) * (B + n + 3) := by
  have h := gomoryHuLoopM_time_le W adj r hB (List.finRange n) (replicateM n r).ret
    (replicateM n 0).ret
  rw [List.length_finRange, length_filter_finRange_ne] at h
  simp only [gomoryHuM, TimeM.time_bind, replicateM_time]
  omega

/-- **Running time with sparse adjacency lists.** With adjacency lists `adj` covering the edges
of `W`, Gusfield's algorithm makes `n - 1` Edmonds–Karp computations, each within
`(adjSteps adj * (n / 2) + 2) * (adjSteps adj + 5 n)` steps (`O(n m²)` for `m` edges), plus
`O(n)` bookkeeping per computation. -/
theorem gomoryHuM_time_le {W : Fin n → Fin n → ℕ} {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u) (r : Fin n) :
    (gomoryHuM W adj r).time ≤
      3 * n + (n - 1) * ((adjSteps adj * (n / 2) + 2) * (adjSteps adj + 5 * n) + n + 3) := by
  refine gomoryHuM_time_le_of_forall W adj r fun s t => ?_
  have hv : AdjValid (Network.mk W s t) adj := hadj
  refine (edmondsKarpM_time_le hv).trans (Nat.mul_le_mul_right _ ?_)
  have := card_symArcs_le_adjSteps hv
  have := Nat.mul_le_mul_right (n / 2) this
  omega

/-- **Running time with dense adjacency lists**: `O(n ^ 6)`. -/
theorem gomoryHuM_time_le_dense {W : Fin n → Fin n → ℕ} (r : Fin n) :
    (gomoryHuM W (defaultAdj n) r).time ≤
      3 * n + (n - 1) * ((n * n * (n / 2) + 2) * (n * n + 5 * n) + n + 3) := by
  have h := gomoryHuM_time_le (W := W) (adj := defaultAdj n)
    (fun u v _ _ => List.mem_finRange v) r
  rwa [adjSteps_defaultAdj] at h

end Cslib.Algorithms.Lean.GomoryHu
