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
all on the original graph, plus `O(n)` bookkeeping per vertex on a parent array. Correctness is
transferred from the abstract algorithm `Cslib.Algorithms.Lean.GomoryHu.gusfieldParent` of
`CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield`, with the Edmonds–Karp minimum cut as the oracle.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM`: Gusfield's algorithm over `Fin n` in `TimeM ℕ`,
  returning the parent array of the tree.
* `Cslib.Algorithms.Lean.GomoryHu.ekCut`: the minimum cut returned by `edmondsKarpM`.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gomoryHuM`: the parent graph of the output is a
  Gomory–Hu tree of `cutWeight W` (cut-equivalent: the side of each tree edge `uv` containing `u`
  is a minimum `u`–`v` cut of `W`).
* `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHuM`: the output is the abstract algorithm
  `gusfieldParent` run with the Edmonds–Karp cut oracle `ekCut`.
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM_time_le_of_forall`: the charged time is at most `2 n`
  plus `n - 1` times (any bound on one Edmonds–Karp computation, plus `n + 2`).
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM_time_le`: the same with the Edmonds–Karp bound
  `edmondsKarpM_time_le`, `O(n m²)` per computation for `m` edges, so `O(n² m²)` in total.
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM_time_le_dense`: `O(n ^ 6)` with dense adjacency lists.

## Cost model

The unit-cost model of `Cslib.Algorithms.Lean.MaxFlow.edmondsKarpM`, extended with `Finset`
membership on the returned cut as a free primitive: `Vector` reads and writes, those membership
tests, equality tests on `Fin n`, and evaluating `W u v` count as `O(1)` primitives inside charged
steps. (Even an `O(n)` membership test would add only `O(n³)` in total.) Charged: `n` ticks to
allocate the parent array, `1` tick per vertex for the loop test `s = r`, and for each non-root
vertex `s`: `1` tick to read its parent, the full Edmonds–Karp cost, `n` ticks for the re-hanging
scan over all vertices, and `1` tick for the final swap test and its two writes.

## Limitations

The output records only the tree. The edge weights `λ(u, p u)` are not returned: Gusfield tracks
them alongside the parent array from the maximum flow values, which is not formalized here. Each
is the cut weight of the side of its tree edge (`IsGomoryHuTree.isLeast_minCutBetween`). The
weights of `W` are natural numbers.

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

/-- The Edmonds–Karp cut is a minimum `s`–`t` cut of the cut function of `W`, for adjacency lists
covering the edges of `W`. -/
theorem isMinCutBetween_ekCut {W : Fin n → Fin n → ℕ} {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u) {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (ekCut W adj s t) := by
  obtain ⟨-, hmin, -⟩ := edmondsKarpM_correct (N := Network.mk W s t) (adj := adj) hadj hst
  exact hmin.isMinCutBetween

/-- One step of Gusfield's algorithm on the parent array `p` for the vertex `s`: one
Edmonds–Karp computation between `s` and its parent `t`, a scan re-hanging the vertices on the
`s`-side below `s`, and the swap of `s` and `t` when the parent of `t` is on the `s`-side. -/
@[expose] def gusfieldStepM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (s : Fin n) : TimeM ℕ (Vector (Fin n) n) := do
  ✓
  let t := vget p s
  let out ← edmondsKarpM (Network.mk W s t) adj
  let q ← rehangM p s t out.cut (List.finRange n) p
  ✓
  if vget p t ∈ out.cut then pure (vset (vset q t s) s (vget p t))
  else pure (vset (vset q t (vget p t)) s t)

theorem gusfieldStepM_time (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (s : Fin n) :
    (gusfieldStepM W adj p s).time =
      (edmondsKarpM (Network.mk W s (vget p s)) adj).time + n + 2 := by
  simp only [gusfieldStepM, TimeM.time_bind, TimeM.time_tick, rehangM_time, List.length_finRange]
  split_ifs <;> simp only [TimeM.time_pure] <;> omega

theorem vget_gusfieldStepM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (s : Fin n) (z : Fin n) :
    vget (gusfieldStepM W adj p s).ret z =
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

/-- Gusfield's loop over the vertices `l`, skipping the root `r`. -/
@[expose] def gomoryHuLoopM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    List (Fin n) → Vector (Fin n) n → TimeM ℕ (Vector (Fin n) n)
  | [], p => pure p
  | s :: l, p => do
    ✓
    if s = r then gomoryHuLoopM W adj r l p
    else
      let p' ← gusfieldStepM W adj p s
      gomoryHuLoopM W adj r l p'

theorem vget_gomoryHuLoopM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    ∀ (l : List (Fin n)) (p : Vector (Fin n) n),
      vget (gomoryHuLoopM W adj r l p).ret = gusfieldLoop (ekCut W adj) r l (vget p)
  | [], p => rfl
  | s :: l, p => by
    by_cases hsr : s = r
    · simp only [gomoryHuLoopM, TimeM.ret_bind, hsr, ↓reduceIte, gusfieldLoop]
      exact vget_gomoryHuLoopM W adj r l p
    · simp only [gomoryHuLoopM, TimeM.ret_bind, hsr, ↓reduceIte, gusfieldLoop]
      rw [vget_gomoryHuLoopM W adj r l]
      congr 1
      funext z
      exact vget_gusfieldStepM W adj p s z

/-- **Gusfield's Gomory–Hu tree algorithm** ([Gusfield1990]) over `Fin n` in `TimeM ℕ`: start
from the star centred at the root `r`, and process the other vertices in order with one
Edmonds–Karp computation each. Returns the parent array of the tree. -/
@[expose] def gomoryHuM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    TimeM ℕ (Vector (Fin n) n) := do
  let p ← replicateM n r
  gomoryHuLoopM W adj r (List.finRange n) p

theorem vget_gomoryHuM (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHuM W adj r).ret = gusfieldParent (ekCut W adj) r (List.finRange n) := by
  simp only [gomoryHuM, TimeM.ret_bind, vget_gomoryHuLoopM, replicateM_ret, gusfieldParent]
  congr 1
  funext z
  exact vget_replicate r z

/-- **Correctness of Gusfield's algorithm with Edmonds–Karp** ([Gusfield1990]): for a weighted
multigraph `W` on `Fin n` and adjacency lists `adj` covering its edges, the parent array computed
by `gomoryHuM` is a Gomory–Hu tree of `W`: for every tree edge `uv`, the side of `T - uv`
containing `u` is a minimum `u`–`v` cut of `W`. -/
theorem isGomoryHuTree_gomoryHuM {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) : IsGomoryHuTree (cutWeight W) (parentGraph (vget (gomoryHuM W adj r).ret)) := by
  rw [vget_gomoryHuM]
  exact isGomoryHuTree_gusfieldParent (cutWeight_compl' hW) (isSubmodular_cutWeight W)
    (fun _ _ hst => isMinCutBetween_ekCut hadj hst) r (List.nodup_finRange n)
    fun x _ => List.mem_finRange x

theorem gomoryHuLoopM_time_le (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n)
    {B : ℕ} (hB : ∀ s t, (edmondsKarpM (Network.mk W s t) adj).time ≤ B) :
    ∀ (l : List (Fin n)) (p : Vector (Fin n) n),
      (gomoryHuLoopM W adj r l p).time ≤ l.length + (l.filter (· ≠ r)).length * (B + n + 2)
  | [], _ => by simp [gomoryHuLoopM]
  | s :: l, p => by
    have ih := gomoryHuLoopM_time_le W adj r hB l
    by_cases hsr : s = r
    · rw [List.filter_cons_of_neg (by simp [hsr])]
      simp only [gomoryHuLoopM, TimeM.time_bind, TimeM.time_tick, hsr, ↓reduceIte,
        List.length_cons]
      have := ih p
      omega
    · rw [List.filter_cons_of_pos (by simp [hsr])]
      simp only [gomoryHuLoopM, TimeM.time_bind, TimeM.time_tick, hsr, ↓reduceIte,
        List.length_cons, gusfieldStepM_time]
      have h1 := ih (gusfieldStepM W adj p s).ret
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
`2 n + (n - 1) (B + n + 2)`: `n` to allocate the parent array, `1` per vertex for the loop, and
for each of the `n - 1` non-root vertices one maximum flow computation, the `n`-step re-hanging
scan and `2` steps of pointer updates. -/
theorem gomoryHuM_time_le_of_forall (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (r : Fin n) {B : ℕ} (hB : ∀ s t, (edmondsKarpM (Network.mk W s t) adj).time ≤ B) :
    (gomoryHuM W adj r).time ≤ 2 * n + (n - 1) * (B + n + 2) := by
  have h := gomoryHuLoopM_time_le W adj r hB (List.finRange n) (replicateM n r).ret
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
      2 * n + (n - 1) * ((adjSteps adj * (n / 2) + 2) * (adjSteps adj + 5 * n) + n + 2) := by
  refine gomoryHuM_time_le_of_forall W adj r fun s t => ?_
  have hv : AdjValid (Network.mk W s t) adj := hadj
  refine (edmondsKarpM_time_le hv).trans (Nat.mul_le_mul_right _ ?_)
  have := card_symArcs_le_adjSteps hv
  have := Nat.mul_le_mul_right (n / 2) this
  omega

/-- **Running time with dense adjacency lists**: `O(n ^ 6)`. -/
theorem gomoryHuM_time_le_dense {W : Fin n → Fin n → ℕ} (r : Fin n) :
    (gomoryHuM W (defaultAdj n) r).time ≤
      2 * n + (n - 1) * ((n * n * (n / 2) + 2) * (n * n + 5 * n) + n + 2) := by
  have h := gomoryHuM_time_le (W := W) (adj := defaultAdj n)
    (fun u v _ _ => List.mem_finRange v) r
  rwa [adjSteps_defaultAdj] at h

end Cslib.Algorithms.Lean.GomoryHu
