/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Construction
public import CslibFrontier.Algorithms.Lean.MaxFlow.PushRelabel
public import CslibFrontier.Algorithms.Lean.MaxFlow.Dinitz
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.MinCutBetween

/-!
# Gomory–Hu trees from push–relabel and Dinitz cut oracles

Gusfield's construction (`gusfieldWithWeights`) takes any oracle returning a minimum `s`–`t` cut
and its value. This module packages the construction for an arbitrary correct oracle as an
`Output` (parent array and edge weights) and instantiates it with the generic push–relabel
algorithm and with Dinitz's algorithm on dense networks, complementing the Edmonds–Karp instance
`gomoryHuM` of `Construction.lean`.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.gusfieldOutput`: Gusfield's construction for a cut oracle `C`
  and value oracle `val`, as an `Output`.
* `Cslib.Algorithms.Lean.GomoryHu.pushRelabelGomoryHu`: Gusfield's construction with the
  push–relabel minimum cut oracle `pushRelabelCut`.
* `Cslib.Algorithms.Lean.GomoryHu.dinitzGomoryHu`: Gusfield's construction with Dinitz's minimum
  cut oracle `dinitzCut`.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gusfieldOutput` and
  `Cslib.Algorithms.Lean.GomoryHu.vget_gusfieldOutput_weight`: for a correct oracle, the parent
  array is a Gomory–Hu tree and the weight of each non-root `u` is `λ(u, parent u)`.
* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_pushRelabelGomoryHu`,
  `Cslib.Algorithms.Lean.GomoryHu.vget_pushRelabelGomoryHu_weight`,
  `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_dinitzGomoryHu` and
  `Cslib.Algorithms.Lean.GomoryHu.vget_dinitzGomoryHu_weight`: the two instances.

No running time is charged here; `gomoryHuM_time_le_of_forall` covers the charged Edmonds–Karp
version.

## References

* [Gusfield1990]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut
open SimpleGraph (parentGraph edgeSide)

variable {n : ℕ}

/-! ### Gusfield's construction for an arbitrary cut oracle -/

/-- Gusfield's construction rooted at `r` for the cut oracle `C` and value oracle `val`, returning
the parent array and the edge weights (`0` at the root). -/
@[expose] def gusfieldOutput (C : Fin n → Fin n → Finset (Fin n)) (val : Fin n → Fin n → ℕ)
    (r : Fin n) : Output n :=
  let res := gusfieldWithWeights C val r 0 (List.finRange n)
  { parent := Vector.ofFn res.1, weight := Vector.ofFn res.2 }

theorem vget_gusfieldOutput_parent (C : Fin n → Fin n → Finset (Fin n))
    (val : Fin n → Fin n → ℕ) (r : Fin n) :
    vget (gusfieldOutput C val r).parent = (gusfieldWithWeights C val r 0 (List.finRange n)).1 :=
  funext fun _ => Vector.getElem_ofFn _

theorem vget_gusfieldOutput_weight_eq (C : Fin n → Fin n → Finset (Fin n))
    (val : Fin n → Fin n → ℕ) (r : Fin n) :
    vget (gusfieldOutput C val r).weight = (gusfieldWithWeights C val r 0 (List.finRange n)).2 :=
  funext fun _ => Vector.getElem_ofFn _

variable {W : Fin n → Fin n → ℕ} {C : Fin n → Fin n → Finset (Fin n)} {val : Fin n → Fin n → ℕ}

/-- **Correctness of Gusfield's construction** ([Gusfield1990]) for any oracle `C` returning
minimum cuts: the parent array of `gusfieldOutput` is a Gomory–Hu tree. -/
theorem isGomoryHuTree_gusfieldOutput (hW : IsMultigraph W)
    (hC : ∀ s t, s ≠ t → IsMinCutBetween (cutWeight W) s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = cutWeight W (C s t)) (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (parentGraph (vget (gusfieldOutput C val r).parent)) := by
  rw [vget_gusfieldOutput_parent]
  exact (gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W) hC hval r 0
    (List.nodup_finRange n) fun x _ => List.mem_finRange x).1

/-- For any correct oracle, the weight that `gusfieldOutput` records at a non-root vertex `u` is
the minimum cut weight `λ(u, parent u)` ([Gusfield1990]). -/
theorem vget_gusfieldOutput_weight (hW : IsMultigraph W)
    (hC : ∀ s t, s ≠ t → IsMinCutBetween (cutWeight W) s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = cutWeight W (C s t)) (r : Fin n) {u : Fin n} (hu : u ≠ r) :
    vget (gusfieldOutput C val r).weight u =
      minCutBetween W u (vget (gusfieldOutput C val r).parent u) := by
  rw [vget_gusfieldOutput_weight_eq, vget_gusfieldOutput_parent]
  obtain ⟨hcut, hw⟩ := (gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W)
    hC hval r 0 (List.nodup_finRange n) fun x _ => List.mem_finRange x).2.2.2 u hu
  exact hw.trans ((isMinCutBetween_cutWeight_iff W).mp hcut).2.2

/-! ### The push–relabel oracle -/

/-- The minimum `s`–`t` cut returned by the generic push–relabel algorithm. -/
@[expose] def pushRelabelCut (W : Fin n → Fin n → ℕ) (s t : Fin n) : Finset (Fin n) :=
  (pushRelabel (Network.mk W s t)).cut

/-- The maximum `s`–`t` flow value returned by the generic push–relabel algorithm. -/
@[expose] def pushRelabelValue (W : Fin n → Fin n → ℕ) (s t : Fin n) : ℕ :=
  (pushRelabel (Network.mk W s t)).flow.value.toNat

theorem isMinCutBetween_pushRelabelCut {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (pushRelabelCut W s t) :=
  (pushRelabel_correct (N := Network.mk W s t) hst).2.1.isMinCutBetween

theorem pushRelabelValue_eq_cutWeight {s t : Fin n} (hst : s ≠ t) :
    pushRelabelValue W s t = cutWeight W (pushRelabelCut W s t) := by
  unfold pushRelabelValue pushRelabelCut
  rw [(pushRelabel_correct (N := Network.mk W s t) hst).2.2.1]
  rfl

/-- Gusfield's construction with the push–relabel minimum cut oracle. -/
@[expose] def pushRelabelGomoryHu (W : Fin n → Fin n → ℕ) (r : Fin n) : Output n :=
  gusfieldOutput (pushRelabelCut W) (pushRelabelValue W) r

theorem isGomoryHuTree_pushRelabelGomoryHu (hW : IsMultigraph W) (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (parentGraph (vget (pushRelabelGomoryHu W r).parent)) :=
  isGomoryHuTree_gusfieldOutput hW (fun _ _ => isMinCutBetween_pushRelabelCut)
    (fun _ _ => pushRelabelValue_eq_cutWeight) r

theorem vget_pushRelabelGomoryHu_weight (hW : IsMultigraph W) (r : Fin n) {u : Fin n}
    (hu : u ≠ r) :
    vget (pushRelabelGomoryHu W r).weight u =
      minCutBetween W u (vget (pushRelabelGomoryHu W r).parent u) :=
  vget_gusfieldOutput_weight hW (fun _ _ => isMinCutBetween_pushRelabelCut)
    (fun _ _ => pushRelabelValue_eq_cutWeight) r hu

/-! ### The Dinitz oracle -/

/-- The minimum `s`–`t` cut returned by Dinitz's algorithm on the dense network. -/
@[expose] def dinitzCut (W : Fin n → Fin n → ℕ) (s t : Fin n) : Finset (Fin n) :=
  (dinitzDense (Network.mk W s t)).cut

/-- The maximum `s`–`t` flow value returned by Dinitz's algorithm on the dense network. -/
@[expose] def dinitzValue (W : Fin n → Fin n → ℕ) (s t : Fin n) : ℕ :=
  (dinitzDense (Network.mk W s t)).flow.value.toNat

theorem isMinCutBetween_dinitzCut {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (dinitzCut W s t) :=
  (dinitzDense_correct (N := Network.mk W s t) hst).2.1.isMinCutBetween

theorem dinitzValue_eq_cutWeight {s t : Fin n} (hst : s ≠ t) :
    dinitzValue W s t = cutWeight W (dinitzCut W s t) := by
  unfold dinitzValue dinitzCut
  rw [(dinitzDense_correct (N := Network.mk W s t) hst).2.2.1]
  rfl

/-- Gusfield's construction with Dinitz's minimum cut oracle. -/
@[expose] def dinitzGomoryHu (W : Fin n → Fin n → ℕ) (r : Fin n) : Output n :=
  gusfieldOutput (dinitzCut W) (dinitzValue W) r

theorem isGomoryHuTree_dinitzGomoryHu (hW : IsMultigraph W) (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (parentGraph (vget (dinitzGomoryHu W r).parent)) :=
  isGomoryHuTree_gusfieldOutput hW (fun _ _ => isMinCutBetween_dinitzCut)
    (fun _ _ => dinitzValue_eq_cutWeight) r

theorem vget_dinitzGomoryHu_weight (hW : IsMultigraph W) (r : Fin n) {u : Fin n} (hu : u ≠ r) :
    vget (dinitzGomoryHu W r).weight u =
      minCutBetween W u (vget (dinitzGomoryHu W r).parent u) :=
  vget_gusfieldOutput_weight hW (fun _ _ => isMinCutBetween_dinitzCut)
    (fun _ _ => dinitzValue_eq_cutWeight) r hu

end Cslib.Algorithms.Lean.GomoryHu
