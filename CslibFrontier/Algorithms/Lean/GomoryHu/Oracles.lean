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
# Gomory-Hu Oracles

This module wraps the Push-Relabel and Dinitz maximum flow algorithms as Gomory-Hu
cut oracles.
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut

variable {n : ℕ}

@[expose] def pushRelabelCut (W : Fin n → Fin n → ℕ) (s t : Fin n) : Finset (Fin n) :=
  (pushRelabel (Network.mk W s t)).cut

@[expose] def pushRelabelValue (W : Fin n → Fin n → ℕ) (s t : Fin n) : ℕ :=
  (pushRelabel (Network.mk W s t)).flow.value.toNat

theorem isMinCutBetween_pushRelabelCut {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (pushRelabelCut W s t) := by
  have h := pushRelabel_correct (N := Network.mk W s t) hst
  exact h.2.1.isMinCutBetween

theorem pushRelabelValue_eq_cutWeight {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t) :
    pushRelabelValue W s t = cutWeight W (pushRelabelCut W s t) := by
  have h := pushRelabel_correct (N := Network.mk W s t) hst
  unfold pushRelabelValue pushRelabelCut
  rw [h.2.2.1]
  rfl

@[expose] def dinitzCut (W : Fin n → Fin n → ℕ) (s t : Fin n) : Finset (Fin n) :=
  (dinitzDense (Network.mk W s t)).cut

@[expose] def dinitzValue (W : Fin n → Fin n → ℕ) (s t : Fin n) : ℕ :=
  (dinitzDense (Network.mk W s t)).flow.value.toNat

theorem isMinCutBetween_dinitzCut {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (dinitzCut W s t) := by
  have h := dinitzDense_correct (N := Network.mk W s t) hst
  exact h.2.1.isMinCutBetween

theorem dinitzValue_eq_cutWeight {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t) :
    dinitzValue W s t = cutWeight W (dinitzCut W s t) := by
  have h := dinitzDense_correct (N := Network.mk W s t) hst
  unfold dinitzValue dinitzCut
  rw [h.2.2.1]
  rfl

@[expose] def pushRelabelGomoryHu (W : Fin n → Fin n → ℕ) (r : Fin n) : Output n :=
  let res := gusfieldWithWeights (pushRelabelCut W) (pushRelabelValue W) r 0 (List.finRange n)
  { parent := Vector.ofFn res.1, weight := Vector.ofFn res.2 }

theorem isGomoryHuTree_pushRelabelGomoryHu {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (SimpleGraph.parentGraph (vget (pushRelabelGomoryHu W r).parent)) := by
  unfold pushRelabelGomoryHu
  have hp : vget (Vector.ofFn (gusfieldWithWeights (pushRelabelCut W) (pushRelabelValue W) r 0 (List.finRange n)).1) =
      (gusfieldWithWeights (pushRelabelCut W) (pushRelabelValue W) r 0 (List.finRange n)).1 := by
    funext v
    exact Vector.getElem_ofFn _
  rw [hp]
  have h := gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W)
    (fun _ _ hst => isMinCutBetween_pushRelabelCut hst)
    (fun _ _ hst => pushRelabelValue_eq_cutWeight hst) r 0 (List.nodup_finRange n)
    fun x _ => List.mem_finRange x
  exact h.1

@[expose] def dinitzGomoryHu (W : Fin n → Fin n → ℕ) (r : Fin n) : Output n :=
  let res := gusfieldWithWeights (dinitzCut W) (dinitzValue W) r 0 (List.finRange n)
  { parent := Vector.ofFn res.1, weight := Vector.ofFn res.2 }

theorem isGomoryHuTree_dinitzGomoryHu {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (SimpleGraph.parentGraph (vget (dinitzGomoryHu W r).parent)) := by
  unfold dinitzGomoryHu
  have hp : vget (Vector.ofFn (gusfieldWithWeights (dinitzCut W) (dinitzValue W) r 0 (List.finRange n)).1) =
      (gusfieldWithWeights (dinitzCut W) (dinitzValue W) r 0 (List.finRange n)).1 := by
    funext v
    exact Vector.getElem_ofFn _
  rw [hp]
  have h := gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W)
    (fun _ _ hst => isMinCutBetween_dinitzCut hst)
    (fun _ _ hst => dinitzValue_eq_cutWeight hst) r 0 (List.nodup_finRange n)
    fun x _ => List.mem_finRange x
  exact h.1

end Cslib.Algorithms.Lean.GomoryHu
