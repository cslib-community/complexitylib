/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Path Decomposition of Integral Flows

Decomposes a feasible integral `s`-`t` flow on a `Cslib.Algorithms.Lean.MaxFlow.Network` into
simple `s`-`t` paths along positive-flow arcs: a flow of value `k` contains `k`
simple `s`-`t` paths such that each arc `(u, v)` lies on at most `f u v` of them. The remaining
flow is a circulation and is not recorded; this is the path half of the classical flow
decomposition. Also provides cancellation of antiparallel flow, which keeps the value and leaves
positive flow on at most one arc of each antiparallel pair. These are the ingredients for deriving
Menger's theorem from the integral max-flow/min-cut theorem
(`CslibFrontier.Algorithms.Lean.MaxFlow.Menger`).

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.IsFlowPath`: a simple `s`-`t` path along
  positive-flow arcs.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.cancel`: cancellation of antiparallel flow.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.exists_isFlowPath`: a flow of positive value has a
  flow path.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.exists_flowPaths`: flow decomposition into paths.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.value_cancel`,
  `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.cancel_eq_zero_or`: cancellation keeps the value and
  removes antiparallel flow.
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

variable {V : Type*} [Fintype V] {N : Network V}

namespace Flow

/-- `p` is a simple `s`-`t` path of `N` along arcs carrying positive flow `f`. -/
@[expose] def IsFlowPath (f : N.Flow) (p : List V) : Prop :=
  p.Nodup ∧ p.head? = some N.s ∧ p.getLast? = some N.t ∧ ∀ e ∈ pathArcs p, 0 < f e.1 e.2

/-- Remove one unit of flow along a simple `s`-`t` path of positive-flow arcs. -/
private def subPath [DecidableEq V] (f : N.Flow) (p : List V) (hp : f.IsFlowPath p) : N.Flow where
  toFun u v := if (u, v) ∈ pathArcs p then f u v - 1 else f u v
  le_cap u v := by
    split_ifs
    · exact le_trans (Nat.sub_le _ _) (f.le_cap u v)
    · exact f.le_cap u v
  conserve v hvs hvt := by
    obtain ⟨hnd, hs, ht, hpos⟩ := hp
    have hsub : ∀ u w : V,
        ((if (u, w) ∈ pathArcs p then f u w - 1 else f u w : ℕ) : ℤ) =
          (f u w : ℤ) - (if (u, w) ∈ pathArcs p then 1 else 0) := by
      intro u w
      split_ifs with h
      · have := hpos (u, w) h
        simp only at this
        omega
      · simp
    have hsum : (∑ w : V, (((if (v, w) ∈ pathArcs p then f v w - 1 else f v w : ℕ) : ℤ) -
        ((if (w, v) ∈ pathArcs p then f w v - 1 else f w v : ℕ) : ℤ))) = 0 := by
      simp only [hsub]
      have hsplit : ∀ w : V,
          ((f v w : ℤ) - (if (v, w) ∈ pathArcs p then 1 else 0)) -
              ((f w v : ℤ) - (if (w, v) ∈ pathArcs p then 1 else 0)) =
            ((f v w : ℤ) - (f w v : ℤ)) -
              ((if (v, w) ∈ pathArcs p then (1 : ℤ) else 0) -
                (if (w, v) ∈ pathArcs p then (1 : ℤ) else 0)) := fun w => by omega
      rw [Finset.sum_congr rfl fun w _ => hsplit w, Finset.sum_sub_distrib,
        sum_pathArcs_sign hnd hs ht v, ← f.netOut_eq_sum_sub v, f.netOut_eq_zero hvs hvt]
      have hsv : N.s ≠ v := hvs.symm
      have htv : N.t ≠ v := hvt.symm
      simp [hsv, htv]
    rw [Finset.sum_sub_distrib] at hsum
    have heq : ((∑ u : V, (if (u, v) ∈ pathArcs p then f u v - 1 else f u v) : ℕ) : ℤ) =
        ((∑ w : V, (if (v, w) ∈ pathArcs p then f v w - 1 else f v w) : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_sum]
      omega
    exact Int.ofNat.inj heq

private theorem subPath_apply [DecidableEq V] (f : N.Flow) (p : List V) (hp : f.IsFlowPath p)
    (u v : V) :
    f.subPath p hp u v = if (u, v) ∈ pathArcs p then f u v - 1 else f u v := rfl

private theorem value_subPath [DecidableEq V] (f : N.Flow) (hst : N.s ≠ N.t) (p : List V)
    (hp : f.IsFlowPath p) : (f.subPath p hp).value = f.value - 1 := by
  obtain ⟨hnd, hs, ht, hpos⟩ := id hp
  have hts : N.t ≠ N.s := hst.symm
  rw [value, netOut_eq_sum_sub]
  have hsub : ∀ u w : V, ((f.subPath p hp u w : ℕ) : ℤ) =
      (f u w : ℤ) - (if (u, w) ∈ pathArcs p then 1 else 0) := by
    intro u w
    rw [subPath_apply]
    split_ifs with h
    · have := hpos (u, w) h
      simp only at this
      omega
    · simp
  simp only [hsub]
  have hsplit : ∀ w : V,
      ((f N.s w : ℤ) - (if (N.s, w) ∈ pathArcs p then 1 else 0)) -
          ((f w N.s : ℤ) - (if (w, N.s) ∈ pathArcs p then 1 else 0)) =
        ((f N.s w : ℤ) - (f w N.s : ℤ)) -
          ((if (N.s, w) ∈ pathArcs p then (1 : ℤ) else 0) -
            (if (w, N.s) ∈ pathArcs p then (1 : ℤ) else 0)) := fun w => by omega
  rw [Finset.sum_congr rfl fun w _ => hsplit w, Finset.sum_sub_distrib,
    sum_pathArcs_sign hnd hs ht N.s, ← f.netOut_eq_sum_sub N.s]
  simp [hts, value]

/-- **A flow of positive value has a flow path.** If `f.value > 0`, some simple `s`-`t` path
uses only arcs with positive flow. -/
theorem exists_isFlowPath (f : N.Flow) (hpos : 0 < f.value) : ∃ p, f.IsFlowPath p := by
  classical
  by_cases hreach : Relation.ReflTransGen (fun x y => 0 < f x y) N.s N.t
  · obtain ⟨p, hnd, hs, ht, harcs⟩ := exists_nodup_list_of_reflTransGen hreach
    exact ⟨p, hnd, hs, ht, harcs⟩
  · exfalso
    let R : Finset V :=
      Finset.univ.filter fun v => Relation.ReflTransGen (fun x y => 0 < f x y) N.s v
    have hR : N.IsCut R := by
      refine ⟨by simp [R, Relation.ReflTransGen.refl], ?_⟩
      simpa [R] using hreach
    have hval := f.value_eq_netFlow_across_cut hR
    have hzero : ∀ u ∈ R, ∀ v ∈ Finset.univ \ R, f u v = 0 := by grind
    have hout : (∑ u ∈ R, ∑ v ∈ Finset.univ \ R, (f u v : ℤ)) = 0 :=
      Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => by simp [hzero u hu v hv]
    have hin : 0 ≤ ∑ u ∈ R, ∑ v ∈ Finset.univ \ R, (f v u : ℤ) :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by omega
    omega

/-- **Flow decomposition into paths** (path part of the classical flow decomposition):
a feasible integral flow `f` of value `k` contains `k` simple `s`-`t` paths along positive-flow
arcs such that every arc `(u, v)` lies on at most `f u v` of them. (The remaining flow consists of
circulations, which are not recorded. If `N.s = N.t`, then `k = 0`.) -/
theorem exists_flowPaths [DecidableEq V] (f : N.Flow) :
    ∃ P : Fin f.value.toNat → List V, (∀ i, f.IsFlowPath (P i)) ∧
      ∀ u v, (Finset.univ.filter fun i => (u, v) ∈ pathArcs (P i)).card ≤ f u v := by
  suffices h : ∀ k : ℕ, ∀ f : N.Flow, f.value.toNat = k →
      ∃ P : Fin k → List V, (∀ i, f.IsFlowPath (P i)) ∧
        ∀ u v, (Finset.univ.filter fun i => (u, v) ∈ pathArcs (P i)).card ≤ f u v from
    h _ f rfl
  intro k
  induction k with
  | zero =>
    intro f _
    exact ⟨Fin.elim0, fun i => i.elim0, fun u v => by simp⟩
  | succ k ih =>
    intro f hk
    have hpos : 0 < f.value := by omega
    have hst : N.s ≠ N.t := fun h => by
      rw [f.value_eq_zero_of_s_eq_t h] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨p, hp⟩ := f.exists_isFlowPath hpos
    let g := f.subPath p hp
    have hg : g.value.toNat = k := by
      have := f.value_subPath hst p hp
      change (f.subPath p hp).value.toNat = k
      omega
    obtain ⟨P, hP, hcount⟩ := ih g hg
    have hle : ∀ u v, g u v ≤ f u v := fun u v => by
      change f.subPath p hp u v ≤ f u v
      rw [subPath_apply]
      split_ifs <;> omega
    refine ⟨Fin.cons p P, fun i => ?_, fun u v => ?_⟩
    · refine Fin.cases hp (fun j => ?_) i
      obtain ⟨hnd, hs, ht, harcs⟩ := hP j
      refine ⟨hnd, hs, ht, fun e he => lt_of_lt_of_le (harcs e he) (hle e.1 e.2)⟩
    · have hsplit : (Finset.univ.filter fun i : Fin (k + 1) =>
          (u, v) ∈ pathArcs ((Fin.cons p P : Fin (k + 1) → List V) i)).card =
          (if (u, v) ∈ pathArcs p then 1 else 0) +
            (Finset.univ.filter fun j : Fin k => (u, v) ∈ pathArcs (P j)).card := by
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hsplit]
      have hc := hcount u v
      change _ ≤ f.subPath p hp u v at hc
      rw [subPath_apply] at hc
      split_ifs at hc ⊢ with huv
      · have := hp.2.2.2 (u, v) huv
        simp only at this
        omega
      · omega

/-- Cancel antiparallel flow: subtract `min (f u v) (f v u)` from both `f u v` and `f v u`. -/
def cancel (f : N.Flow) : N.Flow where
  toFun u v := f u v - min (f u v) (f v u)
  le_cap u v := le_trans (Nat.sub_le _ _) (f.le_cap u v)
  conserve v hvs hvt := by
    have hc : ∑ u, f u v = ∑ w, f v w := f.conserve v hvs hvt
    have h1 : ∑ u, (f u v - min (f u v) (f v u)) =
        ∑ u, f u v - ∑ u, min (f u v) (f v u) :=
      Finset.sum_tsub_distrib _ fun u _ => min_le_left _ _
    have h2 : ∑ w, (f v w - min (f v w) (f w v)) =
        ∑ w, f v w - ∑ w, min (f v w) (f w v) :=
      Finset.sum_tsub_distrib _ fun w _ => min_le_left _ _
    have h3 : ∑ u, min (f u v) (f v u) = ∑ w, min (f v w) (f w v) :=
      Finset.sum_congr rfl fun u _ => min_comm _ _
    change ∑ u, (f u v - min (f u v) (f v u)) = ∑ w, (f v w - min (f v w) (f w v))
    rw [h1, h2, h3, hc]

theorem cancel_apply (f : N.Flow) (u v : V) : f.cancel u v = f u v - min (f u v) (f v u) := by
  rfl

theorem cancel_le (f : N.Flow) (u v : V) : f.cancel u v ≤ f u v := Nat.sub_le _ _

theorem cancel_eq_zero_or (f : N.Flow) (u v : V) : f.cancel u v = 0 ∨ f.cancel v u = 0 := by
  rw [cancel_apply, cancel_apply]
  omega

@[simp]
theorem value_cancel (f : N.Flow) : f.cancel.value = f.value := by
  have hcast : ∀ u v : V, ((f.cancel u v : ℕ) : ℤ) = (f u v : ℤ) - (min (f u v) (f v u) : ℕ) :=
    fun u v => by rw [cancel_apply]; omega
  have hsym : ∑ w, ((min (f N.s w) (f w N.s) : ℕ) : ℤ) =
      ∑ w, ((min (f w N.s) (f N.s w) : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun w _ => by rw [min_comm]
  simp only [value, netOut, hcast, Finset.sum_sub_distrib]
  omega

end Flow

end Network

end Cslib.Algorithms.Lean.MaxFlow
