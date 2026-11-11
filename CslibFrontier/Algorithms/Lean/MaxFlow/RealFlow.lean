/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.WeightedCut.RealCut
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 5000000


/-!
# Real-capacity Maximum Flow

This module defines maximum flows with real capacities.
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.WeightedCut Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K]
  [LinearOrder K] [IsStrictOrderedRing K]

def IsFeasibleRealFlow (W : V → V → K) (s t : V) (f : V × V → K) : Prop :=
  (∀ u v, 0 ≤ f (u, v)) ∧
  (∀ u v, f (u, v) ≤ W u v) ∧
  (∀ v, v ≠ s → v ≠ t → ∑ u, f (u, v) = ∑ w, f (v, w))

def realNetOut (f : V × V → K) (s : V) : K :=
  (∑ w, f (s, w)) - (∑ u, f (u, s))

def IsMaxRealFlow (W : V → V → K) (s t : V) (val : K) : Prop :=
  IsGreatest ((fun f => realNetOut f s) '' {f | IsFeasibleRealFlow W s t f}) val

/-- The equality constraints for flow conservation and capacity bounds, encoded as `A * x ≤ b`.
    To be formulated by `@verifier-math` as per handoff in #3422. -/
def flowLP_A (_W : V → V → K) (s t : V) : Matrix (Sum (V × V) (Sum V V)) (V × V) K :=
  fun i j => match i with
  | Sum.inl e => if e = j then 1 else 0
  | Sum.inr (Sum.inl v) => if v = s ∨ v = t then 0
                           else if j.2 = v ∧ j.1 = v then 0 else if j.2 = v then 1 else if j.1 = v then -1 else 0
  | Sum.inr (Sum.inr v) => if v = s ∨ v = t then 0
                           else if j.1 = v ∧ j.2 = v then 0 else if j.1 = v then 1 else if j.2 = v then -1 else 0

def flowLP_b (W : V → V → K) (_s _t : V) : (Sum (V × V) (Sum V V)) → K :=
  fun i => match i with
  | Sum.inl e => W e.1 e.2
  | Sum.inr _ => 0

def flowLP_c (s _t : V) : (V × V) → K :=
  fun e => if e.1 = s ∧ e.2 = s then 0 else if e.1 = s then 1 else if e.2 = s then -1 else 0

def cutDual (X : Finset V) (s t : V) : Sum (V × V) (Sum V V) → K :=
  fun i => match i with
  | Sum.inl (u, v) => if u ∈ X ∧ v ∉ X then 1 else 0
  | Sum.inr (Sum.inl v) => if v ∈ X ∧ v ≠ s then 1 else 0
  | Sum.inr (Sum.inr _) => 0

theorem sum_trick_1 (f : V × V → K) (v : V) :
    (∑ u : V, ∑ w : V, if w = v ∧ u = v then (0 : K) else if w = v then f (u, w) else if u = v then -f (u, w) else 0) =
    (∑ u : V, ∑ w : V, ((if w = v then f (u, v) else 0) - (if u = v then f (v, w) else 0))) := by
  apply sum_congr rfl; intro u _
  apply sum_congr rfl; intro w _
  by_cases hu : u = v <;> by_cases hw : w = v
  · subst hu hw; simp
  · subst hu; simp [hw]
  · subst hw; simp [hu]
  · simp [hu, hw]

theorem sum_trick_2 (f : V × V → K) (v : V) :
    (∑ u : V, ∑ w : V, if u = v ∧ w = v then (0 : K) else if u = v then f (u, w) else if w = v then -f (u, w) else 0) =
    (∑ u : V, ∑ w : V, ((if u = v then f (v, w) else 0) - (if w = v then f (u, v) else 0))) := by
  apply sum_congr rfl; intro u _
  apply sum_congr rfl; intro w _
  by_cases hu : u = v <;> by_cases hw : w = v
  · subst hu hw; simp
  · subst hu; simp [hw]
  · subst hw; simp [hu]
  · simp [hu, hw]

theorem sum_trick_3 (f : V × V → K) (s : V) :
    (∑ u : V, ∑ w : V, if u = s ∧ w = s then (0 : K) else if u = s then f (u, w) else if w = s then -f (u, w) else 0) =
    (∑ u : V, ∑ w : V, ((if u = s then f (s, w) else 0) - (if w = s then f (u, s) else 0))) := by
  apply sum_trick_2

theorem IsFeasibleRealFlow_iff_flowLP (W : V → V → K) (s t : V) (f : V × V → K) :
    IsFeasibleRealFlow W s t f ↔ (0 ≤ f ∧ flowLP_A W s t *ᵥ f ≤ flowLP_b W s t) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h1_mat : 0 ≤ f := fun e => h1 e.1 e.2
    refine ⟨h1_mat, fun i => ?_⟩
    rcases i with ⟨e⟩ | ⟨v⟩ | ⟨v⟩
    · dsimp [flowLP_A, flowLP_b, mulVec, dotProduct]
      have : (∑ j : V × V, (if e = j then (1 : K) else 0) * f j) = f e := by
        simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
      rw [this]
      exact h2 e.1 e.2
    · dsimp [flowLP_A, flowLP_b, mulVec, dotProduct]
      split_ifs with h
      · simp
      · push_neg at h
        have H1 : (∑ j : V × V, (if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0) * f j) =
            ∑ u, ∑ w, (if w = v ∧ u = v then (0 : K) else if w = v then 1 else if u = v then -1 else 0) * f (u, w) := by
          rw [← sum_product']; apply sum_congr rfl; rintro ⟨u, w⟩ _; simp
        rw [H1]
        have H2 : (∑ u, ∑ w, (if w = v ∧ u = v then (0 : K) else if w = v then 1 else if u = v then -1 else 0) * f (u, w)) =
            ∑ u, ∑ w, if w = v ∧ u = v then (0 : K) else if w = v then f (u, w) else if u = v then -f (u, w) else 0 := by
          apply sum_congr rfl; intro u _; apply sum_congr rfl; intro w _; split_ifs <;> simp
        rw [H2, sum_trick_1]
        simp only [sum_sub_distrib]
        have S1 : (∑ u : V, ∑ w : V, if w = v then f (u, v) else 0) = ∑ u, f (u, v) := by
          apply sum_congr rfl; intro u _; simp
        have S2 : (∑ u : V, ∑ w : V, if u = v then f (v, w) else 0) = ∑ w, f (v, w) := by
          rw [sum_comm]; apply sum_congr rfl; intro w _; simp
        rw [S1, S2]
        exact sub_nonpos.mpr (le_of_eq (h3 v h.1 h.2))
    · dsimp [flowLP_A, flowLP_b, mulVec, dotProduct]
      split_ifs with h
      · simp
      · push_neg at h
        have H1 : (∑ j : V × V, (if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0) * f j) =
            ∑ u, ∑ w, (if u = v ∧ w = v then (0 : K) else if u = v then 1 else if w = v then -1 else 0) * f (u, w) := by
          rw [← sum_product']; apply sum_congr rfl; rintro ⟨u, w⟩ _; simp
        rw [H1]
        have H2 : (∑ u, ∑ w, (if u = v ∧ w = v then (0 : K) else if u = v then 1 else if w = v then -1 else 0) * f (u, w)) =
            ∑ u, ∑ w, if u = v ∧ w = v then (0 : K) else if u = v then f (u, w) else if w = v then -f (u, w) else 0 := by
          apply sum_congr rfl; intro u _; apply sum_congr rfl; intro w _; split_ifs <;> simp
        rw [H2, sum_trick_2]
        simp only [sum_sub_distrib]
        have S1 : (∑ u : V, ∑ w : V, if u = v then f (v, w) else 0) = ∑ w, f (v, w) := by
          rw [sum_comm]; apply sum_congr rfl; intro w _; simp
        have S2 : (∑ u : V, ∑ w : V, if w = v then f (u, v) else 0) = ∑ u, f (u, v) := by
          apply sum_congr rfl; intro u _; simp
        rw [S1, S2]
        exact sub_nonpos.mpr (le_of_eq (h3 v h.1 h.2).symm)
  · rintro ⟨h1, h2⟩
    have h1_fun : ∀ u v, 0 ≤ f (u, v) := fun u v => h1 (u, v)
    refine ⟨h1_fun, fun u v => ?_, fun v hvs hvt => ?_⟩
    · have := h2 (Sum.inl (u, v))
      dsimp [flowLP_A, flowLP_b, mulVec, dotProduct] at this
      have H : (∑ j : V × V, (if (u, v) = j then (1 : K) else 0) * f j) = f (u, v) := by
        simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
      rw [H] at this
      exact this
    · have eq1 := h2 (Sum.inr (Sum.inl v))
      dsimp [flowLP_A, flowLP_b, mulVec, dotProduct] at eq1
      have H1 : (∑ j : V × V, (if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0) * f j) =
          ∑ u, ∑ w, (if w = v ∧ u = v then (0 : K) else if w = v then 1 else if u = v then -1 else 0) * f (u, w) := by
        simp [hvs, hvt]
        rw [← sum_product']; apply sum_congr rfl; rintro ⟨u, w⟩ _; simp
      rw [H1] at eq1
      have H2 : (∑ u, ∑ w, (if w = v ∧ u = v then (0 : K) else if w = v then 1 else if u = v then -1 else 0) * f (u, w)) =
          (∑ u, f (u, v)) - (∑ w, f (v, w)) := by
        have tmp : (∑ u, ∑ w, (if w = v ∧ u = v then (0 : K) else if w = v then 1 else if u = v then -1 else 0) * f (u, w)) =
            ∑ u, ∑ w, if w = v ∧ u = v then (0 : K) else if w = v then f (u, w) else if u = v then -f (u, w) else 0 := by
          apply sum_congr rfl; intro u _; apply sum_congr rfl; intro w _; split_ifs <;> simp
        rw [tmp, sum_trick_1]
        simp only [sum_sub_distrib]
        have S1 : (∑ u : V, ∑ w : V, if w = v then f (u, v) else 0) = ∑ u, f (u, v) := by
          apply sum_congr rfl; intro u _; simp
        have S2 : (∑ u : V, ∑ w : V, if u = v then f (v, w) else 0) = ∑ w, f (v, w) := by
          rw [sum_comm]; apply sum_congr rfl; intro w _; simp
        rw [S1, S2]
      rw [H2] at eq1
      have eq2 := h2 (Sum.inr (Sum.inr v))
      dsimp [flowLP_A, flowLP_b, mulVec, dotProduct] at eq2
      have H3 : (∑ j : V × V, (if v = s ∨ v = t then 0 else if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0) * f j) =
          ∑ u, ∑ w, (if u = v ∧ w = v then (0 : K) else if u = v then 1 else if w = v then -1 else 0) * f (u, w) := by
        simp [hvs, hvt]
        rw [← sum_product']; apply sum_congr rfl; rintro ⟨u, w⟩ _; simp
      rw [H3] at eq2
      have H4 : (∑ u, ∑ w, (if u = v ∧ w = v then (0 : K) else if u = v then 1 else if w = v then -1 else 0) * f (u, w)) =
          (∑ w, f (v, w)) - (∑ u, f (u, v)) := by
        have tmp : (∑ u, ∑ w, (if u = v ∧ w = v then (0 : K) else if u = v then 1 else if w = v then -1 else 0) * f (u, w)) =
            ∑ u, ∑ w, if u = v ∧ w = v then (0 : K) else if u = v then f (u, w) else if w = v then -f (u, w) else 0 := by
          apply sum_congr rfl; intro u _; apply sum_congr rfl; intro w _; split_ifs <;> simp
        rw [tmp, sum_trick_2]
        simp only [sum_sub_distrib]
        have S1 : (∑ u : V, ∑ w : V, if u = v then f (v, w) else 0) = ∑ w, f (v, w) := by
          rw [sum_comm]; apply sum_congr rfl; intro w _; simp
        have S2 : (∑ u : V, ∑ w : V, if w = v then f (u, v) else 0) = ∑ u, f (u, v) := by
          apply sum_congr rfl; intro u _; simp
        rw [S1, S2]
      rw [H4] at eq2
      exact le_antisymm (sub_nonpos.mp eq1) (sub_nonpos.mp eq2)

theorem realNetOut_eq_dotProduct (s t : V) (f : V × V → K) :
    realNetOut f s = flowLP_c s t ⬝ᵥ f := by
  dsimp [realNetOut, flowLP_c, dotProduct]
  have H : (∑ j : V × V, (if j.1 = s ∧ j.2 = s then (0 : K) else if j.1 = s then 1 else if j.2 = s then -1 else 0) * f j) =
      ∑ u, ∑ w, (if u = s ∧ w = s then (0 : K) else if u = s then 1 else if w = s then -1 else 0) * f (u, w) := by
    rw [← sum_product']; apply sum_congr rfl; rintro ⟨u, w⟩ _; simp
  rw [H]
  have H2 : (∑ u, ∑ w, (if u = s ∧ w = s then (0 : K) else if u = s then 1 else if w = s then -1 else 0) * f (u, w)) =
      ∑ u, ∑ w, if u = s ∧ w = s then (0 : K) else if u = s then f (u, w) else if w = s then -f (u, w) else 0 := by
    apply sum_congr rfl; intro u _; apply sum_congr rfl; intro w _; split_ifs <;> simp
  rw [H2, sum_trick_3]
  simp only [sum_sub_distrib]
  have S1 : (∑ u : V, ∑ w : V, if u = s then f (s, w) else 0) = ∑ w, f (s, w) := by
    rw [sum_comm]; apply sum_congr rfl; intro w _; simp
  have S2 : (∑ u : V, ∑ w : V, if w = s then f (u, s) else 0) = ∑ u, f (u, s) := by
    apply sum_congr rfl; intro u _; simp
  rw [S1, S2]

theorem cutDual_nonneg (X : Finset V) (s t : V) : (0 : Sum (V × V) (Sum V V) → K) ≤ cutDual X s t := by
  intro i
  unfold cutDual
  split
  · split_ifs <;> positivity
  · split_ifs <;> positivity
  · positivity

theorem flowLP_c_le_cutDual_mul_A (W : V → V → K) (X : Finset V) (s t : V) (hs : s ∈ X) (ht : t ∉ X) :
    flowLP_c s t ≤ cutDual X s t ᵥ* flowLP_A W s t := by
  intro j
  dsimp [flowLP_c, cutDual, flowLP_A, vecMul, dotProduct]
  have e1 : (∑ i : Sum (V × V) (Sum V V),
      (match i with
        | Sum.inl (u, v) => if u ∈ X ∧ v ∉ X then (1 : K) else 0
        | Sum.inr (Sum.inl v) => if v ∈ X ∧ v ≠ s then (1 : K) else 0
        | Sum.inr (Sum.inr _) => (0 : K)) *
        match i with
        | Sum.inl e => if e = j then (1 : K) else 0
        | Sum.inr (Sum.inl v) =>
          if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0
        | Sum.inr (Sum.inr v) =>
          if v = s ∨ v = t then 0 else if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0) =
      (if j.1 ∈ X ∧ j.2 ∉ X then (1 : K) else 0) +
      (if j.2 ∈ X ∧ j.2 ≠ s ∧ ¬ (j.2 = s ∨ j.2 = t) ∧ j.1 ≠ j.2 then (1 : K) else 0) -
      (if j.1 ∈ X ∧ j.1 ≠ s ∧ ¬ (j.1 = s ∨ j.1 = t) ∧ j.2 ≠ j.1 then (1 : K) else 0) := by
    have s1 : (∑ i : Sum (V × V) (Sum V V),
        (match i with
          | Sum.inl (u, v) => if u ∈ X ∧ v ∉ X then (1 : K) else 0
          | Sum.inr (Sum.inl v) => if v ∈ X ∧ v ≠ s then (1 : K) else 0
          | Sum.inr (Sum.inr _) => (0 : K)) *
          match i with
          | Sum.inl e => if e = j then (1 : K) else 0
          | Sum.inr (Sum.inl v) =>
            if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0
          | Sum.inr (Sum.inr v) =>
            if v = s ∨ v = t then 0 else if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0) =
        (∑ e : V × V, (if e.1 ∈ X ∧ e.2 ∉ X then (1 : K) else 0) * (if e = j then (1 : K) else 0)) +
        (∑ i : Sum V V,
          (match i with
            | Sum.inl v => if v ∈ X ∧ v ≠ s then (1 : K) else 0
            | Sum.inr _ => (0 : K)) *
            match i with
            | Sum.inl v => if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0
            | Sum.inr v => if v = s ∨ v = t then 0 else if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0) := by
      rw [Fintype.sum_sum_type]
      apply congr_arg₂ _
      · apply sum_congr rfl; rintro ⟨u, v⟩ _; rfl
      · apply sum_congr rfl; rintro (v | v) _ <;> rfl
    rw [s1]
    have e1 : (∑ e : V × V, (if e.1 ∈ X ∧ e.2 ∉ X then (1 : K) else 0) * (if e = j then (1 : K) else 0)) =
        if j.1 ∈ X ∧ j.2 ∉ X then (1 : K) else 0 := by
      have H : ∀ e : V × V, (if e.1 ∈ X ∧ e.2 ∉ X then (1 : K) else 0) * (if e = j then (1 : K) else 0) =
          if j = e then (if j.1 ∈ X ∧ j.2 ∉ X then (1 : K) else 0) else 0 := by
        intro e
        by_cases h : e = j
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [sum_congr rfl (fun x _ => H x)]
      rw [Finset.sum_ite_eq]
      simp
    rw [e1]
    have s2 : (∑ i : Sum V V,
          (match i with
            | Sum.inl v => if v ∈ X ∧ v ≠ s then (1 : K) else 0
            | Sum.inr _ => (0 : K)) *
            match i with
            | Sum.inl v => if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0
            | Sum.inr v => if v = s ∨ v = t then 0 else if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0) =
        (∑ v : V, (if v ∈ X ∧ v ≠ s then (1 : K) else 0) * (if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0)) +
        (∑ v : V, (0 : K) * (if v = s ∨ v = t then 0 else if j.1 = v ∧ j.2 = v then (0 : K) else if j.1 = v then 1 else if j.2 = v then -1 else 0)) := by
      rw [Fintype.sum_sum_type]
    rw [s2]
    simp only [zero_mul, sum_const_zero, add_zero]
    have s3 : (∑ v : V, (if v ∈ X ∧ v ≠ s then (1 : K) else 0) * (if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0)) =
        (if j.2 ∈ X ∧ j.2 ≠ s ∧ ¬ (j.2 = s ∨ j.2 = t) ∧ j.1 ≠ j.2 then (1 : K) else 0) - (if j.1 ∈ X ∧ j.1 ≠ s ∧ ¬ (j.1 = s ∨ j.1 = t) ∧ j.2 ≠ j.1 then (1 : K) else 0) := by
      have s4 : ∀ v, (if v ∈ X ∧ v ≠ s then (1 : K) else 0) * (if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0) =
          (if v = j.2 then (if j.2 ∈ X ∧ j.2 ≠ s ∧ ¬ (j.2 = s ∨ j.2 = t) ∧ j.1 ≠ j.2 then (1 : K) else 0) else 0) - (if v = j.1 then (if j.1 ∈ X ∧ j.1 ≠ s ∧ ¬ (j.1 = s ∨ j.1 = t) ∧ j.2 ≠ j.1 then (1 : K) else 0) else 0) := by
        intro v
        by_cases hv2 : v = j.2 <;> by_cases hv1 : v = j.1
        · subst hv2; have heq : j.1 = j.2 := hv1.symm; simp only [heq]; simp
        · subst hv2; simp [hv1, Ne.symm hv1]; try { split_ifs <;> simp_all <;> linarith }
        · subst hv1; simp [hv2, Ne.symm hv2]; try { split_ifs <;> simp_all <;> linarith }
        · simp [hv1, hv2, Ne.symm hv1, Ne.symm hv2]
      have s5 : (∑ v : V, (if v ∈ X ∧ v ≠ s then (1 : K) else 0) * (if v = s ∨ v = t then 0 else if j.2 = v ∧ j.1 = v then (0 : K) else if j.2 = v then 1 else if j.1 = v then -1 else 0)) =
          ∑ v : V, ((if v = j.2 then (if j.2 ∈ X ∧ j.2 ≠ s ∧ ¬ (j.2 = s ∨ j.2 = t) ∧ j.1 ≠ j.2 then (1 : K) else 0) else 0) - (if v = j.1 then (if j.1 ∈ X ∧ j.1 ≠ s ∧ ¬ (j.1 = s ∨ j.1 = t) ∧ j.2 ≠ j.1 then (1 : K) else 0) else 0)) := by
        apply sum_congr rfl; intro v _; exact s4 v
      rw [s5, sum_sub_distrib]
      have c1 : (∑ v : V, if v = j.2 then (if j.2 ∈ X ∧ j.2 ≠ s ∧ ¬ (j.2 = s ∨ j.2 = t) ∧ j.1 ≠ j.2 then (1 : K) else 0) else 0) =
          if j.2 ∈ X ∧ j.2 ≠ s ∧ ¬ (j.2 = s ∨ j.2 = t) ∧ j.1 ≠ j.2 then (1 : K) else 0 := by
        simp [Finset.sum_ite_eq']
      have c2 : (∑ v : V, if v = j.1 then (if j.1 ∈ X ∧ j.1 ≠ s ∧ ¬ (j.1 = s ∨ j.1 = t) ∧ j.2 ≠ j.1 then (1 : K) else 0) else 0) =
          if j.1 ∈ X ∧ j.1 ≠ s ∧ ¬ (j.1 = s ∨ j.1 = t) ∧ j.2 ≠ j.1 then (1 : K) else 0 := by
        simp [Finset.sum_ite_eq']
      rw [c1, c2]
    rw [s3]
    ring
  rw [e1]
  by_cases h1 : j.1 = s <;> by_cases h2 : j.2 = s
  · have h1' : j.1 = s := h1; have h2' : j.2 = s := h2
    try simp only [@eq_comm _ j.2 j.1]
    simp [h1', h2']; try { split_ifs <;> simp_all <;> linarith }
  · have h1' : j.1 = s := h1; have h2' : j.2 ≠ s := h2
    try simp only [@eq_comm _ j.2 j.1]
    simp [h1', h2', hs, ht]
    by_cases hj2 : j.2 ∈ X <;> by_cases h4 : j.2 = t
    all_goals { simp [hj2, h4, hs, ht]; try { split_ifs <;> simp_all <;> linarith } }
  · have h1' : j.1 ≠ s := h1; have h2' : j.2 = s := h2
    try simp only [@eq_comm _ j.2 j.1]
    simp [h1', h2', hs, ht]
    by_cases hj1 : j.1 ∈ X <;> by_cases h3 : j.1 = t
    all_goals { simp [hj1, h3, hs, ht]; try { split_ifs <;> simp_all <;> linarith } }
  · have h1' : j.1 ≠ s := h1; have h2' : j.2 ≠ s := h2
    try simp only [@eq_comm _ j.2 j.1]
    simp [h1', h2']
    by_cases hj1 : j.1 ∈ X <;> by_cases hj2 : j.2 ∈ X <;> by_cases h3 : j.1 = t <;> by_cases h4 : j.2 = t
    all_goals {
      simp [hj1, hj2, h3, h4, hs, ht]
      try simp only [@eq_comm _ j.2 j.1]
      try { split_ifs <;> simp_all <;> linarith }
    }

theorem cutDual_dotProduct_b (W : V → V → K) (X : Finset V) (s t : V) :
    cutDual X s t ⬝ᵥ flowLP_b W s t = realCutWeight W X := by
  dsimp [cutDual, flowLP_b, dotProduct, realCutWeight]
  rw [Fintype.sum_sum_type]
  dsimp
  simp only [mul_zero, sum_const_zero, add_zero]
  rw [← Finset.sum_product']
  have e1 : ∀ a : V × V, (if a.1 ∈ X ∧ a.2 ∉ X then (1 : K) else 0) * W a.1 a.2 =
      if a ∈ X ×ˢ (Finset.univ \ X) then W a.1 a.2 else 0 := by
    intro a
    simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun x _ => e1 x)]
  rw [← Finset.sum_filter]
  have eq2 : Finset.univ.filter (fun x => x ∈ X ×ˢ (Finset.univ \ X)) = X ×ˢ (Finset.univ \ X) := by
    ext x; simp
  rw [eq2]

theorem weak_duality (W : V → V → K) (s t : V) (f : V × V → K)
    (hf : IsFeasibleRealFlow W s t f) (X : Finset V) (hs : s ∈ X) (ht : t ∉ X) :
    realNetOut f s ≤ realCutWeight W X := by
  have H_feas := (IsFeasibleRealFlow_iff_flowLP W s t f).mp hf
  have H_eq := realNetOut_eq_dotProduct s t f
  rw [H_eq]
  have H1 := dotProduct_le_dotProduct_of_nonneg_right (flowLP_c_le_cutDual_mul_A W X s t hs ht) H_feas.1
  have H2 : (cutDual X s t ᵥ* flowLP_A W s t) ⬝ᵥ f = cutDual X s t ⬝ᵥ (flowLP_A W s t *ᵥ f) := by
    exact (dotProduct_mulVec (cutDual X s t) (flowLP_A W s t) f).symm
  rw [H2] at H1
  have H3 := dotProduct_le_dotProduct_of_nonneg_left H_feas.2 (cutDual_nonneg X s t)
  have H4 := cutDual_dotProduct_b W X s t
  linarith

theorem strong_duality (W : V → V → K) (s t : V) (hst : s ≠ t) (hW : ∀ u v, 0 ≤ W u v) :
    ∃ v, IsMaxRealFlow W s t v ∧
      IsLeast ((· ⬝ᵥ flowLP_b W s t) '' {y | 0 ≤ y ∧ flowLP_c s t ≤ y ᵥ* flowLP_A W s t}) v := by
  have H := Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg
    (flowLP_A W s t) (flowLP_b W s t) (flowLP_c s t)
  have hP : ∃ x, 0 ≤ x ∧ flowLP_A W s t *ᵥ x ≤ flowLP_b W s t := by
    use 0
    constructor
    · exact le_refl 0
    · have hf : IsFeasibleRealFlow W s t 0 := by
        dsimp [IsFeasibleRealFlow]
        constructor
        · intro _ _; exact le_refl 0
        · constructor
          · intro u v; exact hW u v
          · intro v _ _; simp
      exact ((IsFeasibleRealFlow_iff_flowLP W s t 0).mp hf).2
  have hD : ∃ y, 0 ≤ y ∧ flowLP_c s t ≤ y ᵥ* flowLP_A W s t := by
    use cutDual {s} s t
    constructor
    · exact cutDual_nonneg {s} s t
    · exact flowLP_c_le_cutDual_mul_A W {s} s t (Finset.mem_singleton_self s) (by simp [hst.symm])
  obtain ⟨v, hG, hL⟩ := H hP hD
  use v
  constructor
  · dsimp [IsMaxRealFlow]
    have Heq : ((fun f => realNetOut f s) '' {f | IsFeasibleRealFlow W s t f}) =
        ((fun x => flowLP_c s t ⬝ᵥ x) '' {x | 0 ≤ x ∧ flowLP_A W s t *ᵥ x ≤ flowLP_b W s t}) := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨f, hf, rfl⟩
        use f
        rw [← realNetOut_eq_dotProduct]
        exact ⟨(IsFeasibleRealFlow_iff_flowLP W s t f).mp hf, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        use x
        rw [realNetOut_eq_dotProduct]
        exact ⟨(IsFeasibleRealFlow_iff_flowLP W s t x).mpr hx, rfl⟩
    rw [Heq]
    exact hG
  · exact hL

end Cslib.Algorithms.Lean.MaxFlow
