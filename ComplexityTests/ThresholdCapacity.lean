/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Capacity
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-! Boundary and non-vacuity clients for scalar-block capacity. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

universe u

-- Exact one-change behavior, including a repeated endpoint at the threshold.
example : ChangesAtMost (fun t : ℕ => decide (2 ≤ t)) 1 := ChangesAtMost.decide_le 2

example : ¬ ChangesAtMost (fun t : ℕ => decide (2 ≤ t)) 0 := by
  intro h
  have := h id monotone_id {1} (by simp)
  simp at this

example {α β γ : Type*} [Preorder α] [Preorder γ] (f : α → β) (g : γ → α)
    (h : ChangesAtMost f 3) (hg : Monotone g) : ChangesAtMost (f ∘ g) 5 :=
  (h.comp_monotone hg).mono (by decide)

-- All keys tie, but the selected group still contains two distinct elements.
example : ∃ P' ⊆ Finset.range 5, ∃ Qbad ⊆ (Finset.univ : Finset Bool),
    2 ≤ P'.card ∧ Qbad.card = 0 ∧
      ∀ q ∈ (Finset.univ : Finset Bool), q ∉ Qbad →
        ∀ p ∈ P', ∀ p' ∈ P', (fun _ : ℕ => q) p = q := by
  obtain ⟨P', hP, Qbad, hQ, hc, hb, _⟩ :=
    ChangesAtMost.exists_sorted_group (Finset.range 5) (Finset.univ : Finset Bool)
      (fun _ => (0 : ℕ)) (fun q _ => q) (G := 2) (by decide)
      (fun q _ => ChangesAtMost.const q)
  exact ⟨P', hP, Qbad, hQ, by simpa using hc, by omega, by simp⟩

example : ∃ P' ⊆ (Finset.univ : Finset (Fin 5)),
    ∃ Qbad ⊆ (Finset.univ : Finset (Fin 4)),
      2 ≤ P'.card ∧ 2 * Qbad.card ≤ 4 ∧
      ∀ q ∈ (Finset.univ : Finset (Fin 4)), q ∉ Qbad →
        ∀ p ∈ P', ∀ p' ∈ P', decide (q.val ≤ p.val) = decide (q.val ≤ p'.val) := by
  simpa using ChangesAtMost.exists_sorted_group
    (Finset.univ : Finset (Fin 5)) (Finset.univ : Finset (Fin 4)) Fin.val
    (fun q t => decide (q.val ≤ t)) (G := 2) (by decide)
    (fun q _ => ChangesAtMost.decide_le q.val)

example {κ β : Type*} (Q : Finset κ) (Ψ : κ → ℕ → β) {T : ℕ}
    (hΨ : ∀ q ∈ Q, ChangesAtMost (Ψ q) T) :
    ∃ P' ⊆ (∅ : Finset ℕ), ∃ Qbad ⊆ Q,
      (∅ : Finset ℕ).card / 3 ≤ P'.card ∧ 3 * Qbad.card ≤ T * Q.card ∧
        ∀ q ∈ Q, q ∉ Qbad → ∀ p ∈ P', ∀ p' ∈ P', Ψ q p = Ψ q p' :=
  ChangesAtMost.exists_sorted_group ∅ Q id Ψ (by decide) hΨ

-- The empty decomposition and zero-change steps have capacity cost one.
private def zeroBlocks (n : ℕ) : BlockDecomposition (fun _ : Fin n → Bool => true) Bool where
  length := 0
  kind := fun _ => .oneDim 0
  history := fun _ _ => false
  output := fun _ => true
  history_zero := fun _ _ => rfl
  step := by simp
  output_history := fun _ => rfl

private def constantBlocks (n rounds : ℕ) :
    BlockDecomposition (fun _ : Fin n → Bool => true) Bool where
  length := rounds
  kind := fun _ => .oneDim 0
  history := fun _ _ => false
  output := fun _ => true
  history_zero := fun _ _ => rfl
  step := fun _ _ => ⟨fun _ => 0, fun _ _ => false, fun _ => ChangesAtMost.const false,
    fun _ => rfl⟩
  output_history := fun _ => rfl

example (n : ℕ) : (zeroBlocks n).cost = 1 := by simp [BlockDecomposition.cost, zeroBlocks]

example (n rounds : ℕ) : (constantBlocks n rounds).cost = 1 := by
  simp [BlockDecomposition.cost, constantBlocks, BlockKind.cost]

example : (BlockKind.oneDim 0).cost = 1 ∧ (BlockKind.oneDim 1).cost = 4 ∧
    (BlockKind.oneDim 3).cost = 12 ∧ (BlockKind.summary 2).cost = 2 := by decide

-- A summary with no values cannot be a step, even when the input dimension is zero.
example {n : ℕ} {H : Type*} (prev next : (Fin n → Bool) → H) :
    ¬ (BlockKind.summary 0).Step prev next := by
  intro h
  obtain ⟨σ, _, _⟩ := h ∅
  exact Fin.elim0 (σ fun _ => false)

-- A nonconstant one-bit function has a valid summary of size two for every coordinate cut.
private def coordinateSummary (rounds : ℕ) (hrounds : 0 < rounds) :
    BlockDecomposition (fun x : Fin 1 → Bool => x 0) Bool where
  length := rounds
  kind := fun _ => .summary 2
  history := fun i x => if i = 0 then false else x 0
  output := id
  history_zero := by simp
  step := by
    intro i hi U
    refine ⟨fun p => if h : (0 : Fin 1) ∈ U then finTwoEquiv.symm (p ⟨0, h⟩) else 0,
      fun _ v q => if h : (0 : Fin 1) ∈ U then finTwoEquiv v else q ⟨0, h⟩, ?_⟩
    intro p q
    by_cases h : (0 : Fin 1) ∈ U <;> simp [Equiv.piEquivPiSubtypeProd, h]
  output_history := by simp [ne_of_gt hrounds]

example (rounds : ℕ) (hrounds : 0 < rounds) :
    (coordinateSummary rounds hrounds).cost = 2 ^ rounds := by
  simp [coordinateSummary, BlockDecomposition.cost, BlockKind.cost]

example : (coordinateSummary 3 (by decide)).cost = 8 := by
  decide +kernel

example (x : Fin 1 → Bool) : (coordinateSummary 1 (by decide)).output
    ((coordinateSummary 1 (by decide)).history 1 x) = x 0 :=
  (coordinateSummary 1 (by decide)).output_history x

-- Scalar updates also have a satisfiable nonzero-change contract, with equality returning true.
private def coordinateScalar : BlockDecomposition (fun x : Fin 1 → Bool => x 0) Bool where
  length := 1
  kind := fun _ => .oneDim 1
  history := fun i x => if i = 0 then false else x 0
  output := id
  history_zero := by simp
  step := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    refine ⟨fun _ => 1, fun _ t => decide ((1 : ℝ) ≤ t),
      fun _ => ChangesAtMost.decide_le 1, ?_⟩
    intro x
    cases hx : x 0 <;> simp [weightedSum, hx]
  output_history := by simp

example : coordinateScalar.cost = 4 := by
  simp [coordinateScalar, BlockDecomposition.cost, BlockKind.cost]

-- On zero coordinates, every set is 2-rectangle-free: each side has at most one point.
example : 2 ^ 0 < 4 * 2 ^ 2 * (constantBlocks 0 3).cost := by
  apply BlockDecomposition.two_pow_lt_mul_cost
  intro b
  apply Frontier.rectangleFree_iff.mpr
  intro X A B _
  left
  have : A.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ A)
  omega

-- A one-bit domain cannot contain a rectangle with two points on each side, for either color.
private theorem oneBit_rectangleFree (f : (Fin 1 → Bool) → Bool) (b : Bool) :
    Frontier.RectangleFree {x | f x = b} 2 := by
  apply Frontier.rectangleFree_iff.mpr
  intro X A B _
  by_cases h : (0 : Fin 1) ∈ X
  · right
    have hX : X = Set.univ := by ext i; fin_cases i; simp [h]
    subst X
    have : B.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ B)
    omega
  · left
    have hX : X = ∅ := by ext i; fin_cases i; simp [h]
    subst X
    have : A.ncard ≤ 1 := by simpa using Set.ncard_le_ncard (Set.subset_univ A)
    omega

example : 2 ^ 1 < 4 * 2 ^ 2 * (coordinateSummary 1 (by decide)).cost :=
  BlockDecomposition.two_pow_lt_mul_cost (oneBit_rectangleFree _) (coordinateSummary 1 (by decide))

example : 2 ^ 1 < 4 * 2 ^ 2 * coordinateScalar.cost :=
  BlockDecomposition.two_pow_lt_mul_cost (oneBit_rectangleFree _) coordinateScalar

example {n K : ℕ} {H : Type u} {f : Cslib.BooleanFunction n}
    (D : BlockDecomposition f H) (h : ∀ b, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * D.cost := D.two_pow_lt_mul_cost h
