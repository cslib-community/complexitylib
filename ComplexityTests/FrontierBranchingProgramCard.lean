/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.BranchingProgram

/-! Regressions for the infinite-cardinality examples reported in #1717. -/

open Cslib.Circuits.Frontier Set

namespace ComplexityTests.FrontierBranchingProgramCard

/-- One step reads the only coordinate; the edge condition ignores its label. -/
private def oneStep (U M : Type) (s : M) (edge : M → M → Prop) : ReadOnceNBP Unit U M where
  length := 1
  revealed t := if t = 0 then ∅ else univ
  revealed_zero := by simp
  revealed_length := by simp
  revealed_mono := by
    intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    · have hb : b ≠ 0 := by omega
      simp [ha, hb]
  start := s
  accept := s
  Edge _ m _ m' := edge m m'

private theorem oneStep_accepted (U M : Type) (s : M) (edge : M → M → Prop)
    (h : edge s s) : (oneStep U M s edge).accepted = univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨fun _ => s, rfl, rfl, fun _ _ => h⟩

-- Only layers 0 and 1 count when comparing accepting paths.
private theorem oneStep_unambiguous (U M : Type) (s : M) (edge : M → M → Prop) :
    (oneStep U M s edge).Unambiguous := by
  intro x γ δ hγ hδ t ht
  have h : t = 0 ∨ t = 1 := by
    change t ≤ 1 at ht
    omega
  rcases h with rfl | rfl
  · exact hγ.start.trans hδ.start.symm
  · exact hγ.accept.trans hδ.accept.symm

private def allEdges : ReadOnceNBP Unit Bool ℕ :=
  oneStep Bool ℕ 0 fun _ _ => True

example : allEdges.accepted = univ := oneStep_accepted _ _ _ _ trivial

example : allEdges.Unambiguous := oneStep_unambiguous _ _ _ _

private theorem allEdges_infinite : (allEdges.edges 0).Infinite := by
  have h : allEdges.edges 0 = univ := by ext e; rfl
  rw [h]
  exact infinite_univ

-- The underlying natural set cardinality is zero, but the public size API is unavailable.
example : (allEdges.edges 0).ncard = 0 := allEdges_infinite.ncard

example : True := by
  fail_if_success have : ℕ := allEdges.size
  trivial

/-- Two useful self-loop edges, with states still in the infinite ambient type ℕ. -/
private def twoLoops : ReadOnceNBP Unit Bool ℕ :=
  oneStep Bool ℕ 0 fun m m' => m = 0 ∧ m' = 0

private def loopCoordinate : twoLoops.newly 0 :=
  ⟨(), by simp [ReadOnceNBP.newly, twoLoops, oneStep]⟩

private def loopEdge (b : Bool) : ℕ × (twoLoops.newly 0 → Bool) × ℕ :=
  (0, fun _ => b, 0)

private theorem loopEdge_injective : Function.Injective loopEdge := by
  intro a b h
  exact congrArg (fun e => e.2.1 loopCoordinate) h

private theorem twoLoops_edges : twoLoops.edges 0 = range loopEdge := by
  ext ⟨m, a, m'⟩
  change (m = 0 ∧ m' = 0) ↔ ∃ b, loopEdge b = (m, a, m')
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨a loopCoordinate, Prod.ext rfl (Prod.ext ?_ rfl)⟩
    funext i
    exact congrArg a (Subsingleton.elim loopCoordinate i)
  · rintro ⟨b, h⟩
    exact ⟨(congrArg Prod.fst h).symm, (congrArg (fun e => e.2.2) h).symm⟩

private instance twoLoops_finite (t : Fin twoLoops.length) : Finite (twoLoops.edges t.val) := by
  have ht : t.val = 0 := by
    have := t.isLt
    change t.val < 1 at this
    omega
  have h : (twoLoops.edges t.val).Finite := by
    rw [ht, twoLoops_edges]
    exact finite_range loopEdge
  exact h.to_subtype

example : twoLoops.accepted = univ := oneStep_accepted _ _ _ _ ⟨rfl, rfl⟩

example : twoLoops.Unambiguous := oneStep_unambiguous _ _ _ _

example : twoLoops.size = 2 := by
  rw [ReadOnceNBP.size]
  change ∑ t ∈ Finset.range 1, (twoLoops.edges t).ncard = 2
  rw [Finset.sum_range_one, twoLoops_edges, ncard_range_of_injective loopEdge_injective]
  simp [Nat.card_eq_fintype_card]

-- Adding every edge contains both useful loops, but cannot supply a finite size of zero.
example (t : ℕ) (m m' : ℕ) (a : twoLoops.newly t → Bool) :
    twoLoops.Edge t m a m' → allEdges.Edge t m a m' := fun _ => trivial

/-- Infinite alphabet, one state, and every input accepted. -/
private def natInputs : ReadOnceNBP Unit ℕ Unit :=
  oneStep ℕ Unit () fun _ _ => True

private theorem natInputs_accepted : natInputs.accepted = univ :=
  oneStep_accepted _ _ _ _ trivial

example : natInputs.Unambiguous := oneStep_unambiguous _ _ _ _

private theorem natInputs_peers (t : ℕ) (x : Unit → ℕ) : natInputs.sweep.peers t x = univ := by
  ext y
  rw [ReadOnceNBP.mem_peers_sweep, natInputs_accepted]
  simp

private theorem natInputs_future_infinite (x : Unit → ℕ) :
    (natInputs.sweep.futureSide 0 x).Infinite := by
  let i₀ : ↥(natInputs.revealed 0)ᶜ := ⟨(), by simp [natInputs, oneStep]⟩
  refine infinite_of_injective_forall_mem
    (f := fun n : ℕ => fun _ : ↥(natInputs.revealed 0)ᶜ => n) ?_ ?_
  · intro m n h
    exact congrFun h i₀
  · intro n
    exact ⟨fun _ => n, by rw [natInputs_peers]; trivial, rfl⟩

private theorem natInputs_past_infinite (x : Unit → ℕ) :
    (natInputs.sweep.pastSide 1 x).Infinite := by
  let i₁ : natInputs.revealed 1 := ⟨(), by simp [natInputs, oneStep]⟩
  refine infinite_of_injective_forall_mem
    (f := fun n : ℕ => fun _ : natInputs.revealed 1 => n) ?_ ?_
  · intro m n h
    exact congrFun h i₁
  · intro n
    exact ⟨fun _ => n, by rw [natInputs_peers]; trivial, rfl⟩

private theorem natInputs_past_zero (x : Unit → ℕ) :
    natInputs.sweep.pastSide 0 x = {fun _ => 0} := by
  ext a
  constructor
  · intro _
    refine mem_singleton_iff.mpr (funext fun i => ?_)
    exact False.elim (by simpa [ReadOnceNBP.sweep, natInputs, oneStep] using i.property)
  · intro ha
    obtain rfl := mem_singleton_iff.mp ha
    exact ⟨fun _ => 0, by rw [natInputs_peers]; trivial, rfl⟩

private theorem natInputs_future_one (x : Unit → ℕ) :
    natInputs.sweep.futureSide 1 x = {fun _ => 0} := by
  ext a
  constructor
  · intro _
    refine mem_singleton_iff.mpr (funext fun i => ?_)
    exact False.elim (by simpa [ReadOnceNBP.sweep, natInputs, oneStep] using i.property)
  · intro ha
    obtain rfl := mem_singleton_iff.mp ha
    exact ⟨fun _ => 0, by rw [natInputs_peers]; trivial, rfl⟩

example : (natInputs.sweep.futureSide 0 (fun _ => 0)).encard = ⊤ :=
  encard_eq_top_iff.mpr (natInputs_future_infinite _)

example : (natInputs.sweep.pastSide 1 (fun _ => 0)).encard = ⊤ :=
  encard_eq_top_iff.mpr (natInputs_past_infinite _)

-- This is the erroneous old natural-cardinality condition, reconstructed explicitly.
example : ∀ t ≤ natInputs.length, ∀ x ∈ natInputs.accepted,
    (natInputs.sweep.pastSide t x).ncard < 1 ∨
      (natInputs.sweep.futureSide t x).ncard < 1 := by
  intro t ht x _
  have h : t = 0 ∨ t = 1 := by
    change t ≤ 1 at ht
    omega
  rcases h with rfl | rfl
  · right
    rw [(natInputs_future_infinite x).ncard]
    decide
  · left
    rw [(natInputs_past_infinite x).ncard]
    decide

example : ¬natInputs.SmallSides 1 := by
  intro h
  have hx : (fun _ => 0) ∈ natInputs.accepted := by rw [natInputs_accepted]; trivial
  rcases h 0 (Nat.zero_le _) _ hx with hpast | hfuture
  · rw [natInputs_past_zero, encard_singleton] at hpast
    norm_num at hpast
  · rw [encard_eq_top_iff.mpr (natInputs_future_infinite _)] at hfuture
    exact (not_lt_of_ge le_top) hfuture

-- One singleton side suffices at each boundary; the other side may remain infinite.
example : natInputs.SmallSides 2 := by
  intro t ht x _
  have h : t = 0 ∨ t = 1 := by
    change t ≤ 1 at ht
    omega
  rcases h with rfl | rfl
  · left
    rw [natInputs_past_zero, encard_singleton]
    norm_num
  · right
    rw [natInputs_future_one, encard_singleton]
    norm_num

end ComplexityTests.FrontierBranchingProgramCard
