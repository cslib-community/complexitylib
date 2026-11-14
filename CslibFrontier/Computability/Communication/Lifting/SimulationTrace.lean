/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DensitySimulation
public import CslibFrontier.Computability.Communication.Lifting.Volume
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite density simulation traces

A trace executes actual density steps on the two sources, swapping the gadget when Bob speaks.
The trace records the total number of queried coordinates and transmitted steps. Each transition
restricts the sources and removes its queries from the free coordinates. The volume theorem
multiplies the one-step guarantees; safety hypotheses are needed to construct steps, rather than
being hidden in the volume conclusion. This module does not yet construct a decision tree.
-/

@[expose] public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- An executed finite trace of density-preserving steps, with the actual query answers supplied.
The two natural-number indices count steps and total queried coordinates. -/
inductive DensityTrace (g : Fin m → Fin m → Bool) (τ σ : ℝ) :
    Finset (Fin n) → Finset (Fin n → Fin m) → Finset (Fin n → Fin m) →
    Finset (Fin n) → Finset (Fin n → Fin m) → Finset (Fin n → Fin m) → ℕ → ℕ → Prop where
  /-- Stop without changing the rectangle. -/
  | stop (F X Y) : DensityTrace g τ σ F X Y F X Y 0 0
  /-- Execute an Alice step and continue. -/
  | alice {F X Y F' X' Y' c q} (st : DensityStep n m) (send) (answer)
      (valid : st.Valid g τ σ F X Y send)
      (tail : DensityTrace g τ σ (F \ st.queried) st.speaker (st.listener answer)
        F' X' Y' c q) :
      DensityTrace g τ σ F X Y F' X' Y' (c + 1) (#st.queried + q)
  /-- Execute a Bob step, reversing the gadget arguments, and continue. -/
  | bob {F X Y F' X' Y' c q} (st : DensityStep n m) (send) (answer)
      (valid : st.Valid (fun y x => g x y) τ σ F Y X send)
      (tail : DensityTrace g τ σ (F \ st.queried) (st.listener answer) st.speaker
        F' X' Y' c q) :
      DensityTrace g τ σ F X Y F' X' Y' (c + 1) (#st.queried + q)

/-- The source-size loss of a trace is at most eight per step and `2τ` per query. -/
theorem DensityTrace.volume {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X Y X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F X Y F' X' Y' c q)
    (hτ : 0 ≤ τ) :
    (#X : ℝ) * #Y ≤ 8 ^ c * (2 * τ) ^ q * #X' * #Y' := by
  induction h with
  | stop => simp
  | @alice F X Y F' X' Y' c q st send answer valid tail ih =>
    calc
      _ ≤ (8 * (2 * τ) ^ #st.queried) *
          ((#st.speaker : ℝ) * #(st.listener answer)) := by
        simpa only [mul_assoc] using valid.volume answer
      _ ≤ (8 * (2 * τ) ^ #st.queried) *
          (8 ^ c * (2 * τ) ^ q * #X' * #Y') :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ, pow_add]; ring
  | @bob F X Y F' X' Y' c q st send answer valid tail ih =>
    calc
      _ ≤ (8 * (2 * τ) ^ #st.queried) *
          ((#(st.listener answer) : ℝ) * #st.speaker) := by
        nlinarith [valid.volume answer]
      _ ≤ (8 * (2 * τ) ^ #st.queried) *
          (8 ^ c * (2 * τ) ^ q * #X' * #Y') :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ, pow_add]; ring

/-- Queries in a trace are fresh: their total number is precisely the loss of free coordinates. -/
theorem DensityTrace.card_free {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X Y X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F X Y F' X' Y' c q) :
    #F' + q = #F := by
  induction h with
  | stop => simp
  | alice st send answer valid tail ih =>
    have := card_sdiff_add_card_eq_card valid.queried_subset
    omega
  | bob st send answer valid tail ih =>
    have := card_sdiff_add_card_eq_card valid.queried_subset
    omega

/-- Every executed step only removes source elements. -/
theorem DensityTrace.subsets {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X Y X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F X Y F' X' Y' c q) : X' ⊆ X ∧ Y' ⊆ Y := by
  induction h with
  | stop => exact ⟨Subset.rfl, Subset.rfl⟩
  | alice st send answer valid tail ih =>
    exact ⟨ih.1.trans valid.speaker_subset, ih.2.trans (valid.listener_subset answer)⟩
  | bob st send answer valid tail ih =>
    exact ⟨ih.1.trans (valid.listener_subset answer), ih.2.trans valid.speaker_subset⟩

/-- Nonempty starting sources remain nonempty along an executed trace. -/
theorem DensityTrace.nonempty {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X Y X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F X Y F' X' Y' c q)
    (hX : X.Nonempty) (hY : Y.Nonempty) : X'.Nonempty ∧ Y'.Nonempty := by
  induction h with
  | stop => exact ⟨hX, hY⟩
  | alice st send answer valid tail ih =>
    exact ih valid.speaker_nonempty (valid.listener_nonempty answer)
  | bob st send answer valid tail ih =>
    exact ih (valid.listener_nonempty answer) valid.speaker_nonempty

/-- A full starting rectangle gives the exact initial volume budget used in amortization. -/
theorem DensityTrace.full_volume {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F univ univ F' X' Y' c q) (hτ : 0 ≤ τ) :
    (m : ℝ) ^ (2 * n) ≤ 8 ^ c * (2 * τ) ^ q * #X' * #Y' := by
  have hv := h.volume hτ
  simpa [Fintype.card_fun, pow_mul, pow_two, mul_pow] using hv

private theorem extend_fixed_partition {F I : Finset (Fin n)}
    {X Y : Finset (Fin n → Fin m)} {q : ℕ} (hIF : I ⊆ F)
    (hfixed : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ I, x i = x' i)
    (h : ∃ AX AY : Finset (Fin n), AX ⊆ F \ I ∧ AY ⊆ F \ I ∧
      Disjoint AX AY ∧ #AX + #AY = q ∧
      (∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ AX, x i = x' i) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, ∀ i ∈ AY, y i = y' i)) :
    ∃ AX AY : Finset (Fin n), AX ⊆ F ∧ AY ⊆ F ∧ Disjoint AX AY ∧
      #AX + #AY = #I + q ∧
      (∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ AX, x i = x' i) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, ∀ i ∈ AY, y i = y' i) := by
  obtain ⟨AX, AY, hAX, hAY, hd, hq, hx, hy⟩ := h
  have hIA : Disjoint I AX := disjoint_left.mpr fun i hi ha =>
    (mem_sdiff.mp (hAX ha)).2 hi
  have hIY : Disjoint I AY := disjoint_left.mpr fun i hi ha =>
    (mem_sdiff.mp (hAY ha)).2 hi
  refine ⟨I ∪ AX, AY, union_subset hIF (hAX.trans sdiff_subset),
    hAY.trans sdiff_subset, disjoint_union_left.mpr ⟨hIY, hd⟩, ?_, ?_, hy⟩
  · rw [card_union_of_disjoint hIA]; omega
  · intro x hx' x' hx'' i hi
    rcases mem_union.mp hi with hi | hi
    · exact hfixed x hx' x' hx'' i hi
    · exact hx x hx' x' hx'' i hi

/-- All queried coordinates can be assigned disjointly to the player whose source was fixed.
This derives the fixed-coordinate hypotheses needed for volume amortization from the trace. -/
theorem DensityTrace.fixed_partition {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X Y X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F X Y F' X' Y' c q) :
    ∃ AX AY : Finset (Fin n), AX ⊆ F ∧ AY ⊆ F ∧ Disjoint AX AY ∧ #AX + #AY = q ∧
      (∀ x ∈ X', ∀ x' ∈ X', ∀ i ∈ AX, x i = x' i) ∧
      (∀ y ∈ Y', ∀ y' ∈ Y', ∀ i ∈ AY, y i = y' i) := by
  induction h with
  | stop => exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | alice st send answer valid tail ih =>
    apply extend_fixed_partition valid.queried_subset ?_ ih
    intro x hx x' hx' i hi
    exact (valid.fixed x (tail.subsets.1 hx) i hi).trans
      (valid.fixed x' (tail.subsets.1 hx') i hi).symm
  | bob st send answer valid tail ih =>
    obtain ⟨AX, AY, hAX, hAY, hd, hq, hx, hy⟩ := ih
    have hswap := extend_fixed_partition (q := #AX + #AY) valid.queried_subset
      (fun y hy y' hy' i hi => (valid.fixed y (tail.subsets.2 hy) i hi).trans
        (valid.fixed y' (tail.subsets.2 hy') i hi).symm)
      ⟨AY, AX, hAY, hAX, hd.symm, by omega, hy, hx⟩
    obtain ⟨AY, AX, hAY, hAX, hd, hq, hy, hx⟩ := hswap
    exact ⟨AX, AY, hAX, hAY, hd.symm, by omega, hx, hy⟩

/-- The query exponent is bounded by the number of executed steps, with no separate endpoint
fixedness or budget assumption: both are derived from the actual trace. -/
theorem DensityTrace.query_bound {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F F' : Finset (Fin n)} {X' Y' : Finset (Fin n → Fin m)} {c q : ℕ}
    (h : DensityTrace g τ σ F univ univ F' X' Y' c q)
    (hm : 0 < m) (hτ : 0 < τ) :
    ((m : ℝ) / (2 * τ)) ^ q ≤ 8 ^ c := by
  obtain ⟨AX, AY, _, _, _, hq, hx, hy⟩ := h.fixed_partition
  have hv := h.full_volume hτ.le
  rw [← hq] at hv ⊢
  exact pow_div_le_of_volume_budget hm hτ (by positivity) hx hy hv

/-- Concatenate actual density traces, adding their step and query counts. -/
theorem DensityTrace.append {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F₀ F₁ F₂ : Finset (Fin n)} {X₀ Y₀ X₁ Y₁ X₂ Y₂ : Finset (Fin n → Fin m)}
    {c₁ q₁ c₂ q₂ : ℕ}
    (h₁ : DensityTrace g τ σ F₀ X₀ Y₀ F₁ X₁ Y₁ c₁ q₁)
    (h₂ : DensityTrace g τ σ F₁ X₁ Y₁ F₂ X₂ Y₂ c₂ q₂) :
    DensityTrace g τ σ F₀ X₀ Y₀ F₂ X₂ Y₂ (c₁ + c₂) (q₁ + q₂) := by
  induction h₁ with
  | stop => simpa using h₂
  | alice st send answer valid tail ih =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      DensityTrace.alice st send answer valid (ih h₂)
  | bob st send answer valid tail ih =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      DensityTrace.bob st send answer valid (ih h₂)

end Cslib.Communication.Lifting
