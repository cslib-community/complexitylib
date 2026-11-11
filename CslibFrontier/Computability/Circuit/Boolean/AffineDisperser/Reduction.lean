/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Operations
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.Reduction

/-!
# Reductions and `0/6/7` accounting for `3.5n` gate elimination

Specialization of `Cslib.Circuits.Boolean.AffineDisperserCore.State.Reduction` to `3.5n` states
with `PairTame` affinity and `0/6/7` degree weights:

* `State.Exclusive`: no constraint has both an unpaired isolated parameter and another parameter as
  parents;
* `State.Reduction.wt_le`, `State.Reduction.wt_le_wt`, `State.Reduction.wt_le_of_exclusive`:
  parameter weight bounds under `0/6/7` weights;
* `State.Reduction.step_of_delete`: deleting a constraint with at most two parameter parents is a
  step;
* `State.Valid.reduction_restrict`, `State.Valid.fixConst`, `State.Valid.reduction_fixConst`:
  restrictions preserving `PairTame` affinity.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.Exclusive`: exclusive states.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Reduction.wt_le`,
  `State.Reduction.wt_le_of_exclusive`: weight bounds under `0/6/7` weights.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Reduction.step_of_delete`: single-deletion steps.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.fixConst`,
  `State.Valid.reduction_restrict`, `State.Valid.reduction_fixConst`: restriction reductions.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Exclusive states -/

/-- No constraint has both an unpaired isolated parameter and another parameter as parents. -/
@[expose] def Exclusive (S : State n) : Prop :=
  ∀ z ∈ S.unpaired, S.deg z = 1 → ∀ N ∈ S.children z, ∀ z' ∈ S.params, z' ≠ z →
    N ∉ S.children z'

/-- In an exclusive state, an unpaired parameter sharing a child with another parameter has
degree at least two. -/
theorem Exclusive.two_le_deg {S : State n} (h : S.Exclusive) {u x : ℕ} {N : ℕ ⊕ ℕ}
    (hu : u ∈ S.unpaired) (hNu : N ∈ S.children u) (hx : x ∈ S.params) (hxu : x ≠ u)
    (hNx : N ∈ S.children x) : 2 ≤ S.deg u := by
  have : 1 ≤ S.deg u := Finset.card_pos.2 ⟨N, hNu⟩
  by_contra hlt
  exact h u hu (by omega) N hNu x hx hxu hNx

/-! ### `0/6/7` weight accounting and single-deletion step -/

section WeightAccounting

variable {S S' : State n} {F : Finset ℕ} {D T : List (ℕ ⊕ ℕ)}

/-- A parameter that is not the partner of a member of `F`, and that no deletion reroutes to,
does not gain weight. -/
theorem Reduction.wt_le (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) (hT : ∀ N ∈ T, N ∉ S.children u) :
    S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · rw [wt_of_mem hu]
    exact (h.wt_le_weight hT).trans (weight_mono (Finset.card_le_card Finset.sdiff_subset))
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- A used parameter that is not the partner of a member of `F` gains at most one in weight. -/
private theorem Reduction.wt_le_add_one (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) (hdeg : 1 ≤ S.deg u) : S'.wt u ≤ S.wt u + 1 := by
  by_cases hu : u ∈ S.unpaired
  · rw [wt_of_mem hu, config_weight]
    have := six_le_weight hdeg
    have := S'.wt_le_bound u
    rw [config_weightBound] at this
    omega
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- An unpaired parameter does not gain weight when it has degree at least two if some deletion
may reroute to it. -/
theorem Reduction.wt_le_wt (h : Reduction f S S' F D T) {u : ℕ} (hu : u ∈ S.unpaired)
    (hT : ∀ N ∈ T, N ∈ S.children u → 2 ≤ S.deg u) : S'.wt u ≤ S.wt u := by
  by_cases hu' : u ∈ S'.unpaired
  · rw [wt_of_mem hu]
    by_cases hN : ∃ N ∈ T, N ∈ S.children u
    · obtain ⟨N, hN, hNu⟩ := hN
      rw [config_weight, weight_of_two_le (hT N hN hNu)]
      exact S'.wt_le_bound u
    · push Not at hN
      exact (h.wt_le_weight hN).trans
        (weight_mono (Finset.card_le_card Finset.sdiff_subset))
  · rw [wt_of_notMem hu']; exact Nat.zero_le _

/-- In an exclusive state, a parameter that is not the partner of a member of `F` does not gain
weight when every deletion that may reroute to it deletes a constraint with another parameter as a
parent. -/
theorem Reduction.wt_le_of_exclusive (h : Reduction f S S' F D T) (hS : S.Valid f)
    (hexcl : S.Exclusive) {u : ℕ} (hpart : ∀ x ∈ F, ¬ S.IsPartner x u)
    (hT : ∀ N ∈ T, N ∈ S.children u → ∃ x ∈ S.params, x ≠ u ∧ N ∈ S.children x) :
    S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · exact Reduction.wt_le_wt h hu fun N hN hNu => by
      obtain ⟨x, hx, hxu, hNx⟩ := hT N hN hNu
      exact hexcl.two_le_deg hu hNu hx hxu hNx
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- Deleting one constraint with at most two parameters as parents is a step of gate
elimination: only those parents may gain weight, each at most one. -/
theorem Reduction.step_of_delete {N : ℕ ⊕ ℕ} (h : Reduction f S S' ∅ [N] [N]) (hS : S.Valid f)
    (hN : (S.params.filter fun u => N ∈ S.children u).card ≤ 2) : Step f S S' := by
  refine h.step hS (by simp) (by simp) ?_
  have hW := h.W_le (fun _ => 0) (fun u => if N ∈ S.children u then 1 else 0) fun u hu => by
    by_cases hNu : N ∈ S.children u
    · rw [ite_eq_left hNu]
      exact Nat.add_le_add_right (Reduction.wt_le_add_one h hS
        (fun _ hx => absurd hx (Finset.notMem_empty _)) (Finset.card_pos.2 ⟨N, hNu⟩)) 0
    · rw [ite_eq_right hNu]
      exact Nat.add_le_add_right (Reduction.wt_le h hS
        (fun _ hx => absurd hx (Finset.notMem_empty _))
        fun N' hN' => by rw [List.mem_singleton] at hN'; exact hN' ▸ hNu) 0
  rw [Finset.sdiff_empty, ← Finset.card_filter] at hW
  simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.length_singleton,
    mul_zero, add_zero] at hW ⊢
  omega

end WeightAccounting

/-! ### Restrictions -/

/-- Restricting a parameter `x` to a constant, or to a literal of a remaining parameter `y` with
at least the children of `x` and, if `x` is paired, its partner, is a reduction. -/
theorem Valid.reduction_restrict {S : State n} (hS : S.Valid f) {x : ℕ} (hx : x ∈ S.params)
    {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x ∧ S.children x ⊆ S.children y ∧
      (S.Paired x → S.IsPartner x y)) :
    Reduction f S (S.restrict x ℓ (S.pairsAvoid x)) {x} [] [] := by
  have hdrop : ∀ pr ∈ S.pairs, pr ∉ S.pairsAvoid x →
      (pr.1 = x ∨ pr.2 = x) ∧ ∀ y, ℓ.Reads y → y = pr.1 ∨ y = pr.2 := fun pr hpr hP => by
    have hprx : pr.1 = x ∨ pr.2 = x := by
      by_contra hc
      exact hP (Finset.mem_filter.2 ⟨hpr, hc⟩)
    refine ⟨hprx, fun y hy => ?_⟩
    obtain ⟨pr', hpr', hxy⟩ := (hℓ y hy).2.2.2 ⟨pr, hpr, hprx⟩
    have := hS.pair_unique hpr hpr' hprx (by rcases hxy with h | h; exacts [Or.inl h.1, Or.inr h.1])
    subst this
    rcases hxy with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  let hrok : S.RestrictOK x ℓ (S.pairsAvoid x) :=
    { mem := hx
      reads := fun y hy => ⟨(hℓ y hy).1, (hℓ y hy).2.1⟩
      subset := Finset.filter_subset _ _
      avoid := fun _ hpr => not_or.1 (Finset.mem_filter.1 hpr).2
      drop := hdrop }
  exact Valid.reduction_restrict_of hS hx
    (fun y hy => ⟨(hℓ y hy).1, (hℓ y hy).2.1, (hℓ y hy).2.2.1⟩)
    (fun k τ hτ htame =>
      hS.phi_affine k (fun u => Function.update (τ u) x (ℓ.eval (τ u)))
        (isAffine_update hτ x (isAffine_lit_eval hτ ℓ)) (RestrictOK.pairTame hrok htame))
    fun _ _ => trivial

/-- Fixing a parameter to a constant preserves validity. -/
theorem Valid.fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    (S.fixConst w b).Valid f :=
  Valid.restrict hS
    { mem := hw
      reads := fun y hy => by simp [Lit.Reads, Lit.const] at hy
      subset := Finset.filter_subset _ _
      avoid := fun _ hpr => not_or.1 (Finset.mem_filter.1 hpr).2
      drop := fun pr hpr hP => by
        refine ⟨?_, fun y hy => by simp [Lit.Reads, Lit.const] at hy⟩
        by_contra h
        exact hP (Finset.mem_filter.2 ⟨hpr, h⟩) }

/-- Fixing a parameter to a constant is a reduction. -/
theorem Valid.reduction_fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params)
    (b : Bool) : Reduction f S (S.fixConst w b) {w} [] [] :=
  Valid.reduction_restrict hS hw fun y hy => by simp [Lit.Reads, Lit.const] at hy

end State

end Cslib.Circuits.Boolean.AffineDisperser
