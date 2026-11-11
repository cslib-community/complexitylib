/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Operations
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.Reduction

/-!
# Zero-locus reductions and `0/6` potential accounting for `4n - 10d`

Specialization of `Cslib.Circuits.Boolean.AffineDisperserCore.State.Reduction` to `4n - 10d`
states with zero-locus pairs and `0/6` degree weights:

* `State.Reduction.wt_le`: non-partners never gain weight, even when deletions reroute to them;
* `State.Reduction.step_of_delete`: deleting any deletable constraint is always a step;
* `State.Valid.reduction_restrict`, `State.Valid.fixConst`, `State.Valid.reduction_fixConst`:
  zero-locus restrictions `(UF)` and `(PF)`.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Reduction.wt_le`: non-partners never gain
  weight.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Reduction.step_of_delete`: single deletion step.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.fixConst`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.reduction_restrict`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.reduction_fixConst`: restrictions `(UF)`
  and `(PF)`.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### `0/6` weight and single-deletion step -/

/-- Under `0/6` weights, a parameter that is not the partner of a member of `F` never gains
weight, even if deletions reroute to it. -/
theorem Reduction.wt_le {S S' : State n} {F : Finset ℕ} {D T : List (ℕ ⊕ ℕ)}
    (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) : S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · by_cases h0 : S.deg u = 0
    · have hempty : S.children u = ∅ := Finset.card_eq_zero.1 h0
      have hT : ∀ N ∈ T, N ∉ S.children u := fun N _ hNu => by
        rw [hempty] at hNu; exact Finset.notMem_empty N hNu
      have hwt := h.wt_le_weight hT
      rw [hempty, Finset.empty_sdiff, Finset.card_empty,
        show config.weight 0 = 0 from rfl] at hwt
      exact hwt.trans (Nat.zero_le _)
    · rw [wt_of_mem hu, show config.weight (S.deg u) = weight (S.deg u) from rfl,
        weight_of_one_le (by omega)]
      exact S'.wt_le_bound u
  · rw [h.wt_eq_zero hS hu hpart]
    exact Nat.zero_le _

/-- Deleting a single constraint is always a step of gate elimination under `0/6` weights:
no parameter can gain weight. -/
theorem Reduction.step_of_delete {S S' : State n} {N : ℕ ⊕ ℕ}
    (h : Reduction f S S' ∅ [N] [N]) (hS : S.Valid f) : Step f S S' := by
  refine h.step hS (by simp) (by simp) ?_
  have hW := h.W_le (fun _ => 0) (fun _ => 0) fun u _ =>
    Nat.add_le_add_right (Reduction.wt_le h hS fun _ hx => absurd hx (Finset.notMem_empty _)) 0
  simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.length_singleton,
    mul_zero, add_zero] at hW ⊢
  omega

/-! ### Restrictions `(UF)` and `(PF)` -/

/-- Restricting a parameter `x` to a constant or to a literal of a remaining parameter `y` having
at least `x`'s children is a reduction whenever every pair containing `x` is satisfied on the
substitution. -/
theorem Valid.reduction_restrict {S : State n} (hS : S.Valid f) {x : ℕ} (hx : x ∈ S.params)
    {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x ∧ S.children x ⊆ S.children y)
    (hdrop : ∀ pr ∈ S.pairs, pr.Contains x →
      ∀ val, pr.Holds (Function.update val x (ℓ.eval val))) :
    Reduction f S (S.restrict x ℓ (S.pairsAvoid x)) {x} [] [] :=
  Valid.reduction_restrict_of hS hx hℓ
    (hS.phi_affine.comp (isAffine_update isAffine_id x (isAffine_lit_eval isAffine_id ℓ)))
    fun val hlocus pr hpr => by
      by_cases hprP : pr ∈ S.pairsAvoid x
      · have hav : ¬ pr.Contains x := (Finset.mem_filter.1 hprP).2
        have h1 : pr.fst ≠ x := fun he => hav (Or.inl he)
        have h2 : pr.snd ≠ x := fun he => hav (Or.inr he)
        exact (ZeroPair.holds_congr (Function.update_of_ne h1 (ℓ.eval val) val)
          (Function.update_of_ne h2 (ℓ.eval val) val)).2 (hlocus pr hprP)
      · have hprx : pr.Contains x := by
          by_contra hc
          exact hprP (Finset.mem_filter.2 ⟨hpr, hc⟩)
        exact hdrop pr hpr hprx val

private theorem restrictOK_fixConst {S : State n} {w : ℕ} (hw : w ∈ S.params) {b : Bool}
    (hb : ∀ pr ∈ S.pairs, pr.Contains w → b = pr.bias w) :
    S.RestrictOK w (Lit.const b) (S.pairsAvoid w) where
  mem := hw
  reads y hy := by simp [Lit.Reads, Lit.const] at hy
  subset := Finset.filter_subset _ _
  avoid pr hpr := (Finset.mem_filter.1 hpr).2
  drop pr hpr hP val := by
    have hprw : pr.Contains w := by
      by_contra hc
      exact hP (Finset.mem_filter.2 ⟨hpr, hc⟩)
    exact ZeroPair.holds_of_eq_bias hprw (by simp [Lit.eval_const, hb pr hpr hprw])

/-- Fixing a parameter to a constant preserves validity when any pair containing it has matching
bias. -/
theorem Valid.fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params) {b : Bool}
    (hb : ∀ pr ∈ S.pairs, pr.Contains w → b = pr.bias w) :
    (S.fixConst w b).Valid f :=
  Valid.restrict hS (restrictOK_fixConst hw hb)

/-- Fixing a parameter to a constant (with matching bias if paired) is a reduction. -/
theorem Valid.reduction_fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params)
    {b : Bool} (hb : ∀ pr ∈ S.pairs, pr.Contains w → b = pr.bias w) :
    Reduction f S (S.fixConst w b) {w} [] [] :=
  Valid.reduction_restrict hS hw (fun y hy => by simp [Lit.Reads, Lit.const] at hy)
    fun pr hpr hpw val => ZeroPair.holds_of_eq_bias hpw (by simp [Lit.eval_const, hb pr hpr hpw])

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
