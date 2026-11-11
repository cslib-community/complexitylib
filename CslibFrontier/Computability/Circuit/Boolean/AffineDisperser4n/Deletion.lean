/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Reduction
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic

/-!
# Deletion steps `(D1)`–`(D4)` for `4n - 10d` gate elimination

Whenever any of the four deletion rules `(D1)`–`(D4)` of [Mishra and Santhanam][MishraSanthanam2027]
applies to a valid state `S` for a `d`-affine disperser with `d < S.a`, one step reduces `m + s`
while keeping `Δa = 0` and `ΔW ≤ -1`.

* `(D1)`: a gate computing an input literal or constant on `EqnsHold val ∧ InZeroLocus val`.
* `(D2)`: a gate read by no other gate and not by the output.
* `(D3)`: an affine equation of at most two terms.
* `(D4)` (`unit_delete`): an unpaired parameter whose sole child is an affine equation `e`, which
  can be swapped with an auxiliary variable occurring in `e` and then dropped along with `e`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.DeletionAvailable`: one of `(D1)`–`(D4)` applies.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.not_out_reads_param`: when `d < S.a`, the
  output does not read a parameter directly.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_unit_delete`: performing `(D4)` on a
  unit-degree unpaired parameter.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_of_deletion`: every available
  deletion yields a valid step with `ΔW ≤ 10 Δa`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  deletion labels follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ}

/-- When `d < S.a`, the output literal of a valid state for a `d`-affine disperser cannot read a
parameter directly. -/
theorem Valid.not_out_reads_param {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) :
    ¬ S.out.Reads x := by
  intro hread
  refine hS.out_not_affine hf ha S.out.neg (Finset.singleton_subset_iff.2 hx)
    fun val _ _ => ?_
  have hread' : S.out.arg = .node x := hread
  simp only [Lit.eval, hread', Arg.eval_node, Finset.sum_singleton]
  cases S.out.neg <;> cases val x <;> rfl

/-- `(D4)` (unit delete): an unpaired parameter `x` with `S.children x = {.inr e}` swaps with an
auxiliary variable occurring in `e`, and then drops `e` and `x`, lowering `s` and `W` by `1`
while preserving `m`, `q`, and `a`. -/
theorem Valid.exists_unit_delete {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a)
    {x e : ℕ} (hx : x ∈ S.unpaired) (hcx : S.children x = {.inr e}) :
    ∃ S' : State n, S'.Valid f ∧ S'.m = S.m ∧ S'.s + 1 = S.s ∧ S'.q = S.q ∧ S'.a = S.a ∧
      S'.W + 1 ≤ S.W := by
  have hxpar : x ∈ S.params := (mem_unpaired.1 hx).1
  have hxu : ¬ S.Paired x := (mem_unpaired.1 hx).2
  obtain ⟨he, hxe⟩ := (SemiCircuit.inr_mem_children _).1 (by
    rw [hcx]; exact Finset.mem_singleton_self _)
  obtain ⟨Q, hQaux, c, T, haff, hxT⟩ :=
    SemiCircuit.exists_affineIn_of_mem_terms hS.wf hxpar he hxe
  let S₁ := S.swap x Q c T
  have hswap : S.SwapOK x Q c T := ⟨hxpar, hxu, hQaux, haff, hxT⟩
  have hS₁ : S₁.Valid f := hS.swap hswap
  have hm₁ : S₁.m = S.m := hS.swap_m hswap
  have hq₁ : S₁.q = S.q := rfl
  have hs₁ : S₁.s = S.s := swap_size S x Q c T
  have hW₁ : S₁.W ≤ S.W := hS.swap_W_le hswap (by simp [deg, hcx])
  have hdrop : S₁.DropEqnOK e x :=
    { mem := he
      aux := Finset.mem_insert_self _ _
      mem_terms := hxe
      only := fun e' he' hee hmem => by
        have : Sum.inr e' ∈ S.children x := (SemiCircuit.inr_mem_children _).2 ⟨he', hmem⟩
        rw [hcx, Finset.mem_singleton, Sum.inr.injEq] at this
        exact hee this
      gates := fun K hK hread => by
        have : Sum.inl K ∈ S.children x := (SemiCircuit.inl_mem_children _).2 ⟨hK, hread⟩
        rw [hcx, Finset.mem_singleton] at this
        cases this
      out := hS.not_out_reads_param hf ha hxpar }
  let S₂ := S₁.dropEqn e x
  have hS₂ : S₂.Valid f := hS₁.dropEqn hdrop
  have hm₂ : S₂.m = S.m := by
    change S₂.params.card = S.params.card
    rw [show S₂.params = S₁.params from dropEqn_params S₁ e x]
    exact hm₁
  have hs₂ : S₂.s + 1 = S.s := by rw [← hs₁]; exact dropEqn_size hdrop
  have hq₂ : S₂.q = S.q := rfl
  have ha₂ : S₂.a = S.a := by simp only [a, hm₂, hq₂]
  have hW₂ : S₂.W + 1 ≤ S.W := by
    have h := W_add_le (S := S₁) (S' := S₂) (N := S₁.params) le_rfl
      (by rw [dropEqn_params]) (fun _ => 0) (fun _ => 0) fun u hu => by
        simp only [add_zero]
        by_cases hup : S₁.Paired u
        · have hup₂ : S₂.Paired u := (paired_congr (dropEqn_pairs S₁ e x)).2 hup
          rw [wt_of_paired hup₂, wt_of_paired hup]
        · have hu2 : u ∈ S₂.unpaired := mem_unpaired.2
            ⟨by rwa [dropEqn_params], fun hp => hup ((paired_congr (dropEqn_pairs S₁ e x)).1 hp)⟩
          have hu1 : u ∈ S₁.unpaired := mem_unpaired.2 ⟨hu, hup⟩
          rw [wt_of_mem hu2, wt_of_mem hu1]
          exact weight_mono (by
            unfold deg
            rw [dropEqn_children]
            exact Finset.card_le_card (Finset.erase_subset _ _))
    simp only [Finset.sum_const_zero, add_zero, hq₂, ← hq₁] at h
    omega
  exact ⟨S₂, hS₂, hm₂, hs₂, hq₂, ha₂, hW₂⟩

/-- Whether one of the four deletion rules `(D1)`–`(D4)` applies to `S`:
* `(D1)`: a gate computing a literal or constant on `EqnsHold val ∧ InZeroLocus val` whose inputs
  are at most those of the gate;
* `(D2)`: a gate read by no gate and not by the output;
* `(D3)`: an equation of at most two terms;
* `(D4)`: an unpaired parameter whose sole child is an affine equation. -/
@[expose] def DeletionAvailable (S : State n) : Prop :=
  (∃ J ∈ S.gates, ∃ ℓ : Lit, (∀ t, ℓ.Reads t → (S.gate J).Reads t) ∧
    ∀ val, S.EqnsHold val → S.InZeroLocus val → (S.gate J).eval val = ℓ.eval val) ∨
  (∃ J ∈ S.gates, (∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J) ∨
  (∃ e ∈ S.eqns, (S.eqn e).terms.card ≤ 2) ∨
  (∃ x ∈ S.unpaired, ∃ e, S.children x = {.inr e})

/-- Whenever any deletion `(D1)`–`(D4)` is available and `d < S.a`, there is a valid step
strictly reducing `m + s` with `Δa = 0` and `ΔW ≤ -1`. -/
theorem Valid.step_of_deletion {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a)
    (hdel : S.DeletionAvailable) : ∃ S', Step f S S' := by
  rcases hdel with ⟨J, hJ, ℓ, hreads, heval⟩ | ⟨J, hJ, hgates, hout⟩ |
      ⟨e, he, hcard⟩ | ⟨x, hx, e, hcx⟩
  · exact ⟨_, (hS.reduction_deleteGate ⟨hJ, hreads, Or.inl heval⟩
      (fun _ _ => List.mem_singleton_self _)).step_of_delete hS⟩
  · exact ⟨_, (hS.reduction_deleteGate (ℓ := Lit.const false)
      ⟨hJ, (fun _ h => by cases h), Or.inr ⟨hgates, hout⟩⟩
      fun _ h => by cases h).step_of_delete hS⟩
  · obtain ⟨S', hred⟩ := hS.exists_reduction_delete (N := .inr e) ⟨he, hcard⟩
    exact ⟨S', hred.step_of_delete hS⟩
  · obtain ⟨S', hS', hm, hs, _, ha', hW⟩ := hS.exists_unit_delete hf ha hx hcx
    exact ⟨S', ⟨hS', by omega, by omega, by omega, by omega⟩⟩

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
