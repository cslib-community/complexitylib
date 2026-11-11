/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Operations
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Reparameterisation

/-!
# Reparameterisation of `3.5n` gate-elimination states

Two reparameterisation operations for `3.5n` states:

* `State.Valid.swap`: specialization of the shared affine reparameterisation `(AR)`
  (`AffineDisperserCore.State.swap`) preserving `PairTame` affinity;
* `State.quad`: the quadratic reparameterisation `(QR)` ([MishraSanthanam2026], §2.4 eq. (3),
  §3.2, and §4.3), substituting `z = D + (x + α)(y + β) + γ + c`, moving `D` into the parameters,
  deleting `G` and `D`, and pairing `x` with `y`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.quad`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.QuadOK`: the quadratic reparameterisation and
  its hypotheses.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.swap`: `(AR)` preserves validity.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.quad`: `(QR)` preserves validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Affine reparameterisation (AR) -/

/-- The affine reparameterisation preserves validity. -/
theorem Valid.swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).Valid f := by
  have hnx : ∀ pr ∈ S.pairs, pr.1 ≠ x ∧ pr.2 ≠ x := fun pr hpr =>
    ⟨fun he => h.unpaired ⟨pr, hpr, Or.inl he⟩, fun he => h.unpaired ⟨pr, hpr, Or.inr he⟩⟩
  refine Valid.swap_of hS h fun k τ hτ htame => ?_
  refine hS.phi_affine k (fun u => Function.update (τ u) x
      (τ u Q + c + ∑ j ∈ T.erase x, τ u j))
    (isAffine_update hτ x (isAffine_add_add_sum hτ Q c (T.erase x))) fun pr hpr => ?_
  obtain ⟨hx1, hx2⟩ := hnx pr hpr
  rcases htame pr hpr with ht | ht | ht
  · exact Or.inl fun u v => by
      dsimp only
      rw [Function.update_of_ne hx1, Function.update_of_ne hx1]
      exact ht u v
  · exact Or.inr (Or.inl fun u v => by
      dsimp only
      rw [Function.update_of_ne hx2, Function.update_of_ne hx2]
      exact ht u v)
  · exact Or.inr (Or.inr fun u v => by
      dsimp only
      rw [Function.update_of_ne hx1, Function.update_of_ne hx1,
        Function.update_of_ne hx2, Function.update_of_ne hx2]
      exact ht u v)

/-! ### Quadratic reparameterisation (QR) -/

/-- Along an affine family on which the pair `(x, y)` is tame, the product
`(u x + α) (u y + β)` is affine. -/
private theorem isAffine_mul_of_pairTame {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ)
    {x y : ℕ} (ht : PairTame τ (x, y)) (α β : Bool) :
    IsAffine fun u => (τ u x + α) * (τ u y + β) := by
  intro u v w
  dsimp only
  have hy := congrFun (hτ u v w) y
  have hx := congrFun (hτ u v w) x
  simp only [Pi.add_apply] at hx hy
  rcases ht with ht | ht | ht
  · have h0 : ∀ u', τ u' x = τ 0 x := fun u' => ht u' 0
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hy]
    generalize τ 0 x = a; generalize τ u y = b₁; generalize τ v y = b₂; generalize τ w y = b₃
    revert a b₁ b₂ b₃ α β; decide
  · have h0 : ∀ u', τ u' y = τ 0 y := fun u' => ht u' 0
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hx]
    generalize τ 0 y = a; generalize τ u x = b₁; generalize τ v x = b₂; generalize τ w x = b₃
    revert a b₁ b₂ b₃ α β; decide
  · have h0 : ∀ u', τ u' x = τ u' y + (τ 0 x + τ 0 y) := fun u' => by
      have := ht u' 0
      simp only at this
      rw [← this]
      generalize τ u' x = a; generalize τ u' y = b
      revert a b; decide
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hy]
    generalize τ 0 x + τ 0 y = a; generalize τ u y = b₁; generalize τ v y = b₂
    generalize τ w y = b₃
    revert a b₁ b₂ b₃ α β; decide

/-- The quadratic reparameterisation: for an AND-type gate `G = (x + α)(y + β) + γ` whose only
child is the XOR-type gate `D = G + z + c`, where `z` is an isolated parameter, substitute
`z = D + G + c` in the parameter map, turn `D` into a parameter (it computes the new parameter
`w` of the source), delete the gates `G` and `D`, and pair `x` with `y`. -/
@[expose] def quad (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : State n where
  toSemiCircuit := S.toSemiCircuit.quad z G D
  pairs := insert (x, y) S.pairs
  phi val := S.phi (Function.update val z (val D + ((val x + α) * (val y + β) + γ) + c))

/-- The hypotheses of the quadratic reparameterisation: the configuration of
`SemiCircuit.QuadOK` on unpaired parameters. -/
structure QuadOK (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : Prop
    extends SemiCircuit.QuadOK S.toSemiCircuit x y z G D α β γ c where
  /-- `x` is not paired. -/
  unpaired_x : ¬ S.Paired x
  /-- `y` is not paired. -/
  unpaired_y : ¬ S.Paired y
  /-- `z` is not paired. -/
  unpaired_z : ¬ S.Paired z

/-- The quadratic reparameterisation replaces `z` with `D` in `S.params`. -/
@[simp] theorem quad_params (S : State n) (x y z G D : ℕ) (α β γ c : Bool) :
    (S.quad x y z G D α β γ c).params = insert D (S.params.erase z) := rfl

/-- The quadratic reparameterisation inserts `(x, y)` into `S.pairs`. -/
@[simp] theorem quad_pairs (S : State n) (x y z G D : ℕ) (α β γ c : Bool) :
    (S.quad x y z G D α β γ c).pairs = insert (x, y) S.pairs := rfl

/-- The quadratic reparameterisation decreases the size of the state by `2`. -/
theorem quad_size {S : State n} {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) : (S.quad x y z G D α β γ c).size + 2 = S.size := by
  have h1 := Finset.card_erase_add_one h.mem_D
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨h.G_ne_D, h.mem_G⟩)
  simp only [SemiCircuit.size] at *
  change ((S.gates.erase D).erase G).card + S.eqns.card + 2 = _
  omega

/-- After the quadratic reparameterisation, the children of `w` are contained in `S.children w`
with `.inl D` and `.inl G` removed. -/
theorem quad_children_subset (S : State n) (x y z G D : ℕ) (α β γ c : Bool) (w : ℕ) :
    (S.quad x y z G D α β γ c).children w ⊆ ((S.children w).erase (.inl D)).erase (.inl G) := by
  intro v hv
  rcases v with K | e
  · simp only [SemiCircuit.inl_mem_children] at hv
    change K ∈ (S.gates.erase D).erase G ∧ _ at hv
    obtain ⟨hK, hr⟩ := hv
    simp only [Finset.mem_erase] at hK ⊢
    exact ⟨fun he => hK.1 (Sum.inl.inj he), fun he => hK.2.1 (Sum.inl.inj he),
      (SemiCircuit.inl_mem_children _).2 ⟨hK.2.2, hr⟩⟩
  · simp only [SemiCircuit.inr_mem_children] at hv
    simp only [Finset.mem_erase, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact (SemiCircuit.inr_mem_children _).2 hv

namespace QuadOK

variable {S : State n} {x y z G D : ℕ} {α β γ c : Bool} (h : S.QuadOK x y z G D α β γ c)
include h

private theorem pair_mem (hS : S.Valid f) : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs,
    pr.1 ∈ (S.quad x y z G D α β γ c).params ∧ pr.2 ∈ (S.quad x y z G D α β γ c).params ∧
      pr.1 ≠ pr.2 := by
  intro pr hpr
  rcases Finset.mem_insert.1 hpr with rfl | hpr
  · exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.x_ne_z, h.mem_x⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.y_ne_z, h.mem_y⟩), h.x_ne_y⟩
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr hpr
    have hz1 : pr.1 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inl he⟩
    have hz2 : pr.2 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inr he⟩
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz1, h1⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz2, h2⟩), h12⟩

private theorem pairs_disjoint (hS : S.Valid f) : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs,
    ∀ pr' ∈ (S.quad x y z G D α β γ c).pairs, pr ≠ pr' →
      pr.1 ≠ pr'.1 ∧ pr.1 ≠ pr'.2 ∧ pr.2 ≠ pr'.1 ∧ pr.2 ≠ pr'.2 := by
  have hnew : ∀ pr ∈ S.pairs, x ≠ pr.1 ∧ x ≠ pr.2 ∧ y ≠ pr.1 ∧ y ≠ pr.2 := fun pr hpr =>
    ⟨fun he => h.unpaired_x ⟨pr, hpr, Or.inl he.symm⟩,
      fun he => h.unpaired_x ⟨pr, hpr, Or.inr he.symm⟩,
      fun he => h.unpaired_y ⟨pr, hpr, Or.inl he.symm⟩,
      fun he => h.unpaired_y ⟨pr, hpr, Or.inr he.symm⟩⟩
  intro pr hpr pr' hpr' hne
  rcases Finset.mem_insert.1 hpr with rfl | hpr <;>
    rcases Finset.mem_insert.1 hpr' with rfl | hpr'
  · exact absurd rfl hne
  · exact hnew pr' hpr'
  · obtain ⟨h1, h2, h3, h4⟩ := hnew pr hpr
    exact ⟨Ne.symm h1, Ne.symm h3, Ne.symm h2, Ne.symm h4⟩
  · exact hS.pairs_disjoint pr hpr pr' hpr' hne

private theorem affine (hS : S.Valid f) {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ)
    (htame : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs, PairTame τ pr) :
    ∃ τ' : BitString k → ℕ → Bool, IsAffine τ' ∧ (∀ pr ∈ S.pairs, PairTame τ' pr) ∧
      ∀ u, ∀ j ∈ S.params, τ' u j = quadValue x y z G D α β γ c (τ u) j := by
  refine ⟨fun u => Function.update (τ u) z (τ u D + ((τ u x + α) * (τ u y + β) + γ) + c),
    ?_, fun pr hpr => ?_, fun u j hj => ?_⟩
  · refine isAffine_update hτ z fun u v w => ?_
    have hm := isAffine_mul_of_pairTame hτ (htame (x, y) (Finset.mem_insert_self _ _)) α β u v w
    have hD := congrFun (hτ u v w) D
    simp only [Pi.add_apply] at hm hD
    simp only [hD, hm]
    generalize τ u D = a₁; generalize τ v D = a₂; generalize τ w D = a₃
    generalize (τ u x + α) * (τ u y + β) = b₁; generalize (τ v x + α) * (τ v y + β) = b₂
    generalize (τ w x + α) * (τ w y + β) = b₃
    cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases γ <;>
      cases c <;> rfl
  · have hz1 : pr.1 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inl he⟩
    have hz2 : pr.2 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inr he⟩
    rcases htame pr (Finset.mem_insert_of_mem hpr) with ht | ht | ht
    · exact Or.inl fun u v => by simp only [Function.update_of_ne hz1]; exact ht u v
    · exact Or.inr (Or.inl fun u v => by simp only [Function.update_of_ne hz2]; exact ht u v)
    · exact Or.inr (Or.inr fun u v => by
        simp only [Function.update_of_ne hz1, Function.update_of_ne hz2]; exact ht u v)
  · have hjG : j ≠ G := fun he => hS.wf.notMem_gates_of_mem_params hj (he ▸ h.mem_G)
    simp only [quadValue, Function.update_of_ne hjG]

end QuadOK

/-- The quadratic reparameterisation preserves validity. -/
theorem Valid.quad {S : State n} (hS : S.Valid f) {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) : (S.quad x y z G D α β γ c).Valid f := by
  have hgp : ∀ {i}, i ∈ S.gates → i ∉ S.params := fun hg => hS.wf.notMem_params_of_mem_gates hg
  have hxG : x ≠ G := fun he => hgp h.mem_G (he ▸ h.mem_x)
  have hyG : y ≠ G := fun he => hgp h.mem_G (he ▸ h.mem_y)
  set σ := quadValue x y z G D α β γ c
  have hσ : ∀ val i, i ≠ z → i ≠ G → σ val i = val i := fun val i hz hG => by
    simp only [σ, quadValue, Function.update_of_ne hG, Function.update_of_ne hz]
  have hσz : ∀ val, σ val z = val D + ((val x + α) * (val y + β) + γ) + c := fun val => by
    have hzG : z ≠ G := by rintro rfl; exact hgp h.mem_G h.mem_z
    simp only [σ, quadValue, Function.update_of_ne hzG, Function.update_self]
  refine Valid.of_transport hS (σ := σ) (hS.wf.quad h.toQuadOK)
    { pair_mem := h.pair_mem hS
      pairs_disjoint := h.pairs_disjoint hS
      phi := fun val => hS.phi_congr _ _ fun j hj => ?_
      phi_affine := fun k τ hτ htame => by
        obtain ⟨τ', hτ', htame', hagree⟩ := h.affine hS hτ htame
        have hcomp := hS.phi_affine k τ' hτ' htame'
        have heq : (S.quad x y z G D α β γ c).phi ∘ τ = S.phi ∘ τ' := by
          funext u
          exact hS.phi_congr _ _ fun j hj => by
            have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ hj)
            simpa only [σ, quadValue, Function.update_of_ne hjG] using (hagree u j hj).symm
        rwa [heq]
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      consistent := fun val hval => (h.toQuadOK.consistent hS.wf hval).1
      locus := fun _ _ => trivial
      out := fun val hval _ => (h.toQuadOK.consistent hS.wf hval).2 }
  · have hjG : j ≠ G := by rintro rfl; exact hgp h.mem_G hj
    simp only [σ, quadValue, Function.update_of_ne hjG]
  · have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ hj)
    by_cases hjz : j = z
    · subst hjz
      have hD := hv D (Finset.mem_insert_self _ _)
      have hx := hv x (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.x_ne_z, h.mem_x⟩))
      have hy := hv y (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.y_ne_z, h.mem_y⟩))
      rw [hσz, hσz, hD, hx, hy]
    · rw [hσ val j hjz hjG, hσ val' j hjz hjG]
      exact hv j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjz, hj⟩))
  · rcases Finset.mem_insert.1 hj with rfl | hj
    · have hz := hv z h.mem_z
      have hx := hv x h.mem_x
      have hy := hv y h.mem_y
      rw [hσ val x h.x_ne_z hxG, hσ val' x h.x_ne_z hxG] at hx
      rw [hσ val y h.y_ne_z hyG, hσ val' y h.y_ne_z hyG] at hy
      rw [hσz, hσz, hx, hy] at hz
      simpa using hz
    · have := hv j (Finset.mem_of_mem_erase hj)
      have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ Finset.mem_of_mem_erase hj)
      rwa [hσ val j (Finset.ne_of_mem_erase hj) hjG,
        hσ val' j (Finset.ne_of_mem_erase hj) hjG] at this

end State

end Cslib.Circuits.Boolean.AffineDisperser
