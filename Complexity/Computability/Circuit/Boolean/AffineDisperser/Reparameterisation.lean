/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Operations
public import Complexity.Computability.Circuit.Boolean.SemiCircuit.Reparameterisation

/-!
# Affine and quadratic reparameterisations

The reparameterisations (AR) and (QR) of [Mishra and Santhanam, Section 3.2][MishraSanthanam2026]
on states of gate elimination. Both change the parameters bijectively, so the image of the
parameter map is unchanged:

* `State.swap`: an unpaired parameter `x` and an auxiliary variable `Q` depending on it exchange
  their roles, and the parameter map substitutes `x = Q + c + ∑ j ∈ T \ {x}, u j`; no equation or
  gate changes (`State.Valid.swap`);
* `State.quad`: for an AND-type gate `G = (x + α)(y + β) + γ` whose only child is the XOR-type
  gate `D = G + z + c` reading an isolated parameter `z`, the parameter map substitutes
  `z = D + G + c`, the gate `D` becomes a parameter, `G` and `D` are deleted and `x` is paired with
  `y` (`State.Valid.quad`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.swap`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.SwapOK`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.quad`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.QuadOK`: the reparameterisations and their
  hypotheses.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.swap`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.quad`: they preserve validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Affine reparameterisation (AR) -/

/-- Exchange the parameter `x` with the auxiliary variable `Q = c + ∑ j ∈ T, u j` depending on
it: `Q` becomes a parameter, `x` an auxiliary variable, and the parameter map substitutes
`x = Q + c + ∑ j ∈ T \ {x}, u j`. No equation or gate changes. -/
def swap (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : State n where
  toSemiCircuit := S.toSemiCircuit.swap x Q
  pairs := S.pairs
  phi val := S.phi (Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j))

/-- The hypotheses of the affine reparameterisation. -/
structure SwapOK (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : Prop where
  mem : x ∈ S.params
  unpaired : ¬ S.Paired x
  aux : Q ∈ S.aux
  affine : S.AffineIn Q c T
  mem_T : x ∈ T

/-- Exchanging `x` and `Q` replaces `x` with `Q` in `S.params`. -/
@[simp] theorem swap_params (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).params = insert Q (S.params.erase x) := rfl

/-- Exchanging `x` and `Q` preserves the pairs of the state. -/
@[simp] theorem swap_pairs (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).pairs = S.pairs := rfl

/-- Exchanging `x` and `Q` preserves the size of the state. -/
theorem swap_size (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).size = S.size := rfl

/-- Exchanging `x` and `Q` preserves the children of every variable. -/
theorem swap_children (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) (z : ℕ) :
    (S.swap x Q c T).children z = S.children z := rfl

/-- The affine reparameterisation preserves validity. -/
theorem Valid.swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).Valid f := by
  have hTx : ∀ j ∈ T.erase x, j ∈ S.params.erase x := fun j hj =>
    Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hj, h.affine.1 (Finset.mem_of_mem_erase hj)⟩
  have hnx : ∀ pr ∈ S.pairs, pr.1 ≠ x ∧ pr.2 ≠ x := fun pr hpr =>
    ⟨fun he => h.unpaired ⟨pr, hpr, Or.inl he⟩, fun he => h.unpaired ⟨pr, hpr, Or.inr he⟩⟩
  let σ : (ℕ → Bool) → ℕ → Bool := fun val =>
    Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j)
  have hσ : ∀ val i, i ≠ x → σ val i = val i := fun val i hi => Function.update_of_ne hi _ _
  have hσx : ∀ val, σ val x = val Q + c + ∑ j ∈ T.erase x, val j := fun val =>
    Function.update_self _ _ _
  have hσid : ∀ val, S.EqnsHold val → σ val = val := fun val hval => by
    funext i
    by_cases hi : i = x
    · subst hi; rw [hσx, h.affine.solve h.mem_T hval]
    · exact hσ val i hi
  refine hS.of_transport (σ := σ) (hS.wf.swap h.mem h.aux h.affine h.mem_T)
    { pair_mem := fun pr hpr => ?_
      pairs_disjoint := hS.pairs_disjoint
      phi := fun _ => rfl
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      affine := fun k τ hτ htame => ⟨fun u => σ (τ u), ?_, fun pr hpr => ?_, fun _ _ _ => rfl⟩
      consistent := fun val hval => by rw [hσid val hval.1]; exact hval
      out := fun val hval => by rw [hσid val hval.1]; rfl }
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr hpr
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨(hnx pr hpr).1, h1⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨(hnx pr hpr).2, h2⟩), h12⟩
  · by_cases hjx : j = x
    · subst hjx
      rw [hσx, hσx, hv Q (Finset.mem_insert_self _ _),
        Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem (hTx i hi))]
    · rw [hσ val j hjx, hσ val' j hjx]
      exact hv j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjx, hj⟩))
  · rcases Finset.mem_insert.1 hj with rfl | hj
    · have h1 := hv x h.mem
      rw [hσx, hσx, Finset.sum_congr rfl fun i hi =>
        (hσ val i (Finset.ne_of_mem_erase hi)).symm.trans
        ((hv i (Finset.mem_of_mem_erase (hTx i hi))).trans
          (hσ val' i (Finset.ne_of_mem_erase hi)))] at h1
      simpa using h1
    · have := hv j (Finset.mem_of_mem_erase hj)
      rwa [hσ val j (Finset.ne_of_mem_erase hj), hσ val' j (Finset.ne_of_mem_erase hj)] at this
  · refine isAffine_update hτ x fun u v w => ?_
    simp only [congrFun (hτ u v w), Pi.add_apply, Finset.sum_add_distrib]
    generalize τ u Q = a₁; generalize τ v Q = a₂; generalize τ w Q = a₃
    generalize ∑ i ∈ T.erase x, τ u i = b₁; generalize ∑ i ∈ T.erase x, τ v i = b₂
    generalize ∑ i ∈ T.erase x, τ w i = b₃
    cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases c <;> rfl
  · obtain ⟨hx1, hx2⟩ := hnx pr hpr
    rcases htame pr hpr with ht | ht | ht
    · exact Or.inl fun u v => by dsimp only; rw [hσ _ _ hx1, hσ _ _ hx1]; exact ht u v
    · exact Or.inr (Or.inl fun u v => by dsimp only; rw [hσ _ _ hx2, hσ _ _ hx2]; exact ht u v)
    · exact Or.inr (Or.inr fun u v => by
        dsimp only; rw [hσ _ _ hx1, hσ _ _ hx1, hσ _ _ hx2, hσ _ _ hx2]; exact ht u v)

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
def quad (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : State n where
  toSemiCircuit := S.toSemiCircuit.quad z G D
  pairs := insert (x, y) S.pairs
  phi val := S.phi (Function.update val z (val D + ((val x + α) * (val y + β) + γ) + c))

/-- The hypotheses of the quadratic reparameterisation: the configuration of
`SemiCircuit.QuadOK` on unpaired parameters. -/
structure QuadOK (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : Prop
    extends SemiCircuit.QuadOK S.toSemiCircuit x y z G D α β γ c where
  unpaired_x : ¬ S.Paired x
  unpaired_y : ¬ S.Paired y
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

/-- The pairs after the quadratic reparameterisation are disjoint pairs of parameters. -/
theorem pair_mem (hS : S.Valid f) : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs,
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

/-- Along an affine family on which the new pairs are tame, substituting `z` keeps it affine
and every old pair tame: the new pair `(x, y)` makes the product `G` affine. -/
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
  refine hS.of_transport (σ := σ) (hS.wf.quad h.toQuadOK)
    { pair_mem := h.pair_mem hS
      pairs_disjoint := h.pairs_disjoint hS
      phi := fun val => hS.phi_congr _ _ fun j hj => ?_
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      affine := fun k τ hτ htame => h.affine hS hτ htame
      consistent := fun val hval => (h.toQuadOK.consistent hS.wf hval).1
      out := fun val hval => (h.toQuadOK.consistent hS.wf hval).2 }
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
