/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.State
public import Complexity.Computability.Circuit.Boolean.SemiCircuit.Simplification

/-!
# Restrictions and deletions on states

The restrictions and deletions of [Mishra and Santhanam, Sections 2.4 and 3.1][MishraSanthanam2026]
on states of gate elimination, each with its validity and its effect on the counted quantities
and on the children of the parameters:

* `State.restrict`: fixing a parameter to a constant or to a literal of another parameter, the
  restrictions (UF) and (PF) of the source;
* `State.deleteGate`: deleting a gate that computes a literal of one of its inputs, or a constant,
  or that is unused, rerouting its uses (D1) and (D2);
* `State.deleteEqn`: deleting an equation `v = ℓ` together with its auxiliary variable `v`,
  rerouting `v` to `ℓ` (D3);
* `State.dropEqn`: deleting an equation together with an auxiliary variable occurring nowhere
  else (the second half of D4), and `State.dropTrivialEqn`: deleting an equation without terms.

Each operation acts on the semi-circuit as the corresponding simplification of
`Complexity.Computability.Circuit.Boolean.SemiCircuit.Simplification`, which preserves
well-formedness. Validity then follows from the semi-circuit level: an operation keeping the
parameter map is valid when consistent assignments lift (`State.Valid.of_liftsTo`), and in general
validity is transported along a map `σ` from the new assignments to the old ones under the
obligations `State.Transport` (`State.Valid.of_transport`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.Transport`: the obligations of transporting
  validity.
* `Cslib.Circuits.Boolean.AffineDisperser.State.restrict`, `State.RestrictOK`,
  `State.deleteGate`, `State.deleteEqn`, `State.dropEqn`, `State.dropTrivialEqn`: the operations
  and the restriction hypotheses.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.of_transport`: transporting validity.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.restrict`, `Valid.deleteGate`,
  `Valid.deleteEqn`, `Valid.dropEqn`, `Valid.dropTrivialEqn`: the operations preserve validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

/-- Evaluating a literal `ℓ` along an affine family of assignments `τ` defines an affine Boolean
function. -/
theorem isAffine_lit_eval {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ) (ℓ : Lit) :
    IsAffine fun u => ℓ.eval (τ u) := by
  intro u v w
  obtain ⟨_ | t, c⟩ := ℓ
  · simp only [Lit.eval, Arg.eval_const]
    generalize ‹Bool› = b
    revert b c; decide
  · simp only [Lit.eval, Arg.eval_node, congrFun (hτ u v w) t, Pi.add_apply]
    generalize τ u t = a; generalize τ v t = b; generalize τ w t = e
    revert a b e c; decide

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Transporting validity -/

/-- A state with the parameters, pairs and parameter map of a valid state is valid when its
semi-circuit is well formed and computes `f`. -/
private theorem Valid.of_phi {S S' : State n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hcomp : ∀ val, S'.Consistent val → S'.out.eval val = f (S'.phi val)) : S'.Valid f where
  wf := hwf
  pair_mem := by rw [hpairs, hparams]; exact hS.pair_mem
  pairs_disjoint := by rw [hpairs]; exact hS.pairs_disjoint
  phi_congr := by rw [hphi, hparams]; exact hS.phi_congr
  phi_affine := by rw [hphi, hpairs]; exact hS.phi_affine
  phi_injective := by rw [hphi, hparams]; exact hS.phi_injective
  computes := hcomp

/-- A state with the parameters, pairs and parameter map of a valid state is valid when its
semi-circuit is well formed and its consistent assignments lift to the old semi-circuit. -/
theorem Valid.of_liftsTo {S S' : State n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hlift : S'.toSemiCircuit.LiftsTo S.toSemiCircuit) : S'.Valid f :=
  hS.of_phi hparams hpairs hphi hwf fun val hval => by
    obtain ⟨w, hw, hwval, hout⟩ := hlift val hval
    rw [hout, hS.computes w hw, hphi]
    exact congrArg f (hS.phi_congr _ _ hwval)

/-- The obligations for transporting validity from `S` to `S'` along a map `σ` from the
assignments of `S'` to those of `S`: `σ` maps consistent assignments to consistent assignments
with the same output, the new parameter map is the old one after `σ`, `σ` matches the parameters
of both states injectively, and `σ` maps affine families on which the new pairs are tame to
families agreeing on the old parameters with affine families on which the old pairs are tame. -/
structure Transport (S S' : State n) (σ : (ℕ → Bool) → ℕ → Bool) : Prop where
  pair_mem : ∀ pr ∈ S'.pairs, pr.1 ∈ S'.params ∧ pr.2 ∈ S'.params ∧ pr.1 ≠ pr.2
  pairs_disjoint : ∀ pr ∈ S'.pairs, ∀ pr' ∈ S'.pairs, pr ≠ pr' →
    pr.1 ≠ pr'.1 ∧ pr.1 ≠ pr'.2 ∧ pr.2 ≠ pr'.1 ∧ pr.2 ≠ pr'.2
  phi : ∀ val, S'.phi val = S.phi (σ val)
  congr : ∀ val val', (∀ j ∈ S'.params, val j = val' j) → ∀ j ∈ S.params, σ val j = σ val' j
  inj : ∀ val val', (∀ j ∈ S.params, σ val j = σ val' j) → ∀ j ∈ S'.params, val j = val' j
  affine : ∀ (k : ℕ) (τ : BitString k → ℕ → Bool), IsAffine τ →
    (∀ pr ∈ S'.pairs, PairTame τ pr) → ∃ τ' : BitString k → ℕ → Bool, IsAffine τ' ∧
      (∀ pr ∈ S.pairs, PairTame τ' pr) ∧ ∀ u, ∀ j ∈ S.params, τ' u j = σ (τ u) j
  consistent : ∀ val, S'.Consistent val → S.Consistent (σ val)
  out : ∀ val, S'.Consistent val → S'.out.eval val = S.out.eval (σ val)

/-- Validity transported along a map `σ` from the assignments of a new, well-formed state to
those of a valid state. -/
theorem Valid.of_transport {S S' : State n} (hS : S.Valid f) {σ : (ℕ → Bool) → ℕ → Bool}
    (hwf : S'.WellFormed) (h : Transport S S' σ) : S'.Valid f where
  wf := hwf
  pair_mem := h.pair_mem
  pairs_disjoint := h.pairs_disjoint
  phi_congr val val' hv := by
    rw [h.phi, h.phi]
    exact hS.phi_congr _ _ (h.congr val val' hv)
  phi_affine k τ hτ htame := by
    obtain ⟨τ', hτ', htame', hagree⟩ := h.affine k τ hτ htame
    have : S'.phi ∘ τ = S.phi ∘ τ' := funext fun u => by
      simp only [Function.comp_apply, h.phi]
      exact hS.phi_congr _ _ fun j hj => (hagree u j hj).symm
    rw [this]
    exact hS.phi_affine k τ' hτ' htame'
  phi_injective val val' hv := h.inj val val' (hS.phi_injective _ _ (by rwa [h.phi, h.phi] at hv))
  computes val hval := by
    rw [h.out val hval, h.phi]
    exact hS.computes _ (h.consistent val hval)

/-- A gate does not read itself. -/
theorem Valid.not_reads_self {S : State n} (hS : S.Valid f) {J : ℕ} (hJ : J ∈ S.gates) :
    ¬ (S.gate J).Reads J :=
  hS.wf.not_reads_self hJ

/-! ### Restrictions (UF) and (PF) -/

/-- Restrict the parameter `x` to the literal `ℓ`, a constant or a literal of another parameter,
keeping the pairs `P`. -/
def restrict (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) : State n where
  toSemiCircuit := S.toSemiCircuit.restrict x ℓ
  pairs := P
  phi val := S.phi (Function.update val x (ℓ.eval val))

/-- The hypotheses of a restriction: `x` is a parameter, `ℓ` reads at most another parameter,
the kept pairs avoid `x`, and every dropped pair contains `x` and the other parameter read by
`ℓ`, if any. -/
structure RestrictOK (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) : Prop where
  mem : x ∈ S.params
  reads : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x
  subset : P ⊆ S.pairs
  avoid : ∀ pr ∈ P, pr.1 ≠ x ∧ pr.2 ≠ x
  drop : ∀ pr ∈ S.pairs, pr ∉ P → (pr.1 = x ∨ pr.2 = x) ∧ ∀ y, ℓ.Reads y → y = pr.1 ∨ y = pr.2

/-- Restricting `x` removes `x` from the parameters of `S`. -/
@[simp] theorem restrict_params (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) :
    (S.restrict x ℓ P).params = S.params.erase x := rfl

/-- The pairs of `S.restrict x ℓ P` are `P`. -/
@[simp] theorem restrict_pairs (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) :
    (S.restrict x ℓ P).pairs = P := rfl

/-- The children of `z` in `S.restrict x ℓ P` are its children after substituting `x` with `ℓ`. -/
theorem restrict_children (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) (z : ℕ) :
    (S.restrict x ℓ P).children z = (S.toSemiCircuit.subst x ℓ).children z := rfl

/-- Restricting a parameter preserves the size of the state. -/
theorem restrict_size (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) :
    (S.restrict x ℓ P).size = S.size := rfl

/-- Restricting `x` to `ℓ` substitutes `x` with `ℓ` in every gate. -/
@[simp] theorem restrict_gate (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) (J : ℕ) :
    (S.restrict x ℓ P).gate J = (S.gate J).subst x ℓ := rfl

/-- Restricting `x` to `ℓ` substitutes `x` with `ℓ` in every equation. -/
@[simp] theorem restrict_eqn (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) (e : ℕ) :
    (S.restrict x ℓ P).eqn e = (S.eqn e).subst x ℓ := rfl

/-- Along an affine family on which the kept pairs are tame, the restricted family is affine
and every pair is tame: a dropped pair has a constant member, or a constant sum when `x` is
restricted to a literal of its partner. -/
private theorem RestrictOK.pairTame {S : State n} {x : ℕ} {ℓ : Lit} {P : Finset (ℕ × ℕ)}
    (h : S.RestrictOK x ℓ P) {k : ℕ} {τ : BitString k → ℕ → Bool}
    (htame : ∀ pr ∈ P, PairTame τ pr) :
    ∀ pr ∈ S.pairs, PairTame (fun u => Function.update (τ u) x (ℓ.eval (τ u))) pr := by
  intro pr hpr
  by_cases hP : pr ∈ P
  · have hav := h.avoid pr hP
    rcases htame pr hP with ht | ht | ht
    · exact Or.inl fun u v => by simpa only [Function.update_of_ne hav.1] using ht u v
    · exact Or.inr (Or.inl fun u v => by simpa only [Function.update_of_ne hav.2] using ht u v)
    · exact Or.inr (Or.inr fun u v => by
        simpa only [Function.update_of_ne hav.1, Function.update_of_ne hav.2] using ht u v)
  · obtain ⟨hx, hy⟩ := h.drop pr hpr hP
    obtain ⟨p1, p2⟩ := pr
    obtain ⟨_ | t, c⟩ := ℓ
    · -- a constant restriction makes the member `x` constant
      simp only at hx
      rcases hx with rfl | rfl
      · exact Or.inl fun u v => by simp only [Function.update_self, Lit.eval, Arg.eval_const]
      · exact Or.inr (Or.inl fun u v => by
          simp only [Function.update_self, Lit.eval, Arg.eval_const])
    · -- a restriction to the partner makes the sum of the pair constant
      have ht := hy t rfl
      have htx : t ≠ x := (h.reads t rfl).2
      refine Or.inr (Or.inr fun u v => ?_)
      simp only at hx ht ⊢
      rcases hx with rfl | rfl <;> rcases ht with rfl | rfl
      · exact absurd rfl htx
      · simp only [Function.update_self, Function.update_of_ne htx, Lit.eval, Arg.eval_node]
        cases τ u t <;> cases τ v t <;> cases c <;> rfl
      · simp only [Function.update_self, Function.update_of_ne htx, Lit.eval, Arg.eval_node]
        cases τ u t <;> cases τ v t <;> cases c <;> rfl
      · exact absurd rfl htx

/-- Restrictions preserve validity. -/
theorem Valid.restrict {S : State n} (hS : S.Valid f) {x : ℕ} {ℓ : Lit} {P : Finset (ℕ × ℕ)}
    (h : S.RestrictOK x ℓ P) : (S.restrict x ℓ P).Valid f := by
  have hℓx : ℓ.arg ≠ .node x := fun he => (h.reads x he).2 rfl
  have hℓeval : ∀ val val' : ℕ → Bool, (∀ j ∈ S.params.erase x, val j = val' j) →
      ℓ.eval val = ℓ.eval val' := fun val val' hv =>
    Lit.eval_congr fun y hy => hv y (Finset.mem_erase.2 ⟨(h.reads y hy).2, (h.reads y hy).1⟩)
  refine hS.of_transport (σ := fun val => Function.update val x (ℓ.eval val))
    (hS.wf.restrict h.mem h.reads)
    { pair_mem := fun pr hpr => ?_
      pairs_disjoint := fun pr hpr pr' hpr' =>
        hS.pairs_disjoint pr (h.subset hpr) pr' (h.subset hpr')
      phi := fun _ => rfl
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      affine := fun k τ hτ htame => ⟨fun u => Function.update (τ u) x (ℓ.eval (τ u)),
        isAffine_update hτ x (isAffine_lit_eval hτ ℓ), h.pairTame htame, fun _ _ _ => rfl⟩
      consistent := fun val hval => consistent_restrict hS.wf h.mem hℓx hval
      out := fun val _ => out_restrict hℓx val }
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr (h.subset hpr)
    exact ⟨Finset.mem_erase.2 ⟨(h.avoid pr hpr).1, h1⟩,
      Finset.mem_erase.2 ⟨(h.avoid pr hpr).2, h2⟩, h12⟩
  · by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self]
      exact hℓeval _ _ hv
    · simp only [Function.update_of_ne hjx]
      exact hv j (Finset.mem_erase.2 ⟨hjx, hj⟩)
  · have := hv j (Finset.mem_of_mem_erase hj)
    simpa only [Function.update_of_ne (Finset.ne_of_mem_erase hj)] using this

/-! ### Deleting a gate (D1) and (D2) -/

/-- Delete the gate `J`, rerouting its uses to the literal `ℓ`. -/
def deleteGate (S : State n) (J : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.deleteGate J ℓ }

/-- Deleting a gate preserves the parameters of the state. -/
@[simp] theorem deleteGate_params (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).params = S.params := rfl

/-- Deleting a gate preserves the pairs of the state. -/
@[simp] theorem deleteGate_pairs (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).pairs = S.pairs := rfl

/-- Deleting a gate preserves the parameter map `phi`. -/
@[simp] theorem deleteGate_phi (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).phi = S.phi := rfl

/-- Deleting gate `J` with replacement `ℓ` substitutes `J` with `ℓ` in every gate. -/
@[simp] theorem deleteGate_gate (S : State n) (J : ℕ) (ℓ : Lit) (K : ℕ) :
    (S.deleteGate J ℓ).gate K = (S.gate K).subst J ℓ := rfl

/-- Deleting gate `J` with replacement `ℓ` substitutes `J` with `ℓ` in every equation. -/
@[simp] theorem deleteGate_eqn (S : State n) (J : ℕ) (ℓ : Lit) (e : ℕ) :
    (S.deleteGate J ℓ).eqn e = (S.eqn e).subst J ℓ := rfl

/-- Deleting gate `J` removes `J` from `S.gates`. -/
@[simp] theorem deleteGate_gates (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).gates = S.gates.erase J := rfl

/-- Deleting a gate decreases the size of the state by `1`. -/
theorem deleteGate_size {S : State n} {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : (S.deleteGate J ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + S.eqns.card + 1 = _
  omega

/-- After deleting gate `J` with replacement `ℓ`, the children of `z` are contained in the
children of `z` after substituting `J` with `ℓ` with `.inl J` removed. -/
theorem deleteGate_children_subset {S : State n} {J : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteGate J ℓ).children z ⊆ ((S.toSemiCircuit.subst J ℓ).children z).erase (.inl J) := by
  intro w hw
  rcases w with K | e
  · simp only [SemiCircuit.inl_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase J _ hw.1
    · exact (SemiCircuit.inl_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inr_ne_inl, (SemiCircuit.inr_mem_children _).2 hw⟩

/-- Deleting a gate removes it from the children of every parameter other than the target of
`ℓ`. -/
theorem deleteGate_children_of_ne {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteGate J ℓ).children z ⊆ (S.children z).erase (.inl J) := by
  have hzJ : z ≠ J := fun he => hS.wf.notMem_gates_of_mem_params hz (he ▸ h.mem)
  have := deleteGate_children_subset (S := S) (J := J) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzJ hzℓ] at this

/-- Deleting a gate preserves validity. -/
theorem Valid.deleteGate {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : (S.deleteGate J ℓ).Valid f :=
  hS.of_liftsTo rfl rfl rfl (hS.wf.deleteGate h) (h.liftsTo hS.wf)

/-! ### Deleting an equation (D3) -/

/-- Delete the equation `e`, which reads `v = ℓ`, and the auxiliary variable `v`, rerouting `v`
to `ℓ`. -/
def deleteEqn (S : State n) (e v : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.deleteEqn e v ℓ }

/-- Deleting an equation preserves the parameters of the state. -/
@[simp] theorem deleteEqn_params (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).params = S.params := rfl

/-- Deleting an equation preserves the pairs of the state. -/
@[simp] theorem deleteEqn_pairs (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).pairs = S.pairs := rfl

/-- Deleting an equation preserves the parameter map `phi`. -/
@[simp] theorem deleteEqn_phi (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).phi = S.phi := rfl

/-- Deleting an equation decreases the size of the state by `1`. -/
theorem deleteEqn_size {S : State n} {e v : ℕ} {ℓ : Lit} (h : S.DeleteEqnOK e v ℓ) :
    (S.deleteEqn e v ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

/-- After deleting equation `e` and auxiliary variable `v` with replacement `ℓ`, the children of
`z` are contained in the children of `z` after substituting `v` with `ℓ` with `.inr e` removed. -/
theorem deleteEqn_children_subset {S : State n} {e v : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteEqn e v ℓ).children z ⊆ ((S.toSemiCircuit.subst v ℓ).children z).erase (.inr e) := by
  intro w hw
  rcases w with K | e'
  · simp only [SemiCircuit.inl_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inl_ne_inr, (SemiCircuit.inl_mem_children _).2 hw⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase e _ hw.1
    · exact (SemiCircuit.inr_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩

/-- Deleting an equation removes it from the children of every parameter other than the target of
`ℓ`. -/
theorem deleteEqn_children_of_ne {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteEqn e v ℓ).children z ⊆ (S.children z).erase (.inr e) := by
  have hzv : z ≠ v := fun he => hS.wf.notMem_aux_of_mem_params hz (he ▸ h.aux)
  have := deleteEqn_children_subset (S := S) (e := e) (v := v) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzv hzℓ] at this

/-- Deleting an equation `v = ℓ` with its auxiliary variable preserves validity. -/
theorem Valid.deleteEqn {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) : (S.deleteEqn e v ℓ).Valid f :=
  hS.of_liftsTo rfl rfl rfl (hS.wf.deleteEqn h) (h.liftsTo hS.wf)

/-! ### Dropping an equation (D4) -/

/-- Delete the equation `e` together with an auxiliary variable `v` occurring nowhere else. -/
def dropEqn (S : State n) (e v : ℕ) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.dropEqn e v }

/-- Dropping an equation preserves the parameters of the state. -/
@[simp] theorem dropEqn_params (S : State n) (e v : ℕ) : (S.dropEqn e v).params = S.params := rfl

/-- Dropping an equation preserves the pairs of the state. -/
@[simp] theorem dropEqn_pairs (S : State n) (e v : ℕ) : (S.dropEqn e v).pairs = S.pairs := rfl

/-- Dropping an equation decreases the size of the state by `1`. -/
theorem dropEqn_size {S : State n} {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

/-- Dropping equation `e` removes `.inr e` from the children of `z`. -/
theorem dropEqn_children (S : State n) (e v z : ℕ) :
    (S.dropEqn e v).children z = (S.children z).erase (.inr e) := by
  ext (K | e')
  · simp only [SemiCircuit.inl_mem_children, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    rfl
  · simp only [SemiCircuit.inr_mem_children, Finset.mem_erase, ne_eq, Sum.inr.injEq]
    change (e' ∈ S.eqns.erase e ∧ _) ↔ _
    rw [Finset.mem_erase]
    tauto

/-- Dropping an equation with an auxiliary variable occurring only there preserves validity. -/
theorem Valid.dropEqn {S : State n} (hS : S.Valid f) {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).Valid f :=
  hS.of_liftsTo rfl rfl rfl (hS.wf.dropEqn h) (h.liftsTo hS.wf)

/-- Delete an equation without terms. -/
def dropTrivialEqn (S : State n) (e : ℕ) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.dropTrivialEqn e }

/-- Dropping a trivial equation preserves the parameters of the state. -/
@[simp] theorem dropTrivialEqn_params (S : State n) (e : ℕ) :
    (S.dropTrivialEqn e).params = S.params := rfl

/-- Dropping a trivial equation preserves the pairs of the state. -/
@[simp] theorem dropTrivialEqn_pairs (S : State n) (e : ℕ) :
    (S.dropTrivialEqn e).pairs = S.pairs := rfl

/-- Dropping a trivial equation decreases the size of the state by `1`. -/
theorem dropTrivialEqn_size {S : State n} {e : ℕ} (he : e ∈ S.eqns) :
    (S.dropTrivialEqn e).size + 1 = S.size := by
  have := Finset.card_erase_add_one he
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

/-- Dropping trivial equation `e` removes `.inr e` from the children of `z`. -/
theorem dropTrivialEqn_children (S : State n) (e z : ℕ) :
    (S.dropTrivialEqn e).children z = (S.children z).erase (.inr e) := by
  ext (K | e')
  · simp only [SemiCircuit.inl_mem_children, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    rfl
  · simp only [SemiCircuit.inr_mem_children, Finset.mem_erase, ne_eq, Sum.inr.injEq]
    change (e' ∈ S.eqns.erase e ∧ _) ↔ _
    rw [Finset.mem_erase]
    tauto

/-- Deleting an equation without terms preserves validity. -/
theorem Valid.dropTrivialEqn {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : (S.dropTrivialEqn e).Valid f :=
  hS.of_liftsTo rfl rfl rfl (hS.wf.dropTrivialEqn he hterms)
    (liftsTo_dropTrivialEqn hS.wf he hterms)

end State

end Cslib.Circuits.Boolean.AffineDisperser
