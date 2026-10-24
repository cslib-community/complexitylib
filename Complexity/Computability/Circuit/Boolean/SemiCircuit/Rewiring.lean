/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit

/-!
# Moving and rewiring gates

Two changes of the gates of a fair semi-circuit that keep its parameters and the function it
computes, as in [Mishra and Santhanam, Sections 2.3 and 4.2][MishraSanthanam2026]:

* `SemiCircuit.moveAffine`: an affine gate reading no gates becomes an auxiliary variable, with its
  equation `SemiCircuit.affEqn` added to the affine system; this does not increase the degree of
  any parameter (`SemiCircuit.deg_moveAffine_le`);
* `SemiCircuit.rewire`: a gate is replaced by a gate reading only parameters that computes the
  same value whenever the other gates take their values.

Both preserve well-formedness, and every consistent assignment of the result is consistent for
the original semi-circuit (`SemiCircuit.MoveOK.liftsTo`, `SemiCircuit.RewireOK.liftsTo`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.moveAffine`, `Cslib.Circuits.Boolean.SemiCircuit.rewire`.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.WellFormed.moveAffine`,
  `Cslib.Circuits.Boolean.SemiCircuit.WellFormed.rewire`: well-formedness is preserved.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Finset

variable {C : SemiCircuit}

/-! ### Moving an affine gate into the affine system -/

/-- Move the affine gate `J` into the affine system as the auxiliary variable `J` with the new
equation `e`. -/
def moveAffine (C : SemiCircuit) (J e : ℕ) : SemiCircuit :=
  { C with
    gates := C.gates.erase J
    aux := insert J C.aux
    eqns := insert e C.eqns
    eqn := Function.update C.eqn e (affEqn (C.gate J) J) }

/-- The hypotheses of moving a gate into the affine system: `J` is an affine gate reading no
gates and `e` is a fresh equation name. -/
structure MoveOK (C : SemiCircuit) (J e : ℕ) : Prop where
  mem : J ∈ C.gates
  fresh : e ∉ C.eqns
  affine : IsAffineOp (C.gate J).op
  inputs : ∀ i, (C.gate J).Reads i → i ∉ C.gates

namespace MoveOK

variable {J e : ℕ} (h : C.MoveOK J e)
include h

theorem eqn_of_mem {e' : ℕ} (he' : e' ∈ C.eqns) : (C.moveAffine J e).eqn e' = C.eqn e' :=
  Function.update_of_ne (show e' ≠ e from fun he => h.fresh (he ▸ he')) _ _

/-- The solutions of the new affine system are those of the old one on which the moved gate
takes its value. -/
theorem eqnsHold_iff (val : ℕ → Bool) : (C.moveAffine J e).EqnsHold val ↔
    C.EqnsHold val ∧ (affEqn (C.gate J) J).Holds val := by
  constructor
  · intro hv
    refine ⟨fun e' he' => ?_, ?_⟩
    · rw [← h.eqn_of_mem he']; exact hv e' (Finset.mem_insert_of_mem he')
    · have := hv e (Finset.mem_insert_self _ _)
      change (Function.update C.eqn e _ e).Holds val at this
      rwa [Function.update_self] at this
  · rintro ⟨hv, hJv⟩ e' he'
    rcases Finset.mem_insert.1 he' with rfl | he'
    · change (Function.update C.eqn e' _ e').Holds val
      rwa [Function.update_self]
    · rw [h.eqn_of_mem he']; exact hv e' he'

private theorem live_eq : (C.moveAffine J e).live = C.live := by
  ext i
  simp only [live, Finset.mem_union]
  change (i ∈ C.params ∨ i ∈ insert J C.aux) ∨ i ∈ C.gates.erase J ↔ _
  simp only [Finset.mem_insert, Finset.mem_erase]
  by_cases hiJ : i = J
  · subst hiJ; simp [h.mem]
  · simp [hiJ]

end MoveOK

theorem MoveOK.mem_params_or_aux (hC : C.WellFormed) {J e : ℕ} (h : C.MoveOK J e) {i : ℕ}
    (hi : (C.gate J).Reads i) : i ∈ C.params ∪ C.aux := by
  have := hC.reads_live J h.mem i hi
  simp only [live, Finset.mem_union] at this
  rcases this with hpa | hg
  · exact Finset.mem_union.2 hpa
  · exact absurd hg (h.inputs i hi)

/-- Moving an affine gate reading no gates into the affine system preserves well-formedness. -/
theorem WellFormed.moveAffine (hC : C.WellFormed) {J e : ℕ} (h : C.MoveOK J e) :
    (C.moveAffine J e).WellFormed := by
  set g := C.gate J
  have hJp : J ∉ C.params := hC.notMem_params_of_mem_gates h.mem
  have hgJ : ¬ g.Reads J := fun hr => h.inputs J hr h.mem
  have hlive := h.live_eq
  refine
    { disjoint_params_aux := Finset.disjoint_left.2 fun i hp ha => ?_
      disjoint_params_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_params_gates
      disjoint_aux_gates := Finset.disjoint_left.2 fun i ha hg => ?_
      reads_lt := fun K hK i hi hr => hC.reads_lt K (Finset.mem_of_mem_erase hK) i
        (Finset.mem_of_mem_erase hi) hr
      reads_live := fun K hK i hr => hlive ▸ hC.reads_live K (Finset.mem_of_mem_erase hK) i hr
      terms_subset := fun e' he' t ht => ?_
      card_terms_le := fun e' he' => ?_
      out_live := fun i hi => hlive ▸ hC.out_live i hi
      solvable := fun u => ?_
      unique := fun val val' hagree heq heq' a ha => ?_ }
  · change i ∈ insert J C.aux at ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hJp hp
    · exact hC.notMem_aux_of_mem_params hp ha
  · change i ∈ insert J C.aux at ha
    change i ∈ C.gates.erase J at hg
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact Finset.notMem_erase i _ hg
    · exact hC.notMem_gates_of_mem_aux ha (Finset.mem_of_mem_erase hg)
  · change t ∈ C.params ∪ insert J C.aux
    have hsub : ∀ t ∈ C.params ∪ C.aux, t ∈ C.params ∪ insert J C.aux := fun t ht => by
      rcases Finset.mem_union.1 ht with hp | ha
      · exact Finset.mem_union_left _ hp
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem ha)
    rcases Finset.mem_insert.1 he' with rfl | he'
    · change t ∈ (Function.update C.eqn e' _ e').terms at ht
      rw [Function.update_self] at ht
      rcases mem_affEqn ht with rfl | ht
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · exact hsub t (h.mem_params_or_aux hC ht)
    · rw [h.eqn_of_mem he'] at ht
      exact hsub t (hC.terms_subset e' he' ht)
  · rcases Finset.mem_insert.1 he' with rfl | he'
    · change (Function.update C.eqn e' _ e').terms.card ≤ 3
      rw [Function.update_self]
      exact card_affEqn_le _ _
    · rw [h.eqn_of_mem he']; exact hC.card_terms_le e' he'
  · obtain ⟨val, hu, heq⟩ := hC.solvable u
    have hw : ∀ i, i ≠ J → Function.update val J (g.eval val) i = val i := fun i hi =>
      Function.update_of_ne hi _ _
    refine ⟨Function.update val J (g.eval val), fun j hj => (hw j fun he => hJp (he ▸ hj)).trans
      (hu j hj), (h.eqnsHold_iff _).2 ⟨fun e' he' => (Equation.holds_congr fun i hi => hw i
        fun he => hC.notMem_terms_of_mem_gates h.mem he' (he ▸ hi)).2 (heq e' he'), ?_⟩⟩
    rw [affEqn_holds h.affine, Function.update_self]
    exact Gate.eval_congr fun i hi => (hw i fun he => hgJ (he ▸ hi)).symm
  · obtain ⟨heq, hJv⟩ := (h.eqnsHold_iff val).1 heq
    obtain ⟨heq', hJv'⟩ := (h.eqnsHold_iff val').1 heq'
    have hagree' := hC.unique val val' hagree heq heq'
    change a ∈ insert J C.aux at ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · rw [(affEqn_holds h.affine _ _).1 hJv, (affEqn_holds h.affine _ _).1 hJv']
      refine Gate.eval_congr fun i hi => ?_
      rcases Finset.mem_union.1 (h.mem_params_or_aux hC hi) with hp | ha
      · exact hagree i hp
      · exact hagree' i ha
    · exact hagree' a ha

/-- A consistent assignment after moving a gate into the affine system is consistent for the
original semi-circuit. -/
theorem MoveOK.liftsTo {J e : ℕ} (h : C.MoveOK J e) : (C.moveAffine J e).LiftsTo C :=
  fun val hval => by
    obtain ⟨heq, hJv⟩ := (h.eqnsHold_iff val).1 hval.1
    refine ⟨val, ⟨heq, fun K hK => ?_⟩, fun _ _ => rfl, rfl⟩
    by_cases hKJ : K = J
    · subst hKJ; exact (affEqn_holds h.affine _ _).1 hJv
    · exact hval.2 K (Finset.mem_erase.2 ⟨hKJ, hK⟩)

/-- Moving a gate into the affine system does not increase the degree of any value other than
the gate. -/
theorem deg_moveAffine_le {J e : ℕ} (h : C.MoveOK J e) {z : ℕ} (hzJ : z ≠ J) :
    (C.moveAffine J e).deg z ≤ C.deg z := by
  have hsub : (C.moveAffine J e).children z ⊆
      (C.children z).erase (.inl J) ∪ (if Sum.inl J ∈ C.children z then {.inr e} else ∅) := by
    intro w hw
    rcases w with K | e'
    · simp only [inl_mem_children] at hw
      change K ∈ C.gates.erase J ∧ _ at hw
      refine Finset.mem_union_left _ (Finset.mem_erase.2
        ⟨fun he => by cases Sum.inl.inj he; exact Finset.notMem_erase _ _ hw.1, ?_⟩)
      exact (inl_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩
    · simp only [inr_mem_children] at hw
      change e' ∈ insert e C.eqns ∧ z ∈ (Function.update C.eqn e _ e').terms at hw
      by_cases hee : e' = e
      · subst hee
        rw [Function.update_self] at hw
        rcases mem_affEqn hw.2 with h' | h'
        · exact absurd h' hzJ
        · refine Finset.mem_union_right _ ?_
          rw [ite_eq_left ((inl_mem_children _).2 ⟨h.mem, h'⟩)]
          exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hee] at hw
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨Sum.inr_ne_inl,
          (inr_mem_children _).2 ⟨Finset.mem_of_mem_insert_of_ne hw.1 hee, hw.2⟩⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  unfold deg
  split_ifs with hJ
  · rw [Finset.card_singleton, Finset.card_erase_add_one hJ]
  · rw [Finset.card_empty, add_zero, Finset.erase_eq_of_notMem hJ]

/-! ### Rewiring a gate -/

/-- Replace the gate `J` by the gate `g`. -/
def rewire (C : SemiCircuit) (J : ℕ) (g : Gate) : SemiCircuit :=
  { C with gate := Function.update C.gate J g }

/-- The hypotheses of rewiring: `g` reads only parameters and computes the value of `J`
whenever all other gates take their values. -/
structure RewireOK (C : SemiCircuit) (J : ℕ) (g : Gate) : Prop where
  mem : J ∈ C.gates
  reads : ∀ i, g.Reads i → i ∈ C.params
  value : ∀ val, (∀ K ∈ C.gates, K ≠ J → val K = (C.gate K).eval val) →
    g.eval val = (C.gate J).eval val

private theorem rewire_gate_of_ne {J K : ℕ} {g : Gate} (hKJ : K ≠ J) :
    (C.rewire J g).gate K = C.gate K :=
  Function.update_of_ne hKJ _ _

private theorem rewire_gate_self {J : ℕ} {g : Gate} : (C.rewire J g).gate J = g :=
  Function.update_self _ _ _

/-- Rewiring a gate to read only parameters preserves well-formedness. -/
theorem WellFormed.rewire (hC : C.WellFormed) {J : ℕ} {g : Gate} (h : C.RewireOK J g) :
    (C.rewire J g).WellFormed where
  disjoint_params_aux := hC.disjoint_params_aux
  disjoint_params_gates := hC.disjoint_params_gates
  disjoint_aux_gates := hC.disjoint_aux_gates
  reads_lt K hK i hi hr := by
    by_cases hKJ : K = J
    · subst hKJ
      rw [rewire_gate_self] at hr
      exact absurd hi (hC.notMem_gates_of_mem_params (h.reads i hr))
    · rw [rewire_gate_of_ne hKJ] at hr; exact hC.reads_lt K hK i hi hr
  reads_live K hK i hr := by
    by_cases hKJ : K = J
    · subst hKJ
      rw [rewire_gate_self] at hr
      simp only [live, Finset.mem_union]
      exact Or.inl (Or.inl (h.reads i hr))
    · rw [rewire_gate_of_ne hKJ] at hr; exact hC.reads_live K hK i hr
  terms_subset := hC.terms_subset
  card_terms_le := hC.card_terms_le
  out_live := hC.out_live
  solvable := hC.solvable
  unique := hC.unique

/-- A consistent assignment of a rewired semi-circuit is consistent for the original one. -/
theorem RewireOK.liftsTo {J : ℕ} {g : Gate} (h : C.RewireOK J g) : (C.rewire J g).LiftsTo C :=
  fun val hval => by
    have hothers : ∀ K ∈ C.gates, K ≠ J → val K = (C.gate K).eval val := fun K hK hKJ => by
      rw [← rewire_gate_of_ne hKJ]; exact hval.2 K hK
    refine ⟨val, ⟨hval.1, fun K hK => ?_⟩, fun _ _ => rfl, rfl⟩
    by_cases hKJ : K = J
    · subst hKJ
      rw [← h.value val hothers, ← rewire_gate_self (C := C) (g := g)]
      exact hval.2 K hK
    · exact hothers K hK hKJ

end Cslib.Circuits.Boolean.SemiCircuit
