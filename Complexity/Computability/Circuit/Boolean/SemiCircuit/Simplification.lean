/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit

/-!
# Restricting parameters and deleting constraints

The simplifications of a fair semi-circuit, each preserving well-formedness:

* `SemiCircuit.restrict`: restricting a parameter to a constant or to a literal of another
  parameter, the restrictions (UF) and (PF) of [Mishra and Santhanam][MishraSanthanam2026];
* `SemiCircuit.deleteGate`: deleting a gate that computes a literal of one of its inputs, or a
  constant, or that is unused, rerouting its uses, the deletions (D1) and (D2);
* `SemiCircuit.deleteEqn`: deleting an equation `v = ℓ` together with its auxiliary variable `v`,
  rerouting `v` to `ℓ`, the deletion (D3);
* `SemiCircuit.dropEqn`: deleting an equation together with an auxiliary variable occurring
  nowhere else, the second half of (D4), and `SemiCircuit.dropTrivialEqn`: deleting an equation
  without terms.

A consistent assignment of a restriction is consistent for the original semi-circuit once the
restricted parameter takes the value of its literal (`SemiCircuit.consistent_restrict`), and
consistent assignments of the deletions lift to the original semi-circuit
(`SemiCircuit.DeleteGateOK.liftsTo`, `SemiCircuit.DeleteEqnOK.liftsTo`,
`SemiCircuit.DropEqnOK.liftsTo`, `SemiCircuit.liftsTo_dropTrivialEqn`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.restrict`, `Cslib.Circuits.Boolean.SemiCircuit.deleteGate`,
  `Cslib.Circuits.Boolean.SemiCircuit.DeleteGateOK`,
  `Cslib.Circuits.Boolean.SemiCircuit.deleteEqn`,
  `Cslib.Circuits.Boolean.SemiCircuit.DeleteEqnOK`,
  `Cslib.Circuits.Boolean.SemiCircuit.dropEqn`,
  `Cslib.Circuits.Boolean.SemiCircuit.DropEqnOK`,
  `Cslib.Circuits.Boolean.SemiCircuit.dropTrivialEqn`: the simplifications and their preconditions.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.WellFormed.restrict`, `WellFormed.deleteGate`,
  `WellFormed.deleteEqn`, `WellFormed.dropEqn`, `WellFormed.dropTrivialEqn`: the simplifications
  preserve well-formedness.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Finset

variable {C : SemiCircuit}

/-! ### Restricting a parameter -/

/-- Restrict the parameter `x` to the literal `ℓ`: reroute `x` to `ℓ` and remove it from the
parameters. -/
def restrict (C : SemiCircuit) (x : ℕ) (ℓ : Lit) : SemiCircuit :=
  { C.subst x ℓ with params := C.params.erase x }

/-- Any live node of `C` distinct from `x` remains live in `C.restrict x ℓ`. -/
theorem mem_live_restrict {x : ℕ} {ℓ : Lit} {i : ℕ} (hi : i ∈ C.live) (hix : i ≠ x) :
    i ∈ (C.restrict x ℓ).live := by
  simp only [live, Finset.mem_union] at hi ⊢
  change (i ∈ C.params.erase x ∨ i ∈ C.aux) ∨ i ∈ C.gates
  rw [Finset.mem_erase]
  tauto

/-- Restricting a parameter to a literal reading at most another parameter preserves
well-formedness. -/
theorem WellFormed.restrict (hC : C.WellFormed) {x : ℕ} {ℓ : Lit} (hx : x ∈ C.params)
    (hℓ : ∀ y, ℓ.Reads y → y ∈ C.params ∧ y ≠ x) : (C.restrict x ℓ).WellFormed := by
  have hℓx : ℓ.arg ≠ .node x := fun he => (hℓ x he).2 rfl
  have hℓeval : ∀ val val' : ℕ → Bool, (∀ j ∈ C.params.erase x, val j = val' j) →
      ℓ.eval val = ℓ.eval val' := fun val val' hv =>
    Lit.eval_congr fun y hy => hv y (Finset.mem_erase.2 ⟨(hℓ y hy).2, (hℓ y hy).1⟩)
  have hlive : ∀ i, ℓ.Reads i → i ∈ C.live := fun i hi => by
    simp only [live, Finset.mem_union]; exact Or.inl (Or.inl (hℓ i hi).1)
  refine
    { disjoint_params_aux := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
        hC.disjoint_params_aux
      disjoint_params_gates := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
        hC.disjoint_params_gates
      disjoint_aux_gates := hC.disjoint_aux_gates
      reads_lt := fun J hJ i hi hr => ?_
      reads_live := fun J hJ i hr => ?_
      terms_subset := fun e he z hz => ?_
      card_terms_le := fun e he => Equation.card_subst_le.trans (hC.card_terms_le e he)
      out_live := fun i hi => ?_
      solvable := fun u => ?_
      unique := fun val val' hagree heq heq' v hv => ?_ }
  · rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hC.reads_lt J hJ i hi hr
    · exact absurd hi (hC.notMem_gates_of_mem_params (hℓ i hr).1)
  · refine mem_live_restrict ?_ fun he => Gate.not_reads_subst hℓx (he ▸ hr)
    rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hC.reads_live J hJ i hr
    · exact hlive i hr
  · have hzx : z ≠ x := by rintro rfl; exact Equation.notMem_subst hℓx hz
    have hmem : z ∈ C.params ∪ C.aux := by
      rcases Equation.mem_of_mem_subst hz with hz | ⟨-, hz⟩
      · exact hC.terms_subset e he hz
      · exact Finset.mem_union_left _ (hℓ z hz).1
    simp only [Finset.mem_union] at hmem ⊢
    change z ∈ C.params.erase x ∨ z ∈ C.aux
    rw [Finset.mem_erase]
    tauto
  · refine mem_live_restrict ?_ fun he => Lit.not_reads_subst hℓx (he ▸ hi)
    rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
    · exact hC.out_live i hi
    · exact hlive i hi
  · obtain ⟨val, hu, heq⟩ := hC.solvable (Function.update u x (ℓ.eval u))
    have hvx : val x = ℓ.eval val := by
      rw [hu x hx, Function.update_self]
      exact hℓeval _ _ fun j hj => by
        rw [hu j (Finset.mem_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    refine ⟨val, fun j hj => ?_, fun e he => (Equation.holds_subst hvx).2 (heq e he)⟩
    rw [hu j (Finset.mem_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · have hold : ∀ w : ℕ → Bool, (C.restrict x ℓ).EqnsHold w →
        C.EqnsHold (Function.update w x (ℓ.eval w)) := fun w hw e he =>
      (Equation.holds_subst_update hℓx w).1 (hw e he)
    have := hC.unique _ _ (fun j hj => by
        by_cases hjx : j = x
        · subst hjx
          simp only [Function.update_self]
          exact hℓeval _ _ hagree
        · simp only [Function.update_of_ne hjx]
          exact hagree j (Finset.mem_erase.2 ⟨hjx, hj⟩))
      (hold val heq) (hold val' heq') v hv
    have hvx : v ≠ x := by rintro rfl; exact hC.notMem_aux_of_mem_params hx hv
    simpa only [Function.update_of_ne hvx] using this

/-- A consistent assignment of a restriction, with the restricted parameter given the value of
its literal, is consistent for the original semi-circuit. -/
theorem consistent_restrict (hC : C.WellFormed) {x : ℕ} {ℓ : Lit} (hx : x ∈ C.params)
    (hℓ : ℓ.arg ≠ .node x) {val : ℕ → Bool} (h : (C.restrict x ℓ).Consistent val) :
    C.Consistent (Function.update val x (ℓ.eval val)) :=
  consistent_of_subst (hC.notMem_gates_of_mem_params hx) hℓ h

/-- Evaluating the output of `C.restrict x ℓ` under `val` equals evaluating the output of `C`
after updating `x` to `ℓ.eval val`. -/
theorem out_restrict {x : ℕ} {ℓ : Lit} (hℓ : ℓ.arg ≠ .node x) (val : ℕ → Bool) :
    (C.restrict x ℓ).out.eval val = C.out.eval (Function.update val x (ℓ.eval val)) :=
  Lit.eval_subst_update hℓ val

/-! ### Deleting a gate -/

/-- Delete the gate `J`, rerouting its uses to the literal `ℓ`. -/
def deleteGate (C : SemiCircuit) (J : ℕ) (ℓ : Lit) : SemiCircuit :=
  { C.subst J ℓ with gates := C.gates.erase J }

/-- The hypotheses of a gate deletion: `J` is a gate, `ℓ` reads at most an input of `J`, and
either `J` computes `ℓ` on the solutions of the affine system or nothing reads `J`. -/
structure DeleteGateOK (C : SemiCircuit) (J : ℕ) (ℓ : Lit) : Prop where
  mem : J ∈ C.gates
  reads : ∀ t, ℓ.Reads t → (C.gate J).Reads t
  value : (∀ val, C.EqnsHold val → (C.gate J).eval val = ℓ.eval val) ∨
    ((∀ K ∈ C.gates, ¬ (C.gate K).Reads J) ∧ ¬ C.out.Reads J)

private theorem DeleteGateOK.not_reads (hC : C.WellFormed) {J : ℕ} {ℓ : Lit}
    (h : C.DeleteGateOK J ℓ) :
    ℓ.arg ≠ .node J := fun he => hC.not_reads_self h.mem (h.reads J he)

private theorem eqnsHold_deleteGate (hC : C.WellFormed) {J : ℕ} {ℓ : Lit} (hJ : J ∈ C.gates)
    (val : ℕ → Bool) : (C.deleteGate J ℓ).EqnsHold val ↔ C.EqnsHold val :=
  forall₂_congr fun e he => by
    change ((C.eqn e).subst J ℓ).Holds val ↔ _
    rw [Equation.subst_of_notMem (hC.notMem_terms_of_mem_gates hJ he)]

/-- Any live node of `C` distinct from `J` remains live in `C.deleteGate J ℓ`. -/
theorem mem_live_deleteGate {J : ℕ} {ℓ : Lit} {i : ℕ} (hi : i ∈ C.live) (hiJ : i ≠ J) :
    i ∈ (C.deleteGate J ℓ).live := by
  simp only [live, Finset.mem_union] at hi ⊢
  change (i ∈ C.params ∨ i ∈ C.aux) ∨ i ∈ C.gates.erase J
  rw [Finset.mem_erase]
  tauto

/-- Deleting a gate preserves well-formedness. -/
theorem WellFormed.deleteGate (hC : C.WellFormed) {J : ℕ} {ℓ : Lit} (h : C.DeleteGateOK J ℓ) :
    (C.deleteGate J ℓ).WellFormed := by
  have hℓJ := h.not_reads hC
  have heqn : ∀ e ∈ C.eqns, (C.eqn e).subst J ℓ = C.eqn e := fun e he =>
    Equation.subst_of_notMem (hC.notMem_terms_of_mem_gates h.mem he)
  have hreads_live : ∀ t, ℓ.Reads t → t ∈ C.live := fun t ht =>
    hC.reads_live J h.mem t (h.reads t ht)
  refine
    { disjoint_params_aux := hC.disjoint_params_aux
      disjoint_params_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_params_gates
      disjoint_aux_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_aux_gates
      reads_lt := fun K hK i hi hr => ?_
      reads_live := fun K hK i hr => ?_
      terms_subset := fun e he => by
        change ((C.eqn e).subst J ℓ).terms ⊆ _
        rw [heqn e he]; exact hC.terms_subset e he
      card_terms_le := fun e he => Equation.card_subst_le.trans (hC.card_terms_le e he)
      out_live := fun i hi => ?_
      solvable := fun u => by
        obtain ⟨val, hu, heq⟩ := hC.solvable u
        exact ⟨val, hu, (eqnsHold_deleteGate hC h.mem val).2 heq⟩
      unique := fun val val' hagree heq heq' =>
        hC.unique val val' hagree ((eqnsHold_deleteGate hC h.mem val).1 heq)
          ((eqnsHold_deleteGate hC h.mem val').1 heq') }
  · have hK' := Finset.mem_of_mem_erase hK
    have hi' := Finset.mem_of_mem_erase hi
    rcases Gate.reads_of_reads_subst hr with hr | ⟨hrJ, hr⟩
    · exact hC.reads_lt K hK' i hi' hr
    · exact (hC.reads_lt J h.mem i hi' (h.reads i hr)).trans (hC.reads_lt K hK' J h.mem hrJ)
  · refine mem_live_deleteGate ?_ fun he => Gate.not_reads_subst hℓJ (he ▸ hr)
    rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hC.reads_live K (Finset.mem_of_mem_erase hK) i hr
    · exact hreads_live i hr
  · refine mem_live_deleteGate ?_ fun he => Lit.not_reads_subst hℓJ (he ▸ hi)
    rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
    · exact hC.out_live i hi
    · exact hreads_live i hi

/-- A consistent assignment of a gate deletion lifts, by giving the deleted gate its value. -/
theorem DeleteGateOK.liftsTo (hC : C.WellFormed) {J : ℕ} {ℓ : Lit} (h : C.DeleteGateOK J ℓ) :
    (C.deleteGate J ℓ).LiftsTo C := by
  intro val hval
  have hℓJ := h.not_reads hC
  set w := Function.update val J ((C.gate J).eval val)
  have hw : ∀ i, i ≠ J → w i = val i := fun i hi => Function.update_of_ne hi _ _
  have hwJval : w J = (C.gate J).eval val := Function.update_self _ _ _
  have hℓw : ℓ.eval w = ℓ.eval val := Lit.eval_congr fun i hi => hw i fun he => hℓJ (he ▸ hi)
  have hJw : (∀ val', C.EqnsHold val' → (C.gate J).eval val' = ℓ.eval val') → w J = ℓ.eval w :=
    fun hv => by rw [hwJval, hv val ((eqnsHold_deleteGate hC h.mem val).1 hval.1), hℓw]
  refine ⟨w, ⟨fun e he => ?_, fun K hK => ?_⟩, fun j hj =>
    hw j fun he => hC.notMem_gates_of_mem_params hj (he ▸ h.mem), ?_⟩
  · refine (Equation.holds_congr fun i hi => hw i fun he' => ?_).2
      ((eqnsHold_deleteGate hC h.mem val).1 hval.1 e he)
    exact hC.notMem_terms_of_mem_gates h.mem he (he' ▸ hi)
  · by_cases hKJ : K = J
    · subst hKJ
      rw [hwJval]
      exact Gate.eval_congr fun i hi =>
        (hw i fun he => hC.not_reads_self h.mem (he ▸ hi)).symm
    · rw [hw K hKJ, hval.2 K (Finset.mem_erase.2 ⟨hKJ, hK⟩)]
      change ((C.gate K).subst J ℓ).eval val = _
      rcases h.value with hv | ⟨hun, -⟩
      · rw [← Gate.eval_subst (hJw hv)]
        exact Gate.eval_congr fun i hi =>
          (hw i fun he => Gate.not_reads_subst hℓJ (he ▸ hi)).symm
      · rw [Gate.eval_subst_of_not_reads (hun K hK)]
        exact Gate.eval_congr fun i hi => (hw i fun he => hun K hK (he ▸ hi)).symm
  · change (C.out.subst J ℓ).eval val = _
    rcases h.value with hv | ⟨-, hun⟩
    · rw [← Lit.eval_subst (hJw hv)]
      exact Lit.eval_congr fun i hi => (hw i fun he => Lit.not_reads_subst hℓJ (he ▸ hi)).symm
    · rw [Lit.subst_of_not_reads hun]
      exact Lit.eval_congr fun i hi => (hw i fun he => hun (he ▸ hi)).symm

/-! ### Deleting an equation -/

/-- Delete the equation `e`, which reads `v = ℓ`, and the auxiliary variable `v`, rerouting `v`
to `ℓ`. -/
def deleteEqn (C : SemiCircuit) (e v : ℕ) (ℓ : Lit) : SemiCircuit :=
  { C.subst v ℓ with aux := C.aux.erase v, eqns := C.eqns.erase e }

/-- The hypotheses of deleting an equation: `e` is an equation stating `v = ℓ` for an auxiliary
variable `v` and a literal `ℓ` reading at most another term of `e`. -/
structure DeleteEqnOK (C : SemiCircuit) (e v : ℕ) (ℓ : Lit) : Prop where
  mem : e ∈ C.eqns
  aux : v ∈ C.aux
  holds : ∀ val, (C.eqn e).Holds val ↔ val v = ℓ.eval val
  reads : ∀ t, ℓ.Reads t → t ∈ (C.eqn e).terms ∧ t ≠ v

/-- Any live node of `C` distinct from `v` remains live in `C.deleteEqn e v ℓ`. -/
theorem mem_live_deleteEqn {e v : ℕ} {ℓ : Lit} {i : ℕ} (hi : i ∈ C.live) (hiv : i ≠ v) :
    i ∈ (C.deleteEqn e v ℓ).live := by
  simp only [live, Finset.mem_union] at hi ⊢
  change (i ∈ C.params ∨ i ∈ C.aux.erase v) ∨ i ∈ C.gates
  rw [Finset.mem_erase]
  tauto

/-- A solution of the affine system after deleting `v = ℓ` extends to a solution of the original
system by giving `v` the value of `ℓ`. -/
private theorem DeleteEqnOK.eqnsHold {e v : ℕ} {ℓ : Lit} (h : C.DeleteEqnOK e v ℓ) {val : ℕ → Bool}
    (hval : (C.deleteEqn e v ℓ).EqnsHold val) :
    C.EqnsHold (Function.update val v (ℓ.eval val)) := by
  have hℓv : ℓ.arg ≠ .node v := fun he => (h.reads v he).2 rfl
  intro e' he'
  by_cases hee : e' = e
  · subst hee
    refine (h.holds _).2 ?_
    rw [Function.update_self]
    exact Lit.eval_congr fun i hi =>
      (Function.update_of_ne (by rintro rfl; exact hℓv hi) _ _).symm
  · exact (Equation.holds_subst_update hℓv val).1 (hval e' (Finset.mem_erase.2 ⟨hee, he'⟩))

/-- Deleting an equation `v = ℓ` with its auxiliary variable preserves well-formedness. -/
theorem WellFormed.deleteEqn (hC : C.WellFormed) {e v : ℕ} {ℓ : Lit} (h : C.DeleteEqnOK e v ℓ) :
    (C.deleteEqn e v ℓ).WellFormed := by
  have hℓv : ℓ.arg ≠ .node v := fun he => (h.reads v he).2 rfl
  have hℓpa : ∀ t, ℓ.Reads t → t ∈ C.params ∪ C.aux := fun t ht =>
    hC.terms_subset e h.mem (h.reads t ht).1
  have hvp : v ∉ C.params := hC.notMem_params_of_mem_aux h.aux
  refine
    { disjoint_params_aux := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_params_aux
      disjoint_params_gates := hC.disjoint_params_gates
      disjoint_aux_gates := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
        hC.disjoint_aux_gates
      reads_lt := fun K hK i hi hr => ?_
      reads_live := fun K hK i hr => ?_
      terms_subset := fun e' he' z hz => ?_
      card_terms_le := fun e' he' => Equation.card_subst_le.trans
        (hC.card_terms_le e' (Finset.mem_of_mem_erase he'))
      out_live := fun i hi => ?_
      solvable := fun u => ?_
      unique := fun val val' hagree heq heq' a ha => ?_ }
  · rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hC.reads_lt K hK i hi hr
    · exfalso
      rcases Finset.mem_union.1 (hℓpa i hr) with hp | ha
      · exact hC.notMem_gates_of_mem_params hp hi
      · exact hC.notMem_gates_of_mem_aux ha hi
  · refine mem_live_deleteEqn ?_ fun he => Gate.not_reads_subst hℓv (he ▸ hr)
    rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hC.reads_live K hK i hr
    · simp only [live, Finset.mem_union]
      exact Or.inl (Finset.mem_union.1 (hℓpa i hr))
  · have hzv : z ≠ v := fun he => Equation.notMem_subst hℓv (he ▸ hz)
    have hmem : z ∈ C.params ∪ C.aux := by
      rcases Equation.mem_of_mem_subst hz with hz | ⟨-, hz⟩
      · exact hC.terms_subset e' (Finset.mem_of_mem_erase he') hz
      · exact hℓpa z hz
    change z ∈ C.params ∪ C.aux.erase v
    simp only [Finset.mem_union, Finset.mem_erase] at hmem ⊢
    tauto
  · refine mem_live_deleteEqn ?_ fun he => Lit.not_reads_subst hℓv (he ▸ hi)
    rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
    · exact hC.out_live i hi
    · simp only [live, Finset.mem_union]
      exact Or.inl (Finset.mem_union.1 (hℓpa i hi))
  · obtain ⟨val, hu, heq⟩ := hC.solvable u
    have hv : val v = ℓ.eval val := (h.holds val).1 (heq e h.mem)
    exact ⟨val, hu, fun e' he' =>
      (Equation.holds_subst hv).2 (heq e' (Finset.mem_of_mem_erase he'))⟩
  · have hext : ∀ w : ℕ → Bool, ∀ i, i ≠ v → Function.update w v (ℓ.eval w) i = w i :=
      fun w i hi => Function.update_of_ne hi _ _
    have := hC.unique _ _ (fun j hj => by
        rw [hext val j fun he => hvp (he ▸ hj), hext val' j fun he => hvp (he ▸ hj)]
        exact hagree j hj) (h.eqnsHold heq) (h.eqnsHold heq') a (Finset.mem_of_mem_erase ha)
    rwa [hext val a (Finset.ne_of_mem_erase ha), hext val' a (Finset.ne_of_mem_erase ha)] at this

/-- A consistent assignment after deleting `v = ℓ` lifts, by giving `v` the value of `ℓ`. -/
theorem DeleteEqnOK.liftsTo (hC : C.WellFormed) {e v : ℕ} {ℓ : Lit} (h : C.DeleteEqnOK e v ℓ) :
    (C.deleteEqn e v ℓ).LiftsTo C := by
  intro val hval
  have hℓv : ℓ.arg ≠ .node v := fun he => (h.reads v he).2 rfl
  have hvg : v ∉ C.gates := hC.notMem_gates_of_mem_aux h.aux
  refine ⟨Function.update val v (ℓ.eval val), ⟨h.eqnsHold hval.1, fun K hK => ?_⟩,
    fun j hj => Function.update_of_ne
      (by rintro rfl; exact hC.notMem_params_of_mem_aux h.aux hj) _ _,
    Lit.eval_subst_update hℓv val⟩
  rw [Function.update_of_ne (by rintro rfl; exact hvg hK), hval.2 K hK]
  exact Gate.eval_subst_update hℓv val

/-! ### Dropping an equation -/

/-- Delete the equation `e` together with an auxiliary variable `v` occurring nowhere else. -/
def dropEqn (C : SemiCircuit) (e v : ℕ) : SemiCircuit :=
  { C with aux := C.aux.erase v, eqns := C.eqns.erase e }

/-- The hypotheses of dropping an equation: the auxiliary variable `v` occurs in the equation
`e` and nowhere else. -/
structure DropEqnOK (C : SemiCircuit) (e v : ℕ) : Prop where
  mem : e ∈ C.eqns
  aux : v ∈ C.aux
  mem_terms : v ∈ (C.eqn e).terms
  only : ∀ e' ∈ C.eqns, e' ≠ e → v ∉ (C.eqn e').terms
  gates : ∀ K ∈ C.gates, ¬ (C.gate K).Reads v
  out : ¬ C.out.Reads v

/-- The value of the dropped auxiliary variable solving its equation. -/
private def dropEqnValue (C : SemiCircuit) (e v : ℕ) (val : ℕ → Bool) : ℕ → Bool :=
  Function.update val v ((C.eqn e).rhs + ∑ i ∈ (C.eqn e).terms.erase v, val i)

private theorem DropEqnOK.eqnsHold {e v : ℕ} (h : C.DropEqnOK e v) {val : ℕ → Bool}
    (hval : (C.dropEqn e v).EqnsHold val) : C.EqnsHold (C.dropEqnValue e v val) := by
  have hext : ∀ i, i ≠ v → C.dropEqnValue e v val i = val i := fun i hi =>
    Function.update_of_ne hi _ _
  intro e' he'
  by_cases hee : e' = e
  · subst hee
    unfold Equation.Holds
    rw [← Finset.add_sum_erase _ _ h.mem_terms,
      Finset.sum_congr rfl fun i hi => hext i (Finset.ne_of_mem_erase hi)]
    change Function.update val v _ v + _ = _
    rw [Function.update_self, add_assoc, BooleanRing.add_self, add_zero]
  · exact (Equation.holds_congr fun i hi => hext i fun he => h.only e' he' hee (he ▸ hi)).2
      (hval e' (Finset.mem_erase.2 ⟨hee, he'⟩))

/-- Dropping an equation with an auxiliary variable occurring only there preserves
well-formedness. -/
theorem WellFormed.dropEqn (hC : C.WellFormed) {e v : ℕ} (h : C.DropEqnOK e v) :
    (C.dropEqn e v).WellFormed := by
  have hvp : v ∉ C.params := hC.notMem_params_of_mem_aux h.aux
  have hlive : ∀ i, i ∈ C.live → i ≠ v → i ∈ (C.dropEqn e v).live := fun i hi hiv => by
    simp only [live, Finset.mem_union] at hi ⊢
    change (i ∈ C.params ∨ i ∈ C.aux.erase v) ∨ i ∈ C.gates
    rw [Finset.mem_erase]
    tauto
  refine
    { disjoint_params_aux := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_params_aux
      disjoint_params_gates := hC.disjoint_params_gates
      disjoint_aux_gates := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
        hC.disjoint_aux_gates
      reads_lt := hC.reads_lt
      reads_live := fun K hK i hr =>
        hlive i (hC.reads_live K hK i hr) fun he => h.gates K hK (he ▸ hr)
      terms_subset := fun e' he' z hz => ?_
      card_terms_le := fun e' he' => hC.card_terms_le e' (Finset.mem_of_mem_erase he')
      out_live := fun i hi => hlive i (hC.out_live i hi) fun he => h.out (he ▸ hi)
      solvable := fun u => by
        obtain ⟨val, hu, heq⟩ := hC.solvable u
        exact ⟨val, hu, fun e' he' => heq e' (Finset.mem_of_mem_erase he')⟩
      unique := fun val val' hagree heq heq' a ha => ?_ }
  · have := hC.terms_subset e' (Finset.mem_of_mem_erase he') hz
    have hzv : z ≠ v := fun he =>
      h.only e' (Finset.mem_of_mem_erase he') (Finset.ne_of_mem_erase he') (he ▸ hz)
    change z ∈ C.params ∪ C.aux.erase v
    simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
    tauto
  · have hext : ∀ w : ℕ → Bool, ∀ i, i ≠ v → C.dropEqnValue e v w i = w i :=
      fun w i hi => Function.update_of_ne hi _ _
    have := hC.unique _ _ (fun j hj => by
        rw [hext val j fun he => hvp (he ▸ hj), hext val' j fun he => hvp (he ▸ hj)]
        exact hagree j hj) (h.eqnsHold heq) (h.eqnsHold heq') a (Finset.mem_of_mem_erase ha)
    rwa [hext val a (Finset.ne_of_mem_erase ha), hext val' a (Finset.ne_of_mem_erase ha)] at this

/-- A consistent assignment after dropping an equation lifts, by solving the equation for the
dropped auxiliary variable. -/
theorem DropEqnOK.liftsTo (hC : C.WellFormed) {e v : ℕ} (h : C.DropEqnOK e v) :
    (C.dropEqn e v).LiftsTo C := by
  intro val hval
  have hext : ∀ i, i ≠ v → C.dropEqnValue e v val i = val i := fun i hi =>
    Function.update_of_ne hi _ _
  refine ⟨C.dropEqnValue e v val, ⟨h.eqnsHold hval.1, fun K hK => ?_⟩,
    fun j hj => hext j fun he => hC.notMem_params_of_mem_aux h.aux (he ▸ hj),
    Lit.eval_congr fun i hi => (hext i fun he => h.out (he ▸ hi)).symm⟩
  rw [hext K fun he => hC.notMem_gates_of_mem_aux h.aux (he ▸ hK), hval.2 K hK]
  exact Gate.eval_congr fun i hi => (hext i fun he => h.gates K hK (he ▸ hi)).symm

/-- Delete an equation without terms. -/
def dropTrivialEqn (C : SemiCircuit) (e : ℕ) : SemiCircuit :=
  { C with eqns := C.eqns.erase e }

/-- An equation without terms of a well-formed semi-circuit always holds, so dropping it keeps
the solutions of the affine system. -/
private theorem eqnsHold_dropTrivialEqn (hC : C.WellFormed) {e : ℕ} (he : e ∈ C.eqns)
    (hterms : (C.eqn e).terms = ∅) (val : ℕ → Bool) :
    (C.dropTrivialEqn e).EqnsHold val ↔ C.EqnsHold val := by
  have htriv : (C.eqn e).Holds val := by
    obtain ⟨val₀, -, heq⟩ := hC.solvable 0
    have h0 := heq e he
    unfold Equation.Holds at h0 ⊢
    rw [hterms, Finset.sum_empty] at h0 ⊢
    exact h0
  refine ⟨fun h e' he' => ?_, fun h e' he' => h e' (Finset.mem_of_mem_erase he')⟩
  by_cases hee : e' = e
  · subst hee; exact htriv
  · exact h e' (Finset.mem_erase.2 ⟨hee, he'⟩)

/-- Dropping an equation with no terms preserves well-formedness. -/
theorem WellFormed.dropTrivialEqn (hC : C.WellFormed) {e : ℕ} (he : e ∈ C.eqns)
    (hterms : (C.eqn e).terms = ∅) : (C.dropTrivialEqn e).WellFormed where
  disjoint_params_aux := hC.disjoint_params_aux
  disjoint_params_gates := hC.disjoint_params_gates
  disjoint_aux_gates := hC.disjoint_aux_gates
  reads_lt := hC.reads_lt
  reads_live := hC.reads_live
  terms_subset := fun e' he' => hC.terms_subset e' (Finset.mem_of_mem_erase he')
  card_terms_le := fun e' he' => hC.card_terms_le e' (Finset.mem_of_mem_erase he')
  out_live := hC.out_live
  solvable := fun u => by
    obtain ⟨val, hu, heq⟩ := hC.solvable u
    exact ⟨val, hu, (eqnsHold_dropTrivialEqn hC he hterms val).2 heq⟩
  unique := fun val val' hagree heq heq' =>
    hC.unique val val' hagree ((eqnsHold_dropTrivialEqn hC he hterms val).1 heq)
      ((eqnsHold_dropTrivialEqn hC he hterms val').1 heq')

/-- Every consistent assignment after dropping an equation with no terms is consistent for the
original semi-circuit. -/
theorem liftsTo_dropTrivialEqn (hC : C.WellFormed) {e : ℕ} (he : e ∈ C.eqns)
    (hterms : (C.eqn e).terms = ∅) : (C.dropTrivialEqn e).LiftsTo C := fun val hval =>
  ⟨val, ⟨(eqnsHold_dropTrivialEqn hC he hterms val).1 hval.1, hval.2⟩, fun _ _ => rfl, rfl⟩

end Cslib.Circuits.Boolean.SemiCircuit
