/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit

/-!
# Exchanging parameters

Two changes of the parameters of a fair semi-circuit, the semi-circuit side of the
reparameterisations (AR) and (QR) of [Mishra and Santhanam, Section 3.2][MishraSanthanam2026]:

* `SemiCircuit.swap`: a parameter `x` and an auxiliary variable `Q` depending on it exchange their
  roles; no gate or equation changes, and well-formedness is preserved (`WellFormed.swap`), since
  on the solutions of the affine system `x` is determined by `Q` and the other parameters
  (`AffineIn.solve`);
* `SemiCircuit.quad`: for an AND-type gate `G` whose only child is the XOR-type gate `D = G + z + c`
  reading an isolated parameter `z`, the gate `D` becomes a parameter in place of `z` and both gates
  are deleted (`WellFormed.quad`); a consistent assignment of the result, with `z` and `G` given
  their values, is consistent for the original semi-circuit (`QuadOK.consistent`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.swap`, `Cslib.Circuits.Boolean.SemiCircuit.quad`,
  `Cslib.Circuits.Boolean.SemiCircuit.QuadOK`, `Cslib.Circuits.Boolean.SemiCircuit.quadValue`.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.WellFormed.swap`,
  `Cslib.Circuits.Boolean.SemiCircuit.WellFormed.quad`: well-formedness is preserved.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Finset

variable {C : SemiCircuit}

/-! ### Exchanging a parameter and an auxiliary variable -/

/-- Exchange the parameter `x` with the auxiliary variable `Q`. No equation or gate changes. -/
def swap (C : SemiCircuit) (x Q : ℕ) : SemiCircuit :=
  { C with params := insert Q (C.params.erase x), aux := insert x (C.aux.erase Q) }

/-- On the solutions of the affine system, a parameter `x` on which `Q = c + ∑ j ∈ T, u j`
depends is `Q + c + ∑ j ∈ T \ {x}, u j`. -/
theorem AffineIn.solve {Q x : ℕ} {c : Bool} {T : Finset ℕ} (h : C.AffineIn Q c T) (hxT : x ∈ T)
    {val : ℕ → Bool} (hval : C.EqnsHold val) : val x = val Q + c + ∑ j ∈ T.erase x, val j := by
  rw [h.2 val hval, ← Finset.add_sum_erase T _ hxT]
  generalize val x = a; generalize ∑ j ∈ T.erase x, val j = b
  cases a <;> cases b <;> cases c <;> rfl

private theorem params_union_aux_swap {x Q : ℕ} (hx : x ∈ C.params) (hQ : Q ∈ C.aux) :
    (C.swap x Q).params ∪ (C.swap x Q).aux = C.params ∪ C.aux := by
  ext i
  change i ∈ insert Q (C.params.erase x) ∪ insert x (C.aux.erase Q) ↔ _
  by_cases hix : i = x
  · subst hix; simp [hx]
  · by_cases hiQ : i = Q
    · subst hiQ; simp [hQ]
    · simp [hix, hiQ]

private theorem live_swap {x Q : ℕ} (hx : x ∈ C.params) (hQ : Q ∈ C.aux) :
    (C.swap x Q).live = C.live := by
  change (C.swap x Q).params ∪ (C.swap x Q).aux ∪ C.gates = _
  rw [params_union_aux_swap hx hQ]
  rfl

/-- Exchanging a parameter `x` with an auxiliary variable depending on it preserves
well-formedness. -/
theorem WellFormed.swap (hC : C.WellFormed) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (hx : x ∈ C.params) (hQ : Q ∈ C.aux) (haff : C.AffineIn Q c T) (hxT : x ∈ T) :
    (C.swap x Q).WellFormed := by
  have hQx : Q ≠ x := fun he => hC.notMem_params_of_mem_aux hQ (he ▸ hx)
  have hpa := params_union_aux_swap hx hQ
  have hlive := live_swap hx hQ
  refine
    { disjoint_params_aux := ?_
      disjoint_params_gates := Finset.disjoint_left.2 fun i hi hg => ?_
      disjoint_aux_gates := Finset.disjoint_left.2 fun i hi hg => ?_
      reads_lt := hC.reads_lt
      reads_live := fun K hK i hr => hlive ▸ hC.reads_live K hK i hr
      terms_subset := fun e he z hz => hpa ▸ hC.terms_subset e he hz
      card_terms_le := hC.card_terms_le
      out_live := fun i hi => hlive ▸ hC.out_live i hi
      solvable := fun u => ?_
      unique := fun val val' hagree heq heq' a ha => ?_ }
  · rw [Finset.disjoint_left]
    intro i hi hi'
    change i ∈ insert Q (C.params.erase x) at hi
    change i ∈ insert x (C.aux.erase Q) at hi'
    simp only [Finset.mem_insert, Finset.mem_erase] at hi hi'
    rcases hi with rfl | ⟨hix, hp⟩ <;> rcases hi' with rfl | ⟨hiQ, ha⟩
    · exact hQx rfl
    · exact hiQ rfl
    · exact hix rfl
    · exact hC.notMem_aux_of_mem_params hp ha
  · change i ∈ insert Q (C.params.erase x) at hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hC.notMem_gates_of_mem_aux hQ hg
    · exact hC.notMem_gates_of_mem_params (Finset.mem_of_mem_erase hi) hg
  · change i ∈ insert x (C.aux.erase Q) at hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hC.notMem_gates_of_mem_params hx hg
    · exact hC.notMem_gates_of_mem_aux (Finset.mem_of_mem_erase hi) hg
  · obtain ⟨val, hu, heq⟩ := hC.solvable
      (Function.update u x (u Q + c + ∑ j ∈ T.erase x, u j))
    refine ⟨val, fun j hj => ?_, heq⟩
    change j ∈ insert Q (C.params.erase x) at hj
    have hT : ∀ i ∈ T.erase x, val i = u i := fun i hi => by
      rw [hu i (haff.1 (Finset.mem_of_mem_erase hi)),
        Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have h1 := haff.solve hxT heq
      rw [hu x hx, Function.update_self, Finset.sum_congr rfl hT] at h1
      generalize u j = a at h1 ⊢; generalize val j = b at h1 ⊢
      generalize ∑ i ∈ T.erase x, u i = s at h1
      cases a <;> cases b <;> cases c <;> cases s <;> simp_all
    · rw [hu j (Finset.mem_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · have hparams : ∀ j ∈ C.params, val j = val' j := by
      intro j hj
      by_cases hjx : j = x
      · subst hjx
        rw [haff.solve hxT heq, haff.solve hxT heq', hagree Q (Finset.mem_insert_self _ _),
          Finset.sum_congr rfl fun i hi => hagree i (Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hi,
              haff.1 (Finset.mem_of_mem_erase hi)⟩))]
      · exact hagree j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjx, hj⟩))
    change a ∈ insert x (C.aux.erase Q) at ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hparams a hx
    · exact hC.unique val val' hparams heq heq' a (Finset.mem_of_mem_erase ha)

/-! ### The quadratic reparameterisation -/

/-- Turn the gate `D` into a parameter in place of `z`, and delete the gates `G` and `D`. -/
def quad (C : SemiCircuit) (z G D : ℕ) : SemiCircuit :=
  { C with params := insert D (C.params.erase z), gates := (C.gates.erase D).erase G }

/-- Any live node of `C` distinct from `z` and `G` remains live in `C.quad z G D`. -/
theorem mem_live_quad {z G D i : ℕ} (hi : i ∈ C.live) (hiz : i ≠ z) (hiG : i ≠ G) :
    i ∈ (C.quad z G D).live := by
  simp only [live, Finset.mem_union] at hi ⊢
  change (i ∈ insert D (C.params.erase z) ∨ i ∈ C.aux) ∨ i ∈ (C.gates.erase D).erase G
  simp only [Finset.mem_insert, Finset.mem_erase]
  by_cases hiD : i = D
  · exact Or.inl (Or.inl (Or.inl hiD))
  · tauto

/-- The configuration of the quadratic reparameterisation: an AND-type gate
`G = (x + α)(y + β) + γ` on the distinct parameters `x` and `y`, whose only child is the XOR-type
gate `D = G + z + c`, where `D` is the only child of the parameter `z`, and neither `G` nor `z` is
the output. -/
structure QuadOK (C : SemiCircuit) (x y z G D : ℕ) (α β γ c : Bool) : Prop where
  mem_x : x ∈ C.params
  mem_y : y ∈ C.params
  mem_z : z ∈ C.params
  x_ne_y : x ≠ y
  x_ne_z : x ≠ z
  y_ne_z : y ≠ z
  mem_G : G ∈ C.gates
  mem_D : D ∈ C.gates
  G_ne_D : G ≠ D
  eval_G : ∀ val, (C.gate G).eval val = (val x + α) * (val y + β) + γ
  eval_D : ∀ val, (C.gate D).eval val = val G + val z + c
  children_G : C.children G = {.inl D}
  children_z : C.children z = {.inl D}
  out_G : ¬ C.out.Reads G
  out_z : ¬ C.out.Reads z

namespace QuadOK

variable {x y z G D : ℕ} {α β γ c : Bool} (h : C.QuadOK x y z G D α β γ c)
include h

private theorem notMem_terms_z {e : ℕ} (he : e ∈ C.eqns) : z ∉ (C.eqn e).terms := fun hz => by
  have : Sum.inr e ∈ C.children z := (inr_mem_children _).2 ⟨he, hz⟩
  rw [h.children_z] at this
  simp at this

private theorem not_reads_z {K : ℕ} (hK : K ∈ C.gates) (hKD : K ≠ D) : ¬ (C.gate K).Reads z :=
  fun hr => by
    have : Sum.inl K ∈ C.children z := (inl_mem_children _).2 ⟨hK, hr⟩
    rw [h.children_z] at this
    exact hKD (Sum.inl.inj (Finset.mem_singleton.1 this))

private theorem not_reads_G {K : ℕ} (hK : K ∈ C.gates) (hKD : K ≠ D) : ¬ (C.gate K).Reads G :=
  fun hr => by
    have : Sum.inl K ∈ C.children G := (inl_mem_children _).2 ⟨hK, hr⟩
    rw [h.children_G] at this
    exact hKD (Sum.inl.inj (Finset.mem_singleton.1 this))

end QuadOK

/-- The quadratic reparameterisation preserves well-formedness. -/
theorem WellFormed.quad (hC : C.WellFormed) {x y z G D : ℕ} {α β γ c : Bool}
    (h : C.QuadOK x y z G D α β γ c) : (C.quad z G D).WellFormed := by
  refine
    { disjoint_params_aux := Finset.disjoint_left.2 fun i hi ha => ?_
      disjoint_params_gates := Finset.disjoint_left.2 fun i hi hg => ?_
      disjoint_aux_gates := Finset.disjoint_of_subset_right
        ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hC.disjoint_aux_gates
      reads_lt := fun K hK i hi hr => hC.reads_lt K
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hK)) i
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)) hr
      reads_live := fun K hK i hr => ?_
      terms_subset := fun e he t ht => ?_
      card_terms_le := hC.card_terms_le
      out_live := fun i hi => mem_live_quad (hC.out_live i hi) (fun he => h.out_z (he ▸ hi))
        (fun he => h.out_G (he ▸ hi))
      solvable := fun u => ?_
      unique := fun val val' hagree heq heq' a ha => ?_ }
  · change i ∈ insert D (C.params.erase z) at hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hC.notMem_aux_of_mem_gates h.mem_D ha
    · exact hC.notMem_aux_of_mem_params (Finset.mem_of_mem_erase hi) ha
  · change i ∈ insert D (C.params.erase z) at hi
    change i ∈ (C.gates.erase D).erase G at hg
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact Finset.notMem_erase i _ (Finset.mem_of_mem_erase hg)
    · exact hC.notMem_gates_of_mem_params (Finset.mem_of_mem_erase hi)
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg))
  · change K ∈ (C.gates.erase D).erase G at hK
    have hKD := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hK)
    have hK' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hK)
    exact mem_live_quad (hC.reads_live K hK' i hr) (fun he => h.not_reads_z hK' hKD (he ▸ hr))
      (fun he => h.not_reads_G hK' hKD (he ▸ hr))
  · have := hC.terms_subset e he ht
    have htz : t ≠ z := fun he' => h.notMem_terms_z he (he' ▸ ht)
    change t ∈ insert D (C.params.erase z) ∪ C.aux
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at this ⊢
    tauto
  · obtain ⟨val, hu, heq⟩ := hC.solvable u
    refine ⟨Function.update val D (u D), fun j hj => ?_, fun e he => ?_⟩
    · change j ∈ insert D (C.params.erase z) at hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact Function.update_self _ _ _
      · rw [Function.update_of_ne (show j ≠ D from fun he =>
          hC.notMem_params_of_mem_gates h.mem_D (he ▸ Finset.mem_of_mem_erase hj)),
          hu j (Finset.mem_of_mem_erase hj)]
    · exact (Equation.holds_congr fun i hi => Function.update_of_ne
        (show i ≠ D from fun he' => hC.notMem_terms_of_mem_gates h.mem_D he (he' ▸ hi)) _ _).2
          (heq e he)
  · have hold : ∀ w : ℕ → Bool, C.EqnsHold w → C.EqnsHold (Function.update w z false) :=
      fun w hw e he => (Equation.holds_congr fun i hi => Function.update_of_ne
        (show i ≠ z from fun he' => h.notMem_terms_z he (he' ▸ hi)) _ _).2 (hw e he)
    have := hC.unique _ _ (fun j hj => by
        by_cases hjz : j = z
        · subst hjz; simp only [Function.update_self]
        · simp only [Function.update_of_ne hjz]
          exact hagree j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjz, hj⟩)))
      (hold val heq) (hold val' heq') a ha
    have haz : a ≠ z := fun he => hC.notMem_aux_of_mem_params (he ▸ h.mem_z) ha
    simpa only [Function.update_of_ne haz] using this

/-- The assignment of the original semi-circuit determined by an assignment of its quadratic
reparameterisation: `z = D + G + c` and `G` takes its value. -/
def quadValue (x y z G D : ℕ) (α β γ c : Bool) (val : ℕ → Bool) : ℕ → Bool :=
  Function.update (Function.update val z (val D + ((val x + α) * (val y + β) + γ) + c)) G
    ((val x + α) * (val y + β) + γ)

/-- A consistent assignment of the quadratic reparameterisation gives a consistent assignment of
the original semi-circuit with the same output. -/
theorem QuadOK.consistent (hC : C.WellFormed) {x y z G D : ℕ} {α β γ c : Bool}
    (h : C.QuadOK x y z G D α β γ c) {val : ℕ → Bool} (hval : (C.quad z G D).Consistent val) :
    C.Consistent (quadValue x y z G D α β γ c val) ∧
      (C.quad z G D).out.eval val = C.out.eval (quadValue x y z G D α β γ c val) := by
  have hzG : z ≠ G := fun he => hC.notMem_gates_of_mem_params h.mem_z (he ▸ h.mem_G)
  have hxG : x ≠ G := fun he => hC.notMem_gates_of_mem_params h.mem_x (he ▸ h.mem_G)
  have hyG : y ≠ G := fun he => hC.notMem_gates_of_mem_params h.mem_y (he ▸ h.mem_G)
  have hDz : D ≠ z := fun he => hC.notMem_gates_of_mem_params h.mem_z (he ▸ h.mem_D)
  set σ := quadValue x y z G D α β γ c val
  have hσ : ∀ i, i ≠ z → i ≠ G → σ i = val i := fun i hz hG => by
    simp only [σ, quadValue, Function.update_of_ne hG, Function.update_of_ne hz]
  have hσx : σ x = val x := hσ x h.x_ne_z hxG
  have hσy : σ y = val y := hσ y h.y_ne_z hyG
  refine ⟨⟨fun e he => (Equation.holds_congr fun i hi => hσ i
    (fun he' => h.notMem_terms_z he (he' ▸ hi))
    (fun he' => hC.notMem_terms_of_mem_gates h.mem_G he (he' ▸ hi))).2 (hval.1 e he),
    fun K hK => ?_⟩, Lit.eval_congr fun i hi => (hσ i (fun he => h.out_z (he ▸ hi))
      (fun he => h.out_G (he ▸ hi))).symm⟩
  by_cases hKG : K = G
  · subst hKG
    rw [h.eval_G, hσx, hσy]
    simp only [σ, quadValue, Function.update_self]
  · by_cases hKD : K = D
    · subst hKD
      rw [hσ K hDz hKG, h.eval_D]
      simp only [σ, quadValue, Function.update_self, Function.update_of_ne hzG]
      generalize val K = a; generalize (val x + α) * (val y + β) + γ = b
      cases a <;> cases b <;> cases c <;> rfl
    · have hK' : K ∈ (C.quad z G D).gates :=
        Finset.mem_erase.2 ⟨hKG, Finset.mem_erase.2 ⟨hKD, hK⟩⟩
      have hKz : K ≠ z := fun he => hC.notMem_gates_of_mem_params h.mem_z (he ▸ hK)
      rw [hσ K hKz hKG, hval.2 K hK']
      exact Gate.eval_congr fun i hi => (hσ i (fun he => h.not_reads_z hK hKD (he ▸ hi))
        (fun he => h.not_reads_G hK hKD (he ▸ hi))).symm

end Cslib.Circuits.Boolean.SemiCircuit
