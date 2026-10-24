/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.MinimalAnd

/-!
# Eliminating the minimal AND

Section 4.3 of [Mishra and Santhanam][MishraSanthanam2026]: in a normal state with `d < a`,
eliminating a minimal AND `G` on the inputs `x` and `y` (`State.MinimalAnd`) is a step of gate
elimination (`State.Valid.step_of_minimalAnd`):

* Case 7, `State.SharedSecondChild`: `deg x = deg y = 2` and `x`, `y` share their second child
  `B`; restricting to a line of `𝔽₂²` on which `G` and `B` are constant (`exists_line_const`)
  deletes both (`State.Valid.step_of_sharedSecondChild`), `ΔW ≤ -18`, `Δa = -1`;
* the bottleneck configuration, `State.Bottleneck`: `deg x = 2` and the unique child `D` of `G`
  reads an unpaired isolated parameter `z`. If `D` is AND-type, fixing `x` and `y` makes `G` and
  `D` constant (Case 9, `State.Valid.step_of_bottleneck_and`, `ΔW ≤ -28`, `Δa = -2`); otherwise
  `D` is XOR-type and the quadratic reparameterisation deletes `G` and `D` (Case 10,
  `State.Valid.step_of_bottleneck_xor`, `ΔW ≤ -14`, `Δa = -1`);
* Case 8, otherwise: fixing `x` so that `G` becomes constant deletes all children of `x` and of
  `G` (`State.Valid.step_fixInput`), `Δa = -1`; only the unpaired isolated parameters below `G`
  can gain weight, at most `deg G` of them (`State.Valid.card_isolated_le`,
  `State.Reduction.wt_add_le_fixInput`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.SharedSecondChild`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Bottleneck`: the configurations of Section 4.3.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.step_of_minimalAnd`: eliminating the
  minimal AND is a step of gate elimination.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Case 7: a shared second child -/

/-- The configuration of Case 7 of [Mishra and Santhanam][MishraSanthanam2026]: `deg x = 2` and
the inputs of the minimal AND share their second child `B`. -/
def SharedSecondChild (S : State n) (G x y : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ B, B ≠ .inl G ∧ B ∈ S.children x ∧ B ∈ S.children y

/-- Restricting one input `x'` of the minimal AND and deleting its two children `G` and `B`,
which are also the children of the other input `y'`, is a step: `Δa = -1`, `ΔW ≤ -18`. -/
private theorem Reduction.step_of_shared {S S' : State n} (hS : S.Valid f) {G x' y' : ℕ}
    {B : ℕ ⊕ ℕ} (hx' : x' ∈ S.unpaired) (hy' : y' ∈ S.unpaired) (hxy : x' ≠ y')
    (hx'2 : S.deg x' = 2) (hy'2 : S.deg y' = 2) (hcy : S.children y' = {.inl G, B})
    (h : Reduction f S S' {x'} [.inl G, B] []) : Step f S S' := by
  have hx'p : ¬ S.Paired x' := (mem_unpaired.1 hx').2
  refine h.step hS (by simp) (by simp) ?_
  have hW := h.W_le (fun u => if u = y' then 7 else 0) (fun _ => 0) fun u hu => by
    by_cases huy : u = y'
    · subst huy
      rw [h.wt_eq_zero_of_subset (by simp [hcy]) (by simp), wt_of_mem hy', ite_eq_left rfl,
        weight_of_two_le hy'2.ge]
    · rw [ite_eq_right huy]
      refine Nat.add_le_add_right (h.wt_le hS (fun z hz hzu => ?_) (by simp)) 0
      rw [Finset.mem_singleton] at hz
      exact hx'p (hz ▸ hzu.paired)
  have hy'm : y' ∈ S.params \ {x'} :=
    Finset.mem_sdiff.2 ⟨(mem_unpaired.1 hy').1, by simpa using hxy.symm⟩
  rw [Finset.sum_ite_eq_of_mem' _ _ _ hy'm, Finset.sum_singleton, wt_of_mem hx',
    weight_of_two_le hx'2.ge, hS.card_pairsMeeting_singleton, ite_eq_right hx'p] at hW
  simp only [Finset.sum_const_zero, List.length_cons, List.length_nil] at hW
  rw [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_right hx'p]
  omega

/-- Restricting a parameter `x'` to a constant or to a literal of another parameter with at least
its children, on which the gates `G` and `B ≠ G`, `B` not reading `G`, are constant, and deleting
both gates, is a reduction. -/
private theorem Valid.exists_reduction_restrict_deleteConst {S : State n} (hS : S.Valid f) {x' : ℕ}
    (hx' : x' ∈ S.params) {ℓ : Lit} (hℓ : ∀ t, ℓ.Reads t → t ∈ S.params ∧ t ≠ x' ∧
      S.children x' ⊆ S.children t ∧ (S.Paired x' → S.IsPartner x' t))
    {G B : ℕ} (hG : G ∈ S.gates) (hB : B ∈ S.gates) (hBG : B ≠ G)
    (hBGr : ¬ (S.gate B).Reads G) {c₁ c₂ : Bool}
    (hGc : ∀ val, (S.gate G).eval (Function.update val x' (ℓ.eval val)) = c₁)
    (hBc : ∀ val, (S.gate B).eval (Function.update val x' (ℓ.eval val)) = c₂) :
    ∃ S', Reduction f S S' {x'} [.inl G, .inl B] [] := by
  have hℓx : ℓ.arg ≠ .node x' := fun he => (hℓ x' he).2.1 rfl
  have h₁ := hS.reduction_restrict hx' hℓ
  have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := c₁) hG fun val _ => by
    rw [restrict_gate, Gate.eval_subst_update hℓx]; exact hGc val
  have hBGr' : ¬ ((S.gate B).subst x' ℓ).Reads G := fun hr => by
    rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hBGr hr
    · exact hS.wf.notMem_gates_of_mem_params (hℓ G hr).1 hG
  exact ⟨_, (h₁.trans_delete h₂).trans_delete (h₂.valid.reduction_deleteConst (J := B)
    (c := c₂) (Finset.mem_erase.2 ⟨hBG, hB⟩) fun val _ => by
      rw [deleteGate_gate, restrict_gate, Gate.eval_subst_of_not_reads hBGr',
        Gate.eval_subst_update hℓx]
      exact hBc val)⟩

/-- Case 7 when the shared second child `B` of `x` and `y` is a gate: on one of the lines `x = c`,
`y = c` or `x = y + c` both `G` and `B` are constant, and restricting to it deletes both. -/
private theorem Valid.exists_reduction_sharedGate {S : State n} (hS : S.Valid f) {G x y B : ℕ}
    (h : S.MinimalAnd G x y) (hcx : S.children x = {.inl G, .inl B})
    (hcy : S.children y = {.inl G, .inl B}) (hBG : B ≠ G) :
    ∃ S' x' y', ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      Reduction f S S' {x'} [.inl G, .inl B] [] := by
  obtain ⟨hB, hBx⟩ := (SemiCircuit.inl_mem_children _).1
    (show Sum.inl B ∈ S.children x by simp [hcx])
  obtain ⟨-, hBy⟩ := (SemiCircuit.inl_mem_children _).1
    (show Sum.inl B ∈ S.children y by simp [hcy])
  obtain ⟨φ, hφ, hG⟩ := h.exists_op
  obtain ⟨ψ, -, hBψ⟩ := Gate.exists_op_of_args (Gate.args_of_reads h.ne hBx hBy)
  have hyx := h.ne.symm
  have hBGr : ¬ (S.gate B).Reads G := fun hr =>
    (Gate.eq_or_eq_of_reads h.ne hBx hBy hr).elim (fun he => h.ne_gate hS h.mem_params_x he.symm)
      fun he => h.ne_gate hS h.mem_params_y he.symm
  have hconst : ∀ x' (c : Bool), ∀ t, (Lit.const c).Reads t → t ∈ S.params ∧ t ≠ x' ∧
      S.children x' ⊆ S.children t ∧ (S.Paired x' → S.IsPartner x' t) := fun _ _ t ht => by
    simp [Lit.Reads, Lit.const] at ht
  rcases exists_line_const (h := ψ) hφ with ⟨c, hφc, hψc⟩ | ⟨c, hφc, hψc⟩ | ⟨c, hφc, hψc⟩
  · -- the line `x = c`
    obtain ⟨S', hred⟩ := hS.exists_reduction_restrict_deleteConst h.mem_params_x (hconst x c) h.mem
      hB hBG hBGr (c₁ := φ c false) (c₂ := ψ c false)
      (fun val => by rw [hG, Lit.eval_const, Function.update_self, Function.update_of_ne hyx]
                     exact hφc _)
      (fun val => by rw [hBψ, Lit.eval_const, Function.update_self, Function.update_of_ne hyx]
                     exact hψc _)
    exact ⟨S', x, y, Or.inl ⟨rfl, rfl⟩, hred⟩
  · -- the line `y = c`
    obtain ⟨S', hred⟩ := hS.exists_reduction_restrict_deleteConst h.mem_params_y (hconst y c) h.mem
      hB hBG hBGr (c₁ := φ false c) (c₂ := ψ false c)
      (fun val => by rw [hG, Lit.eval_const, Function.update_self, Function.update_of_ne h.ne]
                     exact hφc _)
      (fun val => by rw [hBψ, Lit.eval_const, Function.update_self, Function.update_of_ne h.ne]
                     exact hψc _)
    exact ⟨S', y, x, Or.inr ⟨rfl, rfl⟩, hred⟩
  · -- the line `x = y + c`
    obtain ⟨S', hred⟩ := hS.exists_reduction_restrict_deleteConst (ℓ := ⟨.node y, c⟩)
      h.mem_params_x (fun t ht => by
        cases ht
        exact ⟨h.mem_params_y, hyx, by rw [hcx, hcy],
          fun hp => absurd hp (mem_unpaired.1 h.unpaired_x).2⟩)
      h.mem hB hBG hBGr (c₁ := φ c false) (c₂ := ψ c false)
      (fun val => by rw [hG, Function.update_self, Function.update_of_ne hyx]; exact hφc _)
      (fun val => by rw [hBψ, Function.update_self, Function.update_of_ne hyx]; exact hψc _)
    exact ⟨S', x, y, Or.inl ⟨rfl, rfl⟩, hred⟩

/-- Case 7 when the shared second child of `x` and `y` is an equation `v + x + y = rhs`:
restricting to the line `x = y + c` on which `G` is constant makes the equation read `v = rhs + c`,
and both are deleted. -/
private theorem Valid.exists_reduction_sharedEqn {S : State n} (hS : S.Valid f) (hN : S.Normal)
    {G x y e : ℕ} (h : S.MinimalAnd G x y) (hcx : S.children x = {.inl G, .inr e})
    (hcy : S.children y = {.inl G, .inr e}) :
    ∃ S', Reduction f S S' {x} [.inl G, .inr e] [] := by
  obtain ⟨he, hxe⟩ := (SemiCircuit.inr_mem_children _).1
    (show Sum.inr e ∈ S.children x by simp [hcx])
  obtain ⟨-, hye⟩ := (SemiCircuit.inr_mem_children _).1
    (show Sum.inr e ∈ S.children y by simp [hcy])
  obtain ⟨φ, hφ, hG⟩ := h.exists_op
  have hyx := h.ne.symm
  obtain ⟨v, hva, hvx, hvy, hterms⟩ := hS.eq_insert_of_mem_terms hN.no_deletion he
    h.mem_params_x h.mem_params_y h.ne hxe hye
  have hvG : v ≠ G := fun he' => hS.wf.notMem_gates_of_mem_aux hva (he' ▸ h.mem)
  obtain ⟨c, hφc⟩ : ∃ c, ∀ b, φ (b ^^ c) b = φ c false := by
    rcases exists_line_const (h := fun a b => a ^^ b) hφ with ⟨c, -, hc⟩ | ⟨c, -, hc⟩ | ⟨c, hc, -⟩
    · simpa using hc true
    · simpa using hc true
    · exact ⟨c, hc⟩
  have hxy' : Arg.node y ≠ Arg.node x := fun he => hyx (Arg.node.inj he)
  have h₁ := hS.reduction_restrict (ℓ := ⟨.node y, c⟩) h.mem_params_x fun t ht => by
    cases ht
    exact ⟨h.mem_params_y, hyx, by rw [hcx, hcy],
      fun hp => absurd hp (mem_unpaired.1 h.unpaired_x).2⟩
  have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := φ c false) h.mem fun val _ => by
    rw [restrict_gate, Gate.eval_subst_update hxy', hG, Function.update_self,
      Function.update_of_ne hyx]
    exact hφc _
  exact ⟨_, (h₁.trans_delete h₂).trans_delete
    (h₂.valid.reduction_deleteEqn (e := e) (v := v) (ℓ := Lit.const ((S.eqn e).rhs ^^ c))
      (T := []) ⟨he, hva, fun val => by
        rw [deleteGate_eqn, Equation.holds_subst_update (by simp [Lit.const]), restrict_eqn,
          Equation.holds_subst_update hxy', Lit.eval_const]
        simp only [Lit.eval, Arg.eval_node]
        rw [Equation.holds_update_iff hterms hvx hvy h.ne, Function.update_of_ne hvG]
        simp [Lit.const],
        fun t ht => by simp [Lit.Reads, Lit.const] at ht⟩
      fun t ht => by simp [Lit.Reads, Lit.const] at ht)⟩

/-- **Case 7** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: if both inputs `x`,
`y` of the minimal AND have degree two and share their second child `B`, restrict to a line of
`𝔽₂²` on which both `G` and `B` are constant (`exists_line_const`) and delete both; the other
input becomes unused: `Δa = -1`, `ΔW ≤ -18`. -/
theorem Valid.step_of_sharedSecondChild {S : State n} (hS : S.Valid f) (hN : S.Normal)
    {G x y : ℕ} (h : S.MinimalAnd G x y) (h7 : S.SharedSecondChild G x y) :
    ∃ S', Step f S S' := by
  obtain ⟨hx2, B, hBG, hBx, hBy⟩ := h7
  have hy2 : S.deg y = 2 := le_antisymm (hx2 ▸ h.deg_le) h.deg_y
  have hpair : ({.inl G, B} : Finset (ℕ ⊕ ℕ)).card = 2 := Finset.card_pair hBG.symm
  have hcx : S.children x = {.inl G, B} := (Finset.eq_of_subset_of_card_le
    (by simp [Finset.insert_subset_iff, h.mem_children_x, hBx])
    (by rw [hpair]; exact hx2.le)).symm
  have hcy : S.children y = {.inl G, B} := (Finset.eq_of_subset_of_card_le
    (by simp [Finset.insert_subset_iff, h.mem_children_y, hBy])
    (by rw [hpair]; exact hy2.le)).symm
  suffices key : ∃ S' x' y', ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      Reduction f S S' {x'} [.inl G, B] [] by
    obtain ⟨S', x', y', hxy', hred⟩ := key
    rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨S', hred.step_of_shared hS h.unpaired_x h.unpaired_y h.ne hx2 hy2 hcy⟩
    · exact ⟨S', hred.step_of_shared hS h.unpaired_y h.unpaired_x h.ne.symm hy2 hx2 hcx⟩
  rcases B with Bg | e
  · exact hS.exists_reduction_sharedGate h hcx hcy fun he => hBG (by rw [he])
  · obtain ⟨S', hred⟩ := hS.exists_reduction_sharedEqn hN h hcx hcy
    exact ⟨S', x, y, Or.inl ⟨rfl, rfl⟩, hred⟩

/-! ### Case 8: fixing an input -/

/-- The bottleneck configuration of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]:
`deg x = 2` and the minimal AND `G` has a unique child `D`, which reads an unpaired isolated
parameter `z`. -/
def Bottleneck (S : State n) (G x : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ D z, (∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D) ∧ D ∈ S.gates ∧
    z ∈ S.unpaired ∧ S.deg z = 1 ∧ (S.gate D).Reads z

/-- The unpaired isolated parameters whose only child is a child of the gate `G`: they may gain
weight when `G` becomes constant. -/
def IsolatedBelow (S : State n) (G u : ℕ) : Prop :=
  u ∈ S.unpaired ∧ S.deg u = 1 ∧ ∃ N ∈ S.children G, N ∈ S.children u

instance (S : State n) (G : ℕ) : DecidablePred (S.IsolatedBelow G) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- At most `deg G` unpaired isolated parameters have their child among the children of the gate
`G`: a child of `G` has at most one parent other than `G`. -/
theorem Valid.card_isolated_le {S : State n} (hS : S.Valid f) {G : ℕ} (hG : G ∈ S.gates)
    (s : Finset ℕ) (hs : s ⊆ S.params) : (s.filter (S.IsolatedBelow G)).card ≤ S.deg G := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun u => if hu : ∃ N ∈ S.children G, N ∈ S.children u then hu.choose else .inl G)
    (fun u hu => ?_) (fun u hu u' hu' heq => ?_)
  · obtain ⟨-, -, -, hex⟩ := Finset.mem_filter.1 hu
    simp only [dite_eq_left hex]
    exact hex.choose_spec.1
  · obtain ⟨hus, -, -, hex⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
    obtain ⟨hus', -, -, hex'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu')
    simp only [dite_eq_left hex, dite_eq_left hex'] at heq
    have h₁ := hex.choose_spec
    have h₂ := hex'.choose_spec
    rw [heq] at h₁
    generalize hex'.choose = N at h₁ h₂
    have hG' : ∀ {w}, w ∈ S.params → w ≠ G := fun hw he =>
      hS.wf.notMem_gates_of_mem_params hw (he ▸ hG)
    rcases N with K | e
    · obtain ⟨-, hKG⟩ := (SemiCircuit.inl_mem_children _).1 h₁.1
      obtain ⟨-, hKu⟩ := (SemiCircuit.inl_mem_children _).1 h₁.2
      obtain ⟨-, hKu'⟩ := (SemiCircuit.inl_mem_children _).1 h₂.2
      rcases Gate.eq_or_eq_of_reads (hG' (hs hus)).symm hKG hKu hKu' with h' | h'
      · exact absurd h' (hG' (hs hus'))
      · exact h'.symm
    · obtain ⟨he, hGe⟩ := (SemiCircuit.inr_mem_children _).1 h₁.1
      exact absurd hGe (hS.wf.notMem_terms_of_mem_gates hG he)

/-- The constraints deleted by fixing the input `x` of the minimal AND `G`, besides `G` itself:
the other children of `x` and the children of `G`. -/
def fixInputDeleted (S : State n) (G x : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (S.children x).erase (.inl G) ∪ S.children G

/-- Fixing the input `x` of the minimal AND so that `G` becomes constant, and deleting `G`, the
other children of `x` and the children of `G`, is a reduction deleting `deg x + deg G`
constraints. -/
private theorem Valid.exists_reduction_fixInput {S : State n} (hS : S.Valid f) {G x y : ℕ}
    (h : S.MinimalAnd G x y) : ∃ S', Reduction f S S' {x}
      (.inl G :: (S.fixInputDeleted G x).toList) (S.fixInputDeleted G x).toList := by
  have hxG := h.ne_gate hS h.mem_params_x
  obtain ⟨b, c, hc⟩ := Gate.exists_const_of_not_isAffineOp h.and_op (a := y) (w := x) h.args.symm
  have h₁ := hS.reduction_fixConst h.mem_params_x b
  have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := c) h.mem fun val _ => by
    rw [fixConst_gate, Gate.eval_subst_const]; exact hc _ (Function.update_self _ _ _)
  obtain ⟨S', h₃⟩ := h₂.valid.exists_reduction_deleteAll (S.fixInputDeleted G x).toList
      (Finset.nodup_toList _) fun N hNL => by
    rw [Finset.mem_toList, fixInputDeleted, Finset.mem_union] at hNL
    rcases hNL with hNx | hNG
    · exact h₂.deletable N (by simpa using Finset.ne_of_mem_erase hNx)
        (deletable_fixConst_child hS _ b (Finset.mem_of_mem_erase hNx))
    · obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
      exact deletable_deleteGate_child c hK (fun he => hS.not_reads_self h.mem (he ▸ hKG))
        (by rw [fixConst_gate, Gate.reads_subst_of_ne hxG.symm (by simp [Lit.const])]; exact hKG)
  exact ⟨S', (h₁.trans_delete h₂).trans_delete h₃⟩

private theorem MinimalAnd.length_fixInput {S : State n} (hS : S.Valid f) {G x y : ℕ}
    (h : S.MinimalAnd G x y) :
    (Sum.inl G :: (S.fixInputDeleted G x).toList).length = S.deg x + S.deg G := by
  have hdisj : Disjoint ((S.children x).erase (.inl G)) (S.children G) := by
    rw [Finset.disjoint_left]
    intro N hNx hNG
    obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
    exact (h.children K hK hKG).1
      ((SemiCircuit.inl_mem_children _).1 (Finset.mem_of_mem_erase hNx)).2
  have hdx : S.deg x = (S.children x).card := rfl
  have hdG : S.deg G = (S.children G).card := rfl
  unfold fixInputDeleted
  rw [List.length_cons, Finset.length_toList, Finset.card_union_of_disjoint hdisj,
    Finset.card_erase_of_mem h.mem_children_x]
  have := Finset.card_pos.2 ⟨_, h.mem_children_x⟩
  omega

/-- The weights after fixing an input of the minimal AND: outside Case 7, only an unpaired
isolated parameter below `G` gains weight, at most one, and `y` loses one when `deg x = 2`. -/
theorem Reduction.wt_add_le_fixInput {S S' : State n} (hS : S.Valid f) (hN : S.Normal)
    {G x y : ℕ} (h : S.MinimalAnd G x y) (h7 : ¬ S.SharedSecondChild G x y)
    (hred : Reduction f S S' {x} (.inl G :: (S.fixInputDeleted G x).toList)
      (S.fixInputDeleted G x).toList) {u : ℕ} (hux : u ≠ x) :
    S'.wt u + (if u = y ∧ S.deg x = 2 then 1 else 0) ≤
      S.wt u + (if S.IsolatedBelow G u then 1 else 0) := by
  by_cases huy : u = y ∧ S.deg x = 2
  · -- `y` keeps only its second child
    obtain ⟨rfl, hx2⟩ := huy
    have hy2 : S.deg u = 2 := le_antisymm (hx2 ▸ h.deg_le) h.deg_y
    rw [ite_eq_left ⟨rfl, hx2⟩, ite_eq_right fun hg => by
      have := hg.2.1; omega]
    have hT : ∀ N ∈ (S.fixInputDeleted G x).toList, N ∉ S.children u := by
      intro N hNL hNy
      rw [Finset.mem_toList, fixInputDeleted, Finset.mem_union] at hNL
      rcases hNL with hNx | hNG
      · exact h7 ⟨hx2, N, Finset.ne_of_mem_erase hNx, Finset.mem_of_mem_erase hNx, hNy⟩
      · obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
        exact (h.children K hK hKG).2 ((SemiCircuit.inl_mem_children _).1 hNy).2
    have hcard : (S.children u \ (Sum.inl G :: (S.fixInputDeleted G x).toList).toFinset).card
        ≤ 1 := by
      have hsub : S.children u \ (Sum.inl G :: (S.fixInputDeleted G x).toList).toFinset ⊆
          (S.children u).erase (.inl G) := fun N hN' =>
        Finset.mem_erase.2 ⟨fun he => (Finset.mem_sdiff.1 hN').2 (by simp [he]),
          (Finset.mem_sdiff.1 hN').1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem h.mem_children_y] at this
      change _ ≤ S.deg u - 1 at this
      omega
    have hwt := (hred.wt_le_weight (fun N hN' => hT N (by simpa using hN'))).trans
      (weight_mono hcard)
    rw [weight_one] at hwt
    rw [wt_of_mem h.unpaired_y, weight_of_two_le hy2.ge]
    omega
  · rw [ite_eq_right huy]
    by_cases hg : S.IsolatedBelow G u
    · -- an isolated parameter below `G` gains at most one
      rw [ite_eq_left hg, wt_of_mem hg.1, hg.2.1, weight_one]
      have := S'.wt_le_seven u
      omega
    · rw [ite_eq_right hg]
      by_cases hu' : u ∈ S.unpaired
      · refine Nat.add_le_add_right (hred.wt_le_wt hu' fun N hNL hNu => ?_) 0
        rw [Finset.mem_toList, fixInputDeleted, Finset.mem_union] at hNL
        rcases hNL with hNx | hNG
        · exact hN.exclusive.two_le_deg hu' hNu h.mem_params_x (Ne.symm hux)
            (Finset.mem_of_mem_erase hNx)
        · have h1 : 1 ≤ S.deg u := Finset.card_pos.2 ⟨N, hNu⟩
          by_contra hlt
          exact hg ⟨hu', by omega, N, hNG, hNu⟩
      · rw [hred.wt_eq_zero hS hu' fun w hw hwu => by
          rw [Finset.mem_singleton] at hw; subst hw
          exact (mem_unpaired.1 h.unpaired_x).2 hwu.paired]
        omega

/-- Outside the bottleneck configuration, when `deg x = 2` and `G` has one child, no unpaired
isolated parameter lies below `G`. -/
private theorem MinimalAnd.not_isolatedBelow {S : State n} (hS : S.Valid f) {G x y : ℕ}
    (h : S.MinimalAnd G x y) (hbot : ¬ S.Bottleneck G x) (hx2 : S.deg x = 2)
    (hG1 : S.deg G = 1) {u : ℕ} : ¬ S.IsolatedBelow G u := fun ⟨hu1, hu2, N, hNG, hNu⟩ => by
  refine hbot ⟨hx2, ?_⟩
  obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
  have hcG : S.children G = {.inl K} := children_eq_singleton hG1 hNG
  refine ⟨K, u, fun K' hK' => ⟨fun hr => ?_, fun he => he ▸ hKG⟩, hK, hu1, hu2,
    ((SemiCircuit.inl_mem_children _).1 hNu).2⟩
  have : Sum.inl K' ∈ S.children G := (SemiCircuit.inl_mem_children _).2 ⟨hK', hr⟩
  rw [hcG, Finset.mem_singleton] at this
  exact Sum.inl.inj this

/-- **Case 8** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: outside Case 7 and
the bottleneck configuration, fix the input `x` of the minimal AND `G` so that `G` becomes
constant and delete all children of `x` and of `G`. Only the `k₁ ≤ k = deg G` unpaired isolated
parameters below `G` may gain weight, and `y` drops to weight six when `deg x = 2`:
`Δa = -1`, `ΔW ≤ -7 - 2 (deg x + k) + k₁ - [deg x = 2] ≤ -14`. -/
theorem Valid.step_fixInput {S : State n} (hS : S.Valid f) (hN : S.Normal) {G x y : ℕ}
    (h : S.MinimalAnd G x y) (h7 : ¬ S.SharedSecondChild G x y) (hbot : ¬ S.Bottleneck G x) :
    ∃ S', Step f S S' := by
  have hxu : ¬ S.Paired x := (mem_unpaired.1 h.unpaired_x).2
  have hx2 : 2 ≤ S.deg x := h.deg_y.trans h.deg_le
  obtain ⟨S', hred⟩ := hS.exists_reduction_fixInput h
  refine ⟨S', hred.step hS (by simp) (by simp) ?_⟩
  have hW := hred.W_le (fun u => if u = y ∧ S.deg x = 2 then 1 else 0)
    (fun u => if S.IsolatedBelow G u then 1 else 0) fun u hu =>
      hred.wt_add_le_fixInput hS hN h h7 (by simpa using (Finset.mem_sdiff.1 hu).2)
  have hgain := hS.card_isolated_le h.mem (S.params \ {x}) Finset.sdiff_subset
  rw [Finset.card_filter] at hgain
  have hk : 1 ≤ S.deg G := by
    obtain ⟨K, hK, hKG⟩ := h.has_child
    exact Finset.card_pos.2 ⟨_, (SemiCircuit.inl_mem_children _).2 ⟨hK, hKG⟩⟩
  have hym : y ∈ S.params \ {x} := Finset.mem_sdiff.2 ⟨h.mem_params_y, by simpa using h.ne.symm⟩
  have hloss : ∑ u ∈ S.params \ {x}, (if u = y ∧ S.deg x = 2 then 1 else 0) =
      if S.deg x = 2 then 1 else 0 := by
    by_cases hx2' : S.deg x = 2
    · simp only [hx2', and_true, ite_true]
      exact Finset.sum_ite_eq_of_mem' _ _ _ hym
    · simp [hx2']
  rw [hloss, Finset.sum_singleton, wt_of_mem h.unpaired_x, weight_of_two_le hx2,
    hS.card_pairsMeeting_singleton, ite_eq_right hxu, h.length_fixInput hS] at hW
  rw [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_right hxu]
  by_cases hx2' : S.deg x = 2
  · rw [ite_eq_left hx2'] at hW
    rcases Nat.lt_or_ge 1 (S.deg G) with hG2 | hG1
    · omega
    · rw [Finset.sum_eq_zero fun u _ => ite_eq_right
        (h.not_isolatedBelow hS hbot hx2' (by omega))] at hW
      omega
  · rw [ite_eq_right hx2'] at hW
    omega

/-! ### Cases 9 and 10: the bottleneck -/

/-- The weights after the quadratic reparameterisation: `x` and `y` become paired, `z` is
replaced by `D`, which gains at most seven, and no other weight grows. -/
private theorem QuadOK.wt_add_le {S : State n} (hS : S.Valid f) {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) (hx : 2 ≤ S.deg x) (hy : 2 ≤ S.deg y) :
    ∀ u ∈ insert D S.params, (S.quad x y z G D α β γ c).wt u + ((if u = x then 7 else 0) +
      (if u = y then 7 else 0) + (if u = z then 6 else 0)) ≤ S.wt u + (if u = D then 7 else 0) := by
  have hDp := hS.wf.notMem_params_of_mem_gates h.mem_D
  have hDz : D ≠ z := fun he => hDp (he ▸ h.mem_z)
  have hDx : D ≠ x := fun he => hDp (he ▸ h.mem_x)
  have hDy : D ≠ y := fun he => hDp (he ▸ h.mem_y)
  have hpaired : ∀ {u}, u = x ∨ u = y → (S.quad x y z G D α β γ c).Paired u := fun hu =>
    ⟨(x, y), Finset.mem_insert_self _ _, hu.imp Eq.symm Eq.symm⟩
  intro u _
  by_cases hux : u = x
  · subst hux
    rw [wt_of_paired (hpaired (Or.inl rfl)), wt_of_mem (mem_unpaired.2 ⟨h.mem_x, h.unpaired_x⟩),
      weight_of_two_le hx]
    simp [h.x_ne_y, h.x_ne_z, hDx.symm]
  by_cases huy : u = y
  · subst huy
    rw [wt_of_paired (hpaired (Or.inr rfl)), wt_of_mem (mem_unpaired.2 ⟨h.mem_y, h.unpaired_y⟩),
      weight_of_two_le hy]
    simp [h.x_ne_y.symm, h.y_ne_z, hDy.symm]
  by_cases huz : u = z
  · rw [huz] at hux huy ⊢
    have hdz : S.deg z = 1 := by rw [SemiCircuit.deg, h.children_z, Finset.card_singleton]
    rw [wt_of_notMem_params (show z ∉ (S.quad x y z G D α β γ c).params by
      simp [quad_params, hDz.symm]), wt_of_mem (mem_unpaired.2 ⟨h.mem_z, h.unpaired_z⟩), hdz,
      weight_one]
    simp [hux, huy, hDz.symm]
  rw [ite_eq_right hux, ite_eq_right huy, ite_eq_right huz]
  by_cases huD : u = D
  · rw [huD, wt_of_notMem_params hDp, ite_eq_left rfl]
    have := (S.quad x y z G D α β γ c).wt_le_seven D
    omega
  · rw [ite_eq_right huD]
    by_cases hu' : u ∈ (S.quad x y z G D α β γ c).unpaired
    · obtain ⟨hup, hun⟩ := mem_unpaired.1 hu'
      have hup' : u ∈ S.params := by
        simp only [quad_params, Finset.mem_insert, Finset.mem_erase] at hup
        exact (hup.resolve_left huD).2
      have hus : u ∈ S.unpaired := mem_unpaired.2 ⟨hup', fun ⟨pr, hpr, hu⟩ =>
        hun ⟨pr, Finset.mem_insert_of_mem hpr, hu⟩⟩
      rw [wt_of_mem hu', wt_of_mem hus]
      exact Nat.add_le_add_right (weight_mono (Finset.card_le_card
        ((quad_children_subset S x y z G D α β γ c u).trans
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))))) _
    · rw [wt_of_notMem hu']
      omega

/-- The quadratic reparameterisation of the bottleneck configuration, when `x` and `y` have
degree at least two, is a step of gate elimination: `Δa = -1`, `ΔW ≤ -14`. -/
private theorem Valid.step_quad {S : State n} (hS : S.Valid f) {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) (hx : 2 ≤ S.deg x) (hy : 2 ≤ S.deg y) :
    Step f S (S.quad x y z G D α β γ c) := by
  set S' := S.quad x y z G D α β γ c
  have hDp := hS.wf.notMem_params_of_mem_gates h.mem_D
  have hm : S'.m = S.m := by
    change (insert D (S.params.erase z)).card = S.params.card
    rw [Finset.card_insert_of_notMem fun h' => hDp (Finset.mem_of_mem_erase h'),
      Finset.card_erase_add_one h.mem_z]
  have hq : S'.q = S.q + 1 := by
    change (insert (x, y) S.pairs).card = S.pairs.card + 1
    exact Finset.card_insert_of_notMem fun h' => h.unpaired_x ⟨_, h', Or.inl rfl⟩
  have hs : S'.s + 2 = S.s := quad_size h
  have hqm := (hS.quad h).q_le_m
  have hW := W_add_le (S := S) (S' := S') (N := insert D S.params) (Finset.subset_insert _ _)
    (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) _ _ (h.wt_add_le hS hx hy)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_of_mem h.mem_x),
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_of_mem h.mem_y),
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_of_mem h.mem_z),
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_self _ _)] at hW
  exact ⟨hS.quad h, by omega, by simp only [State.a]; omega, by simp only [State.a]; omega,
    by simp only [State.a]; omega⟩

/-- In the bottleneck configuration, `G` has the unique child `D` and `z` the unique child `D`. -/
private theorem MinimalAnd.children_of_bottleneck {S : State n} (hS : S.Valid f) {G x y D z : ℕ}
    (h : S.MinimalAnd G x y) (hDiff : ∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D)
    (hD : D ∈ S.gates) (hz1 : S.deg z = 1) (hDz : (S.gate D).Reads z) :
    S.children G = {.inl D} ∧ S.children z = {.inl D} := by
  refine ⟨?_, children_eq_singleton hz1 ((SemiCircuit.inl_mem_children _).2 ⟨hD, hDz⟩)⟩
  ext N
  constructor
  · intro hNG
    obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
    rw [(hDiff K hK).1 hKG]
    exact Finset.mem_singleton_self _
  · intro hNm
    rw [Finset.mem_singleton] at hNm
    subst hNm
    exact (SemiCircuit.inl_mem_children _).2 ⟨hD, (hDiff D hD).2 rfl⟩

/-- In the bottleneck configuration with `D` AND-type, fixing `x` and `y` so that `G` takes the
value making `D` constant deletes `G`, `D` and the second children `Bx`, `By` of `x` and `y`. -/
private theorem Valid.exists_reduction_bottleneck_and {S : State n} (hS : S.Valid f) {G x y D : ℕ}
    (h : S.MinimalAnd G x y) (hD : D ∈ S.gates) (hDG' : D ≠ G)
    {δ c : Bool} (hc : ∀ val : ℕ → Bool, val G = δ → (S.gate D).eval val = c)
    {x₀ y₀ : Bool} (hδ : (S.gate G).eval (Function.update (Function.update (fun _ => false) y y₀)
      x x₀) = δ) {Bx By : ℕ ⊕ ℕ} (hBx : Bx ∈ S.children x) (hBy : By ∈ S.children y)
    (hBxG : Bx ≠ .inl G) (hByG : By ≠ .inl G) (hBxy : Bx ≠ By) (hBxD : Bx ≠ .inl D)
    (hByD : By ≠ .inl D) : ∃ S', Reduction f S S' {x, y} [.inl G, .inl D, Bx, By] [Bx, By] := by
  have hxG := h.ne_gate hS h.mem_params_x
  have hyG := h.ne_gate hS h.mem_params_y
  obtain ⟨φ, -, hGφ⟩ := h.exists_op
  rw [hGφ, Function.update_self, Function.update_of_ne h.ne.symm, Function.update_self] at hδ
  have h₁ := hS.reduction_fixConst h.mem_params_x x₀
  have h₂ := h₁.valid.reduction_fixConst (Finset.mem_erase.2 ⟨h.ne.symm, h.mem_params_y⟩) y₀
  have h₃ := h₂.valid.reduction_deleteConst (J := G) (c := δ) h.mem fun val _ => by
    rw [fixConst_gate, Gate.eval_subst_const, fixConst_gate, Gate.eval_subst_const, hGφ,
      Function.update_self, Function.update_of_ne h.ne.symm, Function.update_self]
    exact hδ
  have h₄ := h₃.valid.reduction_deleteConst (J := D) (c := c)
    (Finset.mem_erase.2 ⟨hDG', hD⟩) fun val _ => by
      rw [deleteGate_gate, Gate.eval_subst_const, fixConst_gate, Gate.eval_subst_const,
        fixConst_gate, Gate.eval_subst_const]
      exact hc _ (by rw [Function.update_of_ne hxG.symm, Function.update_of_ne hyG.symm,
        Function.update_self])
  obtain ⟨S', h₅⟩ := h₄.valid.exists_reduction_deleteAll [Bx, By] (by simp [hBxy]) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro N (rfl | rfl)
    · exact h₄.deletable _ (by simpa using hBxD) (h₃.deletable _ (by simpa using hBxG)
        (h₂.deletable _ (by simp) (deletable_fixConst_child hS _ x₀ hBx)))
    · exact h₄.deletable _ (by simpa using hByD) (h₃.deletable _ (by simpa using hByG)
        (deletable_fixConst_child h₁.valid _ y₀
          (by rw [fixConst_children _ _ h.ne.symm]; exact hBy))))
  have hred := (((h₁.trans h₂).trans_delete h₃).trans_delete h₄).trans_delete h₅
  rw [← Finset.insert_eq] at hred
  exact ⟨S', hred⟩

/-- **Case 9** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: in the bottleneck
configuration with `D` AND-type, fix `x` and `y` so that `D` becomes constant and delete `G`, `D`
and the second children of `x` and `y`; `z` becomes unused: `Δa = -2`, `ΔW ≤ -28`. -/
theorem Valid.step_of_bottleneck_and {S : State n} (hS : S.Valid f) (hN : S.Normal)
    {G x y D z : ℕ} (h : S.MinimalAnd G x y) (h7 : ¬ S.SharedSecondChild G x y)
    (hx2 : S.deg x = 2) (hDiff : ∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D) (hD : D ∈ S.gates)
    (hz : z ∈ S.unpaired) (hz1 : S.deg z = 1) (hDz : (S.gate D).Reads z)
    (hDand : ¬ IsAffineOp (S.gate D).op) : ∃ S', Step f S S' := by
  have hy2 : S.deg y = 2 := le_antisymm (hx2 ▸ h.deg_le) h.deg_y
  have hDG : (S.gate D).Reads G := (hDiff D hD).2 rfl
  obtain ⟨-, hcz⟩ := h.children_of_bottleneck hS hDiff hD hz1 hDz
  have hzp := (mem_unpaired.1 hz).1
  have hDx : ¬ (S.gate D).Reads x := (h.children D hD hDG).1
  have hDy : ¬ (S.gate D).Reads y := (h.children D hD hDG).2
  obtain ⟨δ, c, hc⟩ := Gate.exists_const_of_not_isAffineOp hDand
    (Gate.args_of_reads (h.ne_gate hS hzp) hDz hDG)
  obtain ⟨φ, hφ, hGφ⟩ := h.exists_op
  obtain ⟨x₀, y₀, hδ⟩ := exists_eq_of_not_isAffineOp' hφ δ
  obtain ⟨Bx, hBx, hBxG⟩ := Finset.exists_mem_ne (show 1 < (S.children x).card by
    change 1 < S.deg x; omega) (.inl G)
  obtain ⟨By, hBy, hByG⟩ := Finset.exists_mem_ne (show 1 < (S.children y).card by
    change 1 < S.deg y; omega) (.inl G)
  have hBxD : Bx ≠ .inl D := fun he => hDx ((SemiCircuit.inl_mem_children _).1 (he ▸ hBx)).2
  have hByD : By ≠ .inl D := fun he => hDy ((SemiCircuit.inl_mem_children _).1 (he ▸ hBy)).2
  obtain ⟨S', hred⟩ := hS.exists_reduction_bottleneck_and h hD
    (fun he => hS.not_reads_self h.mem (he ▸ hDG)) hc (x₀ := x₀) (y₀ := y₀)
    (by rw [hGφ, Function.update_self, Function.update_of_ne h.ne.symm, Function.update_self]
        exact hδ) hBx hBy hBxG hByG (fun he => h7 ⟨hx2, Bx, hBxG, hBx, he ▸ hBy⟩) hBxD hByD
  refine ⟨S', hred.step hS Finset.card_le_two (by simp) ?_⟩
  have hW := hred.W_le (fun u => if u = z then 6 else 0) (fun _ => 0) fun u hu => by
    obtain ⟨-, huF⟩ := Finset.mem_sdiff.1 hu
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huF
    by_cases huz : u = z
    · subst huz
      rw [hred.wt_eq_zero_of_subset (by simp [hcz]) (by simp [hcz, hBxD, hByD]), wt_of_mem hz,
        hz1, weight_one, ite_eq_left rfl]
    · rw [ite_eq_right huz]
      refine Nat.add_le_add_right (hred.wt_le_of_exclusive hS hN.exclusive
        (fun w hw hwu => ?_) fun N hNL _ => ?_) 0
      · rcases Finset.mem_insert.1 hw with rfl | hw
        · exact (mem_unpaired.1 h.unpaired_x).2 hwu.paired
        · rw [Finset.mem_singleton] at hw
          subst hw
          exact (mem_unpaired.1 h.unpaired_y).2 hwu.paired
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hNL
        rcases hNL with rfl | rfl
        · exact ⟨x, h.mem_params_x, Ne.symm huF.1, hBx⟩
        · exact ⟨y, h.mem_params_y, Ne.symm huF.2, hBy⟩
  have hk : (S.pairsMeeting {x, y}).card = 0 := by
    rw [hS.card_pairsMeeting_insert (by simpa using h.ne)
      (by simpa using fun hxy => (mem_unpaired.1 h.unpaired_x).2 hxy.paired),
      hS.card_pairsMeeting_singleton, ite_eq_right (mem_unpaired.1 h.unpaired_y).2,
      ite_eq_right (mem_unpaired.1 h.unpaired_x).2]
  have hzm : z ∈ S.params \ {x, y} := Finset.mem_sdiff.2 ⟨hzp, by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun he => hDx (he ▸ hDz), fun he => hDy (he ▸ hDz)⟩⟩
  rw [Finset.sum_ite_eq_of_mem' _ _ _ hzm, Finset.sum_pair h.ne, wt_of_mem h.unpaired_x,
    wt_of_mem h.unpaired_y, hx2, hy2, weight_of_two_le le_rfl, hk] at hW
  simp only [Finset.sum_const_zero, List.length_cons, List.length_nil] at hW
  rw [Finset.card_pair h.ne, hk]
  omega

/-- **Case 10** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: in the bottleneck
configuration with `D` affine, `D` is XOR-type since no deletion applies, and the quadratic
reparameterisation deletes `G` and `D`: `Δa = -1`, `ΔW ≤ -14`. -/
theorem Valid.step_of_bottleneck_xor {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G x y D z : ℕ}
    (h : S.MinimalAnd G x y) (hDiff : ∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D)
    (hD : D ∈ S.gates) (hz : z ∈ S.unpaired) (hz1 : S.deg z = 1) (hDz : (S.gate D).Reads z)
    (hDaff : IsAffineOp (S.gate D).op) : ∃ S', Step f S S' := by
  have hDG : (S.gate D).Reads G := (hDiff D hD).2 rfl
  obtain ⟨hcG, hcz⟩ := h.children_of_bottleneck hS hDiff hD hz1 hDz
  have hzp := (mem_unpaired.1 hz).1
  have hDargs := Gate.args_of_reads (h.ne_gate hS hzp) hDz hDG
  obtain ⟨c, hDc⟩ := exists_xor_form hDaff
    (fun hun => hN.no_deletion (deletionAvailable_of_unary hD hun))
    (by
      by_contra hconst
      push Not at hconst
      exact hN.no_deletion (deletionAvailable_of_const_op hD hconst))
  obtain ⟨φ, hφ, hGφ⟩ := h.exists_op
  obtain ⟨α, β, γ, hform⟩ := exists_and_form hφ
  refine ⟨_, hS.step_quad (x := x) (y := y) (z := z) (G := G) (D := D) (α := α) (β := β)
    (γ := γ) (c := c)
    { mem_x := h.mem_params_x
      mem_y := h.mem_params_y
      mem_z := hzp
      unpaired_x := (mem_unpaired.1 h.unpaired_x).2
      unpaired_y := (mem_unpaired.1 h.unpaired_y).2
      unpaired_z := (mem_unpaired.1 hz).2
      x_ne_y := h.ne
      x_ne_z := fun he => (h.children D hD hDG).1 (he ▸ hDz)
      y_ne_z := fun he => (h.children D hD hDG).2 (he ▸ hDz)
      mem_G := h.mem
      mem_D := hD
      G_ne_D := fun he => hS.not_reads_self h.mem (he ▸ hDG)
      eval_G := fun val => by
        rw [hGφ, hform]
        cases val x <;> cases val y <;> cases α <;> cases β <;> cases γ <;> rfl
      eval_D := fun val => by
        rcases hDargs with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
        · rw [Gate.eval_of_args hl hr, hDc]
          cases val G <;> cases val z <;> cases c <;> rfl
      children_G := hcG
      children_z := hcz
      out_G := h.not_out
      out_z := hS.not_out_reads_param hf ha hzp }
    (h.deg_y.trans h.deg_le) h.deg_y⟩

/-- **Cases 9 and 10** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026], the
bottleneck configuration: the unique child `D` of the minimal AND `G` reads an unpaired isolated
parameter `z`; its elimination is a step. -/
private theorem Valid.step_of_bottleneck {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G x y : ℕ}
    (h : S.MinimalAnd G x y) (h7 : ¬ S.SharedSecondChild G x y) (hbot : S.Bottleneck G x) :
    ∃ S', Step f S S' := by
  obtain ⟨hx2, D, z, hDiff, hD, hz, hz1, hDz⟩ := hbot
  by_cases hDand : IsAffineOp (S.gate D).op
  · exact hS.step_of_bottleneck_xor hf ha hN h hDiff hD hz hz1 hDz hDand
  · exact hS.step_of_bottleneck_and hN h h7 hx2 hDiff hD hz hz1 hDz hDand

/-- **Section 4.3** of [Mishra and Santhanam][MishraSanthanam2026]: in a normal state with
`d < a`, eliminating the minimal AND is a step of gate elimination. -/
theorem Valid.step_of_minimalAnd {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G x y : ℕ}
    (h : S.MinimalAnd G x y) : ∃ S', Step f S S' := by
  by_cases h7 : S.SharedSecondChild G x y
  · exact hS.step_of_sharedSecondChild hN h h7
  by_cases hbot : S.Bottleneck G x
  · exact hS.step_of_bottleneck hf ha hN h h7 hbot
  · exact hS.step_fixInput hN h h7 hbot

end State

end Cslib.Circuits.Boolean.AffineDisperser
