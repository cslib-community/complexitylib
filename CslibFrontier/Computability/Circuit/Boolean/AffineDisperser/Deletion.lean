/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Reduction
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Reparameterisation

/-!
# Deletions in gate elimination

Case 1 of the preliminary reductions of [Mishra and Santhanam, Section 4.1][MishraSanthanam2026]
(`State.DeletionAvailable`): one of the deletions (D1)–(D4) applies, lowering `s`, keeping `a`
and not increasing `W` (`State.Valid.step_of_deletion`).

* (D1) a gate computing, on the solutions of the affine system, a constant or a literal of one of
  its inputs is deleted, and (D2) so is a gate other than the output with no children; both are
  `State.Reduction`s through `State.reduction_deleteGate`.
* (D3) an equation with at most two terms is deleted (`State.Valid.exists_reduction_delete`).
* (D4) an unpaired parameter whose only child is an equation is exchanged with an auxiliary
  variable of that equation, which is then dropped (`State.Valid.unit_delete`). This changes the
  parameters, so it is not a `State.Reduction`; its accounting is done directly.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.DeletionAvailable`: the configuration of Case 1.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.unit_delete`: the deletion (D4).
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.step_of_deletion`: a deletion is a step of
  gate elimination.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-- The configuration of Case 1: one of the deletions (D1)–(D4) applies. An equation has at most
two terms (D3); a gate computes, on the solutions of the affine system, a constant or a literal of
one of its inputs (D1); a gate other than the output has no children (D2); or an unpaired
parameter has an equation as its only child (D4). -/
def DeletionAvailable (S : State n) : Prop :=
  (∃ e ∈ S.eqns, (S.eqn e).terms.card ≤ 2) ∨
  (∃ J ∈ S.gates, ∃ ℓ : Lit, (∀ t, ℓ.Reads t → (S.gate J).Reads t) ∧
    ∀ val, S.EqnsHold val → (S.gate J).eval val = ℓ.eval val) ∨
  (∃ J ∈ S.gates, (∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J) ∨
  (∃ x ∈ S.unpaired, ∃ e, S.children x = {.inr e})

/-- In a valid state with `d < a`, the output is not a literal of a parameter, by
Lemma 2.3. -/
theorem Valid.not_out_reads_param {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) :
    ¬ S.out.Reads x :=
  not_out_reads_param_of fun h =>
    Valid.out_not_affine hS hf ha S.out.neg (Finset.singleton_subset_iff.2 hx) fun val hcons =>
      h val hcons trivial

/-- (D4): an unpaired parameter `x` whose only child is the equation `e` is exchanged with an
auxiliary variable depending on it and then deleted with `e`; this keeps `a` and lowers `W`. -/
theorem Valid.unit_delete {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) {x e : ℕ} (hx : x ∈ S.unpaired) (hc : S.children x = {.inr e}) :
    ∃ S' : State n, S'.Valid f ∧ S'.m = S.m ∧ S'.s + 1 = S.s ∧ S'.a = S.a ∧ S'.q = S.q ∧
      S'.W + 1 ≤ S.W := by
  obtain ⟨hxp, hxu⟩ := mem_unpaired.1 hx
  have hex : Sum.inr e ∈ S.children x := by rw [hc]; exact Finset.mem_singleton_self _
  obtain ⟨he, hxe⟩ := (SemiCircuit.inr_mem_children _).1 hex
  obtain ⟨Q, hQ, c, T, hT, hxT⟩ := SemiCircuit.exists_affineIn_of_mem_terms hS.wf hxp he hxe
  have hsw : S.SwapOK x Q c T := ⟨hxp, hxu, hQ, hT, hxT⟩
  have hS₁ := Valid.swap hS hsw
  have hQp : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp hQ
  have hQx : Q ≠ x := fun he' => hQp (he' ▸ hxp)
  have hdrop : (S.swap x Q c T).DropEqnOK e x := by
    refine ⟨he, Finset.mem_insert_self _ _, hxe, fun e' he' hee hxe' => ?_, fun K hK hr => ?_,
      Valid.not_out_reads_param hS hf ha hxp⟩
    · have : Sum.inr e' ∈ S.children x := (SemiCircuit.inr_mem_children _).2 ⟨he', hxe'⟩
      rw [hc, Finset.mem_singleton] at this
      exact hee (Sum.inr.inj this)
    · have : Sum.inl K ∈ S.children x := (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
      rw [hc] at this
      simp at this
  have hS' := hS₁.dropEqn hdrop
  set S' := (S.swap x Q c T).dropEqn e x
  have hparams : S'.params = insert Q (S.params.erase x) := rfl
  have hpairs : S'.pairs = S.pairs := rfl
  have hsize : S'.size + 1 = S.size := dropEqn_size hdrop
  have hm : S'.m = S.m := by grind [m]
  have hq : S'.q = S.q := by simp [q, hpairs]
  have ha' : S'.a = S.a := by simp only [a, hm, hq]
  have hchildren : ∀ z, S'.children z = (S.children z).erase (.inr e) := fun z => by
    rw [dropEqn_children, swap_children]
  -- the potential
  have hN : S.params ⊆ insert Q S.params := Finset.subset_insert _ _
  have hN' : S'.params ⊆ insert Q S.params := by
    rw [hparams]; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  have hpt : ∀ z ∈ insert Q S.params, S'.wt z + (if z = x then 6 else 0) ≤
      S.wt z + (if z = Q then 7 else 0) := by
    intro z _
    by_cases hzx : z = x
    · subst hzx
      have h1 : S'.wt z = 0 := wt_of_notMem_params (by
        rw [hparams, Finset.mem_insert, Finset.mem_erase]; tauto)
      have h2 : S.wt z = 6 := by
        rw [wt_of_mem hx, SemiCircuit.deg, hc, Finset.card_singleton, config_weight, weight_one]
      rw [h1, h2, ite_eq_left rfl, ite_eq_right hQx.symm]
    · rw [ite_eq_right hzx]
      by_cases hzQ : z = Q
      · subst hzQ
        rw [ite_eq_left rfl, wt_of_notMem_params hQp]
        have := S'.wt_le_bound z
        rw [config_weightBound] at this
        omega
      · rw [ite_eq_right hzQ]
        by_cases hu : z ∈ S'.unpaired
        · obtain ⟨hzp, hzu⟩ := mem_unpaired.1 hu
          rw [hparams, Finset.mem_insert, Finset.mem_erase] at hzp
          have hzS : z ∈ S.unpaired := mem_unpaired.2 ⟨(hzp.resolve_left hzQ).2,
            (paired_congr hpairs).not.1 hzu⟩
          rw [wt_of_mem hu, wt_of_mem hzS, add_zero]
          refine weight_mono (Finset.card_le_card ?_)
          rw [hchildren]; exact Finset.erase_subset _ _
        · rw [wt_of_notMem hu]; omega
  have hW := W_add_le hN hN' _ _ hpt
  rw [Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_of_mem hxp),
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_self _ _)] at hW
  have hs : S'.s + 1 = S.s := hsize
  rw [config_cs, config_cq] at hW
  exact ⟨S', hS', hm, hs, ha', hq, by omega⟩

/-- (D4) as a step of gate elimination. -/
private theorem Valid.step_unit {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) {x e : ℕ} (hx : x ∈ S.unpaired) (hc : S.children x = {.inr e}) :
    ∃ S', Step f S S' := by
  obtain ⟨S', hS', hm, hs, ha', -, hW⟩ := Valid.unit_delete hS hf ha hx hc
  have ha_eq : S'.a = S.a := ha'
  exact ⟨S', hS', by omega, by omega, by omega, by rw [ha_eq]; omega⟩

/-- A gate has at most two parameters as parents. -/
theorem card_filter_inl_mem_children_le (S : State n) (J : ℕ) :
    (S.params.filter fun u => Sum.inl J ∈ S.children u).card ≤ 2 :=
  (Finset.card_le_card fun _ hu => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hu).1,
    ((SemiCircuit.inl_mem_children _).1 (Finset.mem_filter.1 hu).2).2⟩).trans
    ((S.gate J).card_filter_reads_le _)

/-- **Case 1** of the preliminary reductions: a deletion lowers `s`, keeps `a` and does not
increase `W`. -/
theorem Valid.step_of_deletion {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (h : S.DeletionAvailable) :
    ∃ S', Step f S S' := by
  rcases h with ⟨e, he, hcard⟩ | ⟨J, hJ, ℓ, hreads, hval⟩ | ⟨J, hJ, hun, hout⟩ | ⟨x, hx, e, hc⟩
  · obtain ⟨S', h⟩ := hS.exists_reduction_delete (N := .inr e) ⟨he, hcard⟩
    exact ⟨S', Reduction.step_of_delete h hS ((Finset.card_le_card fun u hu =>
      ((SemiCircuit.inr_mem_children _).1 (Finset.mem_filter.1 hu).2).2).trans hcard)⟩
  · exact ⟨_, Reduction.step_of_delete (hS.reduction_deleteGate
      ⟨hJ, hreads, Or.inl fun val hcons _ => hval val hcons⟩
      fun _ _ => List.mem_singleton_self _) hS
      (S.card_filter_inl_mem_children_le J)⟩
  · exact ⟨_, Reduction.step_of_delete ((hS.reduction_deleteGate (ℓ := Lit.const false) (T := [])
      ⟨hJ, fun t ht => by simp [Lit.Reads, Lit.const] at ht, Or.inr ⟨hun, hout⟩⟩
      fun t ht => by simp [Lit.Reads, Lit.const] at ht).mono (by simp)) hS
      (S.card_filter_inl_mem_children_le J)⟩
  · exact Valid.step_unit hS hf ha hx hc

end State

end Cslib.Circuits.Boolean.AffineDisperser
