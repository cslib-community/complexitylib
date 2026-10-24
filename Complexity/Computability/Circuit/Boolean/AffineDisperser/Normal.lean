/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Deletion
public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Rewiring

/-!
# Preliminary reductions of gate elimination

The six preliminary reductions of [Mishra and Santhanam, Section 4.1][MishraSanthanam2026], each
a step of gate elimination (`State.Step`) from a state whose configuration it names. Every
reduction but the deletion (D4) of `State.Valid.unit_delete` is a `State.Reduction`, so its
accounting is that of `State.Reduction.step` or `State.Reduction.step_of_delete`.

* Case 1, `State.DeletionAvailable`: one of the deletions (D1)–(D4) applies
  (`State.Valid.step_of_deletion`, in `AffineDisperser.Deletion`).
* Case 2, `State.AndOnIsolated`: an AND-type gate reads an unpaired isolated parameter `z` and
  another parameter `w`; fixing `w` makes the gate constant and `z` unused
  (`State.Valid.step_of_andOnIsolated`).
* Case 3, `State.DegeneratePair`: a paired parameter has degree `0` or at least `2`
  (`State.Valid.step_of_degeneratePair`).
* Case 4, `State.PartnersShareChild`: two partners have a common child; restricting one to a
  literal of the other makes it constant (`State.Valid.step_of_partnersShareChild`).
* Case 5, `State.PairInSystem`: a paired parameter occurs in the affine system; fixing its partner
  leaves it to (D4) (`State.Valid.step_of_pairInSystem`).
* Case 6, `State.AndOnPair`: an AND-type gate reads a paired parameter and another parameter
  (`State.Valid.step_of_andOnPair`).

Before them, affine gates reading no gates are moved into the affine system
(`State.Valid.preparation_moveAffine`). When no affine gate can be moved and neither Case 1 nor
Case 2 applies, the state is exclusive (`State.Valid.exclusive`): no constraint has an unpaired
isolated parameter and another parameter as parents. When none of the six cases applies, the
state is *normal* (`State.Normal`, `State.Valid.step_or_normal`): it is exclusive, every parameter
of the affine system is unpaired of degree at least two, and so is every parameter read by an
AND-type gate.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.AndOnIsolated`, `State.DegeneratePair`,
  `State.PartnersShareChild`, `State.PairInSystem`, `State.AndOnPair`: the configurations of
  Cases 2 to 6.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Normal`: normal states.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.step_of_andOnIsolated`,
  `step_of_degeneratePair`, `step_of_partnersShareChild`, `step_of_pairInSystem`,
  `step_of_andOnPair`: the preliminary reductions are steps of gate elimination.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.step_or_normal`: a state where no affine
  gate can be moved has a step or is normal.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Case 2: an AND-type gate on an isolated parameter -/

/-- The configuration of Case 2: an AND-type gate reads an unpaired isolated parameter `z` and
another parameter `w`. -/
def AndOnIsolated (S : State n) : Prop :=
  ∃ G ∈ S.gates, ∃ z w, ¬ IsAffineOp (S.gate G).op ∧
    (((S.gate G).left = .node z ∧ (S.gate G).right = .node w) ∨
      ((S.gate G).left = .node w ∧ (S.gate G).right = .node z)) ∧
    z ∈ S.unpaired ∧ S.deg z = 1 ∧ w ∈ S.params ∧ z ≠ w

/-- **Case 2** of the preliminary reductions: fix `w` so that the AND-type gate becomes
constant and delete it; `z` becomes unused. If `w` is unpaired, `Δa = -1` and `ΔW ≤ -14`;
otherwise the partner of `w` becomes unpaired, `Δa = 0` and `ΔW ≤ -4`. -/
theorem Valid.step_of_andOnIsolated {S : State n} (hS : S.Valid f) (h : S.AndOnIsolated) :
    ∃ S', Step f S S' := by
  obtain ⟨G, hG, z, w, hand, hargs, hz, hz1, hw, hzw⟩ := h
  obtain ⟨hGz, hGw⟩ := Gate.reads_of_args hargs
  have hcz := children_eq_singleton hz1 ((SemiCircuit.inl_mem_children _).2 ⟨hG, hGz⟩)
  obtain ⟨b, c, hc⟩ := Gate.exists_const_of_not_isAffineOp hand hargs
  obtain ⟨S', h⟩ : ∃ S', Reduction f S S' {w} [.inl G] [] := by
    have h₁ := hS.reduction_fixConst hw b
    have h := h₁.trans (h₁.valid.reduction_deleteConst hG fun val _ => by
      rw [fixConst_gate, Gate.eval_subst_const]; exact hc _ (Function.update_self _ _ _))
    rw [Finset.union_empty] at h
    exact ⟨_, h⟩
  refine ⟨S', h.step hS (by simp) (by simp) ?_⟩
  have hW := h.W_le (fun u => if u = z then 6 else 0) (fun u => if S.IsPartner w u then 7 else 0)
    fun u hu => by
      by_cases huz : u = z
      · subst huz
        rw [h.wt_eq_zero_of_subset (by simp [hcz]) (by simp), wt_of_mem hz, hz1, weight_one,
          ite_eq_left rfl]
        omega
      · rw [ite_eq_right huz]
        by_cases hwu : S.IsPartner w u
        · rw [ite_eq_left hwu]; have := S'.wt_le_seven u; omega
        · rw [ite_eq_right hwu]
          exact Nat.add_le_add_right (h.wt_le hS (by simpa using hwu) (by simp)) 0
  have hzw' : z ∈ S.params \ {w} :=
    Finset.mem_sdiff.2 ⟨(mem_unpaired.1 hz).1, by simpa using hzw⟩
  have hgain := hS.sum_partner_le w (S.params \ {w}) 7
  have hk := hS.card_pairsMeeting_singleton w
  rw [Finset.sum_ite_eq' (S.params \ {w}) z, ite_eq_left hzw', Finset.sum_singleton] at hW
  simp only [List.length_singleton] at hW
  rw [Finset.card_singleton]
  by_cases hwp : S.Paired w
  · rw [ite_eq_left hwp] at hk
    rw [wt_of_paired hwp] at hW
    omega
  · rw [ite_eq_right hwp] at hk
    have hwu : w ∈ S.unpaired := mem_unpaired.2 ⟨hw, hwp⟩
    have := six_le_weight (show 1 ≤ S.deg w from
      Finset.card_pos.2 ⟨_, (SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩⟩)
    rw [wt_of_mem hwu, Finset.sum_eq_zero fun u _ => ite_eq_right fun h' => hwp h'.paired] at hW
    omega

/-- When Case 2 does not apply, an unpaired parameter read by an AND-type gate together with
another parameter has degree at least two. -/
private theorem two_le_deg_of_not_andOnIsolated {S : State n} (h2 : ¬ S.AndOnIsolated) {G x y : ℕ}
    (hG : G ∈ S.gates) (hand : ¬ IsAffineOp (S.gate G).op)
    (hargs : ((S.gate G).left = .node x ∧ (S.gate G).right = .node y) ∨
      ((S.gate G).left = .node y ∧ (S.gate G).right = .node x))
    (hxu : x ∈ S.unpaired) (hy : y ∈ S.params) (hxy : x ≠ y) : 2 ≤ S.deg x := by
  have h1 : 1 ≤ S.deg x := Finset.card_pos.2
    ⟨_, (SemiCircuit.inl_mem_children _).2 ⟨hG, (Gate.reads_of_args hargs).1⟩⟩
  by_contra hlt
  exact h2 ⟨G, hG, x, y, hand, hargs, hxu, by omega, hy, hxy⟩

/-! ### Moving affine gates -/

/-- An affine gate reading no gates, which is moved into the affine system before the
preliminary reductions. -/
def Movable (S : State n) (J : ℕ) : Prop :=
  J ∈ S.gates ∧ IsAffineOp (S.gate J).op ∧ ∀ i, (S.gate J).Reads i → i ∉ S.gates

/-- A name larger than every equation name. -/
def freshEqn (S : State n) : ℕ :=
  S.eqns.sup id + 1

theorem freshEqn_notMem (S : State n) : S.freshEqn ∉ S.eqns := fun h => by
  have := Finset.le_sup (f := id) h
  simp only [id, freshEqn] at this
  omega

/-- Moving a movable gate into the affine system is a preparatory operation. -/
theorem Valid.preparation_moveAffine {S : State n} (hS : S.Valid f) {J : ℕ} (hJ : S.Movable J) :
    Preparation f S (S.moveAffine J S.freshEqn) := by
  have hok : S.MoveOK J S.freshEqn := ⟨hJ.1, S.freshEqn_notMem, hJ.2.1, hJ.2.2⟩
  refine ⟨hS.moveAffine hok, rfl, moveAffine_size hok, rfl, ?_⟩
  have hpt : ∀ u ∈ S.params, (S.moveAffine J S.freshEqn).wt u + 0 ≤ S.wt u + 0 := by
    intro u hu
    by_cases hu' : u ∈ S.unpaired
    · have hu₁ : u ∈ (S.moveAffine J S.freshEqn).unpaired := by
        rwa [unpaired_congr rfl rfl]
      rw [wt_of_mem hu₁, wt_of_mem hu']
      exact Nat.add_le_add_right (weight_mono (moveAffine_deg_le hS hok hu)) _
    · rw [wt_of_notMem (by rwa [unpaired_congr rfl rfl]), wt_of_notMem hu']
  have hW := W_add_le (S := S) (S' := S.moveAffine J S.freshEqn) le_rfl le_rfl _ _ hpt
  have hs : (S.moveAffine J S.freshEqn).s = S.s := moveAffine_size hok
  have hq : (S.moveAffine J S.freshEqn).q = S.q := rfl
  simp only [Finset.sum_const_zero] at hW
  omega

/-! ### Exclusive states -/

/-- **Consequence of Cases 1 and 2** of [Mishra and Santhanam][MishraSanthanam2026]: when no
affine gate can be moved, no deletion applies and Case 2 does not apply, the unique child of an
unpaired isolated parameter is a gate whose other input is not a parameter. -/
theorem Valid.exclusive {S : State n} (hS : S.Valid f) (hmov : ∀ J, ¬ S.Movable J)
    (hdel : ¬ S.DeletionAvailable) (h2 : ¬ S.AndOnIsolated) : S.Exclusive := by
  intro z hz hz1 N hN z' hz' hzz hN'
  have hzp := (mem_unpaired.1 hz).1
  have hcz : S.children z = {N} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hz1
    rw [ha] at hN ⊢; rw [Finset.mem_singleton.1 hN]
  rcases N with G | e
  · obtain ⟨hG, hGz⟩ := (SemiCircuit.inl_mem_children _).1 hN
    obtain ⟨-, hGz'⟩ := (SemiCircuit.inl_mem_children _).1 hN'
    have hargs := Gate.args_of_reads (Ne.symm hzz) hGz hGz'
    by_cases haff : IsAffineOp (S.gate G).op
    · refine hmov G ⟨hG, haff, fun i hi hig => ?_⟩
      have hip : i ∈ S.params := by
        rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rcases hi with hi | hi
        · rw [hl] at hi; cases hi; exact hzp
        · rw [hr] at hi; cases hi; exact hz'
        · rw [hl] at hi; cases hi; exact hz'
        · rw [hr] at hi; cases hi; exact hzp
      exact hS.wf.notMem_gates_of_mem_params hip hig
    · exact h2 ⟨G, hG, z, z', haff, hargs, hz, hz1, hz', Ne.symm hzz⟩
  · exact hdel (Or.inr (Or.inr (Or.inr ⟨z, hz, e, hcz⟩)))

/-! ### Case 3: a paired parameter of degree other than one -/

/-- The configuration of Case 3: a paired parameter has degree `0` or at least `2`. -/
def DegeneratePair (S : State n) : Prop :=
  ∃ p ∈ S.params, S.Paired p ∧ (S.deg p = 0 ∨ 2 ≤ S.deg p)

private theorem deg_eq_one_of_not_degeneratePair {S : State n} (h3 : ¬ S.DegeneratePair) {p : ℕ}
    (hp : p ∈ S.params) (hpp : S.Paired p) : S.deg p = 1 := by
  by_contra h
  exact h3 ⟨p, hp, hpp, by omega⟩

/-- **Case 3** of the preliminary reductions. If a paired parameter `p` is unused, fixing its
partner removes the pair: `Δa = 0`, `ΔW ≤ -3`. If `p` has two children, fixing `p` makes both
deletable; the partner becomes unpaired and no other weight grows: `Δa = 0`, `ΔW ≤ 0`. -/
theorem Valid.step_of_degeneratePair {S : State n} (hS : S.Valid f) (hexcl : S.Exclusive)
    (h : S.DegeneratePair) :
    ∃ S', Step f S S' := by
  obtain ⟨p, hp, hpp, hdeg⟩ := h
  obtain ⟨r, hpr⟩ := exists_partner hpp
  have hnot : ∀ x u, S.IsPartner x u → x ∈ ({r} : Finset ℕ) ∨ x ∈ ({p} : Finset ℕ) → u ≠ r →
      u ≠ p → False := fun x u hxu hx hur hup => by
    rcases hx with hx | hx <;> rw [Finset.mem_singleton] at hx <;> subst hx
    · exact hup (hS.isPartner_unique hxu hpr.symm)
    · exact hur (hS.isPartner_unique hxu hpr)
  rcases hdeg with hdeg | hdeg
  · -- fix the partner `r`; `p` becomes unpaired and unused
    have h := hS.reduction_fixConst (hS.partner_mem hpr) false
    refine ⟨_, h.step hS (by simp) (by simp) ?_⟩
    have hW := h.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
      obtain ⟨-, hur⟩ := Finset.mem_sdiff.1 hu
      rw [Finset.mem_singleton] at hur
      by_cases hup : u = p
      · subst hup
        have := h.wt_le_weight (u := u) (fun _ hN => absurd hN List.not_mem_nil)
        rw [Finset.card_eq_zero.1 hdeg, Finset.empty_sdiff, Finset.card_empty, weight_zero] at this
        omega
      · exact Nat.add_le_add_right (h.wt_le_of_exclusive hS hexcl
          (fun x hx hxu => hnot x u hxu (Or.inl hx) hur hup)
          fun _ hN => absurd hN List.not_mem_nil) _
    simp only [Finset.sum_singleton, wt_of_paired hpr.symm.paired,
      hS.card_pairsMeeting_singleton, ite_eq_left hpr.symm.paired,
      Finset.sum_const_zero] at hW
    simp only [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_left hpr.symm.paired]
    omega
  · -- fix `p` and delete two of its children; only the partner `r` may gain weight
    obtain ⟨N₁, hN₁, N₂, hN₂, hne⟩ := Finset.one_lt_card.1 (show 1 < (S.children p).card from hdeg)
    have h₁ := hS.reduction_fixConst hp false
    obtain ⟨S', h₂⟩ := h₁.valid.exists_reduction_deleteAll [N₁, N₂] (by simp [hne]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro N (rfl | rfl)
      exacts [deletable_fixConst_child hS _ false hN₁, deletable_fixConst_child hS _ false hN₂])
    have h := h₁.trans h₂
    rw [Finset.union_empty] at h
    refine ⟨S', h.step hS (by simp) (by simp) ?_⟩
    have hW := h.W_le (fun _ => 0) (fun u => if S.IsPartner p u then 7 else 0) fun u hu => by
      obtain ⟨-, hup⟩ := Finset.mem_sdiff.1 hu
      rw [Finset.mem_singleton] at hup
      by_cases hur : S.IsPartner p u
      · rw [ite_eq_left hur]; have := S'.wt_le_seven u; omega
      · rw [ite_eq_right hur]
        refine Nat.add_le_add_right (h.wt_le_of_exclusive hS hexcl (fun x hx hxu => ?_)
          fun N hN _ => ⟨p, hp, Ne.symm hup, ?_⟩) _
        · rw [Finset.mem_singleton] at hx; subst hx; exact hur hxu
        · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hN
          rcases hN with rfl | rfl <;> assumption
    have hgain := hS.sum_partner_le p (S.params \ {p}) 7
    simp only [Finset.sum_singleton, wt_of_paired hpp, hS.card_pairsMeeting_singleton,
      ite_eq_left hpp, Finset.sum_const_zero, List.nil_append, List.length_cons,
      List.length_nil] at hW
    simp only [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_left hpp]
    omega

/-! ### Case 4: partners with a common child -/

/-- A gate whose operation is a projection or a negated projection computes a literal of an
input, so (D1) applies. -/
theorem deletionAvailable_of_unary {S : State n} {J : ℕ} (hJ : J ∈ S.gates)
    (h : IsUnaryOp (S.gate J).op) : S.DeletionAvailable := by
  refine Or.inr (Or.inl ⟨J, hJ, ?_⟩)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨⟨(S.gate J).left, (S.gate J).op false false⟩, fun t ht => Or.inl ht, fun val _ => ?_⟩
    simp only [Gate.eval, Lit.eval]
    cases (S.gate J).left.eval val <;> cases (S.gate J).right.eval val <;> simp [h1, h2, h3]
  · refine ⟨⟨(S.gate J).right, (S.gate J).op false false⟩, fun t ht => Or.inr ht, fun val _ => ?_⟩
    simp only [Gate.eval, Lit.eval]
    cases (S.gate J).left.eval val <;> cases (S.gate J).right.eval val <;> simp [h1, h2, h3]

/-- A gate with a constant operation computes a constant, so (D1) applies. -/
theorem deletionAvailable_of_const_op {S : State n} {J : ℕ} (hJ : J ∈ S.gates)
    (h : ∀ a b, (S.gate J).op a b = (S.gate J).op false false) : S.DeletionAvailable :=
  Or.inr (Or.inl ⟨J, hJ, Lit.const ((S.gate J).op false false),
    fun t ht => by simp [Lit.Reads, Lit.const] at ht, fun val _ => by
      rw [Gate.eval, h, Lit.eval_const]⟩)

/-- When no deletion applies, an equation containing two parameters `p` and `r` reads
`v + p + r = rhs` for an auxiliary variable `v`. -/
theorem Valid.eq_insert_of_mem_terms {S : State n} (hS : S.Valid f) (hdel : ¬ S.DeletionAvailable)
    {e p r : ℕ} (he : e ∈ S.eqns) (hp : p ∈ S.params) (hr : r ∈ S.params) (hpr : p ≠ r)
    (hpe : p ∈ (S.eqn e).terms) (hre : r ∈ (S.eqn e).terms) :
    ∃ v ∈ S.aux, v ≠ p ∧ v ≠ r ∧ (S.eqn e).terms = {v, p, r} := by
  obtain ⟨v, hv, hvp, hvr⟩ : ∃ v ∈ (S.eqn e).terms, v ≠ p ∧ v ≠ r := by
    by_contra hno
    push Not at hno
    refine hdel (Or.inl ⟨e, he, (Finset.card_le_card (t := {p, r}) fun i hi => ?_).trans
      (Finset.card_le_two)⟩)
    by_cases hip : i = p
    · simp [hip]
    · simp [hno i hi hip]
  have hterms : (S.eqn e).terms = {v, p, r} := (Finset.eq_of_subset_of_card_le
    (by simp [Finset.insert_subset_iff, hv, hpe, hre]) (by
      rw [Finset.card_insert_of_notMem (by simp [hvp, hvr]), Finset.card_pair hpr]
      exact hS.wf.card_terms_le e he)).symm
  refine ⟨v, ?_, hvp, hvr, hterms⟩
  rcases Finset.mem_union.1 (hS.wf.terms_subset e he hv) with hvp' | hva
  · refine absurd (hS.terms_eq_empty_of_subset he ?_) (Finset.ne_empty_of_mem hv)
    rw [hterms]
    simp [Finset.insert_subset_iff, hvp', hp, hr]
  · exact hva

/-- The configuration of Case 4: two partners have a common child. -/
def PartnersShareChild (S : State n) : Prop :=
  ∃ pr ∈ S.pairs, ∃ H, H ∈ S.children pr.1 ∧ H ∈ S.children pr.2

/-- When Case 4 does not apply, partners have no common child. -/
private theorem notMem_children_of_isPartner {S : State n} (h4 : ¬ S.PartnersShareChild) {p r : ℕ}
    (hpr : S.IsPartner p r) {N : ℕ ⊕ ℕ} (hNp : N ∈ S.children p) : N ∉ S.children r :=
  fun hNr => by
    obtain ⟨pr, hpr', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hpr
    · exact h4 ⟨pr, hpr', N, h1 ▸ hNp, h2 ▸ hNr⟩
    · exact h4 ⟨pr, hpr', N, h2 ▸ hNr, h1 ▸ hNp⟩

/-- **Case 4** of the preliminary reductions: if partners `p` and `r` have a common child `H`,
impose `p = r + c` so that `H` becomes constant and delete it; `r` becomes unused:
`Δa = 0`, `ΔW ≤ -5`. -/
theorem Valid.step_of_partnersShareChild {S : State n} (hS : S.Valid f)
    (hdel : ¬ S.DeletionAvailable) (h3 : ¬ S.DegeneratePair) (h : S.PartnersShareChild) :
    ∃ S', Step f S S' := by
  obtain ⟨pr, hpr, H, hHp, hHr⟩ := h
  obtain ⟨hp, hr, hpr12⟩ := hS.pair_mem pr hpr
  set p := pr.1
  set r := pr.2
  have hpp : S.Paired p := ⟨pr, hpr, Or.inl rfl⟩
  have hpart : S.IsPartner p r := ⟨pr, hpr, Or.inl ⟨rfl, rfl⟩⟩
  have hcp := children_eq_singleton (deg_eq_one_of_not_degeneratePair h3 hp hpp) hHp
  have hcr := children_eq_singleton (deg_eq_one_of_not_degeneratePair h3 hr hpart.symm.paired)
    hHr
  have hrp : Arg.node r ≠ Arg.node p := fun h => hpr12 (Arg.node.inj h).symm
  -- restrict `p = r + c` and delete `H`, which becomes constant
  obtain ⟨S', h⟩ : ∃ S', Reduction f S S' {p} [H] [] := by
    have hrestrict : ∀ c : Bool, Reduction f S (S.restrict p ⟨.node r, c⟩ (S.pairsAvoid p))
        {p} [] [] := fun c => hS.reduction_restrict hp fun y hy => by
      cases hy
      exact ⟨hr, Ne.symm hpr12, by rw [hcp, hcr], fun _ => hpart⟩
    rcases H with G | e
    · obtain ⟨hG, hGp⟩ := (SemiCircuit.inl_mem_children _).1 hHp
      obtain ⟨-, hGr⟩ := (SemiCircuit.inl_mem_children _).1 hHr
      obtain ⟨c, d, hd⟩ := Gate.exists_const_of_diag
        (fun hun => hdel (deletionAvailable_of_unary hG hun)) (Gate.args_of_reads hpr12 hGp hGr)
      have h₁ := hrestrict c
      exact ⟨_, h₁.trans (h₁.valid.reduction_deleteConst hG fun val _ => by
        rw [restrict_gate, Gate.eval_subst_update hrp]
        exact hd _ (by simp [Function.update_of_ne hpr12.symm, Lit.eval]))⟩
    · obtain ⟨he, hpe⟩ := (SemiCircuit.inr_mem_children _).1 hHp
      obtain ⟨-, hre⟩ := (SemiCircuit.inr_mem_children _).1 hHr
      obtain ⟨v, hva, hvp, hvr, hterms⟩ := hS.eq_insert_of_mem_terms hdel he hp hr hpr12 hpe hre
      have h₁ := hrestrict false
      exact ⟨_, h₁.trans (h₁.valid.reduction_deleteEqn (v := v) (ℓ := Lit.const (S.eqn e).rhs)
        ⟨he, hva, fun val => by
          rw [restrict_eqn, Equation.holds_subst_update hrp, Lit.eval_const]
          simpa [Lit.eval] using Equation.holds_update_iff hterms hvp hvr hpr12 val false,
          fun t ht => by simp [Lit.Reads, Lit.const] at ht⟩
        fun t ht => by simp [Lit.Reads, Lit.const] at ht)⟩
  refine ⟨S', h.step hS (by simp) (by simp) ?_⟩
  have hW := h.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
    obtain ⟨-, hup⟩ := Finset.mem_sdiff.1 hu
    by_cases hur : u = r
    · subst hur
      rw [h.wt_eq_zero_of_subset (by simp [hcr]) (by simp)]
      omega
    · refine Nat.add_le_add_right (h.wt_le hS (fun x hx hxu => ?_) (by simp)) 0
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hur (hS.isPartner_unique hxu hpart)
  rw [Finset.sum_singleton, wt_of_paired hpp, hS.card_pairsMeeting_singleton,
    ite_eq_left hpp] at hW
  simp only [Finset.sum_const_zero, List.length_singleton] at hW
  rw [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_left hpp]
  omega

/-! ### Case 5: a paired parameter in the affine system -/

/-- The configuration of Case 5: a paired parameter occurs in the affine system. -/
def PairInSystem (S : State n) : Prop :=
  ∃ p, S.Paired p ∧ ∃ e ∈ S.eqns, p ∈ (S.eqn e).terms

/-- **Case 5** of the preliminary reductions: if a paired parameter `p` occurs in the affine
system, fix its partner `r` and delete the unique child of `r`; then `p` is unpaired with at most
one child, an equation, and (D4) removes it if it remains: `Δa = 0`, `ΔW ≤ 0`. -/
theorem Valid.step_of_pairInSystem {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hexcl : S.Exclusive) (h3 : ¬ S.DegeneratePair)
    (h4 : ¬ S.PartnersShareChild) (h : S.PairInSystem) : ∃ S', Step f S S' := by
  obtain ⟨p, hpp, e, he, hpe⟩ := h
  have hp := hS.mem_params_of_paired hpp
  have hcp := children_eq_singleton (deg_eq_one_of_not_degeneratePair h3 hp hpp)
    ((SemiCircuit.inr_mem_children _).2 ⟨he, hpe⟩)
  obtain ⟨r, hpr⟩ := exists_partner hpp
  have hr := hS.partner_mem hpr
  have hrp := hS.partner_ne hpr
  obtain ⟨Hr, hHr⟩ := Finset.card_pos.1 (show 0 < S.deg r by
    rw [deg_eq_one_of_not_degeneratePair h3 hr hpr.symm.paired]; omega)
  have hHrp : Hr ∉ S.children p := fun hHp => notMem_children_of_isPartner h4 hpr hHp hHr
  -- fix `r` and delete its child
  obtain ⟨S₂, h⟩ : ∃ S₂, Reduction f S S₂ {r} [Hr] [Hr] := by
    have h₁ := hS.reduction_fixConst hr false
    obtain ⟨S₂, h₂⟩ := h₁.valid.exists_reduction_deleteAll [Hr] (by simp) fun N hN => by
      rw [List.mem_singleton] at hN; subst hN; exact deletable_fixConst_child hS _ false hHr
    have h := h₁.trans h₂
    rw [Finset.union_empty] at h
    exact ⟨S₂, h⟩
  have hpu₂ : p ∈ S₂.unpaired :=
    (h.mem_unpaired_iff hS).2 ⟨hp, by simpa using hrp.symm, Or.inr ⟨r, by simp, hpr.symm⟩⟩
  have hcp₂ : S₂.children p ⊆ {.inr e} := by
    have := h.children_subset (mem_unpaired.1 hpu₂).1 (by simpa using hHrp)
    rw [hcp] at this
    exact this.trans Finset.sdiff_subset
  have hW := h.W_le (fun _ => 0) (fun u => if u = p then weight (S₂.deg p) else 0) fun u hu => by
    obtain ⟨-, hur⟩ := Finset.mem_sdiff.1 hu
    by_cases hup : u = p
    · subst hup; rw [wt_of_mem hpu₂, ite_eq_left rfl]; omega
    · rw [ite_eq_right hup]
      refine Nat.add_le_add_right (h.wt_le_of_exclusive hS hexcl (fun x hx hxu => ?_)
        fun N hN _ => ?_) 0
      · rw [Finset.mem_singleton] at hx; subst hx
        exact hup (hS.isPartner_unique hxu hpr.symm)
      · rw [List.mem_singleton] at hN; subst hN
        exact ⟨r, hr, Ne.symm (by simpa using hur), hHr⟩
  have hpr' : p ∈ S.params \ {r} := Finset.mem_sdiff.2 ⟨hp, by simpa using hrp.symm⟩
  rw [Finset.sum_ite_eq' (S.params \ {r}) p, ite_eq_left hpr', Finset.sum_singleton,
    wt_of_paired hpr.symm.paired, hS.card_pairsMeeting_singleton,
    ite_eq_left hpr.symm.paired] at hW
  simp only [Finset.sum_const_zero, List.length_singleton] at hW
  have ha₂ := h.a_add hS
  have hm₂ := h.m_add
  have hs₂ := h.s_add
  rw [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_left hpr.symm.paired] at ha₂
  rw [Finset.card_singleton] at hm₂
  simp only [List.length_singleton] at hs₂
  have hdeg₂ : S₂.deg p ≤ 1 := (Finset.card_le_card hcp₂).trans (by simp)
  rcases Nat.lt_or_ge (S₂.deg p) 1 with h0 | h1
  · -- `p` became unused
    rw [show S₂.deg p = 0 by omega, weight_zero] at hW
    exact ⟨S₂, h.valid, by omega, by omega, by omega, by omega⟩
  · -- (D4) on `p` and its equation
    have hcp₂' : S₂.children p = {.inr e} :=
      Finset.eq_of_subset_of_card_le hcp₂ (by rw [Finset.card_singleton]; exact h1)
    rw [show S₂.deg p = 1 by omega, weight_one] at hW
    obtain ⟨S₃, hS₃, hm₃, hs₃, ha₃, -, hW₃⟩ := h.valid.unit_delete hf (by omega) hpu₂ hcp₂'
    exact ⟨S₃, hS₃, by omega, by omega, by omega, by omega⟩

/-! ### Case 6: an AND-type gate on a paired parameter -/

/-- The configuration of Case 6: an AND-type gate reads a paired parameter `p` and another
parameter `w`. -/
def AndOnPair (S : State n) : Prop :=
  ∃ G ∈ S.gates, ∃ p w, ¬ IsAffineOp (S.gate G).op ∧
    (((S.gate G).left = .node p ∧ (S.gate G).right = .node w) ∨
      ((S.gate G).left = .node w ∧ (S.gate G).right = .node p)) ∧
    S.Paired p ∧ w ∈ S.params ∧ p ≠ w

/-- **Case 6** of the preliminary reductions: an AND-type gate `G` reads a paired parameter `p`
with partner `r` and another parameter `w`. Fix `r`, fix `w` so that `G` becomes constant, and
delete `G` and the unique child of `r`; `p` becomes unpaired and unused. If `w` is unpaired,
`Δa = -1` and `ΔW ≤ -14`; otherwise the partner of `w` becomes unpaired, `Δa = 0` and
`ΔW ≤ -3`. -/
theorem Valid.step_of_andOnPair {S : State n} (hS : S.Valid f) (hexcl : S.Exclusive)
    (h2 : ¬ S.AndOnIsolated) (h3 : ¬ S.DegeneratePair) (h4 : ¬ S.PartnersShareChild)
    (h5 : ¬ S.PairInSystem) (h : S.AndOnPair) : ∃ S', Step f S S' := by
  obtain ⟨G, hG, p, w, hand, hargs, hpp, hw, hpw⟩ := h
  have hp := hS.mem_params_of_paired hpp
  obtain ⟨hGp, hGw⟩ := Gate.reads_of_args hargs
  have hcp := children_eq_singleton (deg_eq_one_of_not_degeneratePair h3 hp hpp)
    ((SemiCircuit.inl_mem_children _).2 ⟨hG, hGp⟩)
  obtain ⟨r, hpr⟩ := exists_partner hpp
  have hr := hS.partner_mem hpr
  have hrpaired := hpr.symm.paired
  obtain ⟨Hr, hHr⟩ := Finset.card_pos.1 (show 0 < S.deg r by
    rw [deg_eq_one_of_not_degeneratePair h3 hr hrpaired]; omega)
  have hGr : Sum.inl G ∉ S.children r :=
    notMem_children_of_isPartner h4 hpr (by rw [hcp]; exact Finset.mem_singleton_self _)
  obtain ⟨Hg, rfl⟩ : ∃ Hg, Hr = .inl Hg := by
    rcases Hr with Hg | e
    · exact ⟨Hg, rfl⟩
    · obtain ⟨he, hre⟩ := (SemiCircuit.inr_mem_children _).1 hHr
      exact absurd ⟨r, hrpaired, e, he, hre⟩ h5
  have hHgG : Hg ≠ G := by rintro rfl; exact hGr hHr
  have hwr : w ≠ r := by
    rintro rfl; exact hGr ((SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩)
  have hwpart : ¬ S.IsPartner r w := fun h' => hpw (hS.isPartner_unique hpr.symm h')
  -- an unpaired `w` is not isolated, else Case 2 applies
  have hwdeg : w ∈ S.unpaired → 2 ≤ S.deg w := fun hwu =>
    two_le_deg_of_not_andOnIsolated h2 hG hand hargs.symm hwu hp hpw.symm
  -- fix `r`, fix `w` so that `G` becomes constant, and delete `G` and `Hg`
  obtain ⟨b, c, hc⟩ := Gate.exists_const_of_not_isAffineOp hand hargs
  have h₁ := hS.reduction_fixConst hr false
  have h₂ := h₁.valid.reduction_fixConst (Finset.mem_erase.2 ⟨hwr, hw⟩) b
  have h₃ := h₂.valid.reduction_deleteGate (J := G) (ℓ := Lit.const c) (T := [])
    ⟨hG, fun t ht => by simp [Lit.Reads, Lit.const] at ht, Or.inl fun val _ => by
      simp only [fixConst_gate, Gate.eval_subst_const, Lit.eval_const]
      exact hc _ (by rw [Function.update_of_ne hwr, Function.update_self])⟩
    fun t ht => by simp [Lit.Reads, Lit.const] at ht
  obtain ⟨S', h₄⟩ := h₃.valid.exists_reduction_deleteAll [.inl Hg] (by simp) (by
    simp only [List.mem_singleton, forall_eq]
    exact h₃.deletable _ (by simp [hHgG]) (h₂.deletable _ (by simp)
      (deletable_fixConst_child hS _ false hHr)))
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  simp only [Finset.union_empty, List.nil_append, List.singleton_append, ← Finset.insert_eq] at h
  refine ⟨S', h.step hS Finset.card_le_two (by simp) ?_⟩
  have hW := h.W_le (fun _ => 0) (fun u => if S.IsPartner w u then 7 else 0) fun u hu => by
    obtain ⟨-, huF⟩ := Finset.mem_sdiff.1 hu
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huF
    by_cases hup : u = p
    · subst hup
      rw [h.wt_eq_zero_of_subset (by simp [hcp]) (by simp [hcp, hHgG])]
      omega
    · by_cases hwu : S.IsPartner w u
      · rw [ite_eq_left hwu]; have := S'.wt_le_seven u; omega
      · rw [ite_eq_right hwu]
        refine Nat.add_le_add_right (h.wt_le_of_exclusive hS hexcl (fun x hx hxu => ?_)
          fun N hN _ => ?_) _
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hup (hS.isPartner_unique hxu hpr.symm)
          · rw [Finset.mem_singleton] at hx; subst hx; exact hwu hxu
        · rw [List.mem_singleton] at hN; subst hN
          exact ⟨r, hr, Ne.symm huF.1, hHr⟩
  have hk : (S.pairsMeeting {r, w}).card = (if S.Paired w then 1 else 0) + 1 := by
    rw [hS.card_pairsMeeting_insert (by simpa using hwr.symm) (by simpa using hwpart),
      hS.card_pairsMeeting_singleton, ite_eq_left hrpaired]
  have hgain := hS.sum_partner_le w (S.params \ {r, w}) 7
  rw [Finset.sum_pair hwr.symm, wt_of_paired hrpaired, hk] at hW
  simp only [Finset.sum_const_zero, List.length_cons, List.length_nil] at hW
  rw [Finset.card_pair hwr.symm, hk]
  by_cases hwp : S.Paired w
  · rw [ite_eq_left hwp] at hW ⊢; rw [wt_of_paired hwp] at hW; omega
  · have hwu : w ∈ S.unpaired := mem_unpaired.2 ⟨hw, hwp⟩
    rw [wt_of_mem hwu, weight_of_two_le (hwdeg hwu),
      Finset.sum_eq_zero fun u _ => ite_eq_right fun h' => hwp h'.paired] at hW
    rw [ite_eq_right hwp] at hW ⊢; omega

/-! ### Normal states -/

/-- A state in which no affine gate can be moved and no preliminary reduction applies, recorded by
the consequences used to restructure and eliminate the minimal AND. -/
structure Normal (S : State n) : Prop where
  /-- No affine gate reading no gates remains. -/
  not_movable : ∀ J, ¬ S.Movable J
  /-- No deletion applies. -/
  no_deletion : ¬ S.DeletionAvailable
  /-- No constraint has an unpaired isolated parameter and another parameter as parents. -/
  exclusive : S.Exclusive
  /-- Every parameter occurring in the affine system is unpaired of degree at least two. -/
  system_param : ∀ x ∈ S.params, ∀ e ∈ S.eqns, x ∈ (S.eqn e).terms →
    x ∈ S.unpaired ∧ 2 ≤ S.deg x
  /-- Both parameters read by an AND-type gate are unpaired of degree at least two. -/
  and_param : ∀ G ∈ S.gates, ¬ IsAffineOp (S.gate G).op → ∀ x y,
    (((S.gate G).left = .node x ∧ (S.gate G).right = .node y) ∨
      ((S.gate G).left = .node y ∧ (S.gate G).right = .node x)) →
    x ∈ S.params → y ∈ S.params → x ≠ y → x ∈ S.unpaired ∧ 2 ≤ S.deg x

/-- The preliminary reductions of [Mishra and Santhanam, Section 4.1][MishraSanthanam2026]: if
`d < a` and no affine gate can be moved, one of Cases 1 to 6 applies, giving a step of gate
elimination, or the state is normal. -/
theorem Valid.step_or_normal {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) (hmov : ∀ J, ¬ S.Movable J) : (∃ S', Step f S S') ∨ S.Normal := by
  by_cases hdel : S.DeletionAvailable
  · exact Or.inl (hS.step_of_deletion hf ha hdel)
  by_cases h2 : S.AndOnIsolated
  · exact Or.inl (hS.step_of_andOnIsolated h2)
  have hexcl := hS.exclusive hmov hdel h2
  by_cases h3 : S.DegeneratePair
  · exact Or.inl (hS.step_of_degeneratePair hexcl h3)
  by_cases h4 : S.PartnersShareChild
  · exact Or.inl (hS.step_of_partnersShareChild hdel h3 h4)
  by_cases h5 : S.PairInSystem
  · exact Or.inl (hS.step_of_pairInSystem hf ha hexcl h3 h4 h5)
  by_cases h6 : S.AndOnPair
  · exact Or.inl (hS.step_of_andOnPair hexcl h2 h3 h4 h5 h6)
  refine Or.inr ⟨hmov, hdel, hexcl, fun x hx e he hxe => ?_,
    fun G hG hand x y hargs hx hy hxy => ?_⟩
  · have hxu : x ∈ S.unpaired := mem_unpaired.2 ⟨hx, fun hp => h5 ⟨x, hp, e, he, hxe⟩⟩
    have hex : Sum.inr e ∈ S.children x := (SemiCircuit.inr_mem_children _).2 ⟨he, hxe⟩
    refine ⟨hxu, ?_⟩
    by_contra hlt
    have h1 : S.deg x = 1 := by
      have := Finset.card_pos.2 ⟨_, hex⟩
      change 0 < S.deg x at this
      omega
    exact hdel (Or.inr (Or.inr (Or.inr ⟨x, hxu, e, children_eq_singleton h1 hex⟩)))
  · have hxu : x ∈ S.unpaired :=
      mem_unpaired.2 ⟨hx, fun hp => h6 ⟨G, hG, x, y, hand, hargs, hp, hy, hxy⟩⟩
    exact ⟨hxu, two_le_deg_of_not_andOnIsolated h2 hG hand hargs hxu hy hxy⟩

end State

end Cslib.Circuits.Boolean.AffineDisperser
