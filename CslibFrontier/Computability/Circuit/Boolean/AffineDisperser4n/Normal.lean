/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Deletion

/-!
# Normal form and Cases 1–5a of Lemma 4.2 for `4n - 10d` gate elimination

Every valid state `S` for a `d`-affine disperser with `d < S.a` either admits a step strictly
reducing `m + s` with `ΔW ≤ 10 Δa` (via deletions, moving an affine gate into the affine system,
or eliminating a degenerate pair, shared child, pair in an equation, or AND gate reading a paired
parameter), or else satisfies `State.Normal`:

* no movable affine gate (`¬ S.Movable`);
* no deletion `(D1)`–`(D4)` (`¬ S.DeletionAvailable`);
* every paired parameter has degree `1` (`¬ S.DegeneratePair`);
* partners share no child (`¬ S.PartnersShareChild`);
* no paired parameter occurs in the affine system (`¬ S.PairInSystem`);
* no non-affine gate reads a paired parameter alongside another parameter (`¬ S.AndOnPair`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Movable`: an affine gate reading no gates.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.freshEqn`: a fresh equation name.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.DegeneratePair`: Case 2.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.PartnersShareChild`: Case 3.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.PairInSystem`: Case 4.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.AndOnPair`: Case 5a.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Normal`: normal form of a state.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.preparation_moveAffine`: moving an
  affine gate is a preparatory operation reducing `gates.card`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_or_normal`: Cases 1–5a either yield
  a valid step with `ΔW ≤ 10 Δa` or prove `S.Normal`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  labels follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ}

/-! ### Helper lemmas on pairs -/

private theorem bias_eq_of_mem {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {pr pr' : ZeroPair} (hpr : pr ∈ S.pairs) {p : ℕ} (hp : pr.Contains p) (hpr' : pr' ∈ S.pairs)
    (hp' : pr'.Contains p) : pr.bias p = pr'.bias p := by
  rw [hS.pair_unique hpr hpr' hp hp']

private theorem bias_partner_eq_of_mem {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {pr pr' : ZeroPair} (hpr : pr ∈ S.pairs) {p : ℕ} (hp : pr.Contains p) (hpr' : pr' ∈ S.pairs)
    (hr' : pr'.Contains (pr.partner p)) : pr.partnerBias p = pr'.bias (pr.partner p) := by
  have heq := hS.pair_unique hpr' hpr hr' (pr.contains_partner hp)
  rw [heq]
  exact (ZeroPair.bias_partner (hS.pair_mem pr hpr).2.2 hp).symm

/-! ### Moving affine gates -/

/-- Whether `S` has an affine gate reading no gates, ready to be moved into the affine system. -/
@[expose] def Movable (S : State n) : Prop :=
  ∃ J ∈ S.gates, IsAffineOp (S.gate J).op ∧ ∀ i, (S.gate J).Reads i → i ∉ S.gates

/-- An equation identifier guaranteed not to belong to `S.eqns`. -/
@[expose] def freshEqn (S : State n) : ℕ :=
  if h : S.eqns.Nonempty then S.eqns.max' h + 1 else 0

/-- `S.freshEqn` is not an equation of `S`. -/
theorem freshEqn_notMem (S : State n) : S.freshEqn ∉ S.eqns := by
  unfold freshEqn
  split_ifs with h
  · intro hm
    have hle := Finset.le_max' S.eqns _ hm
    omega
  · intro hm
    exact h ⟨_, hm⟩

/-- Moving an affine gate reading no gates is a preparatory operation reducing `gates.card`. -/
theorem Valid.preparation_moveAffine {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {J : ℕ} (hJ : J ∈ S.gates) (haff : IsAffineOp (S.gate J).op)
    (hin : ∀ i, (S.gate J).Reads i → i ∉ S.gates) :
    let S' := S.moveAffine J S.freshEqn
    Preparation f S S' ∧ S'.gates.card < S.gates.card := by
  have hm : S.MoveOK J S.freshEqn := ⟨hJ, freshEqn_notMem S, haff, hin⟩
  let S' := S.moveAffine J S.freshEqn
  have hS' : S'.Valid f := hS.moveAffine hm
  have hs : S'.s = S.s := moveAffine_size hm
  have hq : S'.q = S.q := by simp only [q, S', moveAffine_pairs]
  have hW : S'.W ≤ S.W := by
    have h := W_add_le (S := S) (S' := S') (N := S.params) le_rfl
      (by rw [moveAffine_params]) (fun _ => 0) (fun _ => 0) fun u hu => by
        simp only [add_zero]
        by_cases hup : S.Paired u
        · have hup' : S'.Paired u := (paired_congr (moveAffine_pairs S J S.freshEqn)).2 hup
          rw [wt_of_paired hup', wt_of_paired hup]
        · have hu' : u ∈ S'.unpaired := mem_unpaired.2 ⟨by rwa [moveAffine_params],
            fun hp => hup ((paired_congr (moveAffine_pairs S _ _)).1 hp)⟩
          have hu0 : u ∈ S.unpaired := mem_unpaired.2 ⟨hu, hup⟩
          rw [wt_of_mem hu', wt_of_mem hu0]
          exact weight_mono (moveAffine_deg_le hS hm hu)
    simp only [Finset.sum_const_zero, add_zero, hs, hq] at h
    omega
  have hcard : S'.gates.card < S.gates.card := by
    have := moveAffine_gates_card hm
    change S'.gates.card + 1 = S.gates.card at this
    omega
  exact ⟨⟨hS', rfl, hs, hq, hW⟩, hcard⟩

/-! ### Case 2: Degenerate paired parameter -/

/-- A paired parameter whose degree is `0` or at least `2` (Case 2). -/
@[expose] def DegeneratePair (S : State n) : Prop :=
  ∃ p, S.Paired p ∧ (S.deg p = 0 ∨ 2 ≤ S.deg p)

/-- When no paired parameter is degenerate, every paired parameter has degree `1`. -/
theorem Paired.deg_eq_one {S : State n} (hndeg : ¬ S.DegeneratePair) {p : ℕ}
    (hp : S.Paired p) : S.deg p = 1 := by
  have h0 : S.deg p ≠ 0 := fun h => hndeg ⟨p, hp, Or.inl h⟩
  have h2 : ¬ 2 ≤ S.deg p := fun h => hndeg ⟨p, hp, Or.inr h⟩
  omega

private theorem Paired.children_eq_singleton {S : State n} (hndeg : ¬ S.DegeneratePair)
    {p : ℕ} (hp : S.Paired p) {H : ℕ ⊕ ℕ} (hH : H ∈ S.children p) : S.children p = {H} :=
  AffineDisperserCore.State.children_eq_singleton (Paired.deg_eq_one hndeg hp).le hH

/-- Fixing the partner of a paired parameter `p` of degree `0` to its bias gives a valid step with
`Δa = 0` and `ΔW ≤ 0` (Case 2). -/
private lemma partner_properties {n} {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) {pr : ZeroPair}
    (hpr : pr ∈ S.pairs) {p : ℕ} (hprp : pr.Contains p) :
    let r := pr.partner p
    r ≠ p ∧ pr.Contains r ∧ r ∈ S.params := by
  let r := pr.partner p
  have hne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hrp : r ≠ p := pr.partner_ne hne hprp
  have hprr : pr.Contains r := pr.contains_partner hprp
  have hrpar : r ∈ S.params := hS.mem_params_of_contains hpr hprr
  exact ⟨hrp, hprr, hrpar⟩

theorem Valid.step_degeneratePair_zero {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p : ℕ} (hprp : pr.Contains p) (hp0 : S.deg p = 0) :
    Step f S (S.fixConst (pr.partner p) (pr.partnerBias p)) := by
  let r := pr.partner p
  have ⟨hrp, hprr, hrpar⟩ := partner_properties hS hpr hprp
  have hpr_part : S.IsPartner p r := isPartner_of_contains hpr hprp hprr hrp.symm
  have hb : ∀ pr' ∈ S.pairs, pr'.Contains r → pr.partnerBias p = pr'.bias r :=
    fun pr' hpr' hcr => bias_partner_eq_of_mem hS hpr hprp hpr' hcr
  have hred := Valid.reduction_fixConst hS hrpar hb
  have hk : (S.pairsMeeting {r}).card = 1 := by
    rw [hS.card_pairsMeeting_singleton r, ite_eq_left ⟨pr, hpr, hprr⟩]
  refine hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) ?_
  have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u _ => by
    simp only [add_zero]
    by_cases hup : u = p
    · subst hup
      have hch : (S.fixConst r (pr.partnerBias u)).children u = S.children u :=
        fixConst_children S (pr.partnerBias u) hrp.symm
      by_cases hu_mem : u ∈ (S.fixConst r (pr.partnerBias u)).unpaired
      · rw [wt_of_mem hu_mem]
        have hdeg0 : (S.fixConst r (pr.partnerBias u)).deg u = 0 := by
          unfold deg; rw [hch]; exact hp0
        rw [hdeg0, config_weight, weight_zero]
        exact Nat.zero_le _
      · rw [wt_of_notMem hu_mem]
        exact Nat.zero_le _
    · exact Reduction.wt_le hred hS fun x hx hxu =>
        hup (hS.isPartner_unique_right
          (by rcases Finset.mem_singleton.1 hx; exact IsPartner.symm hxu) hpr_part)
  rw [hk] at hW ⊢
  simp only [Finset.card_singleton, List.length_nil, Finset.sum_const_zero] at hW ⊢
  omega

/-- Fixing a paired parameter `p` to its bias and deleting two distinct children `N₁ ≠ N₂` of `p`
gives a valid step with `Δa = 0` and `ΔW ≤ 0` (Case 2). -/
theorem Valid.step_degeneratePair_two {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p : ℕ} (hprp : pr.Contains p) {N₁ N₂ : ℕ ⊕ ℕ}
    (hN₁ : N₁ ∈ S.children p) (hN₂ : N₂ ∈ S.children p) (hN₁₂ : N₁ ≠ N₂) :
    Step f S (((S.fixConst p (pr.bias p)).deleteConstraint N₁).deleteConstraint N₂) := by
  have hppar : p ∈ S.params := hS.mem_params_of_contains hpr hprp
  have hb : ∀ pr' ∈ S.pairs, pr'.Contains p → pr.bias p = pr'.bias p :=
    fun pr' hpr' hcp => bias_eq_of_mem hS hpr hprp hpr' hcp
  have hred₁ := Valid.reduction_fixConst hS hppar hb
  have hred₂ := hred₁.valid.reduction_deleteConstraint
    (deletable_fixConst_child hS (S.pairsAvoid p) (pr.bias p) hN₁)
  have hred₃ := hred₂.valid.reduction_deleteConstraint <| hred₂.deletable N₂
    (by simp [hN₁₂.symm]) (deletable_fixConst_child hS (S.pairsAvoid p) (pr.bias p) hN₂)
  have hred := (hred₁.trans_delete hred₂).trans_delete hred₃
  have hk : (S.pairsMeeting {p}).card = 1 := by
    rw [hS.card_pairsMeeting_singleton p, ite_eq_left ⟨pr, hpr, hprp⟩]
  refine hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) ?_
  let gain : ℕ → ℕ := fun u => if S.IsPartner p u then 6 else 0
  have hW := hred.W_le (fun _ => 0) gain fun u _ => by
    by_cases hup : S.IsPartner p u
    · simp only [gain, ite_eq_left hup, add_zero]
      exact (State.wt_le_bound _ u).trans (Nat.le_add_left _ _)
    · simp only [gain, ite_eq_right hup, add_zero]
      exact Reduction.wt_le hred hS fun x hx hxu => hup (Finset.mem_singleton.1 hx ▸ hxu)
  have hgain : ∑ u ∈ S.params \ {p}, gain u ≤ 6 := hS.sum_partner_le p (S.params \ {p}) 6
  rw [hk] at hW ⊢
  simp only [Finset.card_singleton, List.nil_append, List.singleton_append, List.length_cons,
    List.length_nil, Finset.sum_const_zero] at hW ⊢
  omega

/-- Eliminating a degenerate paired parameter gives a valid step with `Δa = 0` and `ΔW ≤ 0`. -/
theorem Valid.step_of_degeneratePair {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hdeg : S.DegeneratePair) : ∃ S', Step f S S' := by
  obtain ⟨p, ⟨pr, hpr, hprp⟩, hp0 | hp2⟩ := hdeg
  · exact ⟨_, Valid.step_degeneratePair_zero hS hpr hprp hp0⟩
  · obtain ⟨N₁, hN₁, N₂, hN₂, hN₁₂⟩ := Finset.one_lt_card.1 hp2
    exact ⟨_, Valid.step_degeneratePair_two hS hpr hprp hN₁ hN₂ hN₁₂⟩

/-! ### Case 3: Partners sharing a child -/

/-- Two paired partners share a child (Case 3). -/
@[expose] def PartnersShareChild (S : State n) : Prop :=
  ∃ pr ∈ S.pairs, (S.children pr.fst ∩ S.children pr.snd).Nonempty

private theorem bool_triangle_aux (f00 f01 f10 f11 α β : Bool) :
    let g := fun a b : Bool => cond a (cond b f11 f10) (cond b f01 f00)
    (∀ b, g α b = g α β) ∨ (∀ a, g a β = g α β) ∨ (∀ b, g (b ^^ !(α ^^ β)) b = g α (!β)) := by
  revert f00 f01 f10 f11 α β
  decide

private theorem bool_triangle_pair (φ : Bool → Bool → Bool) (α β : Bool) :
    (∀ b, φ α b = φ α β) ∨ (∀ a, φ a β = φ α β) ∨ (∀ b, φ (b ^^ !(α ^^ β)) b = φ α (!β)) := by
  have hφ : ∀ a b, φ a b = cond a (cond b (φ true true) (φ true false))
      (cond b (φ false true) (φ false false)) := fun a b => by
    cases a <;> cases b <;> rfl
  have h := bool_triangle_aux (φ false false) (φ false true) (φ true false) (φ true true) α β
  simpa only [← hφ] using h

private theorem step_of_partnersShareChild_finish {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p r : ℕ}
    (hcp : pr.Contains p) (hcr : pr.Contains r) (hpr_ne : p ≠ r)
    {S₂ : State n} {L T : List (ℕ ⊕ ℕ)} (hL : L.length = 1)
    (hred : Reduction f S S₂ {p} L T) (hr_wt : S₂.wt r = 0) : Step f S S₂ := by
  have hpp : S.Paired p := ⟨pr, hpr, hcp⟩
  have hpr_part : S.IsPartner r p := isPartner_of_contains hpr hcr hcp hpr_ne.symm
  have hk : (S.pairsMeeting {p}).card = 1 := by
    rw [hS.card_pairsMeeting_singleton p, ite_eq_left hpp]
  refine hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) ?_
  have hr_part : ∀ u ∈ S.params \ {p}, u ≠ r → ∀ x ∈ ({p} : Finset ℕ), ¬ S.IsPartner x u := by
    rintro u _ hur x hx hxu
    exact hur (hS.isPartner_unique_right (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu) hpr_part)
  have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
    simp only [add_zero]
    by_cases hur : u = r
    · subst hur; rw [hr_wt]; exact Nat.zero_le _
    · exact Reduction.wt_le hred hS (hr_part u hu hur)
  rw [hL] at hW
  rw [hk] at hW ⊢
  simp only [Finset.card_singleton, Finset.sum_const_zero] at hW ⊢
  omega

private theorem partnersShareChild_reduction_restrict {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) {pr : ZeroPair} (hpr : pr ∈ S.pairs)
    (hp_par : pr.fst ∈ S.params) (hr_par : pr.snd ∈ S.params) (hpr_ne : pr.fst ≠ pr.snd)
    (hsub : S.children pr.fst ⊆ S.children pr.snd) :
    Reduction f S (S.restrict pr.fst ⟨.node pr.snd, !(pr.fstBias ^^ pr.sndBias)⟩
      (S.pairsAvoid pr.fst)) {pr.fst} [] [] := by
  let γ : Bool := !(pr.fstBias ^^ pr.sndBias)
  let ℓ : Lit := ⟨.node pr.snd, γ⟩
  have hℓ_reads : ∀ y, ℓ.Reads y →
      y ∈ S.params ∧ y ≠ pr.fst ∧ S.children pr.fst ⊆ S.children y := fun y hy => by
    cases hy
    exact ⟨hr_par, hpr_ne.symm, hsub⟩
  refine Valid.reduction_restrict hS hp_par hℓ_reads fun pr₁ hpr₁ hc val => ?_
  have heq := hS.pair_unique hpr₁ hpr hc (Or.inl rfl)
  rw [heq, ZeroPair.holds_iff_and_eq_false, Function.update_self,
    Function.update_of_ne hpr_ne.symm]
  dsimp only [Lit.eval, Arg.eval_node]
  generalize val pr.snd = b; generalize pr.fstBias = α; generalize pr.sndBias = β
  cases α <;> cases β <;> cases b <;> decide

private theorem step_of_partnersShareChild_fix {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p r G : ℕ} {b c : Bool}
    (hcp : pr.Contains p) (hcr : pr.Contains r) (hpr_ne : p ≠ r) (hb : pr.bias p = b)
    (hG : G ∈ S.gates) (hcrG : S.children r = {.inl G})
    (hconst : ∀ val, (S.gate G).eval (Function.update val p b) = c) :
    Step f S ((S.fixConst p b).deleteGate G (Lit.const c)) := by
  have hp_par : p ∈ S.params := hS.mem_params_of_contains hpr hcp
  have hb' : ∀ pr' ∈ S.pairs, pr'.Contains p → b = pr'.bias p :=
    fun pr' hpr' hc => hb ▸ bias_eq_of_mem hS hpr hcp hpr' hc
  have hred₁ := Valid.reduction_fixConst hS hp_par hb'
  have hred₂ := hred₁.valid.reduction_deleteConst hG fun val _ _ => by
    rw [fixConst_gate, Gate.eval_subst_const]
    exact hconst val
  have hred := hred₁.trans_delete hred₂
  refine step_of_partnersShareChild_finish hS hpr hcp hcr hpr_ne (by simp) hred ?_
  exact hred.wt_eq_zero_of_subset (by simp [hcrG]) (fun _ h => by cases h)

private theorem eq_of_eq_false_true {g : Bool → Bool} (h : g false = g true) (a b : Bool) :
    g a = g b := by
  cases a <;> cases b <;> simp [h]

/-- The successor state of Case 3 for paired partners `pr.fst` and `pr.snd` sharing the child `H`.
For a gate `H = .inl G`, `φ` is the operation of `G` as a function of the values of `pr.fst` and
`pr.snd`. If `φ` does not depend on its second argument when the first is `pr.fstBias`, then
`pr.fst` is fixed to `pr.fstBias`; symmetrically for `pr.snd`. Otherwise `pr.fst` is restricted to
the literal of `pr.snd` that satisfies the pair, on which `G` is constant. In each case the now
constant gate `G` is deleted. For an equation `H = .inr e`, `pr.fst` is restricted to that literal
and `e` is deleted. -/
@[expose] def partnersShareChildStep (S : State n) (pr : ZeroPair) : ℕ ⊕ ℕ → State n
  | .inl G =>
    let φ : Bool → Bool → Bool := fun a b => (S.gate G).op
      (if (S.gate G).left = .node pr.fst then a else b)
      (if (S.gate G).right = .node pr.fst then a else b)
    if φ pr.fstBias false = φ pr.fstBias true then
      (S.fixConst pr.fst pr.fstBias).deleteGate G (Lit.const (φ pr.fstBias pr.sndBias))
    else if φ false pr.sndBias = φ true pr.sndBias then
      (S.fixConst pr.snd pr.sndBias).deleteGate G (Lit.const (φ pr.fstBias pr.sndBias))
    else
      (S.restrict pr.fst ⟨.node pr.snd, !(pr.fstBias ^^ pr.sndBias)⟩
        (S.pairsAvoid pr.fst)).deleteGate G (Lit.const (φ pr.fstBias (!pr.sndBias)))
  | .inr e =>
    (S.restrict pr.fst ⟨.node pr.snd, !(pr.fstBias ^^ pr.sndBias)⟩
      (S.pairsAvoid pr.fst)).deleteConstraint (.inr e)

/-- Eliminating a shared child `H` of paired partners by `S.partnersShareChildStep pr H` gives a
valid step with `Δa = 0` and `ΔW ≤ -5`, provided every paired parameter has degree `1` and every
equation has more than two terms. -/
theorem Valid.step_partnersShareChild_of {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hD3 : ∀ e ∈ S.eqns, 2 < (S.eqn e).terms.card) (hndeg : ¬ S.DegeneratePair)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {H : ℕ ⊕ ℕ} (hHp : H ∈ S.children pr.fst)
    (hHr : H ∈ S.children pr.snd) : Step f S (S.partnersShareChildStep pr H) := by
  have hp_par : pr.fst ∈ S.params := (hS.pair_mem pr hpr).1
  have hr_par : pr.snd ∈ S.params := (hS.pair_mem pr hpr).2.1
  have hpr_ne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hcpH : S.children pr.fst = {H} :=
    Paired.children_eq_singleton hndeg ⟨pr, hpr, Or.inl rfl⟩ hHp
  have hcrH : S.children pr.snd = {H} :=
    Paired.children_eq_singleton hndeg ⟨pr, hpr, Or.inr rfl⟩ hHr
  have hred₁ := partnersShareChild_reduction_restrict hS hpr hp_par hr_par hpr_ne
    (by rw [hcpH, hcrH])
  rcases H with G | e
  · obtain ⟨hG, hGp⟩ := (SemiCircuit.inl_mem_children _).1 hHp
    obtain ⟨_, hGr⟩ := (SemiCircuit.inl_mem_children _).1 hHr
    set φ : Bool → Bool → Bool := fun a b => (S.gate G).op
      (if (S.gate G).left = .node pr.fst then a else b)
      (if (S.gate G).right = .node pr.fst then a else b) with hφdef
    have hφ : ∀ val : ℕ → Bool, (S.gate G).eval val = φ (val pr.fst) (val pr.snd) := fun val => by
      rcases Gate.args_of_reads hpr_ne hGp hGr with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
        simp [hφdef, Gate.eval, hl, hr, hpr_ne.symm]
    change Step f S (if φ pr.fstBias false = φ pr.fstBias true then
        (S.fixConst pr.fst pr.fstBias).deleteGate G (Lit.const (φ pr.fstBias pr.sndBias))
      else if φ false pr.sndBias = φ true pr.sndBias then
        (S.fixConst pr.snd pr.sndBias).deleteGate G (Lit.const (φ pr.fstBias pr.sndBias))
      else
        (S.restrict pr.fst ⟨.node pr.snd, !(pr.fstBias ^^ pr.sndBias)⟩
          (S.pairsAvoid pr.fst)).deleteGate G (Lit.const (φ pr.fstBias (!pr.sndBias))))
    split_ifs with h1 h2
    · refine step_of_partnersShareChild_fix hS hpr (Or.inl rfl) (Or.inr rfl) hpr_ne
        (by simp [ZeroPair.bias]) hG hcrH fun val => ?_
      rw [hφ, Function.update_self, Function.update_of_ne hpr_ne.symm]
      exact eq_of_eq_false_true h1 _ _
    · refine step_of_partnersShareChild_fix hS hpr (Or.inr rfl) (Or.inl rfl) hpr_ne.symm
        (by simp [ZeroPair.bias, hpr_ne]) hG hcpH fun val => ?_
      rw [hφ, Function.update_self, Function.update_of_ne hpr_ne]
      exact eq_of_eq_false_true (g := fun a => φ a pr.sndBias) h2 _ _
    · have h3 : ∀ b, φ (b ^^ !(pr.fstBias ^^ pr.sndBias)) b = φ pr.fstBias (!pr.sndBias) := by
        rcases bool_triangle_pair φ pr.fstBias pr.sndBias with h | h | h
        · exact absurd (by rw [h false, h true]) h1
        · exact absurd (by rw [h false, h true]) h2
        · exact h
      have hred₂ := hred₁.valid.reduction_deleteConst hG fun val _ _ => by
        rw [restrict_gate, Gate.eval_subst_update (by simp [hpr_ne.symm]), hφ,
          Function.update_self, Function.update_of_ne hpr_ne.symm]
        exact h3 (val pr.snd)
      have hred := hred₁.trans_delete hred₂
      refine step_of_partnersShareChild_finish hS hpr (Or.inl rfl) (Or.inr rfl) hpr_ne
        rfl hred ?_
      exact hred.wt_eq_zero_of_subset
        (fun x hx => by change x ∈ S.children pr.snd at hx; rw [hcrH] at hx; simpa using hx)
        (fun _ h => by cases h)
  · obtain ⟨he, hep⟩ := (SemiCircuit.inr_mem_children _).1 hHp
    obtain ⟨_, her⟩ := (SemiCircuit.inr_mem_children _).1 hHr
    let γ : Bool := !(pr.fstBias ^^ pr.sndBias)
    let ℓ : Lit := ⟨.node pr.snd, γ⟩
    let S₁ := S.restrict pr.fst ℓ (S.pairsAvoid pr.fst)
    have hterms : (S₁.eqn e).terms = ((S.eqn e).terms.erase pr.fst).erase pr.snd := by
      change ((S.eqn e).subst pr.fst ℓ).terms = _
      have hsub : (S.eqn e).subst pr.fst ℓ =
          { terms := symmDiff ((S.eqn e).terms.erase pr.fst) {pr.snd},
            rhs := (S.eqn e).rhs ^^ γ } := by
        unfold Equation.subst
        exact ite_eq_left hep
      rw [hsub]
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
      by_cases hir : i = pr.snd
      · simp [hir, hpr_ne.symm, her]
      · simp [hir]
    have hdel : S₁.Deletable (.inr e) := by
      refine ⟨he, ?_⟩
      rw [hterms, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hpr_ne.symm, her⟩),
        Finset.card_erase_of_mem hep]
      have h3 := hS.wf.card_terms_le e he
      have := hD3 e he
      omega
    have hcr1 : S₁.children pr.snd = ∅ := by
      ext (K | e')
      · simp only [Finset.notMem_empty, iff_false]
        intro hK
        obtain ⟨hKm, hKr⟩ := (SemiCircuit.inl_mem_children _).1 hK
        rcases Gate.reads_of_reads_subst hKr with h | ⟨h, _⟩
        · have : Sum.inl K ∈ S.children pr.snd := (SemiCircuit.inl_mem_children _).2 ⟨hKm, h⟩
          rw [hcrH, Finset.mem_singleton] at this
          cases this
        · have : Sum.inl K ∈ S.children pr.fst := (SemiCircuit.inl_mem_children _).2 ⟨hKm, h⟩
          rw [hcpH, Finset.mem_singleton] at this
          cases this
      · simp only [Finset.notMem_empty, iff_false]
        intro he'
        obtain ⟨he'm, he'r⟩ := (SemiCircuit.inr_mem_children _).1 he'
        by_cases hee : e' = e
        · subst hee
          rw [hterms] at he'r
          exact Finset.notMem_erase pr.snd _ he'r
        · have hp_not : pr.fst ∉ (S.eqn e').terms := fun hm => by
            have : Sum.inr e' ∈ S.children pr.fst :=
              (SemiCircuit.inr_mem_children _).2 ⟨he'm, hm⟩
            rw [hcpH, Finset.mem_singleton, Sum.inr.injEq] at this
            exact hee this
          have hsub : ((S.eqn e').subst pr.fst ℓ) = S.eqn e' := by
            simp [Equation.subst, hp_not]
          change pr.snd ∈ ((S.eqn e').subst pr.fst ℓ).terms at he'r
          rw [hsub] at he'r
          have : Sum.inr e' ∈ S.children pr.snd :=
            (SemiCircuit.inr_mem_children _).2 ⟨he'm, he'r⟩
          rw [hcrH, Finset.mem_singleton, Sum.inr.injEq] at this
          exact hee this
    have hred₂ := hred₁.valid.reduction_deleteConstraint hdel
    have hr_wt₁ : S₁.wt pr.snd = 0 := by
      by_cases hru : pr.snd ∈ S₁.unpaired
      · rw [wt_of_mem hru, deg, hcr1, Finset.card_empty, config_weight, weight_zero]
      · exact wt_of_notMem hru
    have hr_wt₂ : (S₁.deleteConstraint (.inr e)).wt pr.snd = 0 := by
      have := Reduction.wt_le hred₂ (u := pr.snd) hred₁.valid
        fun x hx _ => absurd hx (Finset.notMem_empty _)
      exact Nat.eq_zero_of_le_zero (this.trans_eq hr_wt₁)
    exact step_of_partnersShareChild_finish hS hpr (Or.inl rfl) (Or.inr rfl) hpr_ne
      rfl (hred₁.trans_delete hred₂) hr_wt₂

/-- Eliminating a shared child of paired partners gives a valid step with `Δa = 0` and
`ΔW ≤ -5`. -/
theorem Valid.step_of_partnersShareChild {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) (hndel : ¬ S.DeletionAvailable) (hndeg : ¬ S.DegeneratePair)
    (hsh : S.PartnersShareChild) : ∃ S', Step f S S' := by
  obtain ⟨pr, hpr, H, hH⟩ := hsh
  obtain ⟨hHp, hHr⟩ := Finset.mem_inter.1 hH
  refine ⟨_, Valid.step_partnersShareChild_of hS (fun e he => ?_) hndeg hpr hHp hHr⟩
  by_contra hle
  push Not at hle
  exact hndel (Or.inr (Or.inr (Or.inl ⟨e, he, hle⟩)))

/-! ### Case 4: Paired parameter in an affine equation -/

/-- A paired parameter occurring in an affine equation (Case 4). -/
@[expose] def PairInSystem (S : State n) : Prop :=
  ∃ p, S.Paired p ∧ ∃ e ∈ S.eqns, p ∈ (S.eqn e).terms

/-- Fixing a parameter to a constant makes the output read no new name. -/
private theorem out_reads_of_fixConst {S : State n} {w : ℕ} {b : Bool} {t : ℕ}
    (h : (S.fixConst w b).out.Reads t) : S.out.Reads t := by
  rcases Lit.reads_of_reads_subst (show (S.out.subst w (Lit.const b)).Reads t from h)
    with h | ⟨-, h⟩
  · exact h
  · simp [Lit.Reads, Lit.const] at h

/-- After deleting a deletable constraint `N`, the output reads only names that it read before or
that `N` reads. -/
private theorem out_reads_of_deleteConstraint {S : State n} {N : ℕ ⊕ ℕ} (hN : S.Deletable N)
    {t : ℕ} (h : (S.deleteConstraint N).out.Reads t) : S.out.Reads t ∨ N ∈ S.children t := by
  rcases N with J | e
  · rcases Lit.reads_of_reads_subst (show (S.out.subst J (S.gate J).lit).Reads t from h)
      with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr ((SemiCircuit.inl_mem_children _).2 ⟨hN.1, Gate.reads_of_lit_reads h⟩)
  · dsimp only [deleteConstraint] at h
    split_ifs at h with hA hR
    · rcases Lit.reads_of_reads_subst h with h | ⟨-, h⟩
      · exact Or.inl h
      · cases h
        exact Or.inr ((SemiCircuit.inr_mem_children _).2
          ⟨hN.1, Finset.mem_of_mem_erase (Finset.min'_mem _ hR)⟩)
    · rcases Lit.reads_of_reads_subst h with h | ⟨-, h⟩
      · exact Or.inl h
      · simp [Lit.Reads, Lit.const] at h
    · exact Or.inl h


private theorem partnersShareChild_of_mem_children {n} {S : State n}
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p r : ℕ} (hprp : pr.Contains p) (hprr : pr.Contains r)
    (hrp : r ≠ p) {H : ℕ ⊕ ℕ} (hHp : H ∈ S.children p) (hHr : H ∈ S.children r) :
    S.PartnersShareChild :=
  ⟨pr, hpr, H, Finset.mem_inter.2 <| by
    have hc₁ : pr.fst = p ∨ pr.snd = p := hprp
    have hc₂ : pr.fst = r ∨ pr.snd = r := hprr
    rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2
    · exact absurd (h1.symm.trans h2) hrp.symm
    · rw [h1, h2]; exact ⟨hHp, hHr⟩
    · rw [h1, h2]; exact ⟨hHr, hHp⟩
    · exact absurd (h1.symm.trans h2) hrp.symm⟩

private theorem child_ne_of_partner_share_child {n} {S : State n} (hnsh : ¬ S.PartnersShareChild)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p r : ℕ} (hprp : pr.Contains p) (hprr : pr.Contains r)
    (hrp : r ≠ p) {H Hr : ℕ ⊕ ℕ} (hp_ch : S.children p = {H}) (hHr : Hr ∈ S.children r) :
    Hr ≠ H := fun heq => by
  have hHp : H ∈ S.children p := by rw [hp_ch]; exact Finset.mem_singleton_self _
  have hHrp : Hr ∈ S.children p := by rwa [heq]
  exact hnsh (partnersShareChild_of_mem_children hpr hprp hprr hrp hHrp hHr)

/-- Case 4, concretely and without a disperser hypothesis. Let `p` be a paired parameter occurring
in the equation `e` and not read by the output, and `Hr` a child of its partner. Fixing the partner
to its pair bias and deleting `Hr` gives `S₂`, in which `p` is unpaired with children among
`{.inr e}`. If `p` has degree `0` in `S₂`, then `S₂` is a step; otherwise unit-deleting `p` with
any auxiliary variable `Q` affine in parameters containing `p` is a step. -/
theorem Valid.step_pairInSystem_of {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hndeg : ¬ S.DegeneratePair) (hnsh : ¬ S.PartnersShareChild) {pr : ZeroPair}
    (hpr : pr ∈ S.pairs) {p e : ℕ} (hprp : pr.Contains p) (he : e ∈ S.eqns)
    (hpe : p ∈ (S.eqn e).terms) (hout : ¬ S.out.Reads p) {Hr : ℕ ⊕ ℕ}
    (hHr : Hr ∈ S.children (pr.partner p)) :
    let S₂ := (S.fixConst (pr.partner p) (pr.partnerBias p)).deleteConstraint Hr
    S₂.Valid f ∧ p ∈ S₂.unpaired ∧ S₂.children p ⊆ {.inr e} ∧ (S₂.deg p = 0 → Step f S S₂) ∧
      (S₂.deg p ≠ 0 → ∀ Q c T, Q ∈ S₂.aux → S₂.AffineIn Q c T → p ∈ T →
        Step f S ((S₂.swap p Q c T).dropEqn e p)) := by
  intro S₂
  let r := pr.partner p
  have hne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hrp : r ≠ p := pr.partner_ne hne hprp
  have hprr : pr.Contains r := pr.contains_partner hprp
  have hrpar : r ∈ S.params := hS.mem_params_of_contains hpr hprr
  have hppar : p ∈ S.params := hS.mem_params_of_contains hpr hprp
  have hpp : S.Paired p := ⟨pr, hpr, hprp⟩
  have hpr' : S.Paired r := ⟨pr, hpr, hprr⟩
  have hpr_part : S.IsPartner p r := isPartner_of_contains hpr hprp hprr hrp.symm
  have hp_ch : S.children p = {.inr e} :=
    Paired.children_eq_singleton hndeg hpp ((SemiCircuit.inr_mem_children _).2 ⟨he, hpe⟩)
  have hHr_ne : Hr ≠ .inr e := child_ne_of_partner_share_child hnsh hpr hprp hprr hrp hp_ch hHr
  have hb : ∀ pr' ∈ S.pairs, pr'.Contains r → pr.partnerBias p = pr'.bias r :=
    fun pr' hpr' hcr => bias_partner_eq_of_mem hS hpr hprp hpr' hcr
  have hred₁ := Valid.reduction_fixConst hS hrpar hb
  have hdel : (S.fixConst r (pr.partnerBias p)).Deletable Hr :=
    deletable_fixConst_child hS (S.pairsAvoid r) (pr.partnerBias p) hHr
  have hred : Reduction f S S₂ {r} ([] ++ [Hr]) ([] ++ [Hr]) :=
    hred₁.trans_delete (hred₁.valid.reduction_deleteConstraint hdel)
  have hp_mem₂ : p ∈ S₂.params := by
    rw [hred.params]
    exact Finset.mem_sdiff.2 ⟨hppar, by simp [hrp.symm]⟩
  have hp_unp₂ : p ∈ S₂.unpaired := mem_unpaired.2 ⟨hp_mem₂, fun ⟨pr', hpr', hc⟩ => by
    rw [hred.pairs, Finset.mem_filter] at hpr'
    have heq := hS.pair_unique hpr'.1 hpr hc hprp
    rw [heq] at hpr'
    exact hpr'.2 (by
      rcases hprr with h | h
      · exact Or.inl (Finset.mem_singleton.2 h)
      · exact Or.inr (Finset.mem_singleton.2 h))⟩
  have hchp₂ : S₂.children p ⊆ {.inr e} := by
    rcases hred.children p hp_mem₂ with h | ⟨N, hN, hNp⟩
    · exact h.trans (by rw [hp_ch]; exact Finset.sdiff_subset)
    · rw [List.nil_append, List.mem_singleton] at hN
      rw [hN, hp_ch, Finset.mem_singleton] at hNp
      exact absurd hNp hHr_ne
  have hout₂ : ¬ S₂.out.Reads p := fun h => by
    rcases out_reads_of_deleteConstraint hdel h with h | h
    · exact hout (out_reads_of_fixConst h)
    · rw [fixConst_children S _ hrp.symm, hp_ch, Finset.mem_singleton] at h
      exact hHr_ne h
  have hr_part : ∀ u ∈ S.params \ {r}, u ≠ p → ∀ x ∈ ({r} : Finset ℕ), ¬ S.IsPartner x u := by
    rintro u _ hup x hx hxu
    exact hup (hS.isPartner_unique_right
          (by rcases Finset.mem_singleton.1 hx; exact IsPartner.symm hxu) hpr_part)
  have hk : (S.pairsMeeting {r}).card = 1 := by
    rw [hS.card_pairsMeeting_singleton r, ite_eq_left hpr']
  have hW₂ := hred.W_le (fun _ => 0) (fun u => if u = p then S₂.wt p else 0) fun u hu => by
    by_cases hup : u = p
    · subst hup
      simp only [ite_eq_left, add_zero]
      exact Nat.le_add_left _ _
    · simp only [ite_eq_right hup, add_zero]
      exact Reduction.wt_le hred hS (hr_part u hu hup)
  have hsum_gain : ∑ u ∈ S.params \ {r}, (if u = p then S₂.wt p else 0) = S₂.wt p := by
    rw [Finset.sum_eq_single_of_mem p (Finset.mem_sdiff.2 ⟨hppar, by simp [hrp.symm]⟩)
      (fun u _ h => ite_eq_right h), ite_eq_left rfl]
  rw [hk, hsum_gain] at hW₂
  simp only [List.nil_append, List.length_singleton, Finset.sum_const_zero] at hW₂
  refine ⟨hred.valid, hp_unp₂, hchp₂, fun h0 => ?_, fun h0 Q c T hQ haff hpT => ?_⟩
  · have hp_wt₂ : S₂.wt p = 0 := by
      rw [wt_of_mem hp_unp₂, h0, config_weight, weight_zero]
    rw [hp_wt₂] at hW₂
    exact hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) (by
      rw [hk, Finset.card_singleton]; omega)
  · have hcp₂_eq : S₂.children p = {.inr e} := by
      obtain ⟨N, hN⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
      have hNe := Finset.mem_singleton.1 (hchp₂ hN)
      subst hNe
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨hN, fun M hM => Finset.mem_singleton.1 (hchp₂ hM)⟩
    have ha_rel := hred.a_add hS
    rw [hk, Finset.card_singleton] at ha_rel
    obtain ⟨hS₃, hm₃, hs₃, hq₃, ha₃, hW₃⟩ :=
      Valid.unitDelete hred.valid hp_unp₂ hcp₂_eq hout₂ hQ haff hpT
    have hm_rel := hred.m_add
    have hs_rel := hred.s_add
    have hwt_le := S₂.wt_le_bound p
    rw [config_weightBound] at hwt_le
    simp only [Finset.card_singleton, List.nil_append, List.length_singleton] at hm_rel hs_rel
    have ha_eq : ((S₂.swap p Q c T).dropEqn e p).a = S.a := by omega
    exact ⟨hS₃, by omega, by omega, by omega, by rw [ha_eq]; omega⟩

/-- Eliminating a paired parameter in an equation (and unit-deleting if its partner's degree
stays `1`) gives a valid step with `Δa = 0` and `ΔW ≤ 0`. -/
theorem Valid.step_of_pairInSystem {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a)
    (hndeg : ¬ S.DegeneratePair) (hnsh : ¬ S.PartnersShareChild)
    (hsys : S.PairInSystem) : ∃ S', Step f S S' := by
  obtain ⟨p, ⟨pr, hpr, hprp⟩, e, he, hpe⟩ := hsys
  obtain ⟨Hr, hHr⟩ := Finset.card_eq_one.1
    (Paired.deg_eq_one hndeg ⟨pr, hpr, pr.contains_partner hprp⟩)
  have hppar : p ∈ S.params := hS.mem_params_of_contains hpr hprp
  obtain ⟨hS₂, hp₂, hch₂, h0, h1⟩ := Valid.step_pairInSystem_of hS hndeg hnsh hpr hprp he hpe
    (Valid.not_out_reads_param hS hf ha hppar) (by rw [hHr]; exact Finset.mem_singleton_self Hr)
  set S₂ := (S.fixConst (pr.partner p) (pr.partnerBias p)).deleteConstraint Hr
  by_cases hd : S₂.deg p = 0
  · exact ⟨_, h0 hd⟩
  · obtain ⟨N, hN⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hd)
    have hNe := Finset.mem_singleton.1 (hch₂ hN)
    subst hNe
    obtain ⟨he₂, hpe₂⟩ := (SemiCircuit.inr_mem_children _).1 hN
    obtain ⟨Q, hQ, c, T, haff, hpT⟩ :=
      SemiCircuit.exists_affineIn_of_mem_terms hS₂.wf (mem_unpaired.1 hp₂).1 he₂ hpe₂
    exact ⟨_, h1 hd Q c T hQ haff hpT⟩

/-! ### Case 5a: Non-affine gate reading a paired parameter and another parameter -/

/-- A non-affine gate reading a paired parameter `p` and another parameter `w ≠ p` (Case 5a). -/
@[expose] def AndOnPair (S : State n) : Prop :=
  ∃ G ∈ S.gates, ¬ IsAffineOp (S.gate G).op ∧
    ∃ p w, S.Paired p ∧ w ∈ S.params ∧ p ≠ w ∧ (S.gate G).Reads p ∧ (S.gate G).Reads w

private theorem deleteGateConst_and_child {S S₁ : State n} {f : BooleanFunction n}
    {F : Finset ℕ} {G : ℕ} {c : Bool} {Hr : ℕ ⊕ ℕ} {p : ℕ}
    (hred₁ : Reduction f S S₁ F [] [])
    (hG₁ : G ∈ S₁.gates) (hconst : ∀ val, (S₁.gate G).eval val = c)
    (hdel₁ : S₁.Deletable Hr) (hHr_ne : Hr ≠ .inl G) (hcpG : S.children p = {.inl G}) :
    Reduction f S ((S₁.deleteGate G (Lit.const c)).deleteConstraint Hr) F [.inl G, Hr] [Hr] ∧
      ((S₁.deleteGate G (Lit.const c)).deleteConstraint Hr).wt p = 0 := by
  have hred₂ := hred₁.valid.reduction_deleteConst hG₁ fun val _ _ => hconst val
  have hdel₂ : (S₁.deleteGate G (Lit.const c)).Deletable Hr :=
    hred₂.deletable Hr (fun h => hHr_ne (List.mem_singleton.1 h)) hdel₁
  have hred := (hred₁.trans_delete hred₂).trans_delete
    (hred₂.valid.reduction_deleteConstraint hdel₂)
  simp only [List.nil_append] at hred
  refine ⟨hred, hred.wt_eq_zero_of_subset ?_ ?_⟩
  · simp [hcpG]
  · intro N hN hpN
    rw [List.mem_singleton] at hN
    rw [hN, hcpG, Finset.mem_singleton] at hpN
    exact hHr_ne hpN

/-- The successor in Case 5a. A non-affine gate `G` reads the parameter `p` of the pair `pr` and
the parameter `w`, and becomes the constant `c` once `w = b`. Fix the partner of `p` to its
partner bias. If `w` lies in the pair `prw = some q` with `b ≠ q.bias w`, fix the partner of `w`
to its partner bias as well. Then fix `w := b`, delete `G` as the constant `c`, and delete the
constraint `Hr`, the unique child of the partner of `p`. -/
@[expose] def andOnPairStep (S : State n) (G : ℕ) (pr : ZeroPair) (p w : ℕ)
    (prw : Option ZeroPair) (b c : Bool) (Hr : ℕ ⊕ ℕ) : State n :=
  let S₁ := S.fixConst (pr.partner p) (pr.partnerBias p)
  let S₂ := match prw with
    | some q => if b = q.bias w then S₁.fixConst w b
        else (S₁.fixConst (q.partner w) (q.partnerBias w)).fixConst w b
    | none => S₁.fixConst w b
  (S₂.deleteGate G (Lit.const c)).deleteConstraint Hr

/-- Case 5a with an explicit successor: eliminating a non-affine gate `G` reading a paired
parameter `p` and another parameter `w` by `S.andOnPairStep` is a valid step with `ΔW ≤ 10 Δa`.
Here `prw` is the pair of `w`, if any, `G` is the constant `c` once `w = b`, and `Hr` is a child
of the partner of `p`. -/
theorem Valid.step_andOnPair_of {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hndeg : ¬ S.DegeneratePair) (hnsh : ¬ S.PartnersShareChild) {G : ℕ} (hG : G ∈ S.gates)
    {p w : ℕ} {pr : ZeroPair} (hpr : pr ∈ S.pairs)
    (hprp : pr.Contains p) (hwpar : w ∈ S.params) (hpw : p ≠ w) (hGp : (S.gate G).Reads p)
    (hGw : (S.gate G).Reads w) {prw : Option ZeroPair} (hprw_none : prw = none → ¬ S.Paired w)
    (hprw_some : ∀ q, prw = some q → q ∈ S.pairs ∧ q.Contains w) {b c : Bool}
    (hbc : ∀ val : ℕ → Bool, val w = b → (S.gate G).eval val = c) {Hr : ℕ ⊕ ℕ}
    (hHr : Hr ∈ S.children (pr.partner p)) :
    Step f S (S.andOnPairStep G pr p w prw b c Hr) := by
  let r := pr.partner p
  have hne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hrp : r ≠ p := pr.partner_ne hne hprp
  have hprr : pr.Contains r := pr.contains_partner hprp
  have hrpar : r ∈ S.params := hS.mem_params_of_contains hpr hprr
  have hpp : S.Paired p := ⟨pr, hpr, hprp⟩
  have hpr' : S.Paired r := ⟨pr, hpr, hprr⟩
  have hpr_part : S.IsPartner p r := isPartner_of_contains hpr hprp hprr hrp.symm
  have hwr : w ≠ r := fun he => by
    subst he
    apply hnsh
    have hm1 : Sum.inl G ∈ S.children p := (SemiCircuit.inl_mem_children _).2 ⟨hG, hGp⟩
    have hm2 : Sum.inl G ∈ S.children r := (SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩
    exact partnersShareChild_of_mem_children hpr hprp hprr hrp hm1 hm2
  have hcpG : S.children p = {.inl G} :=
    Paired.children_eq_singleton hndeg hpp ((SemiCircuit.inl_mem_children _).2 ⟨hG, hGp⟩)
  have hHr_mem : Hr ∈ S.children r := hHr
  have hHr_ne : Hr ≠ .inl G := child_ne_of_partner_share_child hnsh hpr hprp hprr hrp hcpG hHr_mem
  have hGr_not : ¬ (S.gate G).Reads r := fun hr => by
    rcases Gate.eq_or_eq_of_reads hpw hGp hGw hr with h | h
    · exact hrp h
    · exact hwr.symm h
  have hb_r : ∀ pr' ∈ S.pairs, pr'.Contains r → pr.partnerBias p = pr'.bias r :=
    fun pr' hpr' hcr => bias_partner_eq_of_mem hS hpr hprp hpr' hcr
  have hred_r := Valid.reduction_fixConst hS hrpar hb_r
  let S₁ := S.fixConst r (pr.partnerBias p)
  have hdel_Hr₁ : S₁.Deletable Hr :=
    deletable_fixConst_child hS (S.pairsAvoid r) (pr.partnerBias p) hHr_mem
  have hw_par₁ : w ∈ S₁.params := Finset.mem_erase.2 ⟨hwr, hwpar⟩
  have hS₁G : ∀ val, (S₁.gate G).eval val = (S.gate G).eval val := fun val => by
    rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const])]
    exact Gate.eval_congr fun i hi =>
      Function.update_of_ne (fun h => by subst h; exact hGr_not hi) _ _
  let reduction_fixConst (hb_w : ∀ pr' ∈ S₁.pairs, pr'.Contains w → b = pr'.bias w) :
      Reduction f S (((S₁.fixConst w b).deleteGate G (Lit.const c)).deleteConstraint Hr) {w, r}
        [.inl G, Hr] [Hr] ∧
      (((S₁.fixConst w b).deleteGate G (Lit.const c)).deleteConstraint Hr).wt p = 0 ∧
      ({w, r} : Finset ℕ).card = 2 :=
    have hred_w := Valid.reduction_fixConst hred_r.valid hw_par₁ hb_w
    have hred_fix := hred_r.trans hred_w
    have hred_fix_simp : Reduction f S (S₁.fixConst w b) {w, r} [] [] := by
      simpa only [Finset.union_singleton, List.nil_append] using hred_fix
    have hdel_Hr₂ : (S₁.fixConst w b).Deletable Hr :=
      hred_w.deletable Hr (fun h => by cases h) hdel_Hr₁
    have hconst : ∀ val, ((S₁.fixConst w b).gate G).eval val = c := fun val => by
      rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const]), hS₁G]
      exact hbc _ (by simp [Lit.eval_const])
    have ⟨hred, hp_wt₃⟩ := deleteGateConst_and_child hred_fix_simp hG hconst hdel_Hr₂ hHr_ne hcpG
    ⟨hred, hp_wt₃, Finset.card_pair hwr⟩
  rcases prw with _ | pr_w
  swap
  · obtain ⟨hpr_w, hpr_w_c⟩ := hprw_some pr_w rfl
    dsimp only [andOnPairStep]
    let w' := pr_w.partner w
    have ⟨hww', hpr_w_c', hw'_par⟩ := partner_properties hS hpr_w hpr_w_c
    have hw_part : S.IsPartner w' w := isPartner_of_contains hpr_w hpr_w_c' hpr_w_c hww'
    have hpr_w_ne : pr_w ≠ pr := fun he => by
      rw [he] at hpr_w_c
      rcases hpr_w_c with h | h <;> rcases hprp with h1 | h1 <;> rcases hprr with h2 | h2
      · exact hpw (h1.symm.trans h)
      · exact hpw (h1.symm.trans h)
      · exact hwr (h.symm.trans h2)
      · exact hrp.symm (h1.symm.trans h2)
      · exact hrp (h2.symm.trans h1)
      · exact hwr (h.symm.trans h2)
      · exact hpw (h1.symm.trans h)
      · exact hpw (h1.symm.trans h)
    have hnot_r_prw : ¬ pr_w.Contains r := fun h =>
      hpr_w_ne (hS.pair_unique hpr_w hpr h hprr)
    have hrw' : w' ≠ r := fun he => hnot_r_prw (he ▸ hpr_w_c')
    have hpw' : w' ≠ p := fun he => by
      have hpw_part : S.IsPartner p w := he ▸ hw_part
      exact hwr (hS.isPartner_unique hpw_part hpr_part)
    by_cases hb_eq : b = pr_w.bias w
    · rw [ite_eq_left hb_eq]
      have hb_w : ∀ pr' ∈ S₁.pairs, pr'.Contains w → b = pr'.bias w := fun pr' hpr' hc => by
        rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
        exact hb_eq.trans (bias_eq_of_mem hS hpr_w hpr_w_c hpr'.1 hc)
      obtain ⟨hred, hp_wt₃, hF_card⟩ := reduction_fixConst hb_w
      have hk : (S.pairsMeeting {w, r}).card = 2 := by
        have hp_w : ¬ S.IsPartner w r := fun h => hpw (hS.isPartner_unique_right hpr_part h)
        rw [hS.card_pairsMeeting_insert (by simp [hwr]) (fun y hy => by
          rw [Finset.mem_singleton.1 hy]; exact hp_w),
          hS.card_pairsMeeting_singleton r, ite_eq_left hpr',
          ite_eq_left ⟨pr_w, hpr_w, hpr_w_c⟩]
      refine hred.step hS (by rw [hF_card, hk]; omega) (by simp) ?_
      have hpart_wr : ∀ u ∈ S.params \ {w, r}, u ≠ p → u ≠ w' →
          ∀ x ∈ ({w, r} : Finset ℕ), ¬ S.IsPartner x u := by
        rintro u _ hup huw' x hx hxu
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact huw' (hS.isPartner_unique_right (IsPartner.symm hxu) hw_part)
        · exact hup (hS.isPartner_unique_right (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu)
            hpr_part)
      let gain : ℕ → ℕ := fun u => if u = w' then 6 else 0
      have hW := hred.W_le (fun _ => 0) gain fun u hu => by
        by_cases hup : u = p
        · subst hup
          simp only [gain, ite_eq_right hpw'.symm, hp_wt₃, add_zero]
          exact Nat.zero_le _
        · by_cases huw' : u = w'
          · subst huw'
            simp only [gain, ite_eq_left, add_zero]
            exact (wt_le_bound _ w').trans (Nat.le_add_left _ _)
          · simp only [gain, ite_eq_right huw', add_zero]
            exact Reduction.wt_le hred hS (hpart_wr u hu hup huw')
      have hsum_gain : ∑ u ∈ S.params \ {w, r}, gain u ≤ 6 := by
        by_cases hm : w' ∈ S.params \ {w, r}
        · rw [Finset.sum_eq_single_of_mem w' hm (fun u _ h => ite_eq_right h), ite_eq_left rfl]
        · rw [Finset.sum_eq_zero fun u hu => ite_eq_right (fun h => hm (by subst h; exact hu))]
          omega
      rw [hk] at hW
      rw [hF_card]
      rw [config_ca]
      simp only [List.length_cons, List.length_nil, Finset.sum_const_zero] at hW
      omega
    · rw [ite_eq_right hb_eq]
      have hw'_par₁ : w' ∈ S₁.params := Finset.mem_erase.2 ⟨hrw', hw'_par⟩
      have hb_w' : ∀ pr' ∈ S₁.pairs, pr'.Contains w' → pr_w.partnerBias w = pr'.bias w' :=
        fun pr' hpr' hc => by
          rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
          exact bias_partner_eq_of_mem hS hpr_w hpr_w_c hpr'.1 hc
      have hred_w' := Valid.reduction_fixConst hred_r.valid hw'_par₁ hb_w'
      let S₂ := S₁.fixConst w' (pr_w.partnerBias w)
      have hw_par₂ : w ∈ S₂.params := Finset.mem_erase.2 ⟨hww'.symm, hw_par₁⟩
      have hb_w : ∀ pr' ∈ S₂.pairs, pr'.Contains w → b = pr'.bias w := fun pr' hpr' hcw => by
        rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
        have hpr'1 : pr' ∈ S₁.pairs := hpr'.1
        rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'1
        have heq := hS.pair_unique hpr'1.1 hpr_w hcw hpr_w_c
        rw [heq] at hpr'
        exact absurd hpr_w_c' hpr'.2
      have hred_w := Valid.reduction_fixConst hred_w'.valid hw_par₂ hb_w
      have hred_fix := (hred_r.trans hred_w').trans hred_w
      simp only [List.nil_append, Finset.union_singleton] at hred_fix
      have hdel_Hr₃ : (S₂.fixConst w b).Deletable Hr :=
        hred_w.deletable Hr (fun h => by cases h)
          (hred_w'.deletable Hr (fun h => by cases h) hdel_Hr₁)
      have hGw'_not : ¬ (S.gate G).Reads w' := fun hr => by
        rcases Gate.eq_or_eq_of_reads hpw hGp hGw hr with h | h
        · exact hpw' h
        · exact hww' h
      have hconst : ∀ val, ((S₂.fixConst w b).gate G).eval val = c := fun val => by
        rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const]), Lit.eval_const]
        change ((S₁.fixConst w' (pr_w.partnerBias w)).gate G).eval
          (Function.update val w b) = c
        rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const]), hS₁G]
        rw [Gate.eval_congr fun i hi =>
          Function.update_of_ne (fun h => by subst h; exact hGw'_not hi) _ _]
        exact hbc _ (Function.update_self _ _ _)
      obtain ⟨hred, hp_wt₃⟩ := deleteGateConst_and_child hred_fix hG hconst hdel_Hr₃
        hHr_ne hcpG
      have hF_card : ({w, w', r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (fun h =>
          (Finset.mem_insert.1 h).elim hww'.symm
            (fun h2 => hwr (Finset.mem_singleton.1 h2))),
          Finset.card_pair hrw']
      have hk : (S.pairsMeeting {w, w', r}).card = 2 := by
        have hmeet : S.pairsMeeting {w, w', r} = S.pairsMeeting {w', r} := by
          refine Finset.filter_congr fun pr' hpr' => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ((rfl | h | h) | (rfl | h | h))
            · have heq := hS.pair_unique hpr' hpr_w (Or.inl rfl) hpr_w_c
              rw [heq]
              rcases hpr_w_c' with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · have heq := hS.pair_unique hpr' hpr_w (Or.inr rfl) hpr_w_c
              rw [heq]
              rcases hpr_w_c' with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · tauto
        have hp_w'_r : ¬ S.IsPartner w' r := fun h => hpw' (hS.isPartner_unique_right h hpr_part)
        rw [hmeet, hS.card_pairsMeeting_insert (by simp [hrw']) (fun y hy => by
          rw [Finset.mem_singleton.1 hy]; exact hp_w'_r),
          hS.card_pairsMeeting_singleton r, ite_eq_left hpr',
          ite_eq_left ⟨pr_w, hpr_w, hpr_w_c'⟩]
      refine hred.step hS (by rw [hF_card, hk]; omega) (by simp) ?_
      have hpart_ww'r : ∀ u ∈ S.params \ {w, w', r}, u ≠ p →
          ∀ x ∈ ({w, w', r} : Finset ℕ), ¬ S.IsPartner x u := by
        rintro u hu hup x hx hxu
        have hu_not : u ∉ ({w, w', r} : Finset ℕ) := (Finset.mem_sdiff.1 hu).2
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hu_not (by
            rw [hS.isPartner_unique_right (IsPartner.symm hxu) hw_part]
            simp)
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hu_not (by
              rw [hS.isPartner_unique_right (IsPartner.symm hxu) (IsPartner.symm hw_part)]
              simp)
          · exact hup (hS.isPartner_unique_right (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu)
              hpr_part)
      have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
        simp only [add_zero]
        by_cases hup : u = p
        · subst hup
          rw [hp_wt₃]
          exact Nat.zero_le _
        · exact Reduction.wt_le hred hS (hpart_ww'r u hu hup)
      rw [hk] at hW
      rw [hF_card]
      rw [config_ca]
      simp only [List.length_cons, List.length_nil, Finset.sum_const_zero] at hW
      omega
  · have hwp := hprw_none rfl
    dsimp only [andOnPairStep]
    have hb_w : ∀ pr' ∈ S₁.pairs, pr'.Contains w → b = pr'.bias w := fun pr' hpr' hcw => by
      rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
      exact absurd ⟨pr', hpr'.1, hcw⟩ hwp
    obtain ⟨hred, hp_wt₃, hF_card⟩ := reduction_fixConst hb_w
    have hk : (S.pairsMeeting {w, r}).card = 1 := by
      have hp_w : ¬ S.IsPartner w r := fun h => hpw (hS.isPartner_unique_right hpr_part h)
      rw [hS.card_pairsMeeting_insert (by simp [hwr]) (fun y hy => by
        rw [Finset.mem_singleton.1 hy]; exact hp_w),
        hS.card_pairsMeeting_singleton r, ite_eq_right hwp, ite_eq_left hpr']
    have hw_unp : w ∈ S.unpaired := mem_unpaired.2 ⟨hwpar, hwp⟩
    have hw_deg : 1 ≤ S.deg w := Finset.card_pos.2 ⟨.inl G,
      (SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩⟩
    have hw_wt : S.wt w = 6 := by rw [wt_of_mem hw_unp, config_weight, weight_of_one_le hw_deg]
    have hsum_wt : 6 ≤ ∑ u ∈ ({w, r} : Finset ℕ), S.wt u := by
      rw [Finset.sum_pair hwr, hw_wt]
      omega
    refine hred.step hS (by rw [hF_card, hk]; omega) (by simp) ?_
    have hpart_wr : ∀ u ∈ S.params \ {w, r}, u ≠ p →
        ∀ x ∈ ({w, r} : Finset ℕ), ¬ S.IsPartner x u := by
      rintro u _ hup x hx hxu
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hwp (IsPartner.paired hxu)
      · exact hup (hS.isPartner_unique_right (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu)
          hpr_part)
    have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
      simp only [add_zero]
      by_cases hup : u = p
      · subst hup; rw [hp_wt₃]; exact Nat.zero_le _
      · exact Reduction.wt_le hred hS (hpart_wr u hu hup)
    rw [hk] at hW
    rw [hF_card]
    rw [config_ca]
    simp only [List.length_cons, List.length_nil, Finset.sum_const_zero] at hW
    omega

/-- Eliminating a non-affine gate reading a paired parameter `p` and another parameter `w` gives a
valid step with `ΔW ≤ 10 Δa`. -/
theorem Valid.step_of_andOnPair {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hndeg : ¬ S.DegeneratePair) (hnsh : ¬ S.PartnersShareChild) (hand : S.AndOnPair) :
    ∃ S', Step f S S' := by
  obtain ⟨G, hG, hnotaff, p, w, ⟨pr, hpr, hprp⟩, hwpar, hpw, hGp, hGw⟩ := hand
  obtain ⟨b, c, hbc⟩ := Gate.exists_const_of_not_isAffineOp hnotaff
    (Gate.args_of_reads hpw hGp hGw)
  obtain ⟨Hr, hHr⟩ := Finset.card_eq_one.1
    (Paired.deg_eq_one hndeg ⟨pr, hpr, pr.contains_partner hprp⟩)
  have hHr_mem : Hr ∈ S.children (pr.partner p) := by rw [hHr]; exact Finset.mem_singleton_self _
  by_cases hwp : S.Paired w
  · obtain ⟨q, hq, hqw⟩ := hwp
    exact ⟨_, Valid.step_andOnPair_of hS hndeg hnsh hG hpr hprp hwpar hpw hGp hGw
      (prw := some q) (fun h => nomatch h) (fun _ h => Option.some_injective _ h ▸ ⟨hq, hqw⟩)
      hbc hHr_mem⟩
  · exact ⟨_, Valid.step_andOnPair_of hS hndeg hnsh hG hpr hprp hwpar hpw hGp hGw
      (prw := none) (fun _ => hwp) (fun _ h => nomatch h) hbc hHr_mem⟩

/-! ### Normal form -/

/-- A normal state has no movable affine gate and satisfies none of Cases 1–5a. -/
structure Normal (S : State n) : Prop where
  not_movable : ¬ S.Movable
  no_deletion : ¬ S.DeletionAvailable
  no_deg_pair : ¬ S.DegeneratePair
  no_shared_child : ¬ S.PartnersShareChild
  no_pair_system : ¬ S.PairInSystem
  no_and_pair : ¬ S.AndOnPair

/-- Every parameter occurring in an affine equation of a normal state is unpaired with degree at
least `2`. -/
theorem Normal.unpaired_of_mem_terms {S : State n} (hN : S.Normal) {e x : ℕ} (he : e ∈ S.eqns)
    (hx : x ∈ (S.eqn e).terms) (hxpar : x ∈ S.params) :
    x ∈ S.unpaired ∧ 2 ≤ S.deg x := by
  have hxu : ¬ S.Paired x := fun hp => hN.no_pair_system ⟨x, hp, e, he, hx⟩
  have hxunp : x ∈ S.unpaired := mem_unpaired.2 ⟨hxpar, hxu⟩
  refine ⟨hxunp, ?_⟩
  by_contra hlt
  push Not at hlt
  have hec : Sum.inr e ∈ S.children x := (SemiCircuit.inr_mem_children _).2 ⟨he, hx⟩
  exact hN.no_deletion (Or.inr (Or.inr (Or.inr ⟨x, hxunp, e,
    children_eq_singleton (by omega) hec⟩)))

/-- Any parameter read by a non-affine gate of a normal state is unpaired with degree at least
`1`. -/
theorem Normal.unpaired_of_and_reads {S : State n} (hN : S.Normal) {G p w : ℕ}
    (hG : G ∈ S.gates) (hnotaff : ¬ IsAffineOp (S.gate G).op)
    (hpw : p ≠ w) (hp_par : p ∈ S.params) (hw_par : w ∈ S.params)
    (hGp : (S.gate G).Reads p) (hGw : (S.gate G).Reads w) :
    p ∈ S.unpaired ∧ 1 ≤ S.deg p := by
  have hpu : ¬ S.Paired p := fun hp =>
    hN.no_and_pair ⟨G, hG, hnotaff, p, w, hp, hw_par, hpw, hGp, hGw⟩
  exact ⟨mem_unpaired.2 ⟨hp_par, hpu⟩, Finset.card_pos.2
    ⟨.inl G, (SemiCircuit.inl_mem_children _).2 ⟨hG, hGp⟩⟩⟩

/-- In a normal state, every gate reads two distinct inputs. -/
theorem Normal.two_reads_of_gate {S : State n} (hN : S.Normal) {G : ℕ} (hG : G ∈ S.gates) :
    ∃ a b, a ≠ b ∧ (S.gate G).Reads a ∧ (S.gate G).Reads b := by
  have hndeg : ¬ (S.gate G).Degenerate := fun hd =>
    hN.no_deletion (Or.inl ⟨G, hG, (S.gate G).lit,
      (fun t ht => Gate.reads_of_lit_reads ht), fun val _ _ => Gate.eval_lit hd val⟩)
  unfold Gate.Degenerate at hndeg
  push Not at hndeg
  obtain ⟨hl, hr, hne⟩ := hndeg
  cases hgl : (S.gate G).left with
  | const c => exact absurd hgl (hl c)
  | node a =>
    cases hgr : (S.gate G).right with
    | const c => exact absurd hgr (hr c)
    | node b =>
      refine ⟨a, b, ?_, Or.inl hgl, Or.inr hgr⟩
      intro he
      apply hne
      rw [hgl, hgr, he]

/-- Either Cases 1–5a yield a valid step strictly reducing `m + s` with `ΔW ≤ 10 Δa`, or `S` is in
normal form. -/
theorem Valid.step_or_normal {S : State n} {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hnmov : ¬ S.Movable) :
    (∃ S', Step f S S') ∨ S.Normal := by
  by_cases hdel : S.DeletionAvailable
  · exact Or.inl (Valid.step_of_deletion hS hf ha hdel)
  by_cases hdeg : S.DegeneratePair
  · exact Or.inl (Valid.step_of_degeneratePair hS hdeg)
  by_cases hsh : S.PartnersShareChild
  · exact Or.inl (Valid.step_of_partnersShareChild hS hdel hdeg hsh)
  by_cases hsys : S.PairInSystem
  · exact Or.inl (Valid.step_of_pairInSystem hS hf ha hdeg hsh hsys)
  by_cases hand : S.AndOnPair
  · exact Or.inl (Valid.step_of_andOnPair hS hdeg hsh hand)
  exact Or.inr ⟨hnmov, hdel, hdeg, hsh, hsys, hand⟩

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
