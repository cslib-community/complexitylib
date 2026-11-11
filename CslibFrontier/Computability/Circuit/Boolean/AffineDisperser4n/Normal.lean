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

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ}

/-! ### Helper lemmas on pairs -/

private theorem isPartner_of_contains {S : State n} {pr : ZeroPair} (hpr : pr ∈ S.pairs)
    {p r : ℕ} (hp : pr.Contains p) (hr : pr.Contains r) (hne : p ≠ r) : S.IsPartner p r := by
  rcases hp with h1 | h1 <;> rcases hr with h2 | h2
  · exact absurd (h1.symm.trans h2) hne
  · exact ⟨pr, hpr, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨pr, hpr, Or.inr ⟨h1, h2⟩⟩
  · exact absurd (h1.symm.trans h2) hne

private theorem mem_params_of_contains {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p : ℕ} (hp : pr.Contains p) : p ∈ S.params := by
  rcases hp with h | h <;> rw [← h]
  exacts [(hS.pair_mem pr hpr).1, (hS.pair_mem pr hpr).2.1]

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

private theorem isPartner_unique_right {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    {u p r : ℕ} (hup : S.IsPartner u r) (hpr : S.IsPartner p r) : u = p :=
  hS.isPartner_unique (IsPartner.symm hup) (IsPartner.symm hpr)

private theorem children_eq_singleton {S : State n} {x : ℕ} {H : ℕ ⊕ ℕ}
    (hH : H ∈ S.children x) (hle : S.deg x ≤ 1) : S.children x = {H} := by
  have hpos : 0 < (S.children x).card := Finset.card_pos.2 ⟨H, hH⟩
  have hcard : (S.children x).card = 1 := by unfold deg at hle; omega
  obtain ⟨M, hM⟩ := Finset.card_eq_one.1 hcard
  have h1 := Finset.mem_singleton.1 (hM ▸ hH)
  rwa [← h1] at hM

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
def DegeneratePair (S : State n) : Prop :=
  ∃ p, S.Paired p ∧ (S.deg p = 0 ∨ 2 ≤ S.deg p)

private theorem Paired.deg_eq_one {S : State n} (hndeg : ¬ S.DegeneratePair) {p : ℕ}
    (hp : S.Paired p) : S.deg p = 1 := by
  have h0 : S.deg p ≠ 0 := fun h => hndeg ⟨p, hp, Or.inl h⟩
  have h2 : ¬ 2 ≤ S.deg p := fun h => hndeg ⟨p, hp, Or.inr h⟩
  omega

private theorem Paired.children_eq_singleton {S : State n} (hndeg : ¬ S.DegeneratePair)
    {p : ℕ} (hp : S.Paired p) {H : ℕ ⊕ ℕ} (hH : H ∈ S.children p) : S.children p = {H} :=
  State.children_eq_singleton hH (by rw [hp.deg_eq_one hndeg])

/-- Eliminating a degenerate paired parameter gives a valid step with `Δa = 0` and `ΔW ≤ 0`. -/
theorem Valid.step_of_degeneratePair {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hdeg : S.DegeneratePair) : ∃ S', Step f S S' := by
  obtain ⟨p, ⟨pr, hpr, hprp⟩, hpdeg⟩ := hdeg
  let r := pr.partner p
  have hne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hrp : r ≠ p := pr.partner_ne hne hprp
  have hprr : pr.Contains r := pr.contains_partner hprp
  have hrpar : r ∈ S.params := mem_params_of_contains hS hpr hprr
  have hppar : p ∈ S.params := mem_params_of_contains hS hpr hprp
  have hpr_part : S.IsPartner p r := isPartner_of_contains hpr hprp hprr hrp.symm
  have hprr_pair : S.Paired r := ⟨pr, hpr, hprr⟩
  rcases hpdeg with hp0 | hp2
  · have hb : ∀ pr' ∈ S.pairs, pr'.Contains r → pr.partnerBias p = pr'.bias r :=
      fun pr' hpr' hcr => bias_partner_eq_of_mem hS hpr hprp hpr' hcr
    have hred := hS.reduction_fixConst hrpar hb
    have hk : (S.pairsMeeting {r}).card = 1 := by
      rw [hS.card_pairsMeeting_singleton r, ite_eq_left hprr_pair]
    refine ⟨_, hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) ?_⟩
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
          rw [hdeg0, weight_zero]
          exact Nat.zero_le _
        · rw [wt_of_notMem hu_mem]
          exact Nat.zero_le _
      · exact hred.wt_le hS fun x hx hxu =>
          hup (isPartner_unique_right hS (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu) hpr_part)
    rw [hk] at hW ⊢
    simp only [Finset.card_singleton, List.length_nil, Finset.sum_const_zero] at hW ⊢
    omega
  · have h1lt : 1 < (S.children p).card := by
      have : 1 < S.deg p := by omega
      exact this
    obtain ⟨N₁, hN₁, N₂, hN₂, hN₁₂⟩ := Finset.one_lt_card.1 h1lt
    have hb : ∀ pr' ∈ S.pairs, pr'.Contains p → pr.bias p = pr'.bias p :=
      fun pr' hpr' hcp => bias_eq_of_mem hS hpr hprp hpr' hcp
    have hred₁ := hS.reduction_fixConst hppar hb
    have hdel₁ : (S.fixConst p (pr.bias p)).Deletable N₁ :=
      deletable_fixConst_child hS (S.pairsAvoid p) (pr.bias p) hN₁
    have hdel₂ : (S.fixConst p (pr.bias p)).Deletable N₂ :=
      deletable_fixConst_child hS (S.pairsAvoid p) (pr.bias p) hN₂
    have hnodup : [N₁, N₂].Nodup := List.nodup_cons.2 ⟨by simp [hN₁₂], List.nodup_singleton _⟩
    obtain ⟨S₂, hred₂⟩ := hred₁.valid.exists_reduction_deleteAll [N₁, N₂] hnodup fun N hN => by
      rcases List.mem_cons.1 hN with rfl | hN
      · exact hdel₁
      · rw [List.mem_singleton.1 hN]; exact hdel₂
    have hred := hred₁.trans_delete hred₂
    have hk : (S.pairsMeeting {p}).card = 1 := by
      rw [hS.card_pairsMeeting_singleton p, ite_eq_left ⟨pr, hpr, hprp⟩]
    refine ⟨S₂, hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) ?_⟩
    let gain : ℕ → ℕ := fun u => if S.IsPartner p u then 6 else 0
    have hW := hred.W_le (fun _ => 0) gain fun u _ => by
      by_cases hup : S.IsPartner p u
      · simp only [gain, ite_eq_left hup, add_zero]
        exact (S₂.wt_le_six u).trans (Nat.le_add_left _ _)
      · simp only [gain, ite_eq_right hup, add_zero]
        exact hred.wt_le hS fun x hx hxu => hup (Finset.mem_singleton.1 hx ▸ hxu)
    have hgain : ∑ u ∈ S.params \ {p}, gain u ≤ 6 := hS.sum_partner_le p (S.params \ {p}) 6
    rw [hk] at hW ⊢
    simp only [Finset.card_singleton, List.nil_append, List.length_cons,
      List.length_nil, Finset.sum_const_zero] at hW ⊢
    omega

/-! ### Case 3: Partners sharing a child -/

/-- Two paired partners share a child (Case 3). -/
def PartnersShareChild (S : State n) : Prop :=
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
    (hred : Reduction f S S₂ {p} L T) (hr_wt : S₂.wt r = 0) :
    ∃ S', Step f S S' := by
  have hpp : S.Paired p := ⟨pr, hpr, hcp⟩
  have hpr_part : S.IsPartner r p := isPartner_of_contains hpr hcr hcp hpr_ne.symm
  have hk : (S.pairsMeeting {p}).card = 1 := by
    rw [hS.card_pairsMeeting_singleton p, ite_eq_left hpp]
  refine ⟨S₂, hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) ?_⟩
  have hr_part : ∀ u ∈ S.params \ {p}, u ≠ r → ∀ x ∈ ({p} : Finset ℕ), ¬ S.IsPartner x u := by
    rintro u _ hur x hx hxu
    exact hur (isPartner_unique_right hS (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu) hpr_part)
  have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
    simp only [add_zero]
    by_cases hur : u = r
    · subst hur; rw [hr_wt]; exact Nat.zero_le _
    · exact hred.wt_le hS (hr_part u hu hur)
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
  refine hS.reduction_restrict hp_par hℓ_reads fun pr₁ hpr₁ hc val => ?_
  have heq := hS.pair_unique hpr₁ hpr hc (Or.inl rfl)
  rw [heq, ZeroPair.holds_iff_and_eq_false, Function.update_self,
    Function.update_of_ne hpr_ne.symm]
  dsimp only [Lit.eval, Arg.eval_node]
  generalize val pr.snd = b; generalize pr.fstBias = α; generalize pr.sndBias = β
  cases α <;> cases β <;> cases b <;> decide

private theorem step_of_partnersShareChild_fix {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) {pr : ZeroPair} (hpr : pr ∈ S.pairs) {p r G : ℕ} {c : Bool}
    (hcp : pr.Contains p) (hcr : pr.Contains r) (hpr_ne : p ≠ r)
    (hG : G ∈ S.gates) (hcrG : S.children r = {.inl G})
    (hconst : ∀ val, ((S.gate G).subst p (Lit.const (pr.bias p))).eval val = c) :
    ∃ S', Step f S S' := by
  have hp_par : p ∈ S.params := mem_params_of_contains hS hpr hcp
  have hb : ∀ pr' ∈ S.pairs, pr'.Contains p → pr.bias p = pr'.bias p :=
    fun pr' hpr' hc => bias_eq_of_mem hS hpr hcp hpr' hc
  have hred₁ := hS.reduction_fixConst hp_par hb
  have hred₂ := hred₁.valid.reduction_deleteConst hG fun val _ _ => hconst val
  have hred := hred₁.trans_delete hred₂
  refine step_of_partnersShareChild_finish hS hpr hcp hcr hpr_ne (by simp) hred ?_
  exact hred.wt_eq_zero_of_subset (by simp [hcrG]) (fun _ h => by cases h)

/-- Eliminating a shared child of paired partners gives a valid step with `Δa = 0` and
`ΔW ≤ -5`. -/
theorem Valid.step_of_partnersShareChild {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) (hndel : ¬ S.DeletionAvailable) (hndeg : ¬ S.DegeneratePair)
    (hsh : S.PartnersShareChild) : ∃ S', Step f S S' := by
  obtain ⟨pr, hpr, H, hH⟩ := hsh
  obtain ⟨hHp, hHr⟩ := Finset.mem_inter.1 hH
  let p := pr.fst
  let r := pr.snd
  have hp_par : p ∈ S.params := (hS.pair_mem pr hpr).1
  have hr_par : r ∈ S.params := (hS.pair_mem pr hpr).2.1
  have hpr_ne : p ≠ r := (hS.pair_mem pr hpr).2.2
  have hpp : S.Paired p := ⟨pr, hpr, Or.inl rfl⟩
  have hpr' : S.Paired r := ⟨pr, hpr, Or.inr rfl⟩
  have hcpH : S.children p = {H} := hpp.children_eq_singleton hndeg hHp
  have hcrH : S.children r = {H} := hpr'.children_eq_singleton hndeg hHr
  rcases H with G | e
  · obtain ⟨hG, hGp⟩ := (SemiCircuit.inl_mem_children _).1 hHp
    obtain ⟨_, hGr⟩ := (SemiCircuit.inl_mem_children _).1 hHr
    obtain ⟨φ, _, hφ⟩ := Gate.exists_op_of_args (Gate.args_of_reads hpr_ne hGp hGr)
    rcases bool_triangle_pair φ pr.fstBias pr.sndBias with h1 | h2 | h3
    · refine step_of_partnersShareChild_fix hS hpr (Or.inl rfl) (Or.inr rfl) hpr_ne
        hG hcrH (c := φ pr.fstBias pr.sndBias) fun val => ?_
      rw [Gate.eval_subst_update (by simp [Lit.const]), hφ]
      have hf : Function.update val p ((Lit.const (pr.bias p)).eval val) p = pr.fstBias := by
        rw [Function.update_self, Lit.eval_const]
        simp [p, ZeroPair.bias]
      rw [hf]
      exact h1 _
    · refine step_of_partnersShareChild_fix hS hpr (Or.inr rfl) (Or.inl rfl) hpr_ne.symm
        hG hcpH (c := φ pr.fstBias pr.sndBias) fun val => ?_
      rw [Gate.eval_subst_update (by simp [Lit.const]), hφ]
      have hf : Function.update val r ((Lit.const (pr.bias r)).eval val) r = pr.sndBias := by
        rw [Function.update_self, Lit.eval_const]
        dsimp only [r]
        simp [ZeroPair.bias, (hS.pair_mem pr hpr).2.2]
      rw [hf, Function.update_of_ne hpr_ne]
      exact h2 _
    · let γ : Bool := !(pr.fstBias ^^ pr.sndBias)
      let ℓ : Lit := ⟨.node r, γ⟩
      have hℓ_eval : ∀ val : ℕ → Bool, ℓ.eval val = (val r ^^ γ) := fun _ => rfl
      have hred₁ := partnersShareChild_reduction_restrict hS hpr hp_par hr_par hpr_ne
        (by rw [hcpH, hcrH])
      have hconst : ∀ val, ((S.restrict p ℓ (S.pairsAvoid p)).gate G).eval val =
          φ pr.fstBias (!pr.sndBias) := fun val => by
        rw [restrict_gate, Gate.eval_subst_update (by simp [ℓ, hpr_ne.symm]), hφ,
          Function.update_self, Function.update_of_ne hpr_ne.symm, hℓ_eval]
        exact h3 (val r)
      have hred₂ := hred₁.valid.reduction_deleteConst hG fun val _ _ => hconst val
      have hred := hred₁.trans_delete hred₂
      refine step_of_partnersShareChild_finish hS hpr (Or.inl rfl) (Or.inr rfl) hpr_ne
        rfl hred ?_
      exact hred.wt_eq_zero_of_subset
        (fun x hx => by change x ∈ S.children r at hx; rw [hcrH] at hx; simpa using hx)
        (fun _ h => by cases h)
  · obtain ⟨he, hep⟩ := (SemiCircuit.inr_mem_children _).1 hHp
    obtain ⟨_, her⟩ := (SemiCircuit.inr_mem_children _).1 hHr
    let γ : Bool := !(pr.fstBias ^^ pr.sndBias)
    let ℓ : Lit := ⟨.node r, γ⟩
    have hred₁ := partnersShareChild_reduction_restrict hS hpr hp_par hr_par hpr_ne
      (by rw [hcpH, hcrH])
    let S₁ := S.restrict p ℓ (S.pairsAvoid p)
    have hterms : (S₁.eqn e).terms = ((S.eqn e).terms.erase p).erase r := by
      change ((S.eqn e).subst p ℓ).terms = _
      have hsub : (S.eqn e).subst p ℓ =
          { terms := symmDiff ((S.eqn e).terms.erase p) {r}, rhs := (S.eqn e).rhs ^^ γ } := by
        unfold Equation.subst
        exact ite_eq_left hep
      rw [hsub]
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
      by_cases hir : i = r
      · simp [hir, hpr_ne.symm, r, her]
      · simp [hir]
    have hcard_e : 2 < (S.eqn e).terms.card := by
      by_contra hle
      push Not at hle
      exact hndel (Or.inr (Or.inr (Or.inl ⟨e, he, hle⟩)))
    have hdel : S₁.Deletable (.inr e) := by
      refine ⟨he, ?_⟩
      rw [hterms, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hpr_ne.symm, her⟩),
        Finset.card_erase_of_mem hep]
      have h3 := hS.wf.card_terms_le e he
      omega
    have hcr1 : S₁.children r = ∅ := by
      ext (K | e')
      · simp only [Finset.notMem_empty, iff_false]
        intro hK
        obtain ⟨hKm, hKr⟩ := (SemiCircuit.inl_mem_children _).1 hK
        rcases Gate.reads_of_reads_subst hKr with h | ⟨h, _⟩
        · have : Sum.inl K ∈ S.children r := (SemiCircuit.inl_mem_children _).2 ⟨hKm, h⟩
          rw [hcrH, Finset.mem_singleton] at this
          cases this
        · have : Sum.inl K ∈ S.children p := (SemiCircuit.inl_mem_children _).2 ⟨hKm, h⟩
          rw [hcpH, Finset.mem_singleton] at this
          cases this
      · simp only [Finset.notMem_empty, iff_false]
        intro he'
        obtain ⟨he'm, he'r⟩ := (SemiCircuit.inr_mem_children _).1 he'
        by_cases hee : e' = e
        · subst hee
          rw [hterms] at he'r
          exact Finset.notMem_erase r _ he'r
        · have hp_not : p ∉ (S.eqn e').terms := fun hm => by
            have : Sum.inr e' ∈ S.children p := (SemiCircuit.inr_mem_children _).2 ⟨he'm, hm⟩
            rw [hcpH, Finset.mem_singleton, Sum.inr.injEq] at this
            exact hee this
          have hsub : ((S.eqn e').subst p ℓ) = S.eqn e' := by simp [Equation.subst, hp_not]
          change r ∈ ((S.eqn e').subst p ℓ).terms at he'r
          rw [hsub] at he'r
          have : Sum.inr e' ∈ S.children r := (SemiCircuit.inr_mem_children _).2 ⟨he'm, he'r⟩
          rw [hcrH, Finset.mem_singleton, Sum.inr.injEq] at this
          exact hee this
    obtain ⟨S₂, hred₂⟩ := hred₁.valid.exists_reduction_delete hdel
    have hr_wt₁ : S₁.wt r = 0 := by
      by_cases hru : r ∈ S₁.unpaired
      · rw [wt_of_mem hru, deg, hcr1, Finset.card_empty, weight_zero]
      · exact wt_of_notMem hru
    have hr_wt₂ : S₂.wt r = 0 := by
      have := hred₂.wt_le (u := r) hred₁.valid fun x hx _ => absurd hx (Finset.notMem_empty _)
      rw [show (S.restrict pr.fst ⟨.node pr.snd, !(pr.fstBias ^^ pr.sndBias)⟩
        (S.pairsAvoid pr.fst)) = S₁ from rfl] at this
      omega
    have hred := hred₁.trans_delete hred₂
    exact step_of_partnersShareChild_finish hS hpr (Or.inl rfl) (Or.inr rfl) hpr_ne
      rfl hred hr_wt₂

/-! ### Case 4: Paired parameter in an affine equation -/

/-- A paired parameter occurring in an affine equation (Case 4). -/
def PairInSystem (S : State n) : Prop :=
  ∃ p, S.Paired p ∧ ∃ e ∈ S.eqns, p ∈ (S.eqn e).terms

/-- Eliminating a paired parameter in an equation (and unit-deleting if its partner's degree
stays `1`) gives a valid step with `Δa = 0` and `ΔW ≤ 0`. -/
theorem Valid.step_of_pairInSystem {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a)
    (hndeg : ¬ S.DegeneratePair) (hnsh : ¬ S.PartnersShareChild)
    (hsys : S.PairInSystem) : ∃ S', Step f S S' := by
  obtain ⟨p, ⟨pr, hpr, hprp⟩, e, he, hpe⟩ := hsys
  let r := pr.partner p
  have hne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hrp : r ≠ p := pr.partner_ne hne hprp
  have hprr : pr.Contains r := pr.contains_partner hprp
  have hrpar : r ∈ S.params := mem_params_of_contains hS hpr hprr
  have hppar : p ∈ S.params := mem_params_of_contains hS hpr hprp
  have hpp : S.Paired p := ⟨pr, hpr, hprp⟩
  have hpr' : S.Paired r := ⟨pr, hpr, hprr⟩
  have hpr_part : S.IsPartner p r := isPartner_of_contains hpr hprp hprr hrp.symm
  have hp_ch : S.children p = {.inr e} :=
    hpp.children_eq_singleton hndeg ((SemiCircuit.inr_mem_children _).2 ⟨he, hpe⟩)
  have hdegr : S.deg r = 1 := hpr'.deg_eq_one hndeg
  obtain ⟨Hr, hHr⟩ := Finset.card_eq_one.1 hdegr
  have hHr_mem : Hr ∈ S.children r := by rw [hHr]; exact Finset.mem_singleton_self _
  have hHr_ne : Hr ≠ .inr e := fun heq => by
    apply hnsh
    refine ⟨pr, hpr, Hr, Finset.mem_inter.2 ?_⟩
    have hm1 : Hr ∈ S.children p := by rw [hp_ch, heq]; exact Finset.mem_singleton_self _
    rcases hprp with h1 | h1 <;> rcases hprr with h2 | h2
    · exact absurd (h1.symm.trans h2) hrp.symm
    · rw [h1, h2]; exact ⟨hm1, hHr_mem⟩
    · rw [h1, h2]; exact ⟨hHr_mem, hm1⟩
    · exact absurd (h1.symm.trans h2) hrp.symm
  have hb : ∀ pr' ∈ S.pairs, pr'.Contains r → pr.partnerBias p = pr'.bias r :=
    fun pr' hpr' hcr => bias_partner_eq_of_mem hS hpr hprp hpr' hcr
  have hred₁ := hS.reduction_fixConst hrpar hb
  have hdel : (S.fixConst r (pr.partnerBias p)).Deletable Hr :=
    deletable_fixConst_child hS (S.pairsAvoid r) (pr.partnerBias p) hHr_mem
  obtain ⟨S₂, hred₂⟩ := hred₁.valid.exists_reduction_delete hdel
  have hred := hred₁.trans_delete hred₂
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
  have hr_part : ∀ u ∈ S.params \ {r}, u ≠ p → ∀ x ∈ ({r} : Finset ℕ), ¬ S.IsPartner x u := by
    rintro u _ hup x hx hxu
    exact hup (isPartner_unique_right hS (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu) hpr_part)
  have hk : (S.pairsMeeting {r}).card = 1 := by
    rw [hS.card_pairsMeeting_singleton r, ite_eq_left hpr']
  have hW₂ := hred.W_le (fun _ => 0) (fun u => if u = p then S₂.wt p else 0) fun u hu => by
    by_cases hup : u = p
    · subst hup
      simp only [ite_eq_left, add_zero]
      exact Nat.le_add_left _ _
    · simp only [ite_eq_right hup, add_zero]
      exact hred.wt_le hS (hr_part u hu hup)
  have hsum_gain : ∑ u ∈ S.params \ {r}, (if u = p then S₂.wt p else 0) = S₂.wt p := by
    rw [Finset.sum_eq_single_of_mem p (Finset.mem_sdiff.2 ⟨hppar, by simp [hrp.symm]⟩)
      (fun u _ h => ite_eq_right h), ite_eq_left rfl]
  rw [hk, hsum_gain] at hW₂
  simp only [List.nil_append, List.length_singleton, Finset.sum_const_zero] at hW₂
  by_cases hce : S₂.children p = ∅
  · have hp_wt₂ : S₂.wt p = 0 := by rw [wt_of_mem hp_unp₂, deg, hce, Finset.card_empty, weight_zero]
    rw [hp_wt₂] at hW₂
    exact ⟨S₂, hred.step hS (by rw [Finset.card_singleton, hk]; omega) (by simp) (by
      rw [hk, Finset.card_singleton]; omega)⟩
  · have hcp₂_eq : S₂.children p = {.inr e} := by
      obtain ⟨N, hN⟩ := Finset.nonempty_iff_ne_empty.2 hce
      have hNe := Finset.mem_singleton.1 (hchp₂ hN)
      subst hNe
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨hN, fun M hM => Finset.mem_singleton.1 (hchp₂ hM)⟩
    have ha_rel := hred.a_add hS
    rw [hk, Finset.card_singleton] at ha_rel
    have ha₂ : d < S₂.a := by omega
    obtain ⟨S₃, hS₃, hm₃, hs₃, hq₃, ha₃, hW₃⟩ :=
      hred.valid.exists_unit_delete hf ha₂ hp_unp₂ hcp₂_eq
    have hm_rel := hred.m_add
    have hs_rel := hred.s_add
    have hwt_le := S₂.wt_le_six p
    simp only [Finset.card_singleton, List.nil_append, List.length_singleton] at hm_rel hs_rel
    exact ⟨S₃, ⟨hS₃, by omega, by omega, by omega, by omega⟩⟩

/-! ### Case 5a: Non-affine gate reading a paired parameter and another parameter -/

/-- A non-affine gate reading a paired parameter `p` and another parameter `w ≠ p` (Case 5a). -/
def AndOnPair (S : State n) : Prop :=
  ∃ G ∈ S.gates, ¬ IsAffineOp (S.gate G).op ∧
    ∃ p w, S.Paired p ∧ w ∈ S.params ∧ p ≠ w ∧ (S.gate G).Reads p ∧ (S.gate G).Reads w

private theorem deleteGateConst_and_child {S S₁ : State n} {f : BooleanFunction n}
    {F : Finset ℕ} {G : ℕ} {c : Bool} {Hr : ℕ ⊕ ℕ} {p : ℕ}
    (hred₁ : Reduction f S S₁ F [] [])
    (hG₁ : G ∈ S₁.gates) (hconst : ∀ val, (S₁.gate G).eval val = c)
    (hdel₁ : S₁.Deletable Hr) (hHr_ne : Hr ≠ .inl G) (hcpG : S.children p = {.inl G}) :
    ∃ S₃, Reduction f S S₃ F [.inl G, Hr] [Hr] ∧ S₃.wt p = 0 := by
  have hred₂ := hred₁.valid.reduction_deleteConst hG₁ fun val _ _ => hconst val
  have hdel₂ : (S₁.deleteGate G (Lit.const c)).Deletable Hr :=
    hred₂.deletable Hr (fun h => hHr_ne (List.mem_singleton.1 h)) hdel₁
  obtain ⟨S₃, hred₃⟩ := hred₂.valid.exists_reduction_delete hdel₂
  have hred := (hred₁.trans_delete hred₂).trans_delete hred₃
  simp only [List.nil_append] at hred
  refine ⟨S₃, hred, hred.wt_eq_zero_of_subset ?_ ?_⟩
  · simp [hcpG]
  · intro N hN hpN
    rw [List.mem_singleton] at hN
    rw [hN, hcpG, Finset.mem_singleton] at hpN
    exact hHr_ne hpN

/-- Eliminating a non-affine gate reading a paired parameter `p` and another parameter `w` gives a
valid step with `ΔW ≤ 10 Δa`. -/
theorem Valid.step_of_andOnPair {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hndeg : ¬ S.DegeneratePair) (hnsh : ¬ S.PartnersShareChild) (hand : S.AndOnPair) :
    ∃ S', Step f S S' := by
  obtain ⟨G, hG, hnotaff, p, w, ⟨pr, hpr, hprp⟩, hwpar, hpw, hGp, hGw⟩ := hand
  let r := pr.partner p
  have hne : pr.fst ≠ pr.snd := (hS.pair_mem pr hpr).2.2
  have hrp : r ≠ p := pr.partner_ne hne hprp
  have hprr : pr.Contains r := pr.contains_partner hprp
  have hrpar : r ∈ S.params := mem_params_of_contains hS hpr hprr
  have hpp : S.Paired p := ⟨pr, hpr, hprp⟩
  have hpr' : S.Paired r := ⟨pr, hpr, hprr⟩
  have hpr_part : S.IsPartner p r := isPartner_of_contains hpr hprp hprr hrp.symm
  have hwr : w ≠ r := fun he => by
    subst he
    apply hnsh
    refine ⟨pr, hpr, .inl G, Finset.mem_inter.2 ?_⟩
    have hm1 : Sum.inl G ∈ S.children p := (SemiCircuit.inl_mem_children _).2 ⟨hG, hGp⟩
    have hm2 : Sum.inl G ∈ S.children r := (SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩
    rcases hprp with h1 | h1 <;> rcases hprr with h2 | h2
    · exact absurd (h1.symm.trans h2) hrp.symm
    · rw [h1, h2]; exact ⟨hm1, hm2⟩
    · rw [h1, h2]; exact ⟨hm2, hm1⟩
    · exact absurd (h1.symm.trans h2) hrp.symm
  have hcpG : S.children p = {.inl G} :=
    hpp.children_eq_singleton hndeg ((SemiCircuit.inl_mem_children _).2 ⟨hG, hGp⟩)
  have hdegr : S.deg r = 1 := hpr'.deg_eq_one hndeg
  obtain ⟨Hr, hHr⟩ := Finset.card_eq_one.1 hdegr
  have hHr_mem : Hr ∈ S.children r := by rw [hHr]; exact Finset.mem_singleton_self _
  have hHr_ne : Hr ≠ .inl G := fun heq => by
    apply hnsh
    refine ⟨pr, hpr, Hr, Finset.mem_inter.2 ?_⟩
    have hm1 : Hr ∈ S.children p := by rw [hcpG, heq]; exact Finset.mem_singleton_self _
    rcases hprp with h1 | h1 <;> rcases hprr with h2 | h2
    · exact absurd (h1.symm.trans h2) hrp.symm
    · rw [h1, h2]; exact ⟨hm1, hHr_mem⟩
    · rw [h1, h2]; exact ⟨hHr_mem, hm1⟩
    · exact absurd (h1.symm.trans h2) hrp.symm
  obtain ⟨b, c, hbc⟩ := Gate.exists_const_of_not_isAffineOp hnotaff
    (Gate.args_of_reads hpw hGp hGw)
  have hGr_not : ¬ (S.gate G).Reads r := fun hr => by
    rcases Gate.eq_or_eq_of_reads hpw hGp hGw hr with h | h
    · exact hrp h
    · exact hwr.symm h
  have hb_r : ∀ pr' ∈ S.pairs, pr'.Contains r → pr.partnerBias p = pr'.bias r :=
    fun pr' hpr' hcr => bias_partner_eq_of_mem hS hpr hprp hpr' hcr
  have hred_r := hS.reduction_fixConst hrpar hb_r
  let S₁ := S.fixConst r (pr.partnerBias p)
  have hdel_Hr₁ : S₁.Deletable Hr :=
    deletable_fixConst_child hS (S.pairsAvoid r) (pr.partnerBias p) hHr_mem
  have hw_par₁ : w ∈ S₁.params := Finset.mem_erase.2 ⟨hwr, hwpar⟩
  have hS₁G : ∀ val, (S₁.gate G).eval val = (S.gate G).eval val := fun val => by
    rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const])]
    exact Gate.eval_congr fun i hi =>
      Function.update_of_ne (fun h => by subst h; exact hGr_not hi) _ _
  by_cases hwp : S.Paired w
  · obtain ⟨pr_w, hpr_w, hpr_w_c⟩ := hwp
    let w' := pr_w.partner w
    have hne_w : pr_w.fst ≠ pr_w.snd := (hS.pair_mem pr_w hpr_w).2.2
    have hww' : w' ≠ w := pr_w.partner_ne hne_w hpr_w_c
    have hpr_w_c' : pr_w.Contains w' := pr_w.contains_partner hpr_w_c
    have hw'_par : w' ∈ S.params := mem_params_of_contains hS hpr_w hpr_w_c'
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
    · have hb_w : ∀ pr' ∈ S₁.pairs, pr'.Contains w → b = pr'.bias w := fun pr' hpr' hc => by
        rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
        exact hb_eq.trans (bias_eq_of_mem hS hpr_w hpr_w_c hpr'.1 hc)
      have hred_w := hred_r.valid.reduction_fixConst hw_par₁ hb_w
      have hred_fix := hred_r.trans hred_w
      simp only [Finset.union_singleton, List.nil_append] at hred_fix
      have hdel_Hr₂ : (S₁.fixConst w b).Deletable Hr :=
        hred_w.deletable Hr (fun h => by cases h) hdel_Hr₁
      have hconst : ∀ val, ((S₁.fixConst w b).gate G).eval val = c := fun val => by
        rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const]), hS₁G]
        exact hbc _ (by simp [Lit.eval_const])
      obtain ⟨S₃, hred, hp_wt₃⟩ := deleteGateConst_and_child hred_fix hG hconst hdel_Hr₂
        hHr_ne hcpG
      have hF_card : ({w, r} : Finset ℕ).card = 2 := Finset.card_pair hwr
      have hk : (S.pairsMeeting {w, r}).card = 2 := by
        have hp_w : ¬ S.IsPartner w r := fun h => hpw (isPartner_unique_right hS hpr_part h)
        rw [hS.card_pairsMeeting_insert (by simp [hwr]) (fun y hy => by
          rw [Finset.mem_singleton.1 hy]; exact hp_w),
          hS.card_pairsMeeting_singleton r, ite_eq_left hpr',
          ite_eq_left ⟨pr_w, hpr_w, hpr_w_c⟩]
      refine ⟨S₃, hred.step hS (by rw [hF_card, hk]; omega) (by simp) ?_⟩
      have hpart_wr : ∀ u ∈ S.params \ {w, r}, u ≠ p → u ≠ w' →
          ∀ x ∈ ({w, r} : Finset ℕ), ¬ S.IsPartner x u := by
        rintro u _ hup huw' x hx hxu
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact huw' (isPartner_unique_right hS (IsPartner.symm hxu) hw_part)
        · exact hup (isPartner_unique_right hS (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu)
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
            exact (S₃.wt_le_six w').trans (Nat.le_add_left _ _)
          · simp only [gain, ite_eq_right huw', add_zero]
            exact hred.wt_le hS (hpart_wr u hu hup huw')
      have hsum_gain : ∑ u ∈ S.params \ {w, r}, gain u ≤ 6 := by
        by_cases hm : w' ∈ S.params \ {w, r}
        · rw [Finset.sum_eq_single_of_mem w' hm (fun u _ h => ite_eq_right h), ite_eq_left rfl]
        · rw [Finset.sum_eq_zero fun u hu => ite_eq_right (fun h => hm (by subst h; exact hu))]
          omega
      rw [hk] at hW
      rw [hF_card]
      simp only [List.length_cons, List.length_nil, Finset.sum_const_zero] at hW
      omega
    · have hw'_par₁ : w' ∈ S₁.params := Finset.mem_erase.2 ⟨hrw', hw'_par⟩
      have hb_w' : ∀ pr' ∈ S₁.pairs, pr'.Contains w' → pr_w.partnerBias w = pr'.bias w' :=
        fun pr' hpr' hc => by
          rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
          exact bias_partner_eq_of_mem hS hpr_w hpr_w_c hpr'.1 hc
      have hred_w' := hred_r.valid.reduction_fixConst hw'_par₁ hb_w'
      let S₂ := S₁.fixConst w' (pr_w.partnerBias w)
      have hw_par₂ : w ∈ S₂.params := Finset.mem_erase.2 ⟨hww'.symm, hw_par₁⟩
      have hb_w : ∀ pr' ∈ S₂.pairs, pr'.Contains w → b = pr'.bias w := fun pr' hpr' hcw => by
        rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
        have hpr'1 : pr' ∈ S₁.pairs := hpr'.1
        rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'1
        have heq := hS.pair_unique hpr'1.1 hpr_w hcw hpr_w_c
        rw [heq] at hpr'
        exact absurd hpr_w_c' hpr'.2
      have hred_w := hred_w'.valid.reduction_fixConst hw_par₂ hb_w
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
      obtain ⟨S₃, hred, hp_wt₃⟩ := deleteGateConst_and_child hred_fix hG hconst hdel_Hr₃
        hHr_ne hcpG
      have hF_card : ({w, w', r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hww'.symm, hwr]), Finset.card_pair hrw']
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
        have hp_w'_r : ¬ S.IsPartner w' r := fun h => hpw' (isPartner_unique_right hS h hpr_part)
        rw [hmeet, hS.card_pairsMeeting_insert (by simp [hrw']) (fun y hy => by
          rw [Finset.mem_singleton.1 hy]; exact hp_w'_r),
          hS.card_pairsMeeting_singleton r, ite_eq_left hpr',
          ite_eq_left ⟨pr_w, hpr_w, hpr_w_c'⟩]
      refine ⟨S₃, hred.step hS (by rw [hF_card, hk]; omega) (by simp) ?_⟩
      have hpart_ww'r : ∀ u ∈ S.params \ {w, w', r}, u ≠ p →
          ∀ x ∈ ({w, w', r} : Finset ℕ), ¬ S.IsPartner x u := by
        rintro u hu hup x hx hxu
        have hu_not : u ∉ ({w, w', r} : Finset ℕ) := (Finset.mem_sdiff.1 hu).2
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hu_not (by
            rw [isPartner_unique_right hS (IsPartner.symm hxu) hw_part]
            simp)
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hu_not (by
              rw [isPartner_unique_right hS (IsPartner.symm hxu) (IsPartner.symm hw_part)]
              simp)
          · exact hup (isPartner_unique_right hS (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu)
              hpr_part)
      have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
        simp only [add_zero]
        by_cases hup : u = p
        · subst hup
          rw [hp_wt₃]
          exact Nat.zero_le _
        · exact hred.wt_le hS (hpart_ww'r u hu hup)
      rw [hk] at hW
      rw [hF_card]
      simp only [List.length_cons, List.length_nil, Finset.sum_const_zero] at hW
      omega
  · have hb_w : ∀ pr' ∈ S₁.pairs, pr'.Contains w → b = pr'.bias w := fun pr' hpr' hcw => by
      rw [fixConst_pairs, pairsAvoid, Finset.mem_filter] at hpr'
      exact absurd ⟨pr', hpr'.1, hcw⟩ hwp
    have hred_w := hred_r.valid.reduction_fixConst hw_par₁ hb_w
    have hred_fix := hred_r.trans hred_w
    simp only [Finset.union_singleton, List.nil_append] at hred_fix
    have hdel_Hr₂ : (S₁.fixConst w b).Deletable Hr :=
      hred_w.deletable Hr (fun h => by cases h) hdel_Hr₁
    have hconst : ∀ val, ((S₁.fixConst w b).gate G).eval val = c := fun val => by
      rw [fixConst_gate, Gate.eval_subst_update (by simp [Lit.const]), hS₁G]
      exact hbc _ (by simp [Lit.eval_const])
    obtain ⟨S₃, hred, hp_wt₃⟩ := deleteGateConst_and_child hred_fix hG hconst hdel_Hr₂
      hHr_ne hcpG
    have hF_card : ({w, r} : Finset ℕ).card = 2 := Finset.card_pair hwr
    have hk : (S.pairsMeeting {w, r}).card = 1 := by
      have hp_w : ¬ S.IsPartner w r := fun h => hpw (isPartner_unique_right hS hpr_part h)
      rw [hS.card_pairsMeeting_insert (by simp [hwr]) (fun y hy => by
        rw [Finset.mem_singleton.1 hy]; exact hp_w),
        hS.card_pairsMeeting_singleton r, ite_eq_right hwp, ite_eq_left hpr']
    have hw_unp : w ∈ S.unpaired := mem_unpaired.2 ⟨hwpar, hwp⟩
    have hw_deg : 1 ≤ S.deg w := Finset.card_pos.2 ⟨.inl G,
      (SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩⟩
    have hw_wt : S.wt w = 6 := by rw [wt_of_mem hw_unp, weight_of_one_le hw_deg]
    have hsum_wt : 6 ≤ ∑ u ∈ ({w, r} : Finset ℕ), S.wt u := by
      rw [Finset.sum_pair hwr, hw_wt]
      omega
    refine ⟨S₃, hred.step hS (by rw [hF_card, hk]; omega) (by simp) ?_⟩
    have hpart_wr : ∀ u ∈ S.params \ {w, r}, u ≠ p →
        ∀ x ∈ ({w, r} : Finset ℕ), ¬ S.IsPartner x u := by
      rintro u _ hup x hx hxu
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hwp (IsPartner.paired hxu)
      · exact hup (isPartner_unique_right hS (Finset.mem_singleton.1 hx ▸ IsPartner.symm hxu)
          hpr_part)
    have hW := hred.W_le (fun _ => 0) (fun _ => 0) fun u hu => by
      simp only [add_zero]
      by_cases hup : u = p
      · subst hup; rw [hp_wt₃]; exact Nat.zero_le _
      · exact hred.wt_le hS (hpart_wr u hu hup)
    rw [hk] at hW
    rw [hF_card]
    simp only [List.length_cons, List.length_nil, Finset.sum_const_zero] at hW
    omega

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
    children_eq_singleton hec (by omega)⟩)))

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
  · exact Or.inl (hS.step_of_deletion hf ha hdel)
  by_cases hdeg : S.DegeneratePair
  · exact Or.inl (hS.step_of_degeneratePair hdeg)
  by_cases hsh : S.PartnersShareChild
  · exact Or.inl (hS.step_of_partnersShareChild hdel hdeg hsh)
  by_cases hsys : S.PairInSystem
  · exact Or.inl (hS.step_of_pairInSystem hf ha hdeg hsh hsys)
  by_cases hand : S.AndOnPair
  · exact Or.inl (hS.step_of_andOnPair hdeg hsh hand)
  exact Or.inr ⟨hnmov, hdel, hdeg, hsh, hsys, hand⟩

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
