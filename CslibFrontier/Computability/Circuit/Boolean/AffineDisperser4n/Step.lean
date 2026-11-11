/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Normal

/-!
# Case 5b and Lemma 4.2 (`State.Valid.exists_step`) for `4n - 10d` gate elimination

In a normal state `S` with `d < S.a`, `S.gates` is nonempty (`State.Valid.exists_gate_of_normal`),
and its minimal gate `G` reads no other gates (`State.exists_minGate`) and is non-affine.

* While `G` reads an auxiliary variable `Q ∈ S.aux` (`0 < S.auxIn G`), we find a parameter
  `y` in `Q`'s affine representation distinct from the other input of `G`, perform `(AR)`
  `S.swap y Q c T` (`State.Valid.preparation_swap_auxIn`), which is a preparatory operation keeping
  `gates` unchanged and strictly decreasing `auxIn G`.
* Once `G` reads two distinct unpaired parameters `t₁, t₂ ∈ S.unpaired`, `S.out` cannot read `G`,
  so some gate `K ≠ G` reads `G`. Pair creation `(PC)` (`State.addPair ⟨t₁, α, t₂, β⟩`) makes `G`
  constant `γ` on `Z(P')` and turns `t₁, t₂` from weight `6` into paired (`Δq = +1`, `ΔW = -8`).
  Deleting `G` and then `K` yields `Δm = 0, Δs = -2, Δa = -1, ΔW ≤ -10 = 10 Δa`
  (`State.Valid.step_of_pairCreation`).

Combining with Cases 1–5a gives Lemma 4.2 (`State.Valid.exists_step`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.auxArg`: indicator that an argument is
  auxiliary.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.auxIn`: number of auxiliary arguments of a gate.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_gate_of_normal`: a normal state
  with `d < S.a` has at least one gate.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.preparation_swap_auxIn`: swapping an
  auxiliary input of the minimal gate preserves validity with `ΔW ≤ 0` and lowers `auxIn`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.step_of_pairCreation`: Case 5b `(PC)`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.exists_step`: Lemma 4.2, every valid
  state with `d < S.a` admits a step reducing `m + s` with `Δa ∈ {0, -1, -2}` and `ΔW ≤ 10 Δa`.

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

/-! ### Minimal gate and auxiliary inputs -/

/-- Indicator (`0` or `1`) of whether a gate argument is an auxiliary variable of `S`. -/
@[expose] def auxArg (S : State n) : Arg → ℕ
  | .const _ => 0
  | .node x => if x ∈ S.aux then 1 else 0

/-- The number of arguments of gate `G` that belong to `S.aux` (`0`, `1`, or `2`). -/
@[expose] def auxIn (S : State n) (G : ℕ) : ℕ :=
  S.auxArg (S.gate G).left + S.auxArg (S.gate G).right

/-- In a normal state with `d < S.a`, `S.gates` is nonempty. -/
theorem Valid.exists_gate_of_normal {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a) (_hN : S.Normal) :
    S.gates.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  cases hout : S.out.arg with
  | const b =>
    refine hS.out_not_affine hf ha (b ^^ S.out.neg) (Finset.empty_subset _) fun val _ _ => ?_
    simp [Lit.eval, hout, Arg.eval_const]
  | node i =>
    have hilive := hS.wf.out_live i hout
    simp only [SemiCircuit.live, hne, Finset.union_empty, Finset.mem_union] at hilive
    rcases hilive with hi | hi
    · exact hS.not_out_reads_param hf ha hi hout
    · obtain ⟨c, T, haff⟩ := hS.wf.exists_affineIn hi
      refine hS.out_not_affine hf ha (c ^^ S.out.neg) haff.1 fun val hcons _ => ?_
      simp only [Lit.eval, hout, Arg.eval_node, haff.2 val hcons.1]
      generalize ∑ j ∈ T, val j = s
      cases c <;> cases S.out.neg <;> cases s <;> rfl

/-- The minimum gate identifier in `S.gates` reads no gates. -/
theorem Valid.minGate_reads {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hne : S.gates.Nonempty) :
    let G := S.gates.min' hne
    G ∈ S.gates ∧ ∀ i, (S.gate G).Reads i → i ∉ S.gates := by
  refine ⟨Finset.min'_mem S.gates hne, fun i hread hi => ?_⟩
  have hlt := hS.wf.reads_lt _ (Finset.min'_mem S.gates hne) i hi hread
  have hle := Finset.min'_le S.gates i hi
  omega

/-- If a gate of a normal state reads distinct inputs `a ≠ b` with `a ∈ S.aux`, then `a`'s
affine representation contains some unpaired parameter `y ≠ b` of degree at least `2`. -/
private theorem exists_param_for_swap_of_aux_input {S : State n} {f : BooleanFunction n}
    (hS : S.Valid f) (hN : S.Normal) {G a b : ℕ} (hG : G ∈ S.gates) (hab : a ≠ b)
    (hGa : (S.gate G).Reads a) (hGb : (S.gate G).Reads b) (ha : a ∈ S.aux) :
    ∃ y c T, S.AffineIn a c T ∧ y ∈ T ∧ y ≠ b ∧ y ∈ S.unpaired ∧ 2 ≤ S.deg y := by
  obtain ⟨c, T, haff⟩ := hS.wf.exists_affineIn ha
  by_cases hne : (T.erase b).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hyb : y ≠ b := Finset.ne_of_mem_erase hy
    have hyT : y ∈ T := Finset.mem_of_mem_erase hy
    obtain ⟨e, he, hye⟩ :=
      haff.mem_terms hS.wf (fun hp => hS.wf.notMem_aux_of_mem_params hp ha) hyT
    obtain ⟨hyunp, hdeg⟩ := hN.unpaired_of_mem_terms he hye (haff.1 hyT)
    exact ⟨y, c, T, haff, hyT, hyb, hyunp, hdeg⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exfalso
    by_cases hTe : T = ∅
    · let g' := (S.gate G).subst a (Lit.const c)
      have hg'deg : g'.Degenerate := by
        unfold Gate.Degenerate
        rcases hGa with h | h
        · exact Or.inl ⟨c, by simp [g', Gate.subst, h, Arg.substArg, Lit.const]⟩
        · exact Or.inr (Or.inl ⟨c, by simp [g', Gate.subst, h, Arg.substArg, Lit.const]⟩)
      refine hN.no_deletion (Or.inl ⟨G, hG, g'.lit, fun t ht => ?_, fun val hval _ => ?_⟩)
      · have hg'r := Gate.reads_of_lit_reads ht
        rcases Gate.reads_of_reads_subst hg'r with hr | ⟨_, harg⟩
        · exact hr
        · simp [Lit.const] at harg
      · have hvac : val a = (Lit.const c).eval val := by
          have := haff.2 val hval
          rw [hTe, Finset.sum_empty] at this
          cases c <;> simp [Lit.eval_const, this]
        rw [← Gate.eval_subst hvac]
        exact Gate.eval_lit hg'deg val
    · have hbT : b ∈ T := by
        obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hTe
        by_contra hb
        exact (Finset.eq_empty_iff_forall_notMem.1 hne) y (Finset.mem_erase.2
          ⟨fun heq => hb (heq ▸ hy), hy⟩)
      let ℓ_sub : Lit := ⟨.node b, c⟩
      let g' := (S.gate G).subst a ℓ_sub
      have hT_eq : T = {b} := by
        ext u
        simp only [Finset.mem_singleton]
        constructor
        · intro hu
          by_contra hub
          exact (Finset.eq_empty_iff_forall_notMem.1 hne) u (Finset.mem_erase.2 ⟨hub, hu⟩)
        · rintro rfl; exact hbT
      have hg'deg : g'.Degenerate := by
        unfold Gate.Degenerate
        refine Or.inr (Or.inr ?_)
        rcases Gate.args_of_reads hab hGa hGb with ⟨hl, hr⟩ | ⟨hl, hr⟩
        · dsimp only [g', Gate.subst]
          rw [hl, hr]
          simp [Arg.substArg, ℓ_sub, hab.symm]
        · dsimp only [g', Gate.subst]
          rw [hl, hr]
          simp [Arg.substArg, ℓ_sub, hab.symm]
      refine hN.no_deletion (Or.inl ⟨G, hG, g'.lit, fun t ht => ?_, fun val hval _ => ?_⟩)
      · have hg'r := Gate.reads_of_lit_reads ht
        rcases Gate.reads_of_reads_subst hg'r with hr | ⟨_, harg⟩
        · exact hr
        · have htb : t = b := by
            simp only [ℓ_sub, Arg.node.injEq] at harg
            exact harg.symm
          exact htb ▸ hGb
      · have hvac : val a = ℓ_sub.eval val := by
          have := haff.2 val hval
          rw [hT_eq, Finset.sum_singleton] at this
          rw [this]
          simp only [ℓ_sub, Lit.eval, Arg.eval_node]
          exact Bool.xor_comm _ _
        rw [← Gate.eval_subst hvac]
        exact Gate.eval_lit hg'deg val

/-- Swapping an auxiliary input of the minimal gate with a suitable parameter preserves validity,
keeps `gates` and potential non-increasing, and strictly lowers `auxIn G`. -/
theorem Valid.preparation_swap_auxIn {S : State n} {f : BooleanFunction n} (hS : S.Valid f)
    (hN : S.Normal) (hne : S.gates.Nonempty) (hpos : 0 < S.auxIn (S.gates.min' hne)) :
    ∃ S' : State n, Preparation f S S' ∧ S'.gates = S.gates ∧
      S'.auxIn (S.gates.min' hne) < S.auxIn (S.gates.min' hne) := by
  let G := S.gates.min' hne
  have hG : G ∈ S.gates := Finset.min'_mem S.gates hne
  obtain ⟨u, v, huv, hGu, hGv⟩ := hN.two_reads_of_gate hG
  have haux_or : u ∈ S.aux ∨ v ∈ S.aux := by
    by_contra hno
    push Not at hno
    dsimp only [auxIn] at hpos
    rcases Gate.args_of_reads huv hGu hGv with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [hl, hr] at hpos
      simp [auxArg, hno.1, hno.2] at hpos
    · rw [hl, hr] at hpos
      simp [auxArg, hno.1, hno.2] at hpos
  have ⟨a, b, hab, hGa, hGb, ha_aux⟩ :
      ∃ a b, a ≠ b ∧ (S.gate G).Reads a ∧ (S.gate G).Reads b ∧ a ∈ S.aux := by
    rcases haux_or with hu | hv
    · exact ⟨u, v, huv, hGu, hGv, hu⟩
    · exact ⟨v, u, huv.symm, hGv, hGu, hv⟩
  obtain ⟨y, c, T, haff, hyT, hyb, hyunp, hydeg⟩ :=
    exists_param_for_swap_of_aux_input hS hN hG hab hGa hGb ha_aux
  have hypar : y ∈ S.params := (mem_unpaired.1 hyunp).1
  have hyunp' : ¬ S.Paired y := (mem_unpaired.1 hyunp).2
  have hswap : S.SwapOK y a c T := ⟨hypar, hyunp', ha_aux, haff, hyT⟩
  let S' := S.swap y a c T
  have hS' : S'.Valid f := hS.swap hswap
  have hy_ne_a : y ≠ a := fun h => hS.wf.notMem_aux_of_mem_params hypar (h ▸ ha_aux)
  have hm' : S'.m = S.m := hS.swap_m hswap
  have hs' : S'.s = S.s := swap_size S y a c T
  have hq' : S'.q = S.q := rfl
  have hW' : S'.W ≤ S.W := hS.swap_W_le hswap (by omega)
  have hgates : S'.gates = S.gates := rfl
  have hgateG : S'.gate G = S.gate G := rfl
  have haux_mem_S' : ∀ z, z ∈ S'.aux ↔ z = y ∨ (z ∈ S.aux ∧ z ≠ a) := fun z => by
    change z ∈ insert y (S.aux.erase a) ↔ _
    rw [Finset.mem_insert, Finset.mem_erase, and_comm]
  have hne_y_read : ∀ z, (S.gate G).Reads z → z ≠ y := fun z hz hzy => by
    subst hzy
    rcases Gate.eq_or_eq_of_reads hab hGa hGb hz with h | h
    · exact hy_ne_a h
    · exact hyb h
  have hauxArg_le : ∀ arg, (∀ z, arg = .node z → z ≠ y) →
      S'.auxArg arg ≤ S.auxArg arg := fun arg harg => by
    cases arg with
    | const _ => simp [auxArg]
    | node z =>
      simp only [auxArg]
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        rcases (haux_mem_S' z).1 h1 with rfl | ⟨hza, _⟩
        · exact harg _ rfl rfl
        · exact h2 hza
      · exact Nat.zero_le _
      · exact le_rfl
  have ha_not_S' : a ∉ S'.aux := by
    rw [haux_mem_S']
    rintro (rfl | ⟨_, h⟩)
    · exact hy_ne_a rfl
    · exact h rfl
  have hlt_a : S'.auxArg (.node a) < S.auxArg (.node a) := by
    simp [auxArg, ha_aux, ha_not_S']
  have hle_left : S'.auxArg (S'.gate G).left ≤ S.auxArg (S.gate G).left := by
    rw [hgateG]
    exact hauxArg_le _ fun z hz => hne_y_read z (Or.inl hz)
  have hle_right : S'.auxArg (S'.gate G).right ≤ S.auxArg (S.gate G).right := by
    rw [hgateG]
    exact hauxArg_le _ fun z hz => hne_y_read z (Or.inr hz)
  have hauxIn_lt : S'.auxIn G < S.auxIn G := by
    unfold auxIn
    rcases hGa with hla | hra
    · have hlt_l : S'.auxArg (S'.gate G).left < S.auxArg (S.gate G).left := by
        rw [hgateG, hla]
        exact hlt_a
      omega
    · have hlt_r : S'.auxArg (S'.gate G).right < S.auxArg (S.gate G).right := by
        rw [hgateG, hra]
        exact hlt_a
      omega
  exact ⟨S', ⟨hS', hm', hs', hq', hW'⟩, hgates, hauxIn_lt⟩

/-! ### Case 5b: Pair creation (PC) on the minimal gate -/

/-- When the minimal gate `G` is non-affine and reads two distinct parameters `t₁, t₂`, pair
creation `(PC)` plus deleting `G` and a gate reading `G` gives a valid step with `Δm = 0`,
`Δs = -2`, `Δa = -1`, and `ΔW ≤ -10`. -/
theorem Valid.step_of_pairCreation {S : State n} {f : BooleanFunction n} {d : ℕ}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal)
    {G t₁ t₂ : ℕ} (hG : G ∈ S.gates) (hnotaff : ¬ IsAffineOp (S.gate G).op)
    (htne : t₁ ≠ t₂) (hGt₁ : (S.gate G).Reads t₁) (hGt₂ : (S.gate G).Reads t₂)
    (ht₁par : t₁ ∈ S.params) (ht₂par : t₂ ∈ S.params) :
    ∃ S', Step f S S' := by
  obtain ⟨ht₁unp, ht₁deg⟩ := hN.unpaired_of_and_reads hG hnotaff htne ht₁par ht₂par hGt₁ hGt₂
  obtain ⟨ht₂unp, ht₂deg⟩ := hN.unpaired_of_and_reads hG hnotaff htne.symm ht₂par ht₁par hGt₂ hGt₁
  obtain ⟨α, β, γ, hG_eval⟩ : ∃ α β γ, ∀ val,
      (S.gate G).eval val = (((val t₁ ^^ α) && (val t₂ ^^ β)) ^^ γ) := by
    obtain ⟨α, β, γ, hop⟩ := exists_and_form hnotaff
    rcases Gate.args_of_reads htne hGt₁ hGt₂ with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · refine ⟨α, β, γ, fun val => ?_⟩
      rw [Gate.eval_of_args hl hr, hop]
    · refine ⟨β, α, γ, fun val => ?_⟩
      rw [Gate.eval_of_args hl hr, hop, Bool.and_comm]
  have houtG : ¬ S.out.Reads G := by
    intro hread
    refine hS.false_of_fix hf ha ht₁par α ∅ (Finset.empty_subset _) (Finset.notMem_empty _)
      (γ ^^ S.out.neg) fun val hcons _ hfix => ?_
    have hread' : S.out.arg = .node G := hread
    have hv1 : val t₁ = α := by simpa using hfix
    have hGe : (S.gate G).eval val = γ := by
      rw [hG_eval, hv1, Bool.xor_self, Bool.false_and, Bool.false_xor]
    have hout_g : S.out.eval val = ((S.gate G).eval val ^^ S.out.neg) := by
      simp only [Lit.eval, hread', Arg.eval_node]
      exact congrArg (· ^^ S.out.neg) (hcons.2 G hG)
    rw [hout_g, hGe]
  obtain ⟨K, hK, hKr⟩ : ∃ K ∈ S.gates, (S.gate K).Reads G := by
    by_contra hno
    push Not at hno
    exact hN.no_deletion (Or.inr (Or.inl ⟨G, hG, hno, houtG⟩))
  have hKG : K ≠ G := fun he => hS.not_reads_self hK (he ▸ hKr)
  let pr : ZeroPair := ⟨t₁, α, t₂, β⟩
  have hpc : S.AddPairOK pr := ⟨ht₁unp, ht₂unp, htne⟩
  let S₁ := S.addPair pr
  have hS₁ : S₁.Valid f := hS.addPair hpc
  have hW₁ : S₁.W + 8 = S.W := hS.addPair_W_eq hpc ht₁deg ht₂deg
  have hconstG : ∀ val, S₁.EqnsHold val → S₁.InZeroLocus val → (S₁.gate G).eval val = γ :=
    fun val _ hlocus => by
      have hholds := (ZeroPair.holds_iff_and_eq_false pr val).1
        (hlocus pr (Finset.mem_insert_self _ _))
      change (S.gate G).eval val = γ
      rw [hG_eval]
      simp only [pr] at hholds
      rw [hholds, Bool.false_xor]
  have hG₁ : G ∈ S₁.gates := hG
  have hred₂ := hS₁.reduction_deleteConst hG₁ hconstG
  let S₂ := S₁.deleteGate G (Lit.const γ)
  have hW₂ : S₂.W + 1 ≤ S₁.W := by
    have h := hred₂.W_le (fun _ => 0) (fun _ => 0) fun u _ => by
      simp only [add_zero]
      exact hred₂.wt_le hS₁ fun _ hx => absurd hx (Finset.notMem_empty _)
    have hp0 : S₁.pairsMeeting ∅ = ∅ := by ext; simp [pairsMeeting]
    rw [hp0] at h
    dsimp only [S₂] at *
    simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.length_singleton,
      mul_zero, add_zero] at h
    omega
  have hdelK : S₂.Deletable (.inl K) := deletable_deleteGate_child γ hK hKG hKr
  obtain ⟨S₃, hred₃⟩ := hred₂.valid.exists_reduction_delete hdelK
  have hW₃ : S₃.W + 1 ≤ S₂.W := by
    have h := hred₃.W_le (fun _ => 0) (fun _ => 0) fun u _ => by
      simp only [add_zero]
      exact hred₃.wt_le hred₂.valid fun _ hx => absurd hx (Finset.notMem_empty _)
    have hp0 : S₂.pairsMeeting ∅ = ∅ := by ext; simp [pairsMeeting]
    rw [hp0] at h
    simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.length_singleton,
      mul_zero, add_zero] at h
    omega
  have hm₃ : S₃.m = S.m := by
    have := hred₃.m_add
    have := hred₂.m_add
    have hm1 : S₁.m = S.m := by simp [m, S₁, addPair_params]
    simp only [Finset.card_empty, add_zero] at *
    omega
  have hs₃ : S₃.s + 2 = S.s := by
    have h3 := hred₃.s_add
    have h2 := hred₂.s_add
    have hs1 : S₁.s = S.s := addPair_size S pr
    simp only [List.length_singleton] at h2 h3
    omega
  have hq₃ : S₃.q = S.q + 1 := by
    have h3 := hred₃.q_add
    have h2 := hred₂.q_add
    have hq1 : S₁.q = S.q + 1 := addPair_q hpc
    have hp1 : S₁.pairsMeeting ∅ = ∅ := by ext; simp [pairsMeeting]
    have hp2 : S₂.pairsMeeting ∅ = ∅ := by ext; simp [pairsMeeting]
    rw [hp2, Finset.card_empty, add_zero] at h3
    rw [hp1, Finset.card_empty, add_zero] at h2
    omega
  have ha₃ : S₃.a + 1 = S.a := by
    have hq_le := hS.q_le_m
    have hq3_le := hred₃.valid.q_le_m
    unfold a at *
    omega
  refine ⟨S₃, ⟨hred₃.valid, by omega, by omega, by omega, by omega⟩⟩

/-! ### Lemma 4.2: Every valid state with `d < S.a` admits a step -/

private theorem Valid.exists_step_aux {f : BooleanFunction n} {d : ℕ} (hf : IsAffineDisperser f d) :
    ∀ (k₁ k₂ : ℕ) {S : State n}, S.Valid f → d < S.a → S.gates.card ≤ k₁ →
      (∀ hne : S.gates.Nonempty, S.auxIn (S.gates.min' hne) ≤ k₂) →
      ∃ S', Step f S S' := by
  intro k₁
  induction k₁ using Nat.strong_induction_on with
  | ind k₁ ih₁ =>
    intro k₂
    induction k₂ using Nat.strong_induction_on with
    | ind k₂ ih₂ =>
      intro S hS ha hk₁ hk₂
      by_cases hmov : S.Movable
      · obtain ⟨J, hJ, haff, hin⟩ := hmov
        obtain ⟨hprep, hlt⟩ := hS.preparation_moveAffine hJ haff hin
        let S₁ := S.moveAffine J S.freshEqn
        have ha₁ : d < S₁.a := by rw [hprep.a_eq]; exact ha
        have hk₁' : S₁.gates.card < k₁ := Nat.lt_of_lt_of_le hlt hk₁
        let k₂' := if hne : S₁.gates.Nonempty then S₁.auxIn (S₁.gates.min' hne) else 0
        obtain ⟨S', hstep⟩ := ih₁ S₁.gates.card hk₁' k₂' hprep.valid ha₁ le_rfl fun hne => by
          dsimp only [k₂']
          rw [dite_eq_left hne]
        exact ⟨S', Step.of_preparation hprep hstep⟩
      · rcases hS.step_or_normal hf ha hmov with hstep | hN
        · exact hstep
        · have hne := hS.exists_gate_of_normal hf ha hN
          let G := S.gates.min' hne
          obtain ⟨hG, hmin⟩ := hS.minGate_reads hne
          have hk₂G := hk₂ hne
          by_cases hpos : 0 < S.auxIn G
          · obtain ⟨S₁, hprep, hgates, hlt⟩ := hS.preparation_swap_auxIn hN hne hpos
            have ha₁ : d < S₁.a := by rw [hprep.a_eq]; exact ha
            have hk₁' : S₁.gates.card ≤ k₁ := by rw [hgates]; exact hk₁
            have hk₂' : S₁.auxIn G < k₂ := Nat.lt_of_lt_of_le hlt hk₂G
            obtain ⟨S', hstep⟩ := ih₂ (S₁.auxIn G) hk₂' hprep.valid ha₁ hk₁' fun hne₁ => by
              have hmin_eq : S₁.gates.min' hne₁ = G := by
                simp only [G, hgates]
              rw [hmin_eq]
            exact ⟨S', Step.of_preparation hprep hstep⟩
          · have haux0 : S.auxIn G = 0 := by omega
            have hnotaff : ¬ IsAffineOp (S.gate G).op := fun haff =>
              hmov ⟨G, hG, haff, hmin⟩
            obtain ⟨t₁, t₂, htne, hGt₁, hGt₂⟩ := hN.two_reads_of_gate hG
            have hnot_aux : ∀ t, (S.gate G).Reads t → t ∉ S.aux := by
              intro t ht hta
              rcases ht with hl | hr
              · have h1 : S.auxArg (S.gate G).left = 1 := by simp [auxArg, hl, hta]
                unfold auxIn at haux0
                omega
              · have h2 : S.auxArg (S.gate G).right = 1 := by simp [auxArg, hr, hta]
                unfold auxIn at haux0
                omega
            have hmem_par : ∀ t, (S.gate G).Reads t → t ∈ S.params := fun t ht => by
              have hlive := hS.wf.reads_live G hG t ht
              simp only [SemiCircuit.live, Finset.mem_union] at hlive
              rcases hlive with (hp | ha) | hg
              · exact hp
              · exact absurd ha (hnot_aux t ht)
              · exact absurd hg (hmin t ht)
            exact hS.step_of_pairCreation hf ha hN hG hnotaff htne hGt₁ hGt₂
              (hmem_par t₁ hGt₁) (hmem_par t₂ hGt₂)

/-- Lemma 4.2 (label per issue `#4322`, unverified against [MishraSanthanam2027]): if `S` is a
valid state for a `d`-affine disperser `f` and `d < S.a`, then there is a valid step from `S`
strictly reducing `m + s` with `Δa ∈ {0, -1, -2}` and `ΔW ≤ 10 Δa`. -/
theorem Valid.exists_step {S : State n} {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) : ∃ S', Step f S S' :=
  let k₂ := if hne : S.gates.Nonempty then S.auxIn (S.gates.min' hne) else 0
  hS.exists_step_aux hf S.gates.card k₂ ha le_rfl fun hne => by
    dsimp only [k₂]
    rw [dite_eq_left hne]

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
